{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TupleSections #-}
module Pointfree (pointfreeSteps, pointfree) where

import Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.List.NonEmpty as NE
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set

import qualified Language.Haskell.Exts as HSE

import qualified Names
import qualified Exprs

data PointExp l
  = Lambda l (HSE.Pat l) (HSE.Exp l)

data PointInContext l = PointInContext
  { pointExp :: PointExp l
  , restore :: Maybe (HSE.Exp l -> HSE.Exp l)
  }

noContext :: PointExp l -> PointInContext l
noContext pointExp = PointInContext { pointExp, restore = Nothing }

addRestore :: (HSE.Exp l -> HSE.Exp l) -> PointInContext l -> PointInContext l
addRestore f p@PointInContext{ restore } =
  p{ restore = Just $ f . fromMaybe id restore }

pointfreeSteps :: HSE.Exp () -> [HSE.Exp ()]
pointfreeSteps e =
  -- findPoints finds things from the outside in, but typically we want the
  -- inside out
  case reverse (findPoints e) of
    [] -> []
    inner : _ ->
      let next = eliminatePoint inner
      in
      -- restarts the point-finding process from scratch every time
      -- seems fine since we're usually running on small inputs
      next : pointfreeSteps next

pointfree :: HSE.Exp () -> HSE.Exp ()
pointfree e = NE.last (e :| pointfreeSteps e)

eliminatePoint :: PointInContext () -> HSE.Exp ()
eliminatePoint PointInContext{ pointExp = Lambda () p b, restore } =
  -- until we've applied 'restore', we don't know all the names that are bound
  -- in the expression, so we can't do 'Names.stripPrelude'
  Names.stripPrelude . fromMaybe id restore . uncurry unapply $ simplifyPat p b

findPoints :: HSE.Exp () -> [PointInContext ()]
findPoints (HSE.Lambda () [] body) = findPoints body
findPoints (HSE.Lambda () (pat : pats) body) =
  noContext (Lambda () pat (Exprs.lambda pats body))
  : map (addRestore (Exprs.lambda [pat])) (findPoints (Exprs.lambda pats body))
findPoints (HSE.App () f x) =
  concat
    [ map (addRestore (\y -> Exprs.app f y)) (findPoints x)
    , map (addRestore (\g -> Exprs.app g x)) (findPoints f)
    ]
findPoints e@(HSE.Paren () _) = go id e
  where
    -- this nonsense is so that we keep parens that are already in the
    -- expr, but we don't keep them if we replace the expr with something else
    go k (HSE.Paren () inner) = go (k . HSE.Paren ()) inner
    go k other = map (addParens k) (findPoints other)
    addParens k p@PointInContext{ restore }
      -- the only place we treat Nothing differently from Just id
      = p{ restore = fmap (k .) restore }
findPoints _ = []

-- | convert a lambda away from using complex patterns, i.e. given P and E, try
-- to find a name N and expr X such that @\\N -> X@ is equivalent to @\\P -> E@
simplifyPat :: HSE.Pat () -> HSE.Exp () -> (HSE.Name (), HSE.Exp ())
simplifyPat topP topE =
  simplifyAnnPat Set.empty
    (Names.annotatePatWithAllUnQual topP)
    (Names.annotateExpWith Names.AllUnQual topE)
  where
    simplifyAnnPat
      :: Set (HSE.Name ())
      -> HSE.Pat (Set (HSE.Name ()))
      -> HSE.Exp (Set (HSE.Name ()))
      -> (HSE.Name (), HSE.Exp ())
    simplifyAnnPat _ (HSE.PVar _ n) e = (() <$ n, () <$ e)
    simplifyAnnPat avoid (HSE.PTuple names HSE.Boxed [p1, p2]) e =
      let
        newAvoid = Set.union avoid names
        (n1, e1) = simplifyAnnPat newAvoid p1 e
        (n2, e2) =
          -- this is sad; we basically drop the annotations and then recompute them
          simplifyAnnPat newAvoid p2
          $ Names.annotateExpWith Names.AllUnQual e1
        tupleName = Names.new (Names.combine n1 n2) newAvoid
        tupleExp = HSE.Var () (HSE.UnQual () tupleName)
        finalExp =
          Names.replaceFree n1 (Exprs.app Exprs.fst tupleExp)
          $ Names.replaceFree n2 (Exprs.app Exprs.snd tupleExp)
          $ e2
      in
      (tupleName, finalExp)
    simplifyAnnPat avoid (HSE.PParen _ p) e = simplifyAnnPat avoid p e
    simplifyAnnPat _ p _ = error $ "simplifyAnnPat: unhandled " <> show p

data SpecialCaseExp
  = Const (HSE.Exp ())
  | Id
  | Other (HSE.Exp ())

-- app (unapply n e) n -> e
unapply :: HSE.Name () -> HSE.Exp () -> HSE.Exp ()
unapply n = unSpecial . unapp
  where
    unSpecial (Const r) = Exprs.app Exprs.const r
    unSpecial Id = Exprs.id
    unSpecial (Other r) = r
    -- after this, I don't like pattern-matching on Other because it makes it
    -- harder to add special cases, this makes patterns easier to spot
    other = Other
    compose Id e = e
    compose e Id = e
    compose e1 e2 =
      other $ HSE.InfixApp () (unSpecial e1) Exprs.compose (unSpecial e2)
    unapp whole@(HSE.Var () q)
      | q == HSE.UnQual () n = Id
      | otherwise = Const whole
    unapp whole@(HSE.App () f x) =
      case (unapp f, unapp x) of
        (Const _, Const _) -> Const whole
        (Const _, Id) -> other f
        (Const _, ox) -> compose (other f) ox
        (Id, Const _) -> other (HSE.RightSection () Exprs.dollar x)
        (of_, Const _) -> other (Exprs.apps Exprs.flip [unSpecial of_, x])
        (of_, Id) -> other (Exprs.app Exprs.join (unSpecial of_))
        (of_, ox) ->
          other $ Exprs.apps Exprs.ap [unSpecial of_, unSpecial ox]
    unapp whole@(HSE.InfixApp () l op r) =
      unInfixApp whole (Just l) op (Just r)
    unapp whole@(HSE.LeftSection () l op) =
      unInfixApp whole (Just l) op Nothing
    unapp whole@(HSE.RightSection () op r) =
      unInfixApp whole Nothing op (Just r)
    unapp (HSE.Lambda () [] body) = unapp body
    unapp whole@(HSE.Lambda () (p : ps) body)
      | Set.member n boundNames = Const whole
      | otherwise =
          case unapp (Exprs.lambda ps body) of
            Const _ -> Const whole
            ob -> other
              $ Exprs.app Exprs.flip
              $ Exprs.lambda [p] (unSpecial ob)
      where
        boundNames = foldMap (HSE.ann . Names.annotatePatWithAllUnQual) (p : ps)
    unapp (HSE.Paren () e) = unapp e
    unapp e = error $ "unapp: unhandled " <> show e

    -- we don't use this function with both ml and mr being Nothing, since that
    -- would be a "two-sided section", but we try to return a right-ish answer
    -- there anyway
    unInfixApp whole ml op mr
      | opName == HSE.UnQual () n =
          asPrefixApp
      | otherwise =
          case (unapp <$> ml, unapp <$> mr) of
            (Nothing, Nothing) -> Const whole -- two-sided section
            (Nothing, Just (Const _)) -> Const whole
            (Just (Const _), Nothing) -> Const whole
            (Just (Const _), Just (Const _)) -> Const whole
            (Just (Const l), Just or_) ->
              compose (other (HSE.LeftSection () l op)) or_
            (Just ol, Just (Const r)) ->
              compose (other (HSE.RightSection () op r)) ol
            _ -> asPrefixApp
      where
        opName =
          case op of
            HSE.QVarOp () qn -> qn
            HSE.QConOp () qn -> qn
        asPrefixApp =
          unapp (Exprs.infixAsPrefix ml (Exprs.qopAlone op) mr)
