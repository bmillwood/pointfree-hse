{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE NamedFieldPuns #-}
module Pointfree (pointfreeSteps, pointfree) where

import Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.List.NonEmpty as NE
import Data.Maybe (fromMaybe)
import Data.Monoid (First (First), getFirst)
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
  case getFirst $ foldMap (First . eliminatePoint) points of
    Nothing -> []
    Just next ->
      -- restarts the point-finding process from scratch every time
      -- seems fine since we're usually running on small inputs
      next : pointfreeSteps next
  where
    -- findPoints finds things from the outside in, but typically we want the
    -- inside out
    points = reverse (findPoints e)

pointfree :: HSE.Exp () -> HSE.Exp ()
pointfree e = NE.last (e :| pointfreeSteps e)

eliminatePoint :: PointInContext () -> Maybe (HSE.Exp ())
eliminatePoint PointInContext{ pointExp = Lambda () p b, restore } =
  case
    -- until we've applied 'restore', we don't know all the names that are bound
    -- in the expression, so we can't do 'Names.stripPrelude'
    Right . Names.stripPrelude . fromMaybe id restore
    =<< maybe (Left "unapply") Right . uncurry unapply
    =<< maybe (Left "simplifyPat") Right (simplifyPat p b)
  of
    Left _ -> Nothing
    Right e -> Just e

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
simplifyPat :: HSE.Pat () -> HSE.Exp () -> Maybe (HSE.Name (), HSE.Exp ())
simplifyPat topP topE =
  simplifyAnnPat Set.empty
    (Names.annotatePatWithAllUnQual topP)
    (Names.annotateExpWith Names.AllUnQual topE)
  where
    simplifyAnnPat
      :: Set (HSE.Name ())
      -> HSE.Pat (Set (HSE.Name ()))
      -> HSE.Exp (Set (HSE.Name ()))
      -> Maybe (HSE.Name (), HSE.Exp ())
    simplifyAnnPat _ (HSE.PVar _ n) e = Just (() <$ n, () <$ e)
    simplifyAnnPat avoid (HSE.PTuple names HSE.Boxed [p1, p2]) e = do
      let newAvoid = Set.union avoid names
      (n1, e1) <- simplifyAnnPat newAvoid p1 e
      (n2, e2) <-
        -- this is sad; we basically drop the annotations and then recompute them
        simplifyAnnPat newAvoid p2
        $ Names.annotateExpWith Names.AllUnQual e1
      let
        tupleName = Names.new (Names.combine n1 n2) newAvoid
        tupleExp = HSE.Var () (HSE.UnQual () tupleName)
        finalExp =
          Names.replaceFree n1 (Exprs.app Exprs.fst tupleExp)
          $ Names.replaceFree n2 (Exprs.app Exprs.snd tupleExp)
          $ e2
      Just (tupleName, finalExp)
    simplifyAnnPat avoid (HSE.PParen _ p) e = simplifyAnnPat avoid p e
    simplifyAnnPat _ _ _ = Nothing

data Unapply
  = Const (HSE.Exp ())
  | Id
  | Other (HSE.Exp ())

-- app (unapply n e) n -> e
unapply :: HSE.Name () -> HSE.Exp () -> Maybe (HSE.Exp ())
unapply n = fmap finalise . unapp
  where
    finalise (Const r) = Exprs.app Exprs.const r
    finalise Id = Exprs.id
    finalise (Other r) = r
    unapp e@(HSE.Var () q)
      | q == HSE.UnQual () n = Just Id
      | otherwise = Just (Const e)
    unapp (HSE.App () f x) = do
      uf <- unapp f
      ux <- unapp x
      pure $ case (uf, ux) of
        (Const cf, Const cx) -> Const (Exprs.app cf cx)
        (Const cf, Id) -> Other cf
        (Const cf, Other ox) -> Other (HSE.InfixApp () cf Exprs.compose ox)
        (Id, Const cx) -> Other (HSE.RightSection () Exprs.dollar cx)
        (Id, Id) -> useAp Exprs.id Exprs.id
        (Id, Other ox) -> useAp Exprs.id ox
        (Other of_, Const cx) -> Other (Exprs.apps Exprs.flip [of_, cx])
        (Other of_, Id) -> Other (Exprs.app Exprs.join of_)
        (Other of_, Other ox) -> useAp of_ ox
        where
          useAp af ag = Other (Exprs.apps Exprs.ap [af, ag])
    unapp (HSE.Lambda () [] body) = unapp body
    unapp l@(HSE.Lambda () (p : ps) body)
      | Set.member n boundNames = Just (Const l)
      | otherwise = do
          ub <- unapp (Exprs.lambda ps body)
          Just case ub of
            Const _ -> Const l
            Id -> useFlip Exprs.id
            Other ob -> useFlip ob
      where
        boundNames = foldMap (HSE.ann . Names.annotatePatWithAllUnQual) (p : ps)
        useFlip ob = Other (Exprs.app Exprs.flip (Exprs.lambda [p] ob))
    unapp (HSE.Paren () e) = unapp e
    unapp _ = Nothing
