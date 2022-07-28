{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE NamedFieldPuns #-}
module Pointfree (pointfree) where

import Data.Maybe (fromMaybe)

import qualified Language.Haskell.Exts as HSE

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

pointfree :: HSE.Exp () -> HSE.Exp ()
pointfree e = go (findPoints e)
  where
    go [] = e
    go (PointInContext{ pointExp = Lambda () p b, restore } : points) =
      case simplifyPat p b >>= uncurry unapply of
        Nothing -> go points
        Just f -> pointfree (fromMaybe id restore f)

findPoints :: HSE.Exp () -> [PointInContext ()]
findPoints (HSE.Lambda () [] body) = findPoints body
findPoints (HSE.Lambda () (pat : pats) body) =
  noContext (Lambda () pat (Exprs.lambda pats body))
  : map (addRestore (Exprs.lambda [pat])) (findPoints (Exprs.lambda pats body))
findPoints (HSE.App () f x) =
  concat
    [ map (addRestore (\f -> Exprs.app f x)) (findPoints f)
    , map (addRestore (\x -> Exprs.app f x)) (findPoints x)
    ]
findPoints (HSE.Paren () e) = go (HSE.Paren ()) e
  where
    -- this nonsense is so that we keep parens that are already in the
    -- expr, but we don't keep them if we replace the expr with something else
    go k (HSE.Paren () e) = go (k . HSE.Paren ()) e
    go k e = map (addParens k) (findPoints e)
    addParens k p@PointInContext{ restore }
      -- the only place we treat Nothing differently from Just id
      = p{ restore = fmap (k .) restore }
findPoints _ = []

pointedAt :: PointExp () -> HSE.Exp ()
pointedAt (Lambda () pat (HSE.Lambda () pats body)) = HSE.Lambda () (pat : pats) body
pointedAt (Lambda () pat body) = HSE.Lambda () [pat] body

simplifyPat :: HSE.Pat () -> HSE.Exp () -> Maybe (HSE.Name (), HSE.Exp ())
simplifyPat (HSE.PVar () n) e = Just (n, e)
simplifyPat _ _ = Nothing

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
        useAp f g = Other (Exprs.apps Exprs.ap [f, g])
    unapp (HSE.Paren () e) = unapp e
    unapp _ = Nothing
