{-# LANGUAGE BlockArguments #-}
module Pointfree (pointfree) where

import Data.Maybe (fromMaybe)

import qualified Language.Haskell.Exts as HSE

import qualified Exprs

data PointExp l
  = Lambda l (HSE.Pat l) (HSE.Exp l)

pointfree :: HSE.Exp () -> HSE.Exp ()
pointfree e = go (findPoints e)
  where
    go [] = e
    go ((Lambda () p b, restore) : points) =
      case simplifyPat p b >>= uncurry unapply of
        Nothing -> go points
        Just f -> pointfree (restore f)

findPoints :: HSE.Exp () -> [(PointExp (), HSE.Exp () -> HSE.Exp ())]
findPoints (HSE.Lambda () [] body) = findPoints body
findPoints (HSE.Lambda () (pat : pats) body) =
  (Lambda () pat (Exprs.lambda pats body), id)
  : map (fmap (Exprs.lambda [pat] .)) (findPoints (Exprs.lambda pats body))
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
