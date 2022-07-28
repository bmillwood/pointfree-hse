{-# LANGUAGE BlockArguments #-}
module Pointfree (pointfree) where

import Data.Maybe (fromMaybe)

import qualified Language.Haskell.Exts as HSE

import qualified Exprs

data PointExp l
  = Lambda l (HSE.Pat l) (HSE.Exp l)

pointfree :: HSE.Exp () -> HSE.Exp ()
pointfree e = fromMaybe e do
  (Lambda l p b, restore) <- findPoint e
  (n, sb) <- simplifyPat p b
  f <- unapply n sb
  pure (pointfree (restore f))

findPoint :: HSE.Exp l -> Maybe (PointExp l, HSE.Exp l -> HSE.Exp l)
findPoint (HSE.Lambda la [] body) = fmap (fmap (fmap (HSE.Lambda la []))) (findPoint body)
findPoint (HSE.Lambda la [pat] body) = Just (Lambda la pat body, id)
findPoint (HSE.Lambda la (pat : pats) body)
  = Just (Lambda la pat (HSE.Lambda la pats body), id)
findPoint _ = Nothing

pointedAt :: PointExp l -> HSE.Exp l
pointedAt (Lambda l1 pat (HSE.Lambda l2 pats body)) = HSE.Lambda l1 (pat : pats) body
pointedAt (Lambda l pat body) = HSE.Lambda l [pat] body

simplifyPat :: HSE.Pat l -> HSE.Exp l -> Maybe (HSE.Name l, HSE.Exp l)
simplifyPat (HSE.PVar l n) e = Just (n, e)
simplifyPat _ _ = Nothing

-- app (unapply n e) n -> e
unapply :: HSE.Name () -> HSE.Exp () -> Maybe (HSE.Exp ())
unapply n (HSE.Var () q)
  | q == HSE.UnQual () n = Just Exprs.id
  | otherwise = Just (HSE.App () Exprs.const (HSE.Var () q))
unapply _ _ = Nothing
