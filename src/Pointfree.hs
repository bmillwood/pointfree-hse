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

lambda :: [HSE.Pat ()] -> HSE.Exp () -> HSE.Exp ()
lambda [] b = b
lambda ps1 (HSE.Lambda () ps2 b) = HSE.Lambda () (ps1 ++ ps2) b
lambda ps b = HSE.Lambda () ps b

findPoints :: HSE.Exp () -> [(PointExp (), HSE.Exp () -> HSE.Exp ())]
findPoints (HSE.Lambda () [] body) = findPoints body
findPoints (HSE.Lambda () (pat : pats) body) =
  (Lambda () pat (lambda pats body), id)
  : map (fmap (lambda [pat] .)) (findPoints (lambda pats body))
findPoints _ = []

pointedAt :: PointExp () -> HSE.Exp ()
pointedAt (Lambda () pat (HSE.Lambda () pats body)) = HSE.Lambda () (pat : pats) body
pointedAt (Lambda () pat body) = HSE.Lambda () [pat] body

simplifyPat :: HSE.Pat () -> HSE.Exp () -> Maybe (HSE.Name (), HSE.Exp ())
simplifyPat (HSE.PVar () n) e = Just (n, e)
simplifyPat _ _ = Nothing

-- app (unapply n e) n -> e
unapply :: HSE.Name () -> HSE.Exp () -> Maybe (HSE.Exp ())
unapply n (HSE.Var () q)
  | q == HSE.UnQual () n = Just Exprs.id
  | otherwise = Just (HSE.App () Exprs.const (HSE.Var () q))
unapply _ _ = Nothing
