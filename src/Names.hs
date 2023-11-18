{-# LANGUAGE BlockArguments #-}
module Names
  ( Which(..)
  , annotateExpWith
  , annotatePatWithAllUnQual
  , combine
  , new
  , replaceFree
  , stripPrelude
  ) where

import Data.Set (Set)
import qualified Data.Set as Set

import qualified Language.Haskell.Exts as HSE

import qualified Exprs

combine :: HSE.Name () -> HSE.Name () -> HSE.Name ()
combine (HSE.Ident () i1) (HSE.Ident () i2) = HSE.Ident () (i1 ++ i2)
combine (HSE.Symbol () s1) (HSE.Symbol () s2) = HSE.Symbol () (s1 ++ s2)
combine (HSE.Ident () i) (HSE.Symbol () _) = HSE.Ident () i
combine (HSE.Symbol () _) (HSE.Ident () i) = HSE.Ident () i

new :: HSE.Name () -> Set (HSE.Name ()) -> HSE.Name ()
new base avoid = try 0
  where
    try n
      | Set.member attempt avoid = try (n + 1)
      | otherwise = attempt
      where
        attempt = case base of
          HSE.Ident () i -> HSE.Ident () (i ++ show n)
          HSE.Symbol () i -> HSE.Symbol () (i ++ replicate n '!')

data Which
  = AllUnQual
  | FreeUnQual
  | Bound

annotateExpWith :: Which -> HSE.Exp () -> HSE.Exp (Set (HSE.Name ()))
annotateExpWith = annExp Set.empty

annotatePatWithAllUnQual :: HSE.Pat () -> HSE.Pat (Set (HSE.Name ()))
annotatePatWithAllUnQual = annPat

annExp :: Set (HSE.Name ()) -> Which -> HSE.Exp () -> HSE.Exp (Set (HSE.Name ()))
annExp bound which (HSE.Var () q) = HSE.Var =<< HSE.ann $ annQName bound which q
annExp bound which (HSE.App () f x) = HSE.App newAnn af ax
  where
    af = annExp bound which f
    ax = annExp bound which x
    newAnn = annSubs bound which [HSE.ann af, HSE.ann ax]
annExp bound which (HSE.Lambda () ps body) = HSE.Lambda newAnn aps abody
  where
    aps = map annPat ps
    patnames = foldMap HSE.ann aps
    abody = annExp (Set.union bound patnames) which body
    newAnn = case which of
      AllUnQual -> Set.union patnames (HSE.ann abody)
      FreeUnQual -> HSE.ann abody Set.\\ patnames
      Bound -> bound
annExp bound which (HSE.Paren () e) = HSE.Paren =<< HSE.ann $ annExp bound which e
annExp bound which (HSE.InfixApp () e1 qop e2) = HSE.InfixApp newAnn ae1 aop ae2
  where
    ae1 = annExp bound which e1
    aop = annQOp bound which qop
    ae2 = annExp bound which e2
    newAnn = annSubs bound which [HSE.ann ae1, HSE.ann aop, HSE.ann ae2]
annExp bound which (HSE.LeftSection () e qop) = HSE.LeftSection newAnn ae aop
  where
    ae = annExp bound which e
    aop = annQOp bound which qop
    newAnn = annSubs bound which [HSE.ann ae, HSE.ann aop]
annExp bound which (HSE.RightSection () qop e) = HSE.RightSection newAnn aop ae
  where
    aop = annQOp bound which qop
    ae = annExp bound which e
    newAnn = annSubs bound which [HSE.ann aop, HSE.ann ae]
annExp _ _ e = error $ "annExp: unhandled " ++ show e

annSubs :: Set (HSE.Name ()) -> Which -> [Set (HSE.Name ())] -> Set (HSE.Name ())
annSubs bound Bound _ = bound
annSubs _ _ subs = Set.unions subs

annQName :: Set (HSE.Name ()) -> Which -> HSE.QName () -> HSE.QName (Set (HSE.Name ()))
annQName bound Bound q = bound <$ q
annQName _ _ q@(HSE.UnQual () n) = Set.singleton n <$ q
annQName _ _ q = Set.empty <$ q

annQOp :: Set (HSE.Name ()) -> Which -> HSE.QOp () -> HSE.QOp (Set (HSE.Name ()))
annQOp bound which (HSE.QVarOp () q) = HSE.QVarOp =<< HSE.ann $ annQName bound which q
annQOp bound which (HSE.QConOp () q) = HSE.QConOp =<< HSE.ann $ annQName bound which q

annPat :: HSE.Pat () -> HSE.Pat (Set (HSE.Name ()))
annPat p@(HSE.PVar () n) = Set.singleton n <$ p
annPat (HSE.PParen () p) = HSE.PParen (HSE.ann ap) ap
  where
    ap = annPat p
annPat (HSE.PTuple () boxed ps) = HSE.PTuple (foldMap HSE.ann aps) boxed aps
  where
    aps = map annPat ps
annPat p = error $ "annPat: unhandled " ++ show p

stripPrelude :: HSE.Exp () -> HSE.Exp ()
stripPrelude = (() <$) . strip . annotateExpWith Bound
  where
    stripQName (HSE.Qual bound m n)
      | (() <$ m) == Exprs.prelude && not (Set.member (() <$ n) bound)
        = HSE.UnQual bound n
    stripQName q = q
    stripQOp (HSE.QVarOp bound q) = HSE.QVarOp bound (stripQName q)
    stripQOp (HSE.QConOp bound q) = HSE.QConOp bound (stripQName q)
    strip :: HSE.Exp (Set (HSE.Name ())) -> HSE.Exp (Set (HSE.Name ()))
    strip (HSE.Var bound q) = HSE.Var bound (stripQName q)
    strip (HSE.App bound f x) = HSE.App bound (strip f) (strip x)
    strip (HSE.Lambda bound ps body) = HSE.Lambda bound ps (strip body)
    strip (HSE.Paren bound contents) = HSE.Paren bound (strip contents)
    strip (HSE.InfixApp bound e1 qop e2) =
      HSE.InfixApp bound
        (strip e1)
        (stripQOp qop)
        (strip e2)
    strip (HSE.RightSection bound qop e) =
      HSE.RightSection bound (stripQOp qop) (strip e)
    strip (HSE.LeftSection bound e qop) =
      HSE.LeftSection bound (strip e) (stripQOp qop)
    strip e = error $ "stripPrelude: unhandled " ++ show e

replaceFree :: HSE.Name () -> HSE.Exp () -> HSE.Exp () -> HSE.Exp ()
replaceFree n with = replaceIn . annotateExpWith FreeUnQual
  where
    replaceIn (HSE.Var _ (HSE.UnQual _ vn))
      | (() <$ vn) == n = with
    replaceIn v@(HSE.Var _ _) = () <$ v
    replaceIn (HSE.App _ f x)
      = HSE.App ()
          (replaceIn f)
          (replaceIn x)
    replaceIn (HSE.InfixApp _ l op r) =
      replaceInInfix (Just l) op (Just r)
    replaceIn (HSE.LeftSection _ l op) =
      replaceInInfix (Just l) op Nothing
    replaceIn (HSE.RightSection _ op r) =
      replaceInInfix Nothing op (Just r)
    replaceIn l@(HSE.Lambda free ps body)
      | Set.member n free = HSE.Lambda () (map (() <$) ps) (replaceIn body)
      | otherwise = () <$ l
    replaceIn (HSE.Paren _ e) = HSE.Paren () (replaceIn e)
    replaceIn e = error $ "replaceIn: unhandled " ++ show e
    replaceInInfix ml op mr
      | Set.member n (HSE.ann op) =
        Exprs.infixAsPrefix
          (replaceIn <$> ml)
          with
          (replaceIn <$> mr)
      | otherwise =
        Exprs.infixOrSection
          (replaceIn <$> ml)
          (() <$ op)
          (replaceIn <$> mr)
