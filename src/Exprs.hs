module Exprs where

import Data.Foldable (toList)
import Prelude hiding (flip)

import qualified Language.Haskell.Exts as HSE

prelude :: HSE.ModuleName ()
prelude = HSE.ModuleName () "Prelude"

preludeI :: String -> HSE.Exp ()
preludeI i = HSE.Var () (HSE.Qual () prelude (HSE.Ident () i))

id, const, ap, flip, join, liftA2 :: HSE.Exp ()
id = preludeI "id"
const = preludeI "const"
ap = preludeI "ap"
flip = preludeI "flip"
join = preludeI "join"
liftA2 = preludeI "liftA2"
fst, snd :: HSE.Exp ()
fst = preludeI "fst"
snd = preludeI "snd"

preludeS :: String -> HSE.QOp ()
preludeS s = HSE.QVarOp () (HSE.Qual () prelude (HSE.Symbol () s))

compose, dollar :: HSE.QOp ()
compose = preludeS "."
dollar = preludeS "$"

lambda :: [HSE.Pat ()] -> HSE.Exp () -> HSE.Exp ()
lambda [] b = b
lambda ps1 (HSE.Lambda () ps2 b) = HSE.Lambda () (ps1 ++ ps2) b
lambda ps b = HSE.Lambda () ps b

app :: HSE.Exp () -> HSE.Exp () -> HSE.Exp ()
app f x@(HSE.App () _ _) = HSE.App () f (HSE.Paren () x)
app f x@(HSE.Lambda () _ _) = HSE.App () f (HSE.Paren () x)
app f x = HSE.App () f x

apps :: HSE.Exp () -> [HSE.Exp ()] -> HSE.Exp ()
apps = foldl app

qopAlone :: HSE.QOp () -> HSE.Exp ()
qopAlone (HSE.QVarOp () qn) = HSE.Var () qn
qopAlone (HSE.QConOp () qn) = HSE.Con () qn

infixAsPrefix :: Maybe (HSE.Exp ()) -> HSE.Exp () -> Maybe (HSE.Exp ()) -> HSE.Exp ()
infixAsPrefix ml op mr =
  case (ml, mr) of
    (Nothing, Nothing) -> op
    (Nothing, Just r) -> apps flip [op, r]
    (Just l, _) -> apps op (l : toList mr)

infixOrSection :: Maybe (HSE.Exp ()) -> HSE.QOp () -> Maybe (HSE.Exp ()) -> HSE.Exp ()
infixOrSection Nothing op Nothing = qopAlone op
infixOrSection (Just l) op Nothing = HSE.LeftSection () l op
infixOrSection Nothing op (Just r) = HSE.RightSection () op r
infixOrSection (Just l) op (Just r) = HSE.InfixApp () l op r
