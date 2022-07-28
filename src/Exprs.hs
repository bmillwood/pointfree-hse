module Exprs where

import qualified Language.Haskell.Exts as HSE

varI i = HSE.Var () (HSE.UnQual () (HSE.Ident () i))
id = varI "id"
const = varI "const"
ap = varI "ap"
flip = varI "flip"
join = varI "join"

opS s = HSE.QVarOp () (HSE.UnQual () (HSE.Symbol () s))
compose = opS "."
dollar = opS "$"

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
