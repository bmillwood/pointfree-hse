module Exprs where

import qualified Language.Haskell.Exts as HSE

prelude :: HSE.ModuleName ()
prelude = HSE.ModuleName () "Prelude"

preludeI :: String -> HSE.Exp ()
preludeI i = HSE.Var () (HSE.Qual () prelude (HSE.Ident () i))

id, const, ap, flip, join, fst, snd :: HSE.Exp ()
id = preludeI "id"
const = preludeI "const"
ap = preludeI "ap"
flip = preludeI "flip"
join = preludeI "join"
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
