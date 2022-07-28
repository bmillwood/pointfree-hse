module Exprs where

import qualified Language.Haskell.Exts as HSE

var n = HSE.Var () (HSE.UnQual () (HSE.Ident () n))

id = var "id"
const = var "const"
