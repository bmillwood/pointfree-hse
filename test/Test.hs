module Main (main) where

import qualified Language.Haskell.Exts as HSE

import Pointfree

test :: String -> String -> IO ()
test inp exp =
  case (parse inp, parse exp) of
    (HSE.ParseOk inpE, HSE.ParseOk expE) ->
        if actual == expE
        then pure ()
        else
          error $ unlines
            [ inp
            , " -> " ++ (HSE.prettyPrint actual)
            , " /= " ++ exp
            ]
      where
        actual = pointfree inpE
  where
    parse = fmap (fmap (const ())) . HSE.parseExp

main :: IO ()
main = do
  test "id" "id"
  test "\\x -> x" "id"
  test "\\x -> y" "const y"
  test "\\x -> \\y -> y" "const id"
