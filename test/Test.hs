module Main (main) where

import qualified Language.Haskell.Exts as HSE

import Pointfree

showExp :: HSE.Exp () -> String
showExp = show

test :: String -> String -> IO ()
test inp exp =
  case (parse inp, parse exp) of
    (HSE.ParseOk inpE, HSE.ParseOk expE) ->
        if actual == expE
        then pure ()
        else
          error $ unlines
            [ inp
            , " -> " ++ (showExp actual)
            , " /= " ++ (showExp expE)
            ]
      where
        actual = pointfree inpE
  where
    parse = fmap (fmap (const ())) . HSE.parseExp

main :: IO ()
main = do
  test "y" "y"

  test "\\x -> x" "id"
  test "\\x -> y" "const y"

  test "\\x y -> y" "const id"

  test "\\x -> f y"       "const (f y)"
  test "\\x -> f x"       "f"
  test "\\x -> f (g x)"   "f . g"
  test "\\x -> x y"       "($ y)"
  test "\\x -> x x"       "ap id id"
  test "\\x -> x (g x)"   "ap id g"
  test "\\x -> f x y"     "flip f y"
  test "\\x -> f x x"     "join f"
  test "\\x -> f x (g x)" "ap f g"
