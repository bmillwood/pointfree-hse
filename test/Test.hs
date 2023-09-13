module Main (main) where

import Control.Exception

import qualified Language.Haskell.Exts as HSE

import Pointfree

showExp :: HSE.Exp () -> String
showExp = HSE.prettyPrint
--showExp = show

test :: (String, String) -> IO ()
test (input, expected) =
  case (parse input, parse expected) of
    (HSE.ParseOk inpE, HSE.ParseOk expE) ->
      handle
        (\e -> error $ show (input, expected, (e :: SomeException)))
        $ do
        let actual = pointfree inpE
        if actual == expE
        then pure ()
        else
          error $ unlines
            [ input
            , " -> " ++ (showExp actual)
            , " /= " ++ (showExp expE)
            ]
    (inpR, expR) -> error $ unlines
      [ "parse failure"
      , input
      , " -> " ++ show inpR
      , expected
      , " -> " ++ show expR
      ]
  where
    parse = fmap (fmap (const ())) . HSE.parseExp

main :: IO ()
main = mapM_ test
  -- identity cases
  [ ( "y", "y" )

  -- lambdas with variable body
  , ( "\\x -> x", "id"      )
  , ( "\\x -> y", "const y" )

  -- reaching inside apps
  , ( "f (\\x -> x)", "f id" )

  -- parens
  , ( "(f (\\x -> x))", "(f id)" )
  , ( "\\(x) -> x",     "id"     )

  -- lambdas with application body
  , ( "\\x -> f y"      , "const (f y)" )
  , ( "\\x -> f x"      , "f"           )
  , ( "\\x -> f (g x)"  , "f . g"       )
  , ( "\\x -> x y"      , "($ y)"       )
  , ( "\\x -> x x"      , "ap id id"    ) -- nb. wouldn't typecheck
  , ( "\\x -> x (g x)"  , "ap id g"     )
  , ( "\\x -> f x y"    , "flip f y"    )
  , ( "\\x -> f x x"    , "join f"      )
  , ( "\\x -> f x (g x)", "ap f g"      )

  -- lambdas with lambda body
  , ( "\\x y -> f x", "const . f" )

  -- name confusion
  , ( "\\const y -> x", "const (const x)" )

  -- tuples
  , ( "\\(x, y) -> x",   "fst"        )
  , ( "\\(x, y) -> x y", "ap fst snd" )
  ]
