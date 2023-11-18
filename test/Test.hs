module Main (main) where

import Control.Exception
import Data.Foldable (traverse_)

import qualified Language.Haskell.Exts as HSE

import qualified Names
import Pointfree

showExp :: HSE.Exp () -> String
showExp = HSE.prettyPrint
--showExp = show

parseExp_ :: String -> HSE.ParseResult (HSE.Exp ())
parseExp_ = fmap (fmap (const ())) . HSE.parseExp

test :: (HSE.Exp () -> HSE.Exp ()) -> (String, String) -> IO ()
test f (input, expected) =
  case (parseExp_ input, parseExp_ expected) of
    (HSE.ParseOk inpE, HSE.ParseOk expE) ->
      handle
        (\e -> error $ show (input, expected, (e :: SomeException)))
        $ do
        let actual = f inpE
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

pointfreeCases :: [(String, String)]
pointfreeCases =
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
  , ( "\\x -> f y"        , "const (f y)" )
  , ( "\\x -> f x"        , "f"           )
  , ( "\\x -> f (g x)"    , "f . g"       )
  , ( "\\x -> f (g (h x))", "f . g . h"   )
  , ( "\\x -> x y"        , "($ y)"       )
  , ( "\\x -> x (g x)"    , "ap id g"     )
  , ( "\\x -> f x y"      , "flip f y"    )
  , ( "\\x -> f x x"      , "join f"      )
  , ( "\\x -> f x (g x)"  , "ap f g"      )

  -- infix application
  , ( "\\x -> y + x"  , "(y +)"     )
  , ( "\\x -> x + y"  , "(+ y)"     )
  , ( "\\x y -> x + y", "(+)"       )
  , ( "\\x y -> y + x", "flip (+)"  )
  , ( "\\x -> x + x"  , "join (+)"  )
  , ( "\\x -> x + f x", "ap (+) f"  )
  , ( "\\x -> f x + y", "(+ y) . f" )
  , ( "\\x -> y + f x", "(y +) . f" )

  -- lambdas with lambda body
  , ( "\\x y -> f x", "const . f" )

  -- name confusion
  , ( "\\const y -> x", "const (const x)" )
  , ( "\\y const -> x", "const (const x)" )

  -- tuples
  , ( "\\(x, y) -> x",     "fst"                )
  , ( "\\(x, y) -> x y",   "ap fst snd"         )
  ]

testReplaceFree :: HSE.Exp () -> HSE.Exp ()
testReplaceFree =
  Names.replaceFree
    (HSE.Ident () "n")
    (HSE.Con () (HSE.UnQual () (HSE.Ident () "E")))

replaceFreeCases :: [(String, String)]
replaceFreeCases =
  [ ("n", "E")
  , ("x", "x")
  , ("\\x -> n", "\\x -> E")
  , ("\\n -> n", "\\n -> n")
  ]

-- These aren't really tests so much as examples. But you can look at them with
-- your eyeballs.
writeSteps :: (String, String) -> IO ()
writeSteps (fp, start) =
  case parseExp_ start of
    r@HSE.ParseFailed{} ->
      error (show r)
    HSE.ParseOk startE ->
      writeFile ("test/output/" <> fp <> ".txt")
        $ unlines . map showExp $ startE : pointfreeSteps startE

stepGerms :: [(String, String)]
stepGerms =
  [ ("dots", "\\a b c d -> a (b (c d))")
  , ("flips", "\\a b c d -> d c b a")
  ]

main :: IO ()
main = do
  traverse_ (test pointfree) pointfreeCases
  traverse_ (test testReplaceFree) replaceFreeCases
  traverse_ writeSteps stepGerms
