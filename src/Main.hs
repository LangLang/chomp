module Main( main ) where

{-                               DOCUMENTATION                              -}
{-
    Chomp: A brave new LangLang compiler
-}

{-                                 MODULES                                  -}
-- Driver
import Driver

{-                              IMPLEMENTATION                              -}

main :: IO ()
main =
  putStrLn "Chomp v0.0.1 for LangLang"
  >> driverMain

