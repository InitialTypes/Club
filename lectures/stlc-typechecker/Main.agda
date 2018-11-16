
module Main where

open import Prelude
open import System.File
open import System.FilePath

open import Type
open import TypeCheck
open import Term
open import Term.Show
open import Term.Eval

showVal : ∀ {a} → Value a → String
showVal {a = nat} v = show v
showVal _ = "<function>"

main : IO ⊤
main = do
  prog          ← getProgName
  file ∷ args   ← getArgs
    where _ → putStrLn $ "Usage: " & prog & " FILE ARGS"
  right (a , t) ← flip checkStrings args <$> readTextFile (relative file)
    where left err → putStrLn $ "Error: " & err
  putStrLn $ "Type: " & show a &
           "\nTerm: " & show t &
           "\nVal:  " & showVal (eval t [])
