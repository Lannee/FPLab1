{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Nat using (Nat ; _==_)
open import Data.List using (List ; [] ; _∷_ ; length)
open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_ ; _∧_)
open import Data.String.Base using (String ; unlines ; unwords ; _++_ ; lines ; _<+>_)
open import IO
open import Agda.Builtin.Unit using (⊤)
open import Function using (_$_)
open import System.Exit using (exitSuccess ; exitFailure ; isFailure ; die)

open import prob19

module prob19test where

Prob19CorrectResult : Nat
Prob19CorrectResult = 171

test : IO Bool
test = do
    let recursiveAlgorithmSucceed     = (prob19.recursiveAlgorithm) == Prob19CorrectResult
    putStrLn $ description recursiveAlgorithmSucceed     "Recursive method"

    let tailRecursiveAlgorithmSucceed = (prob19.recursiveAlgorithm) == Prob19CorrectResult
    putStrLn $ description tailRecursiveAlgorithmSucceed "Tail recursive method"

    let filterAlgorithmSucceed        = (prob19.recursiveAlgorithm) == Prob19CorrectResult
    putStrLn $ description filterAlgorithmSucceed        "Filter method"

    let mapAlgorithmSucceed           = (prob19.recursiveAlgorithm) == Prob19CorrectResult
    putStrLn $ description mapAlgorithmSucceed           "Map method"

    let streamAlgorithmSucceed        = (prob19.recursiveAlgorithm) == Prob19CorrectResult
    putStrLn $ description streamAlgorithmSucceed        "Stream method"

    let testSucceed = recursiveAlgorithmSucceed ∧ tailRecursiveAlgorithmSucceed ∧ filterAlgorithmSucceed ∧ mapAlgorithmSucceed ∧ streamAlgorithmSucceed
    if testSucceed then pure true else pure false

    where
        description : Bool → String → String
        description result methodName = methodName <+> (if result then "SUCCEED" else "FAILLED")

main : Main
main = run $ do
  putStrLn "PROB 19 TESTS:"
  successful ← test
  if successful then exitSuccess else exitFailure
