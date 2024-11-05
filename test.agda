{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Nat using (Nat ; _==_)
open import Data.List using (List ; [] ; _∷_ ; length)
-- open import IO.Primitive.Finite using (putStrLn)
open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_ ; _∧_)
open import Data.String.Base using (String ; unlines ; unwords ; _++_ ; lines ; _<+>_)
-- open import Agda.Builtin.IO using (IO)
open import IO
open import Agda.Builtin.Unit using (⊤)
open import Function using (_$_)
open import System.Exit using (exitSuccess ; exitFailure ; isFailure ; die)

open import prob19
open import prob12

module test where

Prob12CorrectResult : Nat
Prob12CorrectResult = 76576500

Prob19CorrectResult : Nat
Prob19CorrectResult = 171


runProb19Test : IO Bool
runProb19Test = do
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

runProb12Test : IO Bool
runProb12Test = do
    let recursiveAlgorithmSucceed     = (findTringularNumber numberOfDivisorsRecursive     500) == Prob12CorrectResult
    putStrLn $ description recursiveAlgorithmSucceed     "Recursive method"

    let tailRecursiveAlgorithmSucceed = (findTringularNumber numberOfDivisorsTailRecursive 500) == Prob12CorrectResult
    putStrLn $ description tailRecursiveAlgorithmSucceed "Tail recursive method"

    let filterAlgorithmSucceed        = (findTringularNumber numberOfDivisorsFilter        500) == Prob12CorrectResult
    putStrLn $ description filterAlgorithmSucceed        "Filter method"

    let mapAlgorithmSucceed           = (findTringularNumber numberOfDivisorsMap           500) == Prob12CorrectResult
    putStrLn $ description mapAlgorithmSucceed           "Map method"

    let streamAlgorithmSucceed        = (findTringularNumber numberOfDivisorsStream        500) == Prob12CorrectResult
    putStrLn $ description streamAlgorithmSucceed        "Stream method"

    let testSucceed = recursiveAlgorithmSucceed ∧ tailRecursiveAlgorithmSucceed ∧ filterAlgorithmSucceed ∧ mapAlgorithmSucceed ∧ streamAlgorithmSucceed
    if testSucceed then pure true else pure false

    where
        description : Bool → String → String
        description result methodName = methodName <+> (if result then "SUCCEED" else "FAILLED")

main : Main
main = run $ do
  putStrLn "PROB 19 TESTS:"
  prob19successful ← runProb19Test
  -- putStrLn "\nPROB 19 TESTS " <+> (if prob19successful then "SUCCEED" else "FAILED" <+> " !")

  putStrLn "\nPROB 12 TESTS:"
  prob12successful ← runProb12Test
  -- putStrLn "\nPROB 12 TESTS " <+> (if prob12successful then "SUCCEED" else "FAILED" <+> " !")

  let successful = prob19successful ∧ prob12successful
  putStrLn (if successful then "\nALL TEST PASSED" else "\nSOME TESTS FAILED" <+> " !")
  if successful then exitSuccess else exitFailure
