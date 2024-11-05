{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Nat using (Nat ; _==_ ; zero ; suc ; _+_ ; _<_ ; _-_ ; _*_)
open import Data.Nat using (_%_ ; _≤_ ; NonZero ; _^_ ; _>_ ; 
                            compare ; less ; greater ; equal ; _/_ ; s<s ; z<s)
open import Data.Nat.Show
open import Data.Bool using (Bool ; true ; false ; if_then_else_ ; _∧_)
open import Data.List using (List ; [] ; _∷_ ; find)
open import Data.Vec as Vec using (filter ; length ; allFin ; map ; count ; foldl′ ; sum)
open import Data.Vec.Bounded.Base using (toVec)
open import Function.Base using (_$_)
open import Relation.Unary using (Decidable)
open import Relation.Binary using (DecidableEquality)
open import Relation.Nullary using (yes ; no)
open import Relation.Binary.PropositionalEquality.Core using (refl)
open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)
open import Codata.Guarded.Stream
open import IO.Primitive.Finite using (putStrLn)
open import Data.Fin using (Fin ; toℕ ; fromℕ<)

open import date

module prob19 where


1Jan1901 : Date
1Jan1901 = 1901 , month.Apr , 1

31Dec2000 : Date
31Dec2000 = 2000 , month.Dec , 31

isSunday : day.Day → Bool
isSunday day.Sun = true
isSunday _ = false

{-# NON_TERMINATING #-}
recursiveAlgorithm : Nat
recursiveAlgorithm = recursiveAlgorithmHelper 1Jan1901 31Dec2000
    where    
        recursiveAlgorithmHelper : Date → Date → Nat
        recursiveAlgorithmHelper start@(_ , _ , startDay) end = 
            if start >ᵇ-Date end 
            then 0
            else if (isSunday $ dayOfWeek start) ∧ (startDay == 1)
                then 1 + recursiveAlgorithmHelper (start +1D) end
                else recursiveAlgorithmHelper (start +1D) end

{-# NON_TERMINATING #-}
tailRecursiveAlgorithm : Nat
tailRecursiveAlgorithm = tailRecursiveAlgorithmHelper 1Jan1901 31Dec2000 0
    where
        tailRecursiveAlgorithmHelper : Date → Date → Nat → Nat
        tailRecursiveAlgorithmHelper start@(_ , _ , startDay) end acc = 
            if start >ᵇ-Date end 
            then acc
            else if (isSunday $ dayOfWeek start) ∧ (startDay == 1)
                then tailRecursiveAlgorithmHelper (start +1D) end (suc acc)
                else tailRecursiveAlgorithmHelper (start +1D) end acc

streamAlgorithm : Nat
streamAlgorithm = 
    foldl′ (λ acc _ → suc acc) 0                                   $ 
    toVec                                                          $ 
    filter (λ e → dayOfWeek e day.≟ day.Sun)                       $ 
    take (monthsBetween 1Jan1901 31Dec2000) (iterate _+1M 1Jan1901)

mapAlgorithm : Nat
mapAlgorithm = sum $ Vec.map (λ e → if isSunday $ dayOfWeek e then 1 else 0) $ Vec.map (λ m → 1Jan1901 +-months toℕ m) $ allFin $ monthsBetween 1Jan1901 31Dec2000
