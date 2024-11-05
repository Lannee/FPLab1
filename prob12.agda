{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Nat using (Nat ; _==_ ; zero ; suc ; _+_ ; _<_ ; _*_)
open import Data.Nat using (_%_ ; _≤_ ; NonZero ; _^_ ; _/_ ; _>?_)
open import Data.Nat.Show
open import Data.Fin as Fin using (toℕ ; suc ; zero)
open import Data.Bool using (Bool ; true ; false ; if_then_else_)
open import Data.List as List using (List ; [] ; _∷_ ; length ; filterᵇ ; find ; allFin ; map ; sum ; foldl)
open import Data.Vec as Vec using (map ; sum)
open import Function.Base using (_$_)
open import Relation.Unary using (Decidable)
open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import IO.Primitive.Finite using (putStrLn)
open import Agda.Builtin.String using (String)
open import Codata.Guarded.Stream as S using (Stream ; nats ; map ; head ; tail ; _∷_ ; _[_])
open import Data.Vec.Bounded using (toVec)
open import Relation.Unary using (Pred)
open import Agda.Primitive using (Level)
open import Codata.Guarded.Stream as Stream
open import Relation.Nullary.Decidable using (does)

module prob12 where

numberOfDivisorsFilter : Nat → Nat
numberOfDivisorsFilter n = foldl (λ acc _ → suc acc) 0 $ filterᵇ (λ {Fin.zero → false ; x@(Fin.suc _) → n % toℕ x == 0}) $ allFin (suc n)

numberOfDivisorsMap : Nat → Nat
numberOfDivisorsMap n = List.sum $ List.map (λ {Fin.zero → 0 ; x@(Fin.suc _) → if n % toℕ x == zero then 1 else 0}) $ allFin (suc n)

numberOfDivisorsStream : Nat → Nat
numberOfDivisorsStream n = Vec.sum $ Vec.map (λ {zero → 0 ; x@(suc _) → if n % x == zero then 1 else 0}) $ take (suc n) $ iterate suc 0

numberOfDivisorsRecursive : Nat → Nat
numberOfDivisorsRecursive zero = zero
numberOfDivisorsRecursive n@(suc n-1) = inner n n
    where 
        inner : (n : Nat) {{_ : NonZero n}} → Nat → Nat
        inner n zero = zero
        inner n div@(suc div-1) = (if n % div == 0 then 1 else 0) + inner n div-1

numberOfDivisorsTailRecursive : Nat → Nat
numberOfDivisorsTailRecursive zero = zero
numberOfDivisorsTailRecursive n@(suc n-1) = inner n n 0
    where 
        inner : (n : Nat) {{_ : NonZero n}} → Nat → Nat → Nat
        inner n zero acc = acc
        inner n div@(suc div-1) acc = inner n div-1 $ acc + (if n % div == 0 then 1 else 0)

triangleNumber : (n : Nat) .{{_ : NonZero n}} → Nat
triangleNumber n = (n * (suc n)) / 2


{-# NON_TERMINATING #-}
findTringularNumber : (Nat → Nat) → Nat → Nat
findTringularNumber countDivisors divisors = go 1
    where
        go : (n : Nat) .{{_ : NonZero n}} → Nat
        go n = 
            if divisors < (countDivisors (triangleNumber n))
            then triangleNumber n
            else go (suc n)
