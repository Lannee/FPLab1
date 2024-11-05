{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Nat using (Nat ; _==_ ; zero ; suc ; _+_ ; _<_ ; _*_ ; _-_)
open import Data.Nat using (_%_ ; _≤_ ; NonZero ; ≢-nonZero ; _^_ ; _/_ ; _>?_)
open import Data.Nat.Show
open import Data.Fin as Fin using (toℕ ; suc ; zero)
open import Data.Bool using (Bool ; true ; false ; if_then_else_)
open import Data.List as List using (List ; [] ; _∷_ ; length ; filterᵇ ; find ; allFin ; map ; sum ; foldl)
open import Data.Vec as Vec using (map ; sum)
open import Function.Base using (_$_ ; _∘_)
open import Relation.Unary using (Decidable)
open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import IO.Primitive.Finite using (putStrLn)
open import Agda.Builtin.String using (String)
open import Codata.Guarded.Stream as S using (Stream ; nats ; map ; head ; tail ; _∷_)
open import Data.Vec.Bounded using (toVec)
open import Relation.Unary using (Pred)
open import Agda.Primitive using (Level)
open import Codata.Guarded.Stream as Stream
open import Relation.Nullary.Decidable using (does)
open import Data.Float using (⌊_⌋ ; fromℕ ; sqrt)
open import Data.Integer using (∣_∣)
open import Data.Maybe using (just ; nothing)

module prob12 where

flooredSqrt : Nat → Nat 
flooredSqrt n with ⌊ sqrt $ fromℕ n ⌋
... | just i = ∣ i ∣
... | nothing = 0

range : Nat → List Nat
range zero = []
range n@(suc n-1) = n ∷ range n-1

numberOfDivisorsFilter : Nat → Nat
numberOfDivisorsFilter n with flooredSqrt n
... | zero = zero
... | sqrtn@(suc _) = (λ e → 2 * e - (if n % sqrtn == 0 then 1 else 0)) $
    foldl (λ acc _ → suc acc) 0 $ filterᵇ (λ {zero → false ; x@(suc _) → n % x == 0}) $ range (suc sqrtn)

numberOfDivisorsMap : Nat → Nat
numberOfDivisorsMap n with flooredSqrt n
... | zero = zero
... | sqrtn@(suc _) = (λ e → 2 * e - (if n % sqrtn == 0 then 1 else 0)) $
    List.sum $ List.map (λ {zero → 0 ; x@(suc _) → if n % x == zero then 1 else 0}) $ range (suc sqrtn)

numberOfDivisorsStream : Nat → Nat
numberOfDivisorsStream n with flooredSqrt n
... | zero = zero
... | sqrtn@(suc _) = (λ e → 2 * e - (if n % sqrtn == 0 then 1 else 0)) $
    Vec.sum $ Vec.map (λ {zero → 0 ; x@(suc _) → if n % x == zero then 1 else 0}) $ take (suc sqrtn) $ iterate suc 0

numberOfDivisorsRecursive : Nat → Nat
numberOfDivisorsRecursive zero = zero
numberOfDivisorsRecursive n@(suc _) with flooredSqrt n
... | zero = zero
... | sqrtn@(suc _) = 2 * inner n sqrtn - (if n % sqrtn == 0 then 1 else 0)
    where 
        inner : (n : Nat) {{_ : NonZero n}} → Nat → Nat
        inner n zero = zero
        inner n div@(suc div-1) = (if n % div == 0 then 1 else 0) + inner n div-1

numberOfDivisorsTailRecursive : Nat → Nat
numberOfDivisorsTailRecursive zero = zero
numberOfDivisorsTailRecursive n@(suc _) with flooredSqrt n
... | zero = zero
... | sqrtn@(suc _) = 2 * inner n sqrtn 0 - (if n % sqrtn == 0 then 1 else 0)
    where 
        inner : (n : Nat) {{_ : NonZero n}} → Nat → Nat → Nat
        inner n zero acc = acc
        inner n div@(suc div-1) acc = inner n div-1 $ acc + (if n % div == 0 then 1 else 0)


{-# TERMINATING #-}
findTringularNumber : (Nat → Nat) → Nat → Nat
findTringularNumber countDivisors divisors = go 1 2
    where
        go : Nat → Nat → Nat
        go prevTriag nextInd = if divisors < countDivisors newTriag then newTriag else go newTriag (suc nextInd)
            where
                newTriag : Nat
                newTriag = prevTriag + nextInd

main : IO ⊤
main = putStrLn $ show $ findTringularNumber numberOfDivisorsFilter 500             