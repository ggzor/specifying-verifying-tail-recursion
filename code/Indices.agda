module Indices where

open import Data.Nat using (ℕ; _+_; _≟_; suc)
open import Data.List using (List; []; _++_; _∷_; map)
open import Relation.Nullary using (yes; no)

indices : ℕ → List ℕ → List ℕ
indices n [] = []
indices n (x ∷ xs) with n ≟ x
... | yes _ = 0 ∷ map suc (indices n xs)
... | no  _ = map suc (indices n xs)

indices-tl-1 : ℕ → List ℕ → ℕ → List ℕ
indices-tl-1 n [] count = []
indices-tl-1 n (x ∷ xs) count with n ≟ x
... | yes _ = count ∷ indices-tl-1 n xs (suc count)
... | no  _ = indices-tl-1 n xs (suc count)

open import Data.Product using (_,_ ; _×_)

indices-tl-2 : ℕ → List ℕ → (ℕ × List ℕ) → List ℕ
indices-tl-2 n [] (_ , l) = l
indices-tl-2 n (x ∷ xs) (v , l) with n ≟ x
... | yes _ = indices-tl-2 n xs (v + 1 , v ∷ l)
... | no _ = indices-tl-2 n xs (v + 1 , l)

test-indices : List ℕ
test-indices = indices 4 (2 ∷ 1 ∷ 4 ∷ 3 ∷ 4 ∷ [])

test-indices-tl-1 : List ℕ
test-indices-tl-1 = indices-tl-1 4 (2 ∷ 1 ∷ 4 ∷ 3 ∷ 4 ∷ []) 0

test-indices-tl-2 : List ℕ
test-indices-tl-2 = indices-tl-2 4 (2 ∷ 1 ∷ 4 ∷ 3 ∷ 4 ∷ []) (0 , [])

