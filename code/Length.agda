module Length where

open import Data.Nat using (ℕ; suc; _+_)
open import Data.List using (List; []; _∷_; _++_)

variable A : Set

len : List A → ℕ
len [] = 0
len (x ∷ xs) = suc (len xs)

len-tail : List A → ℕ → ℕ
len-tail [] n = n
len-tail (x ∷ xs) n = len-tail xs (suc n)

-- Functional equality

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; trans; sym)
open import Data.Nat.Properties using (+-suc)

len-pull-generalized :
    ∀ (xs : List A) (n p : ℕ)
    → n + len-tail xs p ≡ len-tail xs (n + p)
len-pull-generalized [] n p = refl
len-pull-generalized (x ∷ xs) n p
  rewrite (sym (+-suc n p))
        = len-pull-generalized xs n (suc p)

len-pull : ∀ (xs : List A)
            → suc (len-tail xs 0) ≡ len-tail xs 1
len-pull xs = len-pull-generalized xs 1 0

len≡len-tail : ∀ (xs : List A)
                   → len xs ≡ len-tail xs 0
len≡len-tail [] = refl
len≡len-tail (x ∷ xs) =
  let ind-h = len≡len-tail xs
      suc-cong = cong suc ind-h
      suc-pull = len-pull xs
   in trans suc-cong suc-pull

-- Other properties

concat-len : ∀ (xs ys : List A) → len (xs ++ ys) ≡ len xs + len ys
concat-len [] ys = refl
concat-len (x ∷ xs) ys = cong suc (concat-len xs ys)

concat-len-tail : ∀ (xs ys : List ℕ)
                   → len-tail (xs ++ ys) 0 ≡ len-tail xs 0 + len-tail ys 0
concat-len-tail [] ys = refl
concat-len-tail (x ∷ xs) ys
  rewrite sym (len-pull (xs ++ ys))
        | sym (len-pull xs)
        = cong suc (concat-len-tail xs ys)

