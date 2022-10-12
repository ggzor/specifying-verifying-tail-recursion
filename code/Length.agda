module Length where

open import Data.Nat using (ℕ; suc; _+_)
open import Data.List using (List; []; _∷_; _++_)

variable A : Set

len : List A → ℕ
len [] = 0
len (x ∷ xs) = suc (len xs)

len-tl : List A → ℕ → ℕ
len-tl [] n = n
len-tl (x ∷ xs) n = len-tl xs (suc n)

-- Functional equality

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; trans; sym)
open import Data.Nat.Properties using (+-suc)

len-pull-generalized :
    ∀ (xs : List A) (n p : ℕ)
    → n + len-tl xs p ≡ len-tl xs (n + p)
len-pull-generalized [] n p = refl
len-pull-generalized (x ∷ xs) n p
  rewrite (sym (+-suc n p))
        = len-pull-generalized xs n (suc p)

len-pull : ∀ (xs : List A)
            → suc (len-tl xs 0) ≡ len-tl xs 1
len-pull xs = len-pull-generalized xs 1 0

len≡len-tl : ∀ (xs : List A)
               → len xs ≡ len-tl xs 0
len≡len-tl [] = refl
len≡len-tl (x ∷ xs) =
  let ind-h = len≡len-tl xs
      suc-cong = cong suc ind-h
      suc-pull = len-pull xs
   in trans suc-cong suc-pull

-- Other properties

concat-len : ∀ (xs ys : List A) → len (xs ++ ys) ≡ len xs + len ys
concat-len [] ys = refl
concat-len (x ∷ xs) ys = cong suc (concat-len xs ys)

concat-len-tl : ∀ (xs ys : List ℕ)
                   → len-tl (xs ++ ys) 0 ≡ len-tl xs 0 + len-tl ys 0
concat-len-tl [] ys = refl
concat-len-tl (x ∷ xs) ys
  rewrite sym (len-pull (xs ++ ys))
        | sym (len-pull xs)
        = cong suc (concat-len-tl xs ys)

