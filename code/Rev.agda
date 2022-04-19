module Rev where

open import Data.List using (List; []; _∷_; _++_; [_])

variable A : Set

reverse : List A -> List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ (x ∷ [])

reverse-tail : List A -> List A -> List A
reverse-tail [] ys = ys
reverse-tail (x ∷ xs) ys = reverse-tail xs (x ∷ ys)

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; subst)

reverse-pull-generalized :
  ∀ (xs ys zs : List A)
  → reverse-tail xs ys ++ zs
      ≡ reverse-tail xs (ys ++ zs)
reverse-pull-generalized [] ys zs = refl
reverse-pull-generalized (x ∷ xs) ys zs =
  reverse-pull-generalized xs (x ∷ ys) zs

reverse-pull :
  ∀ (x : A) (xs : List A)
  → reverse-tail xs [] ++ (x ∷ [])
      ≡ reverse-tail xs (x ∷ [])
reverse-pull x xs =
  reverse-pull-generalized xs [] (x ∷ [])

reverse≡reverse-tail : ∀ (xs : List A)
                     → reverse xs ≡ reverse-tail xs []
reverse≡reverse-tail [] = refl
reverse≡reverse-tail (x ∷ xs) =
  let ind-h = reverse≡reverse-tail xs
      append-cong = cong (_++ (x ∷ [])) ind-h
      append-pull = reverse-pull x xs
   in trans append-cong append-pull

