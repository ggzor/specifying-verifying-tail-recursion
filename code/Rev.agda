module Rev where

open import Data.List using (List; []; _∷_; _++_; [_])

variable A : Set

reverse : List A -> List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ (x ∷ [])

reverse-tl : List A -> List A -> List A
reverse-tl [] ys = ys
reverse-tl (x ∷ l) l' = reverse-tl l (x ∷ l')

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)

reverse-pull-generalized :
  ∀ (xs ys zs : List A)
  → reverse-tl xs ys ++ zs
      ≡ reverse-tl xs (ys ++ zs)
reverse-pull-generalized [] ys zs = refl
reverse-pull-generalized (x ∷ xs) ys zs =
  reverse-pull-generalized xs (x ∷ ys) zs

reverse-pull :
  ∀ (x : A) (xs : List A)
  → reverse-tl xs [] ++ (x ∷ [])
      ≡ reverse-tl xs (x ∷ [])
reverse-pull x xs =
  reverse-pull-generalized xs [] (x ∷ [])

reverse≡reverse-tl : ∀ (xs : List A)
              → reverse xs ≡ reverse-tl xs []
reverse≡reverse-tl [] = refl
reverse≡reverse-tl (x ∷ xs) =
  let ind-h = reverse≡reverse-tl xs
      append-cong = cong (_++ (x ∷ [])) ind-h
      append-pull = reverse-pull x xs
   in trans append-cong append-pull

