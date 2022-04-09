open import Data.List using (List; []; _∷_; _++_; [_])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)

module GenericBasic
  (A : Set)
  (R : Set)
  (empty : R)
  (_<>_ : R → R → R)
  (<>-identityˡ : ∀ (r : R) → empty <> r ≡ r)
  (<>-identityʳ : ∀ (r : R) → r <> empty ≡ r)
  (<>-assoc : ∀ (r s t : R) → (r <> s) <> t ≡ r <> (s <> t))
  (f : A → R)
  where

reduce : List A → R
reduce [] = empty
reduce (x ∷ xs) = f x <> reduce xs

reduce-tail : List A → R → R
reduce-tail [] r = r
reduce-tail (x ∷ xs) r = reduce-tail xs (r <> f x)

reduce-pull-generalized :
  ∀ (r s : R) (xs : List A)
  → r <> reduce-tail xs s ≡ reduce-tail xs (r <> s)
reduce-pull-generalized r s [] = refl
reduce-pull-generalized r s (x ∷ xs)
  rewrite <>-assoc r s (f x)
        = reduce-pull-generalized r (s <> f x) xs

reduce-pull :
  ∀ (r : R) (xs : List A)
  → r <> reduce-tail xs empty
  ≡ reduce-tail xs (empty <> r)
reduce-pull r []
  rewrite <>-identityˡ r
        | <>-identityʳ r = refl
reduce-pull r (x ∷ xs)
  rewrite <>-identityˡ (f x)
        | <>-identityˡ r
        = reduce-pull-generalized r (f x) xs

reduce≡reduce-tail : ∀ (xs : List A)
                   → reduce xs ≡ reduce-tail xs empty
reduce≡reduce-tail [] = refl
reduce≡reduce-tail (x ∷ xs) =
  let ind-h = reduce≡reduce-tail xs
      op-cong = cong (f x <>_) ind-h
      op-pull = reduce-pull (f x) xs
   in trans op-cong op-pull

