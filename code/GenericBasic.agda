open import Data.List using (List; []; _∷_; _++_; [_])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)

open import Algebra.Structures using (IsMonoid)

module GenericBasic
  {A : Set}
  {R : Set}
  (f : A → R)
  (_<>_ : R → R → R)
  (empty : R)
  (m : IsMonoid _≡_ _<>_ empty)
  where

open IsMonoid m using ()
  renaming ( identityˡ to <>-identityˡ
           ; identityʳ to <>-identityʳ
           ; assoc to <>-assoc
           )

reduce : List A → R
reduce [] = empty
reduce (x ∷ xs) = f x <> reduce xs

reduce-tl : List A → R → R
reduce-tl [] r = r
reduce-tl (x ∷ xs) r = reduce-tl xs (r <> f x)

reduce-pull-generalized :
  ∀ (r s : R) (xs : List A)
  → r <> reduce-tl xs s ≡ reduce-tl xs (r <> s)
reduce-pull-generalized r s [] = refl
reduce-pull-generalized r s (x ∷ xs)
  rewrite <>-assoc r s (f x)
        = reduce-pull-generalized r (s <> f x) xs

reduce-pull :
  ∀ (r : R) (xs : List A)
  → r <> reduce-tl xs empty
  ≡ reduce-tl xs (empty <> r)
reduce-pull r []
  rewrite <>-identityˡ r
        | <>-identityʳ r = refl
reduce-pull r (x ∷ xs)
  rewrite <>-identityˡ (f x)
        | <>-identityˡ r
        = reduce-pull-generalized r (f x) xs

reduce≡reduce-tl : ∀ (xs : List A)
                   → reduce xs ≡ reduce-tl xs empty
reduce≡reduce-tl [] = refl
reduce≡reduce-tl (x ∷ xs) =
  let ind-h = reduce≡reduce-tl xs
      op-cong = cong (f x <>_) ind-h
      op-pull = reduce-pull (f x) xs
   in trans op-cong op-pull

