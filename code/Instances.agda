module Instances where

-----------------------------------------------
-- The length function using the Generic module
-----------------------------------------------

open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Properties using (+-0-isMonoid)
open import GenericBasic
  {A = ℕ} (λ _ → 1) _+_ 0 +-0-isMonoid
  renaming ( reduce to len
           ; reduce-tail to len-tail
           ; reduce≡reduce-tail to len≡len-tail
           )

-----------------------------------------------
-- The reverse function using the Generic module
-----------------------------------------------

open import Algebra.Structures using (IsMonoid)
open import Function using (flip)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; cong₂; refl; cong)
open import Relation.Binary.PropositionalEquality.Properties
  using (isEquivalence)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ; ++-identityˡ; ++-isMagma; ++-assoc)
open import Data.Product using (_,_)

++-flipped-isMonoid : {A : Set}
                    → IsMonoid {A = List A} _≡_
                        (flip _++_) []
++-flipped-isMonoid {A} = record
  { isSemigroup = record
    { isMagma = record
      { isEquivalence = isEquivalence
      ; ∙-cong = cong₂ (flip _++_)
      }
    ; assoc = λ x y z → sym (++-assoc z y x)
    }
  ; identity = ++-identityʳ , ++-identityˡ
  }

open import GenericBasic
  {A = ℕ} (λ x → x ∷ []) (flip _++_) []
           ++-flipped-isMonoid
  renaming ( reduce to reverse
           ; reduce-tail to reverse-tail
           ; reduce≡reduce-tail to reverse≡reverse-tail
           )

-----------------------------------------------
-- The indices function using the Generic module
-----------------------------------------------

open import Data.Nat using (suc)
open import Data.Nat.Properties using (+-identityʳ; +-assoc)
open import Data.List using (map)
open import Data.List.Relation.Unary.All using (construct)
open import Data.List.Properties using (++-identityʳ; map-id; map-++-commute; map-compose)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Product.Properties using (×-≡,≡↔≡)

prod-eq : ∀ {A B : Set} {a c : A} {b d : B}
        → a ≡ c → b ≡ d → (a , b) ≡ (c , d)
prod-eq refl refl = refl

IndicesData : Set
IndicesData = ℕ × List ℕ

empty : IndicesData
empty = 0 , []

_<>_ : IndicesData → IndicesData → IndicesData
(ln , ll) <> (rn , rl) =
  ln + rn , ll ++ map (ln +_) rl

<>-identityʳ : ∀ (x : IndicesData) → x <> empty ≡ x
<>-identityʳ (ln , ll) =
  prod-eq (+-identityʳ ln) (++-identityʳ ll)

<>-identityˡ : ∀ (x : IndicesData) → empty <> x ≡ x
<>-identityˡ (rn , rl) = prod-eq refl (map-id rl)

map-sum : ∀ (zl : List ℕ) (xn yn : ℕ)
        → map (λ x → (xn + yn) + x) zl
        ≡ map (λ x → xn + (yn + x)) zl
map-sum [] xn yn = refl
map-sum (x ∷ zl) xn yn rewrite +-assoc xn yn x =
  cong ((xn + (yn + x)) ∷_) (map-sum zl xn yn)

<>-assoc : ∀ (x y z : IndicesData)
         → (x <> y) <> z ≡ x <> (y <> z)
<>-assoc (xn , xl) (yn , yl) (zn , zl)
  rewrite ++-assoc xl (map (_+_ xn) yl) (map (_+_ (xn + yn)) zl)
        | map-++-commute (_+_ xn) yl (map (_+_ yn) zl)
        | sym (map-compose {g = (_+_ xn)} {f = (_+_ yn)} zl) =
  prod-eq (+-assoc xn yn zn)
          (cong (xl ++_)
            (cong ((map (_+_ xn) yl) ++_)
              (map-sum zl xn yn)))

<>-indices-isMonoid : IsMonoid _≡_ _<>_ empty
<>-indices-isMonoid = record
  { isSemigroup = record
      { isMagma = record
          { isEquivalence = isEquivalence
          ; ∙-cong = cong₂ _<>_
          }
      ; assoc = <>-assoc
      }
  ; identity = <>-identityˡ , <>-identityʳ
  }

open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary using (yes; no)

module _ {A : Set} (_≟_ : Decidable {A = A} _≡_) (needle : A) where
  embed : A → IndicesData
  embed x with x ≟ needle
  ... | yes _ = 1 , (0 ∷ [])
  ... | no _  = 1 , []

  open import GenericBasic 
    {A = A} embed _<>_ empty <>-indices-isMonoid

  -- Get only the snd element from the result

  indices : List A → List ℕ
  indices xs = proj₂ (reduce xs)

  indices-tail : List A → List ℕ
  indices-tail xs = proj₂ (reduce-tail xs empty)

