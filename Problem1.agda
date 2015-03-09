module Problem1 where

open import Defs

import Relation.Binary.PropositionalEquality as ≡
open import Level
open import Algebra
open import Categories.Category
open import Data.Unit
open import Data.Product

open import Categories.Object.Terminal
CMon-Terminal : Terminal CMon
CMon-Terminal = record
  { ⊤        = CMon-1
  ; !        = λ {M} → CMon-T! M
  ; !-unique = λ _ → ≡.refl
  }

open import Categories.Object.Product
CMon-Product : ∀ {M N} → Product CMon M N
CMon-Product {M} {N} = record
  { A×B       = M ⊗C N
  ; π₁        = CMon-π₁ {M} {N}
  ; π₂        = CMon-π₂ {M} {N}
  ; ⟨_,_⟩     = λ {C} → ⟨_,_⟩ {C}
  ; commute₁  = ≡.refl
  ; commute₂  = ≡.refl
  ; universal = λ {C} {f} {g} {i} → universal {C} {f} {g} {i}
  }
  where
    open Category CMon
    module M = CommutativeMonoid M
    module N = CommutativeMonoid N
    ⟨_,_⟩ : {C : Obj} → C ⇒ M → C ⇒ N → C ⇒ (M ⊗C N)
    ⟨_,_⟩ {C} f g = record
      { map        = < f.map , g.map >
      ; cong       = < f.cong , g.cong >
      ; map-resp-ε = f.map-resp-ε , g.map-resp-ε
      ; map-resp-∙ = λ x y → f.map-resp-∙ x y , g.map-resp-∙ x y
      }
      where
        module f = MonMap f; module g = MonMap g
        module C = CommutativeMonoid C
    -- Ugh
    universal : {C : Obj} {f : C ⇒ M} {g : C ⇒ N} {i : C ⇒ (M ⊗C N)}
      (p : _≡_ {C} {M} (_∘_ {C} {M ⊗C N} {M} (CMon-π₁ {M} {N}) i) f)
      (q : _≡_ {C} {N} (_∘_ {C} {M ⊗C N} {N} (CMon-π₂ {M} {N}) i) g)
      → _≡_ {C} {M ⊗C N} (⟨_,_⟩ {C} f g) i
    universal ≡.refl ≡.refl = ≡.refl

open import Categories.Object.Products renaming (Products to FiniteProducts)
CMon-FiniteProducts : FiniteProducts CMon
CMon-FiniteProducts = record
  { terminal = CMon-Terminal
  ; binary   = record { product = CMon-Product }
  }
