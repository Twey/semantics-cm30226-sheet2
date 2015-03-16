\begin{code}

module Problem1 where

open import Defs

import Function as ⇒
import Relation.Binary.PropositionalEquality as ≡
open import Level
open import Algebra
open import Categories.Category
open import Data.Unit
open import Data.Product

CMon-1 : CommutativeMonoid zero zero
CMon-1 = record
  { Carrier             = Carrier
  ; _≈_                 = _≈_
  ; _∙_                 = _∙_
  ; ε                   = ε
  ; isCommutativeMonoid = record
    { isSemigroup = isSemigroup
    ; identityˡ   = proj₁ identity
    ; comm        = λ _ _ → ≡.refl
    }
  }
  where open Monoid Mon-1

CMon-T! : (M : CommutativeMonoid zero zero) → CMonMap M CMon-1
CMon-T! = Mon-T! ⇒.∘ CommutativeMonoid.monoid

_⊗C_ : (M N : CommutativeMonoid zero zero) → CommutativeMonoid zero zero
M ⊗C N = record
  { Carrier             = Carrier
  ; _≈_                 = _≈_
  ; _∙_                 = _∙_
  ; ε                   = ε
  ; isCommutativeMonoid = record
    { isSemigroup = isSemigroup
    ; identityˡ   = proj₁ identity
    ; comm        = λ { (m , n) (m′ , n′) → M.comm m m′ , N.comm n n′ }
    }
  }
  where
    module M = CommutativeMonoid M
    module N = CommutativeMonoid N
    open Monoid (M.monoid ⊗M N.monoid)

CMon-π₁ : ∀ {M N} → CMonMap (M ⊗C N) M
CMon-π₁ {M = M} = record
  { map        = proj₁
  ; cong       = proj₁
  ; map-resp-ε = M.refl
  ; map-resp-∙ = λ _ _ → M.refl
  }
  where module M = CommutativeMonoid M

CMon-π₂ : ∀ {M N} → CMonMap (M ⊗C N) N
CMon-π₂ {N = N} = record
  { map        = proj₂
  ; cong       = proj₂
  ; map-resp-ε = N.refl
  ; map-resp-∙ = λ _ _ → N.refl
  }
  where module N = CommutativeMonoid N

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

\end{code}
