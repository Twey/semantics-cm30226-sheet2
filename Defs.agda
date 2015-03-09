module Defs where

import Function as ⇨
open import Level
open import Algebra
open import Categories.Category
import Relation.Binary.PropositionalEquality as ≡

record MonMap {o ℓ o′ ℓ′} (S : Monoid o ℓ) (T : Monoid o′ ℓ′)
    : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
  constructor monMap
  
  module S = Monoid S; module T = Monoid T; open T

  field
    map         : S.Carrier → Carrier
    .cong       : ∀ {x y} → x S.≈ y → map x ≈ map y
    .map-resp-ε : map S.ε ≈ ε
    .map-resp-∙ : ∀ x y → map (x S.∙ y) ≈ map x ∙ map y

MonMap-id : ∀ {o ℓ} {M : Monoid o ℓ} → MonMap M M
MonMap-id {M = M} = record
  { map = ⇨.id; map-resp-ε = refl; map-resp-∙ = λ _ _ → refl; cong = ⇨.id }
  where refl = Monoid.refl M

MonMap-∘ : ∀ {o ℓ} {A B C : Monoid o ℓ}
  → MonMap B C → MonMap A B → MonMap A C
MonMap-∘ f g = record
  { map        = f.map ⇨.∘ g.map
  ; cong       = f.cong ⇨.∘ g.cong
  ; map-resp-ε = f.T.trans (f.cong g.map-resp-ε) f.map-resp-ε
  ; map-resp-∙ = λ x y → f.T.trans (f.cong (g.map-resp-∙ x y)) (f.map-resp-∙ _ _)
  }
  where
    module f = MonMap f; module g = MonMap g

-- Does this have finite coproducts?
Mon : Category (suc zero) zero zero
Mon = record
  { Obj       = Monoid zero zero
  ; _⇒_       = MonMap
  ; _≡_       = ≡._≡_
  ; id        = MonMap-id
  ; _∘_       = MonMap-∘
  ; assoc     = ≡.refl
  ; identityˡ = ≡.refl
  ; identityʳ = ≡.refl
  ; equiv     = ≡.isEquivalence
  ; ∘-resp-≡  = ≡.cong₂ MonMap-∘
  }

open import Data.Unit
open import Data.Product

Mon-1 : Monoid zero zero
Mon-1 = record
  { Carrier  = ⊤
  ; _≈_      = ≡._≡_
  ; _∙_      = λ _ _ → tt
  ; ε        = tt
  ; isMonoid = record
    { isSemigroup = record
      { isEquivalence = ≡.isEquivalence
      ; assoc         = λ _ _ _ → ≡.refl
      ; ∙-cong        = λ _ _ → ≡.refl
      }
    ; identity = (λ _ → ≡.refl) , (λ _ → ≡.refl)
    }
  }

Mon-T! : (M : Monoid zero zero) → MonMap M Mon-1
Mon-T! M = record
  { map        = λ _ → tt
  ; cong       = λ _ → ≡.refl
  ; map-resp-ε = ≡.refl
  ; map-resp-∙ = λ _ _ → ≡.refl
  }

_⊗M_ : (M N : Monoid zero zero) → Monoid zero zero
M ⊗M N = record
  { Carrier  = M.Carrier × N.Carrier
  ; _≈_      = λ { (m , n) (m′ , n′) → m M.≈ m′ × n N.≈ n′ }
  ; _∙_      = zip M._∙_ N._∙_
  ; ε        = (M.ε , N.ε)
  ; isMonoid = record
    { isSemigroup = record
      { isEquivalence = record
        { refl  = M.refl , N.refl
        ; sym   = map M.sym N.sym
        ; trans = zip M.trans N.trans
        }
      ; assoc = λ { (xₘ , xₙ) (yₘ , yₙ) (zₘ , zₙ)
                      → M.assoc xₘ yₘ zₘ , N.assoc xₙ yₙ zₙ }
      ; ∙-cong = zip M.∙-cong N.∙-cong
      }
      ; identity = (λ { (m , n) → proj₁ M.identity m , proj₁ N.identity n })
                 , (λ { (m , n) → proj₂ M.identity m , proj₂ N.identity n })
    }
  }
  where
    module M = Monoid M; module N = Monoid N

CMonMap : ∀ {o ℓ o′ ℓ′}
    (S : CommutativeMonoid o ℓ)
    (T : CommutativeMonoid o′ ℓ′)
    → Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′)
CMonMap S T = MonMap (CommutativeMonoid.monoid S) (CommutativeMonoid.monoid T)

CMon : Category (suc zero) zero zero
CMon = record
  { Obj       = CommutativeMonoid zero zero
  ; _⇒_       = CMonMap
  ; _≡_       = ≡._≡_
  ; id        = MonMap-id
  ; _∘_       = MonMap-∘
  ; assoc     = ≡.refl
  ; identityˡ = ≡.refl
  ; identityʳ = ≡.refl
  ; equiv     = ≡.isEquivalence
  ; ∘-resp-≡  = ≡.cong₂ MonMap-∘
  }

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
CMon-T! = Mon-T! ⇨.∘ CommutativeMonoid.monoid

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
