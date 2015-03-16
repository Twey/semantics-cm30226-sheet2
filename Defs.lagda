\begin{code}

module Defs where

import Function as ⇒
open import Level
open import Algebra
open import Categories.Category
import Relation.Binary.PropositionalEquality as ≡
open import Relation.Binary.Core using (Rel)

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
  { map = ⇒.id; map-resp-ε = refl; map-resp-∙ = λ _ _ → refl; cong = ⇒.id }
  where refl = Monoid.refl M

MonMap-∘ : ∀ {o ℓ} {A B C : Monoid o ℓ}
  → MonMap B C → MonMap A B → MonMap A C
MonMap-∘ f g = record
  { map        = f.map ⇒.∘ g.map
  ; cong       = f.cong ⇒.∘ g.cong
  ; map-resp-ε = f.T.trans (f.cong g.map-resp-ε) f.map-resp-ε
  ; map-resp-∙ = λ x y → f.T.trans (f.cong (g.map-resp-∙ x y)) (f.map-resp-∙ _ _)
  }
  where
    module f = MonMap f; module g = MonMap g

MonMap-≡ : ∀ {o ℓ} {A B : Monoid o ℓ} → Rel (MonMap A B) (ℓ ⊔ o)
MonMap-≡ {B = B} f g = ∀ x → f.map x ≈ g.map x
  where open Monoid B; module f = MonMap f; module g = MonMap g

Mon : Category (suc zero) zero zero
Mon = record
  { Obj       = Monoid zero zero
  ; _⇒_       = MonMap
  ; _≡_       = MonMap-≡
  ; id        = MonMap-id
  ; _∘_       = MonMap-∘
  ; assoc     = λ {_} {_} {_} {D} x → Monoid.refl D
  ; identityˡ = λ {_} {B} _ → Monoid.refl B
  ; identityʳ = λ {_} {B} x → Monoid.refl B
  ; equiv     = λ {A} {B} → let module B = Monoid B; module A = Monoid A in record
    { refl  = λ _ → B.refl
    ; sym   = λ p x → B.sym (p x)
    ; trans = λ p q x → B.trans (p x) (q x)
    }
  ; ∘-resp-≡  = λ {_} {_} {C} {f} {_} {_} {i} f≈g h≈i x →
      Monoid.trans C (MonMap.cong f (h≈i x)) (f≈g (MonMap.map i x))
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

\end{code}
