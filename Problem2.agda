module Problem2 where

open import Defs

open import Level
open import Algebra
open import Categories.Category
open import Categories.Object.Initial
open import Data.Product
open import Data.Unit
import Relation.Binary.PropositionalEquality as ≡

Mon-I! : (M : Monoid zero zero) → MonMap Mon-1 M
Mon-I! M = record
  { map        = λ _ → ε
  ; cong       = λ _ → refl
  ; map-resp-ε = refl
  ; map-resp-∙ = λ _ _ → sym (proj₁ identity ε)
  }
  where open Monoid M

postulate
  ext : ∀ {a b} {A : Set a} {B : Set b} {f g : A → B}
      → (∀ x → f x ≡.≡ g x) → f ≡.≡ g

Mon-Initial : Initial Mon
Mon-Initial = record
  { ⊥ = Mon-1
  ; ! = Mon-I! _
  ; !-unique = unique
  }
  where
    open Category Mon
    .blah : ∀ (A : Monoid zero zero) (fmap : ⊤ → Monoid.Carrier A) (frε : Monoid._≈_ A (fmap tt) (Monoid.ε A)) → (λ _ → Monoid.ε A) ≡.≡ fmap
    blah A fmap frε = ext (λ { tt → {!Monoid.sym A frε!} })
    .unique : {A : Obj} (f : Mon-1 ⇒ A) → Mon-I! A ≡ f
    unique {A} (monMap fmap fcong fmap-resp-ε fmap-resp-∙) with blah A fmap (irr fmap-resp-ε)
    unique (monMap ._ fcong fmap-resp-ε fmap-resp-∙) | ≡.refl = {!!}
