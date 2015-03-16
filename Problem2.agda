module Problem2 where

open import Defs

open import Level
open import Algebra
open import Categories.Category
open import Categories.Object.Initial
open import Data.Product
open import Data.Unit
import Relation.Binary.PropositionalEquality as ≡
open import Relation.Unary hiding (∅)

Mon-I! : (M : Monoid zero zero) → MonMap Mon-1 M
Mon-I! M = record
  { map        = λ _ → ε
  ; cong       = λ _ → refl
  ; map-resp-ε = refl
  ; map-resp-∙ = λ _ _ → sym (proj₁ identity ε)
  }
  where open Monoid M

Mon-Initial : Initial Mon
Mon-Initial = record
  { ⊥        = Mon-1
  ; !        = Mon-I! _
  ; !-unique =
      λ {A} f → λ { tt → Monoid.sym A (MonMap.map-resp-ε f) }
  }

_⊕M_ : (M N : Monoid zero zero) → Monoid zero zero
M ⊕M N = record
  { Carrier = M.Carrier N.Carrier
  ; _≈_ = {!!}
  ; _∙_ = {!!}
  ; ε = {!!}
  ; isMonoid = {!!} }
  where module M = Monoid M; module N = Monoid N
