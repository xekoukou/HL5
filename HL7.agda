module HL7 where

open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Bool
open import Level

postulate
  World : Set

private
  variable
    α β : Level
    w w₁ w₂ : World

record CO (w : World) (A : Set α) : Set α where
  field
-- This is used so as to keep the World during Compilation, since types are erased. (???)
    wi : World
    eq : wi ≡ w
    v : A



HSet : ∀{α} → Set (suc α)
HSet {α} = (w : World) → Set α


private
  variable
    HA HB HC : HSet {α}

⟨_⟩ : Set α → HSet {α}
⟨ A ⟩ w = A


infix 9 !_!_
  
!_!_ : World → HSet {α} → HSet {α}
!_!_ w' HA w = HA w'


g : {HA : HSet {α}} → {HB : (w : World) → HA w → Set} → (a : HA w) → HB w a → ⊥
g = {!!}
  
○ : HSet {α} → HSet {α}
○ HA w = CO w (HA w)


infix 11 □_

□_ : HSet {α} → HSet {α}
(□ HA) w = ∀ w' → !_!_ w' HA w

infix 11 ◇_
◇_ : HSet {α} → HSet
(◇ HA) w = Σ World (λ w' → !_!_ w' HA w)

□-refl : (w : World) → (□ HA) w → HA w
□-refl w □a = □a w

K : (w : World) → (□ (λ w → HA w → HB w)) w → (□ (λ w → HA w)) w → HB w
K w □f □a = □f w (□a w)


return : (w : World) →  HA w → ○ HA w
CO.wi (return w x) = w
CO.eq (return w x) = refl
CO.v (return w x) = x

_>>=_ : (w : World) → ○ HA w → (HA w → ○ HB w) → ○ HB w
CO.wi (_>>=_ w x f) = w
CO.eq (_>>=_ w x f) = refl
CO.v (_>>=_ w x f) = CO.v (f (CO.v x))



postulate
  get    : ∀ {w' w S} → CO {α} w' S → CO w S


↓ : (w : World) → (! w₁ ! ○ HA) w → ○ (! w₁ ! HA) w
↓ w = get

○ₛ : (w : World) → ○ ⟨ Set ⟩ w → Set
○ₛ w Q = CO w (CO.v Q)

_>>=2_ : (w : World) → {HP : (w : World) → HA w → ○ ⟨ Set ⟩ w} → (ha : ○ HA w) → ((a : HA w) → ○ₛ w (HP w a)) → ○ₛ w (_>>=_ {HA = HA} w ha (HP w))
CO.wi (_>>=2_ w {HP} ha f) = w
CO.eq (_>>=2_ w {HP} ha f) = refl
CO.v (_>>=2_ w {HP} ha f) = CO.v (f (CO.v ha))



f : (w : World) → (! w₁ ! ⟨ Bool ⟩) w → ○ ⟨ Set ⟩ w
f w false = return w Bool
f w true  = return w ⊥



d : (w : World) → (ha : (! w₁ ! ○ ⟨ Bool ⟩) w) → ○ₛ w (_>>=_ w (↓ w ha) (f {w₁ = w₁} w))
d {w₁ = w₁} w ha = _>>=2_ w {HP = {!!}} (↓ w ha) λ { false → {!!} ; true → {!!}}
