module HL5 where


open import Prelude.Nat
open import Prelude.Semiring
open import Prelude.Ord
open import Prelude.Product
open import Prelude.Function hiding (!)
open import Prelude.Maybe
open import Prelude.Bool
open import Relation.Binary.PropositionalEquality
open import Prelude.List
open import Prelude.Unit
import Level as L

open import Common public
import Internal as I
open import Macros

private
  variable
    α β : L.Level

-- Set parametrized by the world it lives in.
HSet : Set (L.suc α)
HSet {α} = {@(tactic iw) 〈w〉 : World} → Set α

⟦_⟧ : HSet {α} → Set α
⟦ HA ⟧ = {@(tactic iw) 〈w〉 : World} → HA

⟦_⟧′ : HSet {α} → Set α
⟦ HA ⟧′ = {〈w〉 : World} → HA

infix 9 !_!_
  
!_!_ : World → HSet {α} → HSet {α}
!_!_ w HA = HA {w}

⟨_⟩ : Set α → HSet {α}
⟨ A ⟩ = A

○ : HSet {α} → HSet {α}
○ HA {w} = I.CO w (HA {w})

return : ∀{@(tactic ihs) HA : HSet {α}} → ⟦( HA → ○ HA )⟧′
return {HA = HA} {w} ha = I.return {IA = λ w → HA {w}} w ha

_>>=_ : {@(tactic ihs) HA : HSet {α}} {HB : HSet {β}}
        → ⟦( ○ HA → (HA → ○ HB) → ○ HB )⟧′
_>>=_ {HA = HA} {HB} {w} ha f = I.bind {IA = λ w → HA {w}} {IB = λ w → HB {w}} w ha f

↓ : ∀{@(tactic ihs) HA : HSet {α}} → {w₁ : World} → ⟦( ! w₁ ! ○ HA → ○ (! w₁ ! HA) )⟧′
↓ {w₁ = w₁} {w} ha = I.get w₁ w ha

↓¡_∼>_¡ : ∀{α} → ∀{HA : HSet {α}} → (w₂ w₁ : World) → ⟦( ! w₁ ! ○ HA → ! w₂ ! ○ (! w₁ ! HA) )⟧′
↓¡ w₂ ∼> w₁ ¡ = ↓

○S : HSet {L.suc α}
○S {α} = ○ ⟨ Set α ⟩ → ⟨ Set α ⟩

○ₛ : ⟦ ○S {α} ⟧
○ₛ {_} {w} Q = ○ (λ {w'} → I.CO.v Q) {w}

_>>=ᵈ_ : {HA : HSet {α}} → ⟦( {@(tactic ifs) HP : ⟦( HA → ○ ⟨ Set α ⟩ )⟧′}
         → (ha : ○ HA) → ((a : HA) → ○ₛ (HP a)) → ○ₛ {α = α} (_>>=_ ha HP) )⟧′
_>>=ᵈ_ {HA = HA} {w} {HP} x f = I.bind2 {IA = λ w'' → HA {w''}} w {IP = λ w'' → HP {w''}} x f


infix 11 □_

□_ : HSet {α} → HSet {α}
□ HA = ∀ w → ! w ! HA

infix 11 ◇_
◇_ : HSet {α} → HSet
◇ HA = Σ World (λ w → ! w ! HA)

□-refl : ∀{HA : HSet {α}} → {w : World} → □ HA → HA
□-refl {w = w} □a = □a w

K : ∀{HA HB : HSet {α}} → {w : World} → □ (λ {_} → HA → HB) → □ HA → HB
K {w = w} □f □a = □f w (□a w)
