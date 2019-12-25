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
open import Macros

private
  variable
    α β : L.Level

-------------------------------------------

-- Concurrent Indexed Container.
record CO (w : World) (A : Set α) : Set α where
  constructor co
  field
-- This is used so as to keep the World during Compilation, since types are erased. (???)
    wi : World
    eq : wi ≡ w
    v : A

-- Set parametrized by the world it lives in.
HSet : ∀{α} → Set (L.suc α)
HSet {α} = {@(tactic iw) 〈w〉 : World} → Set α

⟦_⟧ : HSet {α} → Set α
⟦ HA ⟧ = {@(tactic iw) 〈w〉 : World} → HA

○ : HSet {α} → HSet {α}
○ HA {w} = CO w HA


⟨_⟩ : Set α → HSet {α}
⟨ A ⟩ = A

infix 9 !_!_
  
!_!_ : World → HSet {α} → HSet {α}
!_!_ w HA = HA {w}

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

return : ∀{HA : HSet {α}} → {w : World} → HA → ○ HA
CO.wi (return {w = w} x) = w
CO.eq (return x) = refl
CO.v (return x) = x

_>>=_ : {@(tactic ihs) HA : HSet {α}} {HB : HSet {β}} → {w : World}
        → ○ HA → (HA → ○ HB) → ○ HB
CO.wi (_>>=_ {w = w} x f) = w
CO.eq (_>>=_ x f) = refl
CO.v (_>>=_ x f) = CO.v (f (CO.v x))

postulate
  get    : ∀ {w' w S} → CO {α} w' S → CO w S

↓ : ∀{@(tactic ihs) HA : HSet {α}} → {w₁ w : World} → ! w₁ ! ○ HA → ○ (! w₁ ! HA)
↓ = get

○ₛ : {@(tactic iw) w : World} → ○ ⟨ Set α ⟩ → Set α
○ₛ {w = w} Q = CO w (CO.v Q)
 
_>>=2_ : {HA : HSet {α}} → {w : World} → {@(tactic ifs) HP : {w' : World} → HA → ○ ⟨ Set α ⟩}
         → (ha : ○ HA) → ((a : HA) → ○ₛ (HP a)) → ○ₛ (ha >>= HP)
CO.wi (_>>=2_ {w = w} x f) = w
CO.eq (x >>=2 f) = refl
CO.v (x >>=2 f) = CO.v (f (CO.v x))


f : {w₁ w : World} → ! w₁ ! ⟨ Bool ⟩ → ○ ⟨ Set ⟩
f false = return Bool
f true  = return ⊤

d : {w₁ w : World} → (ha : (! w₁ ! ○ ⟨ Bool ⟩)) → ○ₛ (↓ ha >>= f {w₁})
d {w₁ = w₁} ha = _>>=2_ (↓ ha) λ { false → return true ; true → return tt}

↓¡_¡ : ∀{HA : HSet {α}} → (w₂ : World) → {w₁ w : World} → ! w₁ ! ○ HA → ! w₂ ! ○ (! w₁ ! HA)
↓¡ w ¡ = get

-- ¡_¡ : ∀{HA : HSet {α}} → (w₁ : World) → {w : World} → HA → ! w₁ ! HA
-- ¡ w ¡ a = {!a!}

