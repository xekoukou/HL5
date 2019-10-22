module HL5 where

open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Data.Empty

postulate
  World : Set
  server : World
  client : World

record CO (w : World) (A : Set) : Set where
  field
-- This is used so as to keep the World during Compilation, since types are erased. (???)
    wi : World
    eq : wi ≡ w
    v : A

postulate
  return : ∀ {w S} → S → CO w S
  _>>=_    : ∀ {w S S'} → CO w S → (S → CO w S') → CO w S'
  ↓    : ∀ {w' w S} → CO w' S → CO w S

private
  variable
    w w₁ w₂ : World

HSet : Set₁
HSet = (w : World) → Set

private
  variable
    HA HB HC : HSet

○ : HSet → HSet
○ HA w = CO w (HA w)

_at_ : HSet → World → HSet
(HA at w') w = HA w'


⟨_⟩ : Set → HSet
⟨ A ⟩ w = A

infixr 9 _⇒_

_⇒_ : HSet → HSet → HSet
(HA ⇒ HB) w = HA w → HB w

∀w : (World → HSet) → HSet
∀w F w = ∀ w' → (F w') w

∃w : (World → HSet) → HSet
∃w F w = Σ World (λ w' → F w' w)

infix 10 _∨_
_∨_ : (HA HB : HSet) → HSet
(HA ∨ HB) w = HA w ⊎ HB w

⊞_ : (World → HSet) → HSet
(⊞ F) = ∀w (λ w' → (F w') at w')

infix 11 □_

□_ : HSet → HSet
(□ HA) = ∀w (λ w' → HA at w')

infix 11 ◇_
◇_ : HSet → HSet
◇ HA = ∃w (HA at_)

infix 1 ⊨_

⊨_ : HSet → Set
⊨_ HA = ∀ w → HA w

□-refl : ⊨ □ HA ⇒ HA
□-refl {HA} w □a = □a w

K : ⊨ □ (HA ⇒ HB) ⇒ □ HA ⇒ HB
K w □a⇒b □a = □a⇒b w (□a w)

◇v : ⊨ ◇ (HA ∨ HB) ⇒ ◇ HA ∨ ◇ HB 
◇v w (w′ , inj₁ x) = inj₁ (w′ , x)
◇v w (w′ , inj₂ y) = inj₂ (w′ , y)

◇5 : ⊨ ◇ □ HA ⇒ □ HA
◇5 w (w' , □a) = □a

curry5 : ⊨ (◇ HA ⇒ □ HB) ⇒ □ (HA ⇒ HB)
curry5 w ◇a⇒□b w' a = ◇a⇒□b (w' , a) w'

□trans : ⊨ □ HA ⇒ □ □ HA
□trans w □a w' = □a

◇refl : ⊨ HA ⇒ ◇ HA
◇refl w a = w , a

◇trans : ⊨ ◇ ◇ HA ⇒ ◇ HA
◇trans w (w' , ◇a) = ◇a

K◇ : ⊨ □ (HA ⇒ HB) ⇒ ◇ HA ⇒ ◇ HB
K◇ w □a⇒□b (w' , a) = w' , □a⇒□b w' a 

◇⊥ : ⊨ ◇ ⟨ ⊥ ⟩ ⇒ ⟨ ⊥ ⟩
◇⊥ w (w' , a) = a

□5 : ⊨ ◇ HA ⇒ □ ◇ HA
□5 w ◇a w'' = ◇a


open import Data.Nat

hello : ⊨ ○ ⟨ ℕ ⟩
hello w = do
      return 3
