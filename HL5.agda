module HL5 where

open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Level

postulate
  World : Set

record CO (w : World) (A : Set) : Set where
  field
-- This is used so as to keep the World during Compilation, since types are erased. (???)
    wi : World
    eq : wi ≡ w
    v : A


private
  variable
    α β : Level
    w w₁ w₂ : World

HSet : ∀{α} → Set (suc α)
HSet {α} = (w : World) → Set α

private
  variable
    HA HB HC : HSet {α}

infix 1 ⊨_

⊨_ : HSet {α} → Set α
⊨ HA = ∀ {w} → HA w

⟨_⟩ : Set α → HSet {α}
⟨ A ⟩ w = A

infix 9 !_!_

!_!_ : World → HSet {α} → HSet
(! w' ! HA ) w = HA w'


○ : HSet → HSet
○ HA w = CO w (HA w)

infixr 8 _⇒_

_⇒_ : HSet {α} → HSet {α} → HSet
(HA ⇒ HB) w = HA w → HB w

∀w : (World → HSet {α}) → HSet
∀w F w = ∀ w' → (F w') w

∃w : (World → HSet {α}) → HSet
∃w F w = Σ World (λ w' → F w' w)

infix 10 _∨_
_∨_ : (HA HB : HSet {α}) → HSet
(HA ∨ HB) w = HA w ⊎ HB w

⊞_ : (World → HSet {α}) → HSet
(⊞ F) = ∀w (λ w' → ! w' ! (F w'))

infix 11 □_

□_ : HSet {α} → HSet
(□ HA) = ∀w (λ w' → ! w' ! HA)

infix 11 ◇_
◇_ : HSet {α} → HSet
◇ HA = ∃w (λ x → !_!_ x HA)

□-refl : ⊨ □ HA ⇒ HA
□-refl {w = w} □a = □a w

K : ⊨ □ (HA ⇒ HB) ⇒ □ HA ⇒ HB
K {w = w} □a⇒b □a = □a⇒b w (□a w)

◇v : ⊨ ◇ (HA ∨ HB) ⇒ ◇ HA ∨ ◇ HB 
◇v (w′ , inj₁ x) = inj₁ (w′ , x)
◇v (w′ , inj₂ y) = inj₂ (w′ , y)

◇5 : ⊨ ◇ □ HA ⇒ □ HA
◇5 (w' , □a) = □a

curry5 : ⊨ (◇ HA ⇒ □ HB) ⇒ □ (HA ⇒ HB)
curry5 ◇a⇒□b w' a = ◇a⇒□b (w' , a) w'

□trans : ⊨ □ HA ⇒ □ □ HA
□trans □a w' = □a

◇refl : ⊨ HA ⇒ ◇ HA
◇refl {w = w} a = w , a

◇trans : ⊨ ◇ ◇ HA ⇒ ◇ HA
◇trans {w = w} (w' , ◇a) = ◇a

K◇ : ⊨ □ (HA ⇒ HB) ⇒ ◇ HA ⇒ ◇ HB
K◇ □a⇒□b (w' , a) = w' , □a⇒□b w' a 

◇⊥ : ⊨ ◇ ⟨ ⊥ ⟩ ⇒ ⟨ ⊥ ⟩
◇⊥ (w' , a) = a

□5 : ⊨ ◇ HA ⇒ □ ◇ HA
□5 ◇a w'' = ◇a

casev : ⊨ ! w ! (HA ∨ HB)
        ⇒ (! w ! HA ⇒ ! w₁ ! HC)
        ⇒ (! w ! HB ⇒ ! w₁ ! HC)
        ⇒  ! w₁ ! HC
casev (inj₁ x) a->c b->c = a->c x
casev (inj₂ y) a->c b->c = b->c y


unatv : (! w₁ ! HA) w → HA w₁
unatv x = x



return : ⊨ HA ⇒ ○ HA
CO.wi (return {w = w} x) = w
CO.eq (return x) = refl
CO.v (return x) = x

_>>=_ : ⊨ ○ HA ⇒ (HA ⇒ ○ HB) ⇒ ○ HB
CO.wi (_>>=_ {w = w} x f) = w
CO.eq (_>>=_ x f) = refl
CO.v (_>>=_ x f) = CO.v (f (CO.v x))


postulate
  get    : ∀ {w' w S} → CO w' S → CO w S


↓ : ⊨ (! w₁ ! ○ HA) ⇒ ○ (! w₁ ! HA)
↓ = get


