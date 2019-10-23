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
⊨_ HA = ∀{w} → HA w

⟨_⟩ₐ : ∀{A} → A → ⊨ ⟨ A ⟩
⟨ a ⟩ₐ = a

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
◇trans (w' , ◇a) = ◇a

K◇ : ⊨ □ (HA ⇒ HB) ⇒ ◇ HA ⇒ ◇ HB
K◇ □a⇒□b (w' , a) = w' , □a⇒□b w' a 

◇⊥ : ⊨ ◇ ⟨ ⊥ ⟩ ⇒ ⟨ ⊥ ⟩
◇⊥ (w' , a) = a

□5 : ⊨ ◇ HA ⇒ □ ◇ HA
□5 ◇a w'' = ◇a

_$_ : ⊨ HA ⇒ HB → ⊨ HA → ⊨ HB
(f $ b) {w = w} = f {w = w} (b {w = w})

casev : (HA ∨ HB) w
        → (HA w → HC w₁)
        → (HB w → HC w₁)
        → HC w₁
casev (inj₁ x) a->c b->c = a->c x
casev (inj₂ y) a->c b->c = b->c y


unatv : (HA at w₁) w → HA w₁
unatv x = x


return : ⊨ HA ⇒ ○ HA
CO.wi (return {w = w} x) = w
CO.eq (return x) = refl
CO.v (return x) = x

_>>=_ : ⊨ ○ HA ⇒ (HA ⇒ ○ HB) ⇒ ○ HB
CO.wi (_>>=_ {w = w} x f) = w
CO.eq (_>>=_ x f) = refl
CO.v (_>>=_ x f) = CO.v (f (CO.v x))

pure : ∀{A} → ⊨ ⟨ A ⟩ ⇒ ○ ⟨ A ⟩
pure = return


postulate
  ↓    : ∀ {w' w S} → CO w' S → CO w S

-- postulate
--   return : ∀ {w S} → S → CO w S
--   _>>=_    : ∀ {w S S'} → CO w S → (S → CO w S') → CO w S'
--   ↓    : ∀ {w' w S} → CO w' S → CO w S


open import Data.Nat

hello : ⊨ ○ ⟨ ℕ ⟩ at client
hello =  {!return {HA = ?} {w = ?} $ ?!} -- return {HA = {!!}} {w = {!!}} {!!} 