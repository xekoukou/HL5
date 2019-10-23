module HL5 where

open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Level

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
    α β : Level
    w w₁ w₂ : World

HSet : ∀{α} → Set (suc α)
HSet {α} = (w : World) → Set α

private
  variable
    HA HB HC : HSet {α}

infix 1 ⊨_

⊨_ : HSet {α} → Set α
⊨_ HA = ∀ w → HA w

⟨_⟩ₛ : Set α → HSet
⟨ A ⟩ₛ w = A

⟨_⟩ : ∀{A : Set α} → A → ⊨ ⟨ A ⟩ₛ
⟨ a ⟩ w = a

infix 9 !_!ₛ_
infix 9 !_!_

!_!ₛ_ : World → HSet {α} → HSet
(! w' !ₛ HA ) w = HA w'

!_!_ : (w : World) → ⊨ HA → ⊨ ! w !ₛ HA
(! w ! a) w' = a w

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
□-refl w □a = □a w

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

infixl 8 _$_

_$_ : ⊨ HA ⇒ HB → ⊨ HA → ⊨ HB
(f $ b) w = f w (b w)

casev : (HA ∨ HB) w
        → (HA w → HC w₁)
        → (HB w → HC w₁)
        → HC w₁
casev (inj₁ x) a->c b->c = a->c x
casev (inj₂ y) a->c b->c = b->c y


unatv : (! w₁ ! HA) w → HA w₁
unatv x = x


return : ⊨ HA ⇒ ○ HA
CO.wi (return w x) = w
CO.eq (return w x) = refl
CO.v (return w x) = x

bind : ⊨ ○ HA ⇒ (HA ⇒ ○ HB) ⇒ ○ HB
CO.wi (bind w x f) = w
CO.eq (bind w x f) = refl
CO.v (bind w x f) = CO.v (f (CO.v x))


postulate
  ↓    : ∀ {w' w S} → CO w' S → CO w S

-- postulate
--   return : ∀ {w S} → S → CO w S
--   _>>=_    : ∀ {w S S'} → CO w S → (S → CO w S') → CO w S'
--   ↓    : ∀ {w' w S} → CO w' S → CO w S

infixl 8 _$ₒ_

_$ₒ_ : ⊨ ○ (HA ⇒ HB) → ⊨ ○ HA → ⊨ ○ HB
_$ₒ_ {HA} {HB} f a = q where
  g : ⊨ (HA ⇒ HB) ⇒ ○ HB
  g _ f = bind {HA = HA} {HB = HB} _ (a _) λ x → return {HA = HB} _ (f x)
  q = bind $ f $ g

open import Data.Nat

hello : ∀ w → ⊨ ! w ! ○ ⟨ ℕ ⟩
hello w = ! w ! (bind $ (return $ ⟨ 3 ⟩) $ {!return $ (⟨ _+_ ⟩ $ ⟨ 3 ⟩)!})
