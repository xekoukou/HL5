module Examples where


open import HL5

open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Function
open import Level

open import Data.Nat
open import Data.Unit
open import Data.String
open import Data.Bool


-- Hello

hello : ⊨ ○ ⟨ String ⟩
hello = return "hello!!"

helloName : ∀ w → ⊨ ! w ! ○ ⟨ String ⟩ ⇒ ○ ⟨ String ⟩
helloName w v
  = do nm ← ↓ v
       return ("hello " ++ nm)


-- Ping Pong

data Piong : Set where
  ping : Piong
  pong : Piong

pingOnce : ∀ q → ⊨ ○ ⟨ Piong ⟩ ⇒ ! q ! ○ ⟨ Piong ⟩
pingOnce q png
  = do
       z ← ↓ png
       case z of λ { ping → return pong
                   ; pong → return ping}


-- The initial ping is sent by the implicit world {w₁}
gpingN : ∀ w q → ℕ → ⊨ ○ ⟨ Piong ⟩ ⇒ ! q ! ○ ⟨ Piong ⟩
gpingN w q zero png = pingOnce q png
gpingN w q (suc n) png = gpingN w q n (pingOnce w (pingOnce q png))

pingN : ∀ w q → ⊨ ! w ! ○ ⟨ Piong ⟩ ⇒ ! q ! ○ ⟨ Piong ⟩
pingN w q = gpingN w q 5 {w}

postulate
  Env : World


ee : ⊢ ⟨ ℕ ⟩ ⇒ ⟨ Set ⟩
ee w zero = String
ee w (suc x) = ℕ

gg : ⊢ ee ⇒ᵈHSet
gg w (ℕ.zero , snd) = String
gg w (ℕ.suc e , ℕ.zero) = String
gg w (ℕ.suc e , ℕ.suc snd) = ℕ

nn : ⊢ gg ⇒ᵈHSet
nn = ⊢⊨ λ { ((ℕ.zero , snd₁) , snd) → {!!} ; ((ℕ.suc fst , snd₁) , snd) → {!!}}

dd : ⊨ gg ⇒ᵈHVal
dd (ℕ.zero , snd) = "Ahoy"
dd (ℕ.suc fst , ℕ.zero) = "ole"
dd (ℕ.suc fst , ℕ.suc snd) = 3


-- Dependent types

module _ where

  open import Data.Bool

  F : Bool → Set
  F false = String
  F true = ℕ

  d : (b : Bool) → F b
  d false = "Aha"
  d true = 3

  ll : ∀ w → ⊨ ○ ⟨ Bool ⟩ ⇒ ! w ! ○ ⟨ Set ⟩
  ll w v = do
             b ← ↓ v
             return (F b)

private
  variable
    α β : Level


  ff : Bool → ⊢ ⟨ Set ⟩
  ff = λ { false → ⟨ String ⟩ ; true → ⟨ ℕ ⟩ }

  mm : ∀ w → ⊢ ⟨ Bool ⟩ ⇒ ⟨ Set ⟩
  mm w w₁ b = (! w ! ○ (case b of ff )) w₁
               

--  rr : ∀ w → ⊨ (mm w ○⇒ᵈHVal)
--  rr w v = _>>=_ {HB = λ _ → ff (CO.v v) w} (↓ v) λ { false → {!!}
--                                                    ; true → {!!}} where


----------


  dsd : ∀ {w} → ⊢ ○ ⟨ Bool ⟩ ⇒ ! w ! ○ ⟨ Set ⟩
  dsd = ⊢⊨ λ v → do
                    b ← ↓ v
                    case b of λ { false → return String
                                ; true → return ℕ}


  private
    variable
      HA HB HC : HSet {α}


  sds : (S : ⊢ ○ ⟨ Set ⟩) → HSet
  sds S w = CO.v (S w)

  dwd : ⊢ ○ ⟨ Set ⟩ ⇒ ⟨ Set ⟩
  dwd w x = CO.v x
-- 
--   qqw : ∀ w → ⊨ !! w !! dsd ○⇒ᵈHVal
--   qqw w v with get {w = w} v
--   ... | q = do
--               s ← q
--               case s of λ { false → {!!}
--                           ; true → {!!}}
-- 
  -- qq : (S : ⊢ ○ ⟨ Set ⟩) → ⊨ sds S
  -- qq = {!!}
  
  -- vv : ∀ w → (ff : ⊢ ○ ⟨ Bool ⟩ ⇒ ! w ! ○ ⟨ Set ⟩) → {!!}
  -- vv w ff w₁ = (v : (○ ⟨ Bool ⟩) w₁) → {!!}


_>>=ᵈ_ : (f : ⊢ HA ⇒ ○ ⟨ Set ⟩ ) → ⊨ (HA ⇒ ○ HB) ⇒ ○ HA ⇒ ○ HB
_>>=ᵈ_ = {!!}

VSet : Set₁
VSet = World → Set

a : {VS : VSet} → ∀ w → VS w → ⊤
a = {!!}

b : {VS : VSet} → ∀ w → VS w → ⊤
b = {!!}



_>>=a_ : ⊨ ○ HA ⇒ (HA ⇒ ○ HB) ⇒ ○ HB
_>>=a_ = _>>=_
