module Examples2 where


open import HL8

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


-- Hello World.

module HelloWorld where

  postulate
    Bob : World
    Tom : World
    Env : World
  
  
  Name : HSet
  Name = ○ ⟨ String ⟩
  
  name : ⟦ Name ⟧
  name = return "Tom"
  
  Hello : ∀ w → HSet
  Hello w = ! w ! ○ ⟨ String ⟩ → ○ ⟨ String ⟩
  
  hello : ∀ w' → ⟦ Hello w' ⟧
  hello w' v 
    = do
         nm ← ↓ v
         return ("Hello " ++ nm)
  
  End : ∀ w → HSet
  End w = ! w ! ○ ⟨ String ⟩ → ○ ⟨ ⊤ ⟩
  
  end : ∀ w → ⟦ End w ⟧
  end w t = ↓ (t >>= λ _ → return tt)
  
  system : ⟦( ! Bob ! (Hello Tom) → ! Tom ! Name → ! Env ! End Tom → ! Env ! ○ ⟨ ⊤ ⟩ )⟧
  system hnm hl end
    = end (↓ (hnm hl))

-- I am at your command.

open import Prelude.Nat

postulate
  Client : World
  Server : World

data What : Set where
  aNum    : What
  aString : What

GiveMeS : ∀ w → HSet
GiveMeS w = ! w ! ⟨ What ⟩ → ○ ⟨ Set ⟩

giveMeS : ∀ w → ⟦ GiveMeS w ⟧
giveMeS w q
  = do
      case q of
        λ { aNum → return Nat
          ; aString → return String}

GiveMe : ∀ w → HSet
GiveMe w = (what : ! w ! ○ ⟨ What ⟩) → ○ₛ (↓ what >>= giveMeS w)

giveMe : ∀ w → ⟦ GiveMe w ⟧
giveMe w v = (↓ v) >>=2 {!!}
