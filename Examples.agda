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

private
  variable
    α : Level

End : (A : Set α) → ∀ w → HSet {α}
End A w = ! w ! ○ ⟨ A ⟩ → ○ ⟨ ⊤ ⟩
  
end : ∀ A w → ⟦ End {α} A w ⟧
end A w t = ↓ (t >>= λ _ → return tt)


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
  
  
  system : ⟦( ! Bob ! (Hello Tom) → ! Tom ! Name → ! Env ! End String Tom → ! Env ! ○ ⟨ ⊤ ⟩ )⟧
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

giveMeS : ∀ w → ⟦ GiveMeS w ⟧′
giveMeS w aNum = return Nat
giveMeS w aString = return String

GiveMe : ∀ w → HSet
GiveMe w = (what : ! w ! ○ ⟨ What ⟩) → ○ₛ (↓ what >>= giveMeS w)

giveMe : ∀ w → ⟦ GiveMe w ⟧′
giveMe w v = (↓ v) >>=ᵈ λ { aNum → return 3
                          ; aString → return "I can only give you my word."}


