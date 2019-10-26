module Examples where


open import HL5

open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Function
open import Level

open import Data.Nat
open import Data.String


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
