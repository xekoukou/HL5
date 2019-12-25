module Internal where

import Level as L
open import Relation.Binary.PropositionalEquality
open import Common public

private
  variable
    α β : L.Level

-------------------------------------------
-- Desugared (Internal) Structures that need to be
-- compiled by the backend.

-- Concurrent Indexed Container.
record CO (w : World) (A : Set α) : Set α where
  constructor co
  field
-- This is used so as to keep the World during Compilation, since types are erased. (???)
    wi : World
    eq : wi ≡ w
    v : A

postulate
  get    : ∀ {S} → ∀ w' w → CO {α} w' S → CO w S

ISet : Set (L.suc α)
ISet {α} = (w : World) → Set α

return : ∀{IA : ISet {α}} → (w : World) → IA w → CO w (IA w)
CO.wi (return w x) = w
CO.eq (return w x) = refl
CO.v (return w x) = x

bind : {IA : ISet {α}} {IB : ISet {β}} → (w : World)
        → CO w (IA w) → (IA w → CO w (IB w)) → CO w (IB w)
CO.wi (bind w x f) = w
CO.eq (bind w x f) = refl
CO.v (bind w x f) = CO.v (f (CO.v x))

COₛ : (w : World) → CO w (Set α) → Set α
COₛ w Q = CO w (CO.v Q)

bind2 : {IA : ISet {α}} → (w : World) → {IP : (w' : World) → IA w' → CO w' (Set α)}
         → (ia : CO w (IA w)) → ((a : IA w) → COₛ w (IP w a)) → COₛ w (bind {IA = IA} w ia (IP w))
CO.wi (bind2 w x f) = w
CO.eq (bind2 w x f) = refl
CO.v (bind2 w x f) = CO.v (f (CO.v x))

