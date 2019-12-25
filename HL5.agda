module HL8 where


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

postulate
  World : Set

private
  variable
    α β : L.Level

-------------------------------------------
-- Macros for the implicit arguments.

module _ where

  open import Reflection
  open import Agda.Builtin.Reflection
  
  _ifMeta_else_ : {A : Set} → Term → (Meta → List (Arg Term) → TC A) → TC A → TC A
  meta x args ifMeta f else k = f x args
  _ ifMeta _ else k = k

  _ifMeta_ : {A : Set} → Term → (Meta → List (Arg Term) → TC A) → TC A
  t ifMeta f = t ifMeta f else (typeError ((strErr "Not possible") ∷ []))

  private
    -- It finds the first implicit argument that is of type World.
    findWorld : List (Arg Type) → TC (Maybe Nat)
    findWorld [] = return nothing
    findWorld (arg (arg-info hidden _) (def f args) ∷ ts)
      = case (primQNameEquality f (quote World)) of
          λ { false → do
                        r ← findWorld ts
                        case r of
                          λ { nothing → return nothing
                            ; (just x) → return (just (suc x))}
            ; true → return (just 0)}
    findWorld (_ ∷ ts) = do
                           r ← findWorld ts
                           case r of
                             λ { nothing → return nothing
                               ; (just x) → return (just (suc x))}
    
  iw : Term → TC ⊤
  iw hole
    = hole ifMeta (λ _ _ → 
       do
         ctx ← getContext
         r ← (findWorld ctx)
         case r of λ { nothing → typeError (strErr "Couldn't find implicit argument of type World." ∷ [])
                     ; (just x) → unify (var x []) hole})
  

  module _ where

    h5 : (f : Term → Nat → Term) → Nat → Abs Term → Abs Term
    h5 f n (abs s x) = abs s (f x n)

    h6 : (f : Term → Nat → Term) → Nat → Arg Term → Arg Term
    h6 f n (arg i x) = arg i (f x n)

    mutual 
      h9 : Arg Pattern → Nat
      h9 (arg i x) = h8 x

      {-# TERMINATING #-}
      h8 : Pattern → Nat
      h8 (con c ps) = h10 ps
      h8 dot = zero
      h8 (var s) = suc zero
      h8 (lit l) = zero
      h8 (proj f) = zero
      h8 absurd = zero

      h10 : List (Arg Pattern) → Nat
      h10 = foldr (λ x y → y + (h9 x)) zero

    h7 : (f : Term → Nat → Term) → Nat → Clause → Clause
    h7 f n (clause ps t) = clause ps (f t (n + h10 ps))
    h7 f n (absurd-clause ps) = (absurd-clause ps)
    
    {-# TERMINATING #-}
    h4 : Term → Nat → Term
    h4 (var x args) n = case n ≤? x of
                               λ { true → var (suc x) (map (h6 h4 n) args)
                                 ; false → var x (map (h6 h4 n) args)}
    h4 (con c args) n = con c (map (h6 h4 n) args)
    h4 (def f args) n = def f (map (h6 h4 n) args)
    h4 (lam v t) n = lam v (h5 h4 (suc n) t)
    h4 (pat-lam cs args) n = pat-lam (map (h7 h4 n) cs) (map (h6 h4 n) args)
    h4 (pi a b) n = pi (h6 h4 n a) (h5 h4 (suc n) b)
    h4 (agda-sort (set t)) n = agda-sort (set (h4 t n))
    h4 (agda-sort (lit n₁)) n = agda-sort (lit n₁)
    h4 (agda-sort unknown) n = agda-sort unknown
    h4 (lit l) n = lit l
    h4 (meta x x₁) n = meta x x₁
    h4 unknown n = unknown
    
       
    h2 : List Constraint → (Constraint → TC (Maybe Term)) → TC Term
    h2 [] f = typeError (strErr "There are no valid constraints for this HSet." ∷ [])
    h2 (x ∷ xs) f = do
      v ← f x
      case v of
        λ { nothing → h2 xs f
          ; (just x) → return x}


    private

      h3 : Term → Maybe Meta
      h3 (lam hidden (abs _ (meta m _))) = just m
      h3 v = nothing

      h1 : Meta → Constraint → TC (Maybe Term)
      h1 m (valueCmp _ _ (meta _ _) (meta _ _))
        = return nothing
      h1 m (valueCmp _ _ (meta m' _) t) with (primMetaEquality m m')
      ... | false = return nothing
      ... | true
        = return (just (h4 t 0))
      h1 m (valueCmp _ _ t (meta m' _)) with (primMetaEquality m m')
      ... | false = return nothing
      ... | true
        = return (just (h4 t 0))
      h1 _ unsupported = return nothing
      h1 _ _ = typeError (strErr "Invalid constraint." ∷ []) 

    ihs : Term → TC ⊤
    ihs hole = hole ifMeta λ m _ →
      do
       
         delayMacro
         typ ← inferType hole
         nhole ← checkType hole typ
         case (h3 nhole) of
           λ { nothing → unify hole nhole
             ; (just m) → do
                            cs ← getConstraintsMentioning (m ∷ [])
                            t ← h2 cs (h1 m)
                            unify hole (lam hidden (abs "w" t))}

  module _ where
    private
      h11 : Term → Maybe (Bool × Meta)
      h11 (lam _ (abs _ (lam _ (abs _ (con _ (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ (arg _ (meta m _)) ∷ [])))))) = just (true , m)
      h11 (lam _ (abs _ (con _ (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ (arg _ (meta m _)) ∷ [])))) = just (false , m)
      h11 v = nothing

      h12 : Constraint → TC (Maybe Term)
      h12 (valueCmp _ _ (meta _ _) (def _ (_ ∷ _ ∷ _ ∷ arg _ (var x []) ∷ [])))
        = return (just (var x []))
      h12 (valueCmp _ _ (meta _ _) (def _ (_ ∷ _ ∷ _ ∷ arg _ (con c []) ∷ [])))
        = return (just (con c []))
      h12 (valueCmp _ _ (meta _ _) (def _ (_ ∷ _ ∷ _ ∷ arg _ (def f []) ∷ [])))
        = return (just (def f []))
      h12 (valueCmp _ _ (meta _ _) (def _ (_ ∷ _ ∷ _ ∷ arg _ (pat-lam cs []) ∷ [])))
        = return (just (pat-lam cs []))
      h12 (valueCmp _ _ (def _ (_ ∷ _ ∷ _ ∷ arg _ (var x []) ∷ [])) (meta _ _))
        = return (just (var x []))
      h12 (valueCmp _ _ (def _ (_ ∷ _ ∷ _ ∷ arg _ (con c []) ∷ [])) (meta _ _))
        = return (just (con c []))
      h12 (valueCmp _ _ (def _ (_ ∷ _ ∷ _ ∷ arg _ (def f []) ∷ [])) (meta _ _))
        = return (just (def f []))
      h12 (valueCmp _ _ (def _ (_ ∷ _ ∷ _ ∷ arg _ (pat-lam cs []) ∷ [])) (meta _ _))
        = return (just (pat-lam cs []))
      h12 (valueCmp _ _ (meta _ _) (def _ (_ ∷ _ ∷ _ ∷ arg _ (var x args@(y ∷ ys)) ∷ [])))
        = return (just (var x (take (length args - 2) args)))
      h12 (valueCmp _ _ (meta _ _) (def _ (_ ∷ _ ∷ _ ∷ arg _ (con c args@(y ∷ ys)) ∷ [])))
        = return (just (con c (take (length args - 2) args)))
      h12 (valueCmp _ _ (meta _ _) (def _ (_ ∷ _ ∷ _ ∷ arg _ (def f args@(y ∷ ys)) ∷ [])))
        = return (just (def f (take (length args - 2) args)))
      h12 (valueCmp _ _ (meta _ _) (def _ (_ ∷ _ ∷ _ ∷ arg _ (pat-lam cs args@(y ∷ ys)) ∷ [])))
        = return (just (pat-lam cs (take (length args - 2) args)))
      h12 (valueCmp _ _ (def _ (_ ∷ _ ∷ _ ∷ arg _ (var x args@(y ∷ ys)) ∷ [])) (meta _ _))
        = return (just (var x (take (length args - 2) args)))
      h12 (valueCmp _ _ (def _ (_ ∷ _ ∷ _ ∷ arg _ (con c args@(y ∷ ys)) ∷ [])) (meta _ _))
        = return (just (con c (take (length args - 2) args)))
      h12 (valueCmp _ _ (def _ (_ ∷ _ ∷ _ ∷ arg _ (def f args@(y ∷ ys)) ∷ [])) (meta _ _))
        = return (just (def f (take (length args - 2) args)))
      h12 (valueCmp _ _ (def _ (_ ∷ _ ∷ _ ∷ arg _ (pat-lam cs args@(y ∷ ys)) ∷ [])) (meta _ _))
        = return (just (pat-lam cs (take (length args - 2) args)))
      h12 _ = return nothing
    
    ifs : Term → TC ⊤
    ifs hole =
      do
         delayMacro
         typ ← inferType hole
         nhole ← checkType hole typ
         case (h11 nhole) of
          λ { nothing → do
                           unify hole nhole
            ; (just m) →
                 do
                   cs ← getConstraintsMentioning (snd m ∷ [])
                   t ← h2 cs h12
                   unify hole t}
    
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

