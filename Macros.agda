module Macros where

-------------------------------------------
-- Macros for the implicit arguments.

open import Reflection
open import Agda.Builtin.Reflection
open import Prelude.List
open import Prelude.Maybe
open import Prelude.Nat
open import Prelude.Ord
open import Prelude.Semiring
open import Prelude.Function
open import Prelude.Unit
open import Prelude.Bool
open import Prelude.Product

open import Common

-------------------------------------------------
-- The macro iw finds the fist implicit argument of type World that is in context.
-- This way, we can have pointwise application of the world in Sets.
-- ex. ⟦ HA → HB ⟧

private

  -- It finds the first implicit argument that is of type World.
  findWorld : List (Arg Type) → TC (Maybe Nat)
  findWorld [] = return nothing
  findWorld (arg (arg-info hidden _) (def f args) ∷ ts)
    = case (primQNameEquality f (quote World)) of
        λ { false → do
                      r ← findWorld ts
                      return (maybe nothing (λ x → just (suc x)) r)
          ; true → return (just 0)}
  findWorld (_ ∷ ts) = do
                         r ← findWorld ts
                         return (maybe nothing (λ x → just (suc x)) r)
  
iw : Term → TC ⊤
iw hole
  = do
       ctx ← getContext
       r ← (findWorld ctx)
       case r of λ { nothing → typeError (strErr "Couldn't find implicit argument of type World." ∷ [])
                   ; (just x) → unify (var x []) hole}


------------------------------------------------
-- Because HSets are paremetric to an implicit variable w , the constraints cannot be solved because
-- the solution to them is not unique, there are multiple HSet that are equal at a specific world w.
-- The macro ihs finds the first of those HSets that fits by inspecting on the constraints.

  
private

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

  h2 : List (Closure Constraint) → (Constraint → TC (Maybe Term)) → TC (Maybe Term)
  h2 [] f = return nothing
  h2 (closure _ x ∷ xs) f = do
    v ← f x
    case v of
      λ { nothing → h2 xs f
        ; (just x) → return (just x)}


  h1' : Meta → Constraint → TC (Maybe Term)
  h1' m (valueCmp _ _ (meta m' (_ ∷ _)) t) with (primMetaEquality m m')
  ... | false = return nothing
  ... | true = typeError (strErr "aha" ∷ [])
  h1' m (valueCmp _ _ t (meta m' (_ ∷ _))) with (primMetaEquality m m')
  ... | false = return nothing
  ... | true = typeError (strErr "aha2" ∷ [])
  h1' _ unsupported = return nothing
  h1' _ _ = typeError (strErr "Invalid constraint." ∷ []) 

  h1 : Meta → Constraint → TC (Maybe Term)
  h1 m (valueCmp _ _ (meta _ _) (meta _ _))
    = typeError (strErr "HL5 Internal Error. Please report this." ∷ [])
                                               -- Is this even possible ?
                                               -- I think this constraint would have been immediately removed.
  h1 m (valueCmp _ _ (meta m' (_ ∷ _)) t) with (primMetaEquality m m')
  ... | false = return nothing
  h1 m (valueCmp _ _ (meta m' (_ ∷ _)) (var x args@(y ∷ ys))) | true
    = return (just (var x (take (length args - 2) args)))
  h1 m (valueCmp _ _ (meta m' (_ ∷ _)) (con c args@(y ∷ ys))) | true
    = return (just (con c (take (length args - 2) args)))
  h1 m (valueCmp _ _ (meta m' (_ ∷ _)) (def f args@(y ∷ ys))) | true
    = return (just (def f (take (length args - 2) args)))
  h1 m (valueCmp _ _ (meta m' (_ ∷ _)) (pat-lam cs args@(y ∷ ys))) | true
    = return (just (pat-lam cs (take (length args - 2) args)))
  h1 m (valueCmp _ _ (meta m' (_ ∷ _)) t) | true = return (just  (lam hidden (abs "wₘ" (h4 t 0))))
  h1 m (valueCmp _ _ t (meta m' (_ ∷ _))) with (primMetaEquality m m')
  ... | false = return nothing
  h1 m (valueCmp _ _ (var x args@(y ∷ ys)) (meta m' (_ ∷ _))) | true
    = return (just (var x (take (length args - 2) args)))
  h1 m (valueCmp _ _ (con c args@(y ∷ ys)) (meta m' (_ ∷ _))) | true
    = return (just (con c (take (length args - 2) args)))
  h1 m (valueCmp _ _ (def f args@(y ∷ ys)) (meta m' (_ ∷ _))) | true
    = return (just (def f (take (length args - 2) args)))
  h1 m (valueCmp _ _ (pat-lam cs args@(y ∷ ys)) (meta m' (_ ∷ _))) | true
    = return (just (pat-lam cs (take (length args - 2) args)))
  h1 m (valueCmp _ _ t (meta m' (_ ∷ _))) | true = return (just (lam hidden (abs "wₘ" (h4 t 0))))
  h1 _ unsupported = return nothing
  h1 _ _ = typeError (strErr "Invalid constraint." ∷ []) 

  h3 : Term → TC (Maybe Meta)
  h3 (lam hidden (abs _ (meta m _))) = return (just m)
  h3 (lam hidden (abs _ t)) = return nothing
  h3 t = typeError (termErr t ∷ [])

ihs : Term → TC ⊤
ihs hole = 
  do
     delayMacro
     typ ← inferType hole
--     typeError {A = ⊤} (termErr typ ∷ [])
     nhole ← checkType hole typ
--     typeError {A = ⊤} (termErr nhole ∷ [])
     tm ← h3 nhole
     case tm of
       λ { nothing → return tt -- The meta has already being solved.
         ; (just m) → do
                         mtype ← inferType (meta m [])
--                         typeError {A = ⊤} (termErr mtype ∷ [])
                         cs ← getConstraintsMentioning (m ∷ [])
                         mt ← h2 cs (h1 m)
                         case mt of
                           λ { nothing → return tt -- The meta has already being solved,
                                                   -- (probably because of an old constraint.)
                             ; (just t) → unify (meta m []) t}}


---------------------------------------------
-- ifs

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
                       unify hole nhole -- ???
        ; (just m) →
             do
               cs ← getConstraintsMentioning (snd m ∷ [])
               mt ← h2 cs h12
               case mt of
                 λ { nothing → return tt -- The meta has already being solved,
                                         -- (probably because of an old constraint.)
                   ; (just t) → unify hole t}}
