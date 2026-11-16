{-# OPTIONS --cohesion --without-K --flat-split #-}

-- A ROOTED inventory of shape axioms, by reflection. Claude (Fable),
-- 13 November 2026; generator checkpoint after fable-impl-11. A test tool:
-- nothing of the frontend or of the library imports it.
--
--   shape-axioms diagrams wrappers
-- is the number of DISTINCT names that head the normal forms of
--   ClosedField.KB d, ClosedField.KC d   for d in `diagrams`,
--   C.Output.whole-context s             for s in `wrappers`,
-- where every name is given at top level, without arguments. Names are
-- compared as names, not as printed text: two generated axioms print
-- alike. Each head must be a name that reflection reports as an axiom;
-- otherwise the macro fails.
--
-- WHAT THIS IS: a count of SELECTED NORMALISED PAYLOAD HEADS. In the
-- terms of DECLARATION-INVENTORY-TOOLING-01 it bears on question C for
-- the listed roots, in payload positions only, and it is less than the
-- reachability inventory proposed there:
--   * it does not traverse types, arguments of the head, function bodies
--     or other declarations, so it is not a dependency closure;
--   * it is not the signature of the file (question A): an axiom that no
--     listed payload has as its head is not seen;
--   * it does not look for metas inside the arguments it discards, and
--     it does not enforce that a root is a completed closed top-level
--     name; the roots of the tests are, by inspection;
--   * reflection reports abstract definitions as axioms too; the heads
--     met in the tests are the generated constants  contextual-shape (0).
-- The wider inventory (REFLECTION-ISSUES R46) remains open.
module DiagramInventory where

import CapturedShape as C
open import DiagramData using (module ClosedField)
open import Agda.Builtin.Reflection
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Unit using (⊤; tt)

private
  infixl 1 _>>=_
  _>>=_ = bindTC
  ret = returnTC

  v : {A : Set} → A → Arg A
  v = arg (arg-info visible (modality relevant quantity-ω))

  headOf : Term → TC Name
  headOf (def n _) = ret n
  headOf t = typeError
    (strErr "The payload does not reduce to an applied name: " ∷ termErr t ∷ [])

  reported : Name → Definition → TC Name
  reported n axiom = ret n
  reported n _ = typeError
    (strErr "The head of the payload is not reported as an axiom: " ∷ nameErr n ∷ [])

  payloadHead : Term → TC Name
  payloadHead t =
    normalise t >>= headOf >>= λ n → getDefinition n >>= reported n

  member : Name → List Name → Bool
  member n [] = false
  member n (m ∷ ms) with primQNameEquality n m
  ... | true = true
  ... | false = member n ms

  insert : Name → List Name → List Name
  insert n ns with member n ns
  ... | true = ns
  ... | false = n ∷ ns

  length : List Name → Nat
  length [] = zero
  length (_ ∷ ns) = suc (length ns)

  ofDiagram : Name → List Term
  ofDiagram d =
    def (quote ClosedField.KB) (v (def d []) ∷ []) ∷
    def (quote ClosedField.KC) (v (def d []) ∷ []) ∷ []

  ofWrapper : Name → Term
  ofWrapper s = def (quote C.Output.whole-context) (v (def s []) ∷ [])

  append : List Term → List Term → List Term
  append [] ys = ys
  append (x ∷ xs) ys = x ∷ append xs ys

  payloads : List Name → List Name → List Term
  payloads [] [] = []
  payloads [] (s ∷ ss) = ofWrapper s ∷ payloads [] ss
  payloads (d ∷ ds) ss = append (ofDiagram d) (payloads ds ss)

  heads : List Term → List Name → TC (List Name)
  heads [] seen = ret seen
  heads (t ∷ ts) seen = payloadHead t >>= λ n → heads ts (insert n seen)

macro
  shape-axioms : List Name → List Name → Term → TC ⊤
  shape-axioms diagrams wrappers hole =
    withNormalisation false (withReconstructed false
      (heads (payloads diagrams wrappers) [])) >>= λ ns →
    unify hole (lit (nat (length ns)))
