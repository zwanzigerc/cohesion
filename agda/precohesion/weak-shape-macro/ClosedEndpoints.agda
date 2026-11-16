{-# OPTIONS --cohesion --without-K --flat-split #-}

-- SET-SOURCE STAGE C3: the two endpoints of the closed classifier agree
-- only under the support. Opus, 14 November 2026; opus-closed-limits-01
-- (delta 04), implementing FABLE-PLAN-SET-SOURCE-01 §6.1.
--
-- At the support data of PrincipalFilter.Principal sO … Quantified … Closed
-- (as the kernel's Support forms them):
--   c3-generic : for any Σ-type over O j with inclusion fst, a code p with
--                p-to-P, a point c over p, a point t over top: c ≡ t → P
--   C3.bottom  = (p , path-from p P-to-p), the kernel's false endpoint
--   C3.c3-bottom : bottom ≡ truth-point → P
-- Proof: ap inclusion gives p ≡ top in O j; Laws.truth-out gives El p;
-- p-to-P. Only the stated direction is used later. Nothing postulated.
module ClosedEndpoints where

open import Foundations
open import NativeSharp using (♯)
open import GlobalPrecohesion using (ShapeData)
open import GlobalPropositions using (FunExt₂)
open import SmallPropositions using (PropExt)
open import BaseClassifier using (O; El; top)
open import BaseClassifierLaws using (module Laws)
open import PrincipalFilter using (module Principal)

-- Generic form (used at the kernel with the kernel's OWN instance of the
-- support, so that no second instance of PrincipalFilter is compared with
-- it; FABLE-PLAN-SET-SOURCE-01 §13.1): C is any Σ over O j, inclusion is fst.
c3-generic : {@♭ i : Level} (@♭ fe-j : FunExt₂ (lsuc i) (lsuc i))
             (@♭ pe-j : PropExt (lsuc i))
           → {P : Set (lsuc i)} {X : O (lsuc i) → Set (lsuc (lsuc i))}
           → (p : O (lsuc i)) → (El p → P)
           → {c t : Σ (O (lsuc i)) X} → fst t ≡ top → fst c ≡ p → c ≡ t → P
c3-generic fe-j pe-j p p-to-P t-top c-p e =
  p-to-P (Laws.truth-out fe-j pe-j p (sym c-p ∙ ap fst e ∙ t-top))

module C3 {@♭ i : Level} (@♭ sO : ShapeData (♯ (O i)))
  (@♭ sQ : ShapeData (Principal.Q sO))
  (@♭ fe-i : FunExt₂ i i) (@♭ pe-i : PropExt i)
  (@♭ fe-j : FunExt₂ (lsuc i) (lsuc i))
  (@♭ sR : ShapeData (Principal.R sO))
  (@♭ pe-j : PropExt (lsuc i))
  (@♭ fe-jk : FunExt₂ (lsuc i) (lsuc (lsuc i))) where

  open Principal sO using (P; C; inclusion; truth-point)
  module Qd = Principal.Quantified sO sQ fe-i pe-i fe-j
  module Cl = Qd.Closed sR pe-j fe-jk

  bottom : C
  bottom = Qd.p , Cl.path-from Qd.p Qd.P-to-p

  c3-bottom : bottom ≡ truth-point → P
  c3-bottom = c3-generic fe-j pe-j Qd.p Qd.p-to-P refl refl
