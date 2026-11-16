{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Decidable equality, sethood and discreteness of Bool, in a module that
-- declares no axiom and makes no capture.
-- fable-impl-10. Until fable-impl-09 this function was defined in
-- OpenContextExamples, so that every user of it had the three captures of
-- that file in its import closure (M7-EXTERNAL-PRODUCT-SOURCE-AUDIT-01
-- section 7; CURRENT-REFLECTION-DISPOSITION-01 item 4).
-- OpenContextExamples now re-exports it from here under the same name.
module BoolDecidable where

open import Foundations
open import Agda.Builtin.Bool
open import DecidableBase using (DecEq; yes; no; decidable-set)

bool-dec : DecEq Bool
bool-dec false false = yes refl
bool-dec true true = yes refl
bool-dec false true = no (λ ())
bool-dec true false = no (λ ())

-- Sethood and discreteness of Bool, for fixtures that should not import
-- ClosedSliceExamples (which declares two source types and two shapes).
-- ClosedSliceExamples has its own proofs, bool-set and bool-discrete; the
-- older examples keep using those.
bool-is-set : IsSet Bool
bool-is-set = decidable-set bool-dec

bool-is-discrete : Discrete Bool
bool-is-discrete false = (box false , refl) , λ where
  (box false , refl) → refl
bool-is-discrete true = (box true , refl) , λ where
  (box true , refl) → refl
