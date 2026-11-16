{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Types for DependentContextExamples. They are in a module of their own
-- because a capture refuses definitions of its own file that do not unfold
-- (CaptureOpaqueLocal): source and context types must be imported.
module DependentContextFixtures where

open import Foundations
open import Agda.Builtin.Bool
open import DecidableBase using (DecEq; yes)
open import BoolDecidable using (bool-dec)

-- A family of types with decidable equality over Bool.
Code : Bool → Set
Code true = Bool
Code false = ⊤

code-dec : (@♭ b : Bool) → DecEq (Code b)
code-dec true = bool-dec
code-dec false = λ _ _ → yes refl

-- A source type that depends on both variables of the context.
Source : (b : Bool) → Code b → Set
Source true true = Bool
Source true false = ⊤
Source false _ = Bool × Bool
