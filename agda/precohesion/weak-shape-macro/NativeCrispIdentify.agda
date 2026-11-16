{-# OPTIONS --cohesion --without-K --flat-split #-}

-- NATIVE FACTS, no frontend module imported (FABLE-REVIEW-03.txt, section
-- 2.6). Expected: ACCEPTED by Agda 2.9.0-rc3. These are the ways in which a
-- clause refines parameters and leaves a context that the capture macro
-- can run in.
module NativeCrispIdentify where
open import Foundations
open import Agda.Builtin.Bool using (Bool; true; false)

-- Control: an ordinary variable is refined to a constructor.
ordinary-to-constructor : (b : Bool) (e : b ≡ true) → Bool
ordinary-to-constructor b refl = b

-- Two crisp variables are identified by matching on a crisp equation.
crisp-identified : (@♭ a b : Bool) (@♭ e : a ≡ b) → Bool
crisp-identified a b refl = a

-- An ordinary module parameter is refined away by an ordinary equation;
-- the remaining clause variable is crisp.
module RefinedAway (b : Bool) where
  refined-away : (@♭ A : Set) → b ≡ true → Set
  refined-away A refl = A

-- Two crisp module parameters are identified.
module Identified (@♭ a b : Bool) where
  identified : (@♭ e : a ≡ b) → Bool
  identified refl = a
