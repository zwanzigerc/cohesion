{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Fixtures for the target-style assembly clients of fable-impl-11.
-- Claude (Fable), 13 November 2026. No postulate, no capture: definitions
-- only. They are in a module of their own because a capture refuses
-- definitions of its own file that do not unfold, and because a client's
-- declaration inventory should not contain the shapes of older examples.
module AssemblyFixtures where

open import Foundations
open import Agda.Builtin.Bool
open import Agda.Builtin.Unit using (⊤)
open import CaptureContext using (Raise; raise; lower)
open import ShapeElim using (raise-set; raise-discrete)
open import DecidableBase using (DecEq; yes; no)
open import BoolDecidable using (bool-dec; bool-is-set; bool-is-discrete)

------------------------------------------------------------------------
-- Level zero, closed.

collapse : Bool → Bool
collapse _ = false

keep : Bool → Bool
keep b = b

-- A family of sets over Bool that is not constant.
Colours : Bool → Set
Colours false = ⊤
Colours true = Bool

-- A constant family. Its reindexing along ANY map C → Bool is the same
-- constant family over C: the total source no longer shows the map.
Constant : Bool → Set
Constant _ = Bool

------------------------------------------------------------------------
-- Level one. The base is Bool raised to Set₁, and the fibres are the
-- universe Set.

ℓ₁ : Level
ℓ₁ = lsuc lzero

Bool₁ : Set₁
Bool₁ = Raise ℓ₁ Bool

bool₁-discrete : Discrete Bool₁
bool₁-discrete = raise-discrete bool-is-discrete

bool₁-set : IsSet Bool₁
bool₁-set = raise-set bool-is-set

bool₁-dec : DecEq Bool₁
bool₁-dec (raise x) (raise y) with bool-dec x y
... | yes e = yes (ap raise e)
... | no n = no (λ e → n (ap lower e))

collapse₁ : Bool₁ → Bool₁
collapse₁ _ = raise false

-- The fibres are the universe Set. No sethood of it is assumed or used.
Types : Bool₁ → Set₁
Types _ = Set

-- A map of Bool₁ that depends on a Boolean parameter.
pick : Bool → Bool₁ → Bool₁
pick true x = x
pick false _ = raise false
