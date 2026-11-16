{-# OPTIONS --without-K --cohesion #-}

-- THE ORDINARY FOUNDATION OF THE DESIGNATED SET-SOURCE CLIENT: thirteen
-- named assumptions, at the levels 0, 1 and 2.
-- Claude (Fable), 14 November 2026; fable-impl-23
-- (FABLE-PLAN-SET-SOURCE-01, section 11.3 a;
-- SET-SOURCE-PLAN-ASTRA-RELEASE-01, "Foundation and public client").
--
-- THIS MODULE POSTULATES. It is the only module of the staged client
-- that does, apart from the shape declarations themselves, and it is
-- separate so that the assumptions can be counted: every other module of
-- the library takes extensionality, truncations and quotients as
-- parameters and remains as it was.
--
-- What is assumed, for the levels of a diagram of level 0:
--   function extensionality at the pairs (0,0), (1,1), (2,2), (0,1), (1,2)
--   propositional extensionality at 0 and at 1
--   a set truncation at 0 (OrdinaryTruncation.SetTruncation: carrier,
--     unit, sethood, own-level recursor, unit law, uniqueness)
--   small quotients (SmallQuotient.Quotients, of ARBITRARY types of the
--     level by proposition-valued equivalence relations) with their
--     own-level eliminators, at 1 and 2
--   effectivity of the quotients at 1
-- At level 0 the theorem uses the set truncation only (to truncate the
-- fibres of the two payloads), so that is what is assumed there, and not
-- a quotient structure. It is assumed as ONE opaque constant on purpose:
-- with the truncation DEFINED from a quotient structure, the conversion
-- of τ₀ at two convertible but differently written arguments did not
-- finish in 60 seconds in this client; with the constant it is
-- immediate.
-- Nothing modal: the statements mention neither ♭ nor ♯ nor a shape, and
-- this module imports only modules that are literally --safe.
--
-- These are bounded ORDINARY assumptions about types. They are not
-- derived here, and an elementary topos of sets alone does not supply
-- quotients of arbitrary types. ORDINARY-QUOTIENTS-IN-THE-NONSTABLE-
-- MODEL-01 argues that the ordinary presheaf model of the reflection
-- interprets constants of exactly these types; that argument is not
-- checked here. A client that imports this module has these thirteen
-- assumptions, by name, and says so.
--
-- Being closed constants they may be used crisply, and they may occur in
-- the source types of declared shapes.
module SetSourceFoundation where

open import Foundations
open import SmallPropositions using (PropExt)
open import OrdinaryTruncation using (FunExtBetween; SetTruncation)
open import SmallQuotient using (Quotients; Eliminates; Effective)

private
  ℓ₁ ℓ₂ : Level
  ℓ₁ = lsuc lzero
  ℓ₂ = lsuc ℓ₁

postulate
  -- function extensionality
  fe₀₀ : FunExtBetween lzero lzero
  fe₁₁ : FunExtBetween ℓ₁ ℓ₁
  fe₂₂ : FunExtBetween ℓ₂ ℓ₂
  fe₀₁ : FunExtBetween lzero ℓ₁
  fe₁₂ : FunExtBetween ℓ₁ ℓ₂

  -- propositional extensionality
  pe₀ : PropExt lzero
  pe₁ : PropExt ℓ₁

  -- a set truncation at the level of the diagram
  truncation₀ : SetTruncation lzero

  -- small quotients with their own-level eliminators
  Q₁ : Quotients ℓ₁
  E₁ : Eliminates Q₁ ℓ₁
  Q₂ : Quotients ℓ₂
  E₂ : Eliminates Q₂ ℓ₂

  -- effectivity, at the level of the support only
  effective₁ : Effective Q₁
