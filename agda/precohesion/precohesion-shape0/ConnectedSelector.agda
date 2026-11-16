{-# OPTIONS --safe --without-K --cohesion #-}

-- The elementary selector lemma of the connected-interval theorem.
-- Opus, 13 November 2026; opus-connected-interval-01, implementing
-- CONNECTED-INTERVAL-PLAN-FABLE-01.txt section 1.1 / 2.1 as released by
-- CONNECTED-INTERVAL-PLAN-ASTRA-02.txt.
--
-- For types U, V of arbitrary levels, a map h : U → U → V → U, a path
-- v₀ ≡ v₁ and the endpoint laws  h u v v₀ ≡ u,  h u v v₁ ≡ v,  U is a
-- proposition. No sethood of U or V, no function extensionality, no
-- truncation, no K. The lemma is therefore valid for higher U, and a later
-- full-shape adapter may import it; it does NOT by itself say anything
-- about full shape.
--
-- Literally --safe. Imports Foundations only. --cohesion appears only
-- because Foundations has it; nothing modal is used here.
module ConnectedSelector where

open import Foundations using (Level; IsProp; _≡_; refl; sym; ap; _∙_; tt)

selector : ∀ {a b} {U : Set a} {V : Set b} (h : U → U → V → U) (v₀ v₁ : V)
         → v₀ ≡ v₁
         → ((u v : U) → h u v v₀ ≡ u) → ((u v : U) → h u v v₁ ≡ v)
         → IsProp U
selector h v₀ v₁ p L₀ L₁ u v = sym (L₀ u v) ∙ ap (h u v) p ∙ L₁ u v

-- The acceptance control of CONNECTED-INTERVAL-REVIEW-01.txt section 4.
-- For empty U the lemma gives IsProp U and no centre. In particular the
-- connected-interval theorem gives IsProp of the modal output for every A,
-- but a centre only under Merely A; nothing here asserts that the shape of
-- ♯ Empty is empty (false without the Nullstellensatz: the arrow-topos
-- quadruple has T A = 1 for every A).
data Empty : Set where

control : IsProp Empty
control = selector (λ u _ _ → u) tt tt refl (λ u _ → refl) (λ ())
