{-# OPTIONS --safe --without-K #-}

-- A type with a majority operation is a set.
-- Claude (Fable), 12 November 2026; see HIGHER-RESEARCH-FABLE-01.txt, section 3.
--
-- Let maj be a ternary operation on M with paths
--   maj x x y ≡ x,   maj x y x ≡ x,   maj y x x ≡ x     for all x, y.
-- Nothing else is assumed: no coherence between the three paths, no
-- associativity or commutativity. Then every loop in M is trivial.
--
-- The statement and its use are Astra's (HIGHER-MAIN-ATTEMPT-02.txt,
-- MAJORITY-REVIEW-01.txt); this file is an independent machine check of it.
-- The argument here: for a loop p at x, the first law carries p to
--   ap (λ z → maj z z x) p,
-- which splits as  ap (λ z → maj z x x) p ∙ ap (λ z → maj x z x) p.  By the
-- third and second law both factors are ap of a function that is homotopic
-- to a constant, hence trivial.
--
-- Use: the median  (x ∧ y) ∨ (y ∧ z) ∨ (x ∧ z)  is a majority operation on
-- any lattice object. A finite-product-preserving endofunctor T carries it
-- to a majority operation on TΩ, so TΩ is a set, with no continuity axiom
-- and no Nullstellensatz.
--
-- Plain Agda: no cohesion, no axioms, no K.
module MajoritySet where

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality
open import IdempotentUnit
  using (sym; _∙_; ap; right-inverse; conj; natural-loop; diagonal)

private
  variable
    a b : Level

  -- ap of a function with a homotopy to a constant kills loops.
  constant-loop : {X : Set a} {Y : Set b} (g : X → Y) (y₀ : Y)
                → ((z : X) → g z ≡ y₀)
                → {x : X} (p : x ≡ x) → ap g p ≡ refl
  constant-loop g y₀ h {x} p = general p ∙ right-inverse (h x)
    where
    general : {x′ y′ : _} (q : x′ ≡ y′) → ap g q ≡ h x′ ∙ sym (h y′)
    general {x′} refl = sym (right-inverse (h x′))

  -- A loop carried to a trivial loop was trivial.
  conj-trivial : {X : Set a} {u e : X} (h : u ≡ e) (p : e ≡ e)
               → conj h p ≡ refl → p ≡ refl
  conj-trivial refl p t = t

  product-trivial : {X : Set a} {u : X} {d x y : u ≡ u}
                  → d ≡ x ∙ y → x ≡ refl → y ≡ refl → d ≡ refl
  product-trivial s refl refl = s

module _ {M : Set a} (maj : M → M → M → M)
  (first-two : (x y : M) → maj x x y ≡ x)
  (outer-two : (x y : M) → maj x y x ≡ x)
  (last-two : (x y : M) → maj y x x ≡ x) where

  loop-trivial : (x : M) (p : x ≡ x) → p ≡ refl
  loop-trivial x p = conj-trivial (first-two x x) p
    ( sym (natural-loop (λ z → maj z z x) (λ z → first-two z x) p)
    ∙ product-trivial
        (diagonal (λ z w → maj z w x) p)
        (constant-loop (λ z → maj z x x) x (λ z → last-two x z) p)
        (constant-loop (λ w → maj x w x) x (λ w → outer-two x w) p) )

  -- Hence M is a set: parallel paths are equal.
  is-set : (x y : M) (s t : x ≡ y) → s ≡ t
  is-set x .x s refl = loop-trivial x s
