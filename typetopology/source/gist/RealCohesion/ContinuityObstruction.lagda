Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 25 October 2026. See the AI disclosure in
gist.RealCohesion.index.

From zero-shape separation to the failure of countable continuity.

Let ○ be the reflection of a reflective subuniverse, as in
gist.RealCohesion.ShapeContinuity, and let A be a crisp type with two
crisp sequences u and v. Suppose that, for every n, the points u n and
v n have the same zero-shape, but that the sequences u and v themselves
don't. We show that then the comparison

 κ A : ○ (ℕ → A) → (ℕ → ○ A)

is not an equivalence, assuming countable choice for crisp families.

The argument. Effectivity of set truncation turns the coordinatewise
equality of zero-shapes into a crisp family of mere identifications
∥ η A (u n) ＝ η A (v n) ∥. Countable choice for crisp families gives
merely an identification in each coordinate at once, and so, by
function extensionality, merely an identification
κ A (η u) ＝ κ A (η v). If κ A were an equivalence, this would give
merely an identification η u ＝ η v, and so an identification of the
zero-shapes of u and v, which is impossible. We eliminate the
truncation into the empty type, so no choice of an untruncated
identification is needed.

The identity types of ○ A may have higher structure, so the choice
principle has to apply to arbitrary type families, not only to
families of sets. It is the case of ℕ of Shulman's discrete axiom of
choice [1, Theorem 6.30], which he derives from his Axiom AC. We take
it as a hypothesis, Crisp-Countable-Choice of
gist.RealCohesion.CrispCountableChoice, which is crisp in its family
and in the proof that the family is pointwise inhabited.

The argument needs neither the axioms of cohesion nor that A is a set.
Its application in gist.RealCohesion.FiniteHeightContinuity is to a
set.

[1] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer
    Science 28(6), 856–941, 2018. https://arxiv.org/abs/1509.07584v3

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.SetTrunc
open import UF.Subsingletons
open import Modal.Subuniverse

module gist.RealCohesion.ContinuityObstruction
        (@♭ fe : Fun-Ext)
        (@♭ pe : Prop-Ext)
        (@♭ pt : propositional-truncations-exist)
        (@♭ st : set-truncations-exist)
        {@♭ 𝓤 𝓥 : Universe}
        (@♭ P : subuniverse 𝓤 𝓥)
        (@♭ P-is-reflective : subuniverse-is-reflective P)
       where

open import UF.Base
open import UF.Equiv
open import gist.RealCohesion.ShapeContinuity fe pe pt st P P-is-reflective
open import gist.RealCohesion.CrispCountableChoice pt public

open PropositionalTruncation pt
open set-truncations-exist st

\end{code}

The main lemma.

\begin{code}

κ-is-not-equiv-if-zero-shapes-separate
 : Crisp-Countable-Choice 𝓤
 → (@♭ A : 𝓤 ̇ )
   (@♭ u v : ℕ → A)
 → @♭ ((n : ℕ) → η₀ A (u n) ＝ η₀ A (v n))
 → η₀ (ℕ → A) u ≠ η₀ (ℕ → A) v
 → ¬ is-equiv (κ A)
κ-is-not-equiv-if-zero-shapes-separate ccc A u v h ν κ-is-equiv =
 ∥∥-rec 𝟘-is-prop γ
  (ccc (λ n → η A (u n) ＝ η A (v n))
       (λ n → η₀-identifications-are-mere-η-identifications A (h n)))
 where
  γ : ((n : ℕ) → η A (u n) ＝ η A (v n)) → 𝟘
  γ p = ν (ap set-trunc-in I)
   where
    I : η (ℕ → A) u ＝ η (ℕ → A) v
    I = equivs-are-lc (κ A) κ-is-equiv
         (κ A (η (ℕ → A) u) ＝⟨ κ-on-units A u ⟩
          (λ n → η A (u n)) ＝⟨ dfunext fe p ⟩
          (λ n → η A (v n)) ＝⟨ (κ-on-units A v)⁻¹ ⟩
          κ A (η (ℕ → A) v) ∎)

\end{code}
