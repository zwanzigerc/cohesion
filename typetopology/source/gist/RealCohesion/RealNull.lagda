Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 25 October 2026. See the AI disclosure in
gist.RealCohesion.index.

The ℝ-null types, and a reflection onto them.

Shulman's shape modality ʃ is nullification at the real line [1,
Definition 9.6]. TypeTopology doesn't provide his higher-inductive
construction of ʃ, so modules that use the shape assume a reflective
subuniverse whose modal types, among all types, not only the crisp
ones, are exactly the ℝ-null types. This module collects what is
shared by such modules: the subuniverse of ℝ-null types and two
consequences of the identification. Under Axiom R♭, in the form of
singly generated punctual cohesion with generator ℝ pointed by 0
(gist.CohesiveApartness.Flat), the modal crisp types are exactly the
♭-discrete ones, as in Shulman's setting. And maps from ℝ to a modal
type are constant.

These were first part of gist.RealCohesion.RealShapeContinuity, which
re-exports them. They are separate so that modules that don't need set
truncations or set quotients needn't assume them.

[1] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer
    Science 28(6), 856–941, 2018. https://arxiv.org/abs/1509.07584v3

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import Modal.Subuniverse

module gist.RealCohesion.RealNull
        (@♭ fe : Fun-Ext)
        (@♭ pe : Prop-Ext)
        (@♭ pt : propositional-truncations-exist)
       where

open import UF.Equiv-FunExt
open import DedekindReals.Type fe pe pt
open import gist.CohesiveApartness.Flat

\end{code}

The ℝ-null types form a subuniverse of 𝓤₁, the universe of ℝ.

\begin{code}

ℝ-null : subuniverse 𝓤₁ 𝓤₁
ℝ-null = is-null ℝ , (λ X → being-equiv-is-prop'' fe (λ (x : X) (_ : ℝ) → x))

\end{code}

For a subuniverse whose types are exactly the ℝ-null ones.

\begin{code}

module _ {𝓥 : Universe}
         (P : subuniverse 𝓤₁ 𝓥)
         (P-is-ℝ-null : (X : 𝓤₁ ̇ ) → subuniverse-contains P X ↔ is-null ℝ X)
       where

 modal-iff-♭-discrete-under-R♭
  : Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → (@♭ X : 𝓤₁ ̇ ) → subuniverse-contains P X ↔ is-♭-discrete X
 modal-iff-♭-discrete-under-R♭ r♭ X = I , II
  where
   I : subuniverse-contains P X → is-♭-discrete X
   I m = rl-implication (r♭ X)
          (lr-implication (null-iff-maps-are-constant fe ℝ 0ℝ X)
            (lr-implication (P-is-ℝ-null X) m))

   II : is-♭-discrete X → subuniverse-contains P X
   II d = rl-implication (P-is-ℝ-null X)
           (rl-implication (null-iff-maps-are-constant fe ℝ 0ℝ X)
             (lr-implication (r♭ X) d))

 maps-from-ℝ-to-modal-types-are-constant
  : (X : 𝓤₁ ̇ )
  → subuniverse-contains P X
  → (f : ℝ → X) (r : ℝ) → f r ＝ f 0ℝ
 maps-from-ℝ-to-modal-types-are-constant X m =
  lr-implication (null-iff-maps-are-constant fe ℝ 0ℝ X)
   (lr-implication (P-is-ℝ-null X) m)

\end{code}
