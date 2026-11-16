Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 25 October 2026. See the AI disclosure in
gist.RealCohesion.index.

The countable continuity comparison and zero-shape, for an arbitrary
reflective subuniverse.

Shulman conjectures that his Axioms R♭ and AC imply that the canonical
map ʃ (A^S) → (ʃ A)^S is an equivalence for every crisp set A and
crisp discrete set S [1, §10.3]. Here we define the ingredients of
this statement for an arbitrary reflective subuniverse, whose
reflection we write ○, in place of the shape ʃ, and for S = ℕ:

 * the action ○-map of ○ on maps, and the comparison

    κ A : ○ (ℕ → A) → (ℕ → ○ A),

   defined coordinatewise from the evaluation maps, so that we don't
   need to assume that a countable product of modal types is modal;

 * the zero-shape Π₀ X = ∥ ○ X ∥₀, the set truncation of ○ X, with its
   unit η₀ X : X → Π₀ X and its action on maps;

 * the fact that set truncation is effective: if two points have the
   same image in the set truncation, then they are merely equal. We
   prove this by the usual encode-decode argument, as TypeTopology's
   UF.SetTrunc only provides the truncation itself.

Following TypeTopology, the existence of propositional truncations, set
truncations and the reflection are assumptions, given as module
parameters.

[1] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer
    Science 28(6), 856–941, 2018. https://arxiv.org/abs/1509.07584v3

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.SetTrunc
open import UF.Subsingletons
open import Modal.Subuniverse

module gist.RealCohesion.ShapeContinuity
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
        (st : set-truncations-exist)
        {𝓤 𝓥 : Universe}
        (P : subuniverse 𝓤 𝓥)
        (P-is-reflective : subuniverse-is-reflective P)
       where

open import Modal.ReflectiveSubuniverse P P-is-reflective public
open import gist.RealCohesion.ReflectionMaps P P-is-reflective public
open import UF.Base
open import UF.Sets
open import UF.SubtypeClassifier
open import UF.SubtypeClassifier-Properties

open PropositionalTruncation pt
open set-truncations-exist st

\end{code}

The action ○-map of the reflection on maps, and its computation rule
○-map-on-units on units, are in gist.RealCohesion.ReflectionMaps, and
are re-exported here.

The countable continuity comparison. Its n-th coordinate is the action
of ○ on evaluation at n. On units it is the pointwise unit.

\begin{code}

κ : (A : 𝓤 ̇ ) → ○ (ℕ → A) → (ℕ → ○ A)
κ A z n = ○-map (λ (f : ℕ → A) → f n) z

κ-on-units : (A : 𝓤 ̇ ) (f : ℕ → A)
           → κ A (η (ℕ → A) f) ＝ (λ n → η A (f n))
κ-on-units A f = dfunext fe (λ n → ○-map-on-units (λ (g : ℕ → A) → g n) f)

\end{code}

Set truncation is effective. For a point a of X, we define a family of
propositions over the set truncation of X, whose value at the image of
x is the mere identity type ∥ a ＝ x ∥. This uses that Ω is a set,
which needs propositional and function extensionality.

\begin{code}

set-trunc-rec-β : {𝓦 𝓣 : Universe} {X : 𝓦 ̇ } (Y : 𝓣 ̇ )
                  (Y-is-set : is-set Y)
                  (f : X → Y)
                  (x : X)
                → set-trunc-rec Y Y-is-set f (set-trunc-in x) ＝ f x
set-trunc-rec-β Y Y-is-set = set-trunc-ind-β (λ _ → Y) (λ _ → Y-is-set)

set-trunc-is-effective : {𝓦 : Universe} {X : 𝓦 ̇ } {a b : X}
                       → set-trunc-in a ＝ set-trunc-in b
                       → ∥ a ＝ b ∥
set-trunc-is-effective {𝓦} {X} {a} {b} p = γ
 where
  code : set-trunc X → Ω 𝓦
  code = set-trunc-rec (Ω 𝓦) (Ω-is-set fe pe) (λ x → ∥ a ＝ x ∥ , ∥∥-is-prop)

  β : (x : X) → code (set-trunc-in x) ＝ (∥ a ＝ x ∥ , ∥∥-is-prop)
  β = set-trunc-rec-β (Ω 𝓦) (Ω-is-set fe pe) (λ x → ∥ a ＝ x ∥ , ∥∥-is-prop)

  I : code (set-trunc-in a) holds
  I = transport⁻¹ _holds (β a) ∣ refl ∣

  II : code (set-trunc-in b) holds
  II = transport (λ - → code - holds) p I

  γ : ∥ a ＝ b ∥
  γ = transport _holds (β b) II

\end{code}

The zero-shape, its unit, and its action on maps.

\begin{code}

Π₀ : 𝓤 ̇ → 𝓤 ̇
Π₀ X = set-trunc (○ X)

η₀ : (X : 𝓤 ̇ ) → X → Π₀ X
η₀ X x = set-trunc-in (η X x)

Π₀-map : {X Y : 𝓤 ̇ } → (X → Y) → Π₀ X → Π₀ Y
Π₀-map f = set-trunc-rec _ set-trunc-is-set (set-trunc-in ∘ ○-map f)

Π₀-map-on-units : {X Y : 𝓤 ̇ } (f : X → Y) (x : X)
                → Π₀-map f (η₀ X x) ＝ η₀ Y (f x)
Π₀-map-on-units {X} {Y} f x =
 Π₀-map f (η₀ X x)              ＝⟨ set-trunc-rec-β _ set-trunc-is-set
                                     (set-trunc-in ∘ ○-map f) (η X x) ⟩
 set-trunc-in (○-map f (η X x)) ＝⟨ ap set-trunc-in (○-map-on-units f x) ⟩
 η₀ Y (f x)                     ∎

\end{code}

Two points with the same image under η₀ have merely equal images under
η, by effectiveness.

\begin{code}

η₀-identifications-are-mere-η-identifications
 : (X : 𝓤 ̇ ) {x y : X}
 → η₀ X x ＝ η₀ X y
 → ∥ η X x ＝ η X y ∥
η₀-identifications-are-mere-η-identifications X = set-trunc-is-effective

\end{code}
