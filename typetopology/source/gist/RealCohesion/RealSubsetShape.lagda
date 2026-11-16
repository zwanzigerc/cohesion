Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 25 and 26 October 2026; prose corrected 13 November 2026,
after the final audits; the constancy of maps from ℝ to 𝟚 below made
an instance of gist.RealCohesion.PunctualCohesion, 13 November 2026,
in the consolidation that followed. See the AI disclosure in
gist.RealCohesion.index. The counterexample is from the research notes
[1, Theorem 5.3], by Claude Opus; its semantic audit by GPT-6 Astra was
positive; the Boolean-labeling implementation follows Astra's gameplan
(25 October 2026) [3].

A subset of the real line whose shape is not a set.

Shulman writes that it is natural to conjecture that, assuming
Axiom R♭, the shape of every subset of ℝ is a set [2, after
Theorem 11.3]; this is the first problem in the real-cohesive section
of the nLab page of open problems. The notes [1, Theorem 5.3] show
that it fails in Shulman's intended model, already for the image of a
suitable crisp function g : ℝ → ℝ.

Here we assemble the internal argument. The reflection ○ is any
reflection onto the ℝ-null types (gist.RealCohesion.RealNull).

The conditional core. Let T be the image of a crisp g with g 1 ＝ g 0,
and assume that the zero indicator on the crisp points of the kernel
of g is invariant along crisp real paths. Then, under the assumptions
listed below except the continuity of crisp functions, ○ T is not a
set. This is the conditional core only.

The concrete theorem. Let g be the dyadic function of
gist.RealCohesion.DyadicOscillation: the extension to ℝ of a
1-Lipschitz rational function with plateaux and bumps of alternating
signs accumulating at 0. We have g 1 ＝ g 0 ＝ 0, and the invariance of
the zero indicator is proved from crisp excluded middle and the
continuity of crisp functions (gist.RealCohesion.ZeroPlateauInvariant
and gist.RealCohesion.DyadicOscillation). Hence the shape of the image
of g, a subtype of TypeTopology's Dedekind reals, is not a set. So not
every subset of ℝ has a set as its shape, and not even every crisp
one.

The assumptions of the concrete theorem, all explicit parameters:

 * standard univalent and modal structure: univalence, which gives
   function and propositional extensionality, propositional
   truncations, and a reflective subuniverse whose modal types in 𝓤₁
   are exactly the ℝ-null types. Mathematically the argument needs
   univalence only for 𝓤₀, for the smallness of the labelings in
   gist.RealCohesion.BooleanCocycleObstruction, besides the
   extensionality principles; the library lemma used there assumes
   global univalence.

 * that 𝟚 is ♭-discrete. This is proved in --safe mode from the
   native ♯ of Agda 2.9.0 (gist.CohesiveApartness.CrispInduction), and
   gist.RealCohesion.Theorems instantiates the theorems below with that
   proof. gist.RealCohesion.FlatSplit, which is not --safe, does the
   same with the proof by --flat-split of
   gist.CohesiveApartness.FlatSplit, the route for Agda 2.8.

 * the following principles. They hold in Shulman's intended model,
   sheaves on Cartesian spaces with continuous maps, as argued
   informally below and in the modules that state them; this is not
   formalized. Descent and the modality of B₂ are additional
   principles, which we do not derive from Shulman's axioms, and we do
   not assume Axiom T, from which Shulman derives continuity.
   - Crisp excluded middle, Crisp-EM 𝓤₁. Crisp propositions are
     propositions of the base, where excluded middle holds.
   - The continuity of crisp real functions at crisp points,
     Crisp-Real-Continuity (gist.RealCohesion.CrispRealAnalysis). It
     is a weak form of Shulman's Theorem 11.5 [2], which is stated
     with Axioms R♭ and T and whose proof also uses crisp excluded
     middle, through his Theorem 8.32. In the model a crisp map
     ℝ → ℝ is a continuous function.
   - Unique Boolean real-path descent
     (gist.RealCohesion.RealPathDescent). In the model, any two points
     of a plot domain are joined by an affine real path.
   - Axiom R♭, as singly generated punctual cohesion with
     generator ℝ.
   - That the type B₂ of two-element types is modal. In the model, B₂
     classifies locally trivial two-element families. Over a Cartesian
     space these are double covers, which are trivial, and their
     automorphism group is the constant group S₂. So B₂ is the
     constant homotopy type B(S₂), which is ℝ-null.

There are no further hypotheses about the concrete g: everything about
it is proved, using the principles above for the invariance of its
zero indicator.

[1] Answers to some open problems in real-cohesive homotopy type
    theory. Research notes, draft of 25 October 2026.
    references/C01-write-up-2026-10-25.tex

[2] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer
    Science 28(6), 856–941, 2018. https://arxiv.org/abs/1509.07584v3

[3] GPT-6 Astra. Gameplan for Opus: a subset of the Dedekind reals
    whose shape is not a set, 25 October 2026.
    references/A32-subset-shape-gameplan.md

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Univalence
open import Modal.Subuniverse

module gist.RealCohesion.RealSubsetShape
        (@♭ ua : Univalence)
        (@♭ pt : propositional-truncations-exist)
       where

open import UF.Base
open import UF.ImageAndSurjection pt
open import UF.Sets
open import UF.SubtypeClassifier
open import UF.UA-FunExt

fe : Fun-Ext
fe = Univalence-gives-Fun-Ext ua

pe : Prop-Ext
pe {𝓤} = Univalence-gives-PropExt ua 𝓤

open import DedekindReals.Type fe pe pt
open import gist.CohesiveApartness.Flat
open import gist.RealCohesion.RealKernelCocycle fe pe pt
open import gist.RealCohesion.RealNull fe pe pt
open import gist.RealCohesion.RealPathDescent fe pe pt
open import gist.RealCohesion.CrispRealAnalysis fe pe pt
 using (Crisp-Real-Continuity)
open import gist.RealCohesion.DyadicOscillation fe pe pt
 using (g-at-1-is-g-at-0 ; dyadic-zero-indicator-is-invariant)
 renaming (g to dyadic-g)
open import UF.Embeddings using (is-embedding ; pr₁-is-embedding)
import gist.RealCohesion.PunctualCohesion fe as PC

\end{code}

The image of the dyadic function, as a subtype of ℝ.

\begin{code}

dyadic-image-predicate : ℝ → Ω 𝓤₁
dyadic-image-predicate y =
 (y ∈image dyadic-g) , being-in-the-image-is-prop y dyadic-g

dyadic-image : 𝓤₁ ̇
dyadic-image = Σ y ꞉ ℝ , dyadic-image-predicate y holds

dyadic-image-is-a-subtype : is-embedding (λ (t : dyadic-image) → pr₁ t)
dyadic-image-is-a-subtype =
 pr₁-is-embedding (λ y → holds-is-prop (dyadic-image-predicate y))

\end{code}

A reflection onto the ℝ-null types. Its reflection of ℝ is
contractible.

\begin{code}

module _ {@♭ 𝓥 : Universe}
         (@♭ P : subuniverse 𝓤₁ 𝓥)
         (@♭ P-is-reflective : subuniverse-is-reflective P)
         (@♭ P-is-ℝ-null : (X : 𝓤₁ ̇ ) → subuniverse-contains P X ↔ is-null ℝ X)
       where

 open import Modal.ReflectiveSubuniverse P P-is-reflective
 open import gist.RealCohesion.ReflectionMaps P P-is-reflective
  using (constant-unit-gives-singleton)
 open import gist.RealCohesion.BooleanCocycleObstruction ua pt P P-is-reflective

 ○ℝ-is-singleton : is-singleton (○ ℝ)
 ○ℝ-is-singleton = constant-unit-gives-singleton fe ℝ 0ℝ
                    (maps-from-ℝ-to-modal-types-are-constant P P-is-ℝ-null
                      (○ ℝ) (○-is-modal ℝ) (η ℝ))

\end{code}

The conditional core: the assumptions, and the theorem. The predicate
on ℝ that defines T is membership in the image of g.

\begin{code}

 module _ (@♭ cem : Crisp-EM 𝓤₁)
          (@♭ descent : Unique-Boolean-Real-Path-Descent 𝓤₁)
          (r♭ : Singly-Generated-Punctual-Cohesion ℝ 0ℝ)
          (𝟚-is-♭-discrete : is-♭-discrete 𝟚)
          (B₂-is-modal : is-modal B₂)
          (@♭ g : ℝ → ℝ)
          (@♭ g-at-1-is-g-at-0 : g 1ℝ ＝ g 0ℝ)
          (@♭ zero-indicator-is-invariant : Real-Path-Invariant (N cem g)
            (h cem g))
        where

  maps-from-ℝ-to-𝟚-are-constant : (k : ℝ → 𝟚) (x y : ℝ) → k x ＝ k y
  maps-from-ℝ-to-𝟚-are-constant k x y = I x ∙ I y ⁻¹
   where
    I : (r : ℝ) → k r ＝ k 0ℝ
    I = PC.generator-maps-are-constant (λ (_ : 𝟙 {𝓤₀}) → ℝ)
         (singly-generated-punctual-cohesion-gives-Axiom-C1 fe ℝ 0ℝ r♭)
         𝟚 𝟚-is-♭-discrete ⋆ k

  image-predicate : ℝ → Ω 𝓤₁
  image-predicate y = (y ∈image g) , being-in-the-image-is-prop y g

  shape-of-the-image-is-not-a-set
   : ¬ is-set (○ (Σ y ꞉ ℝ , image-predicate y holds))
  shape-of-the-image-is-not-a-set =
   with-crisp-extension descent (N-is-set cem g) zero-indicator-is-invariant γ
   where
    γ : (@♭ 𝓒 : Boolean-Extension (N cem g) (h cem g))
      → ¬ is-set (○ (Σ y ꞉ ℝ , image-predicate y holds))
    γ 𝓒 = reflection-is-not-a-set
           ℝ
           (T cem g)
           (T-is-set cem g)
           (q cem g)
           (q-is-surjection cem g)
           ○ℝ-is-singleton
           maps-from-ℝ-to-𝟚-are-constant
           B₂-is-modal
           (kernel-cocycle cem g descent zero-indicator-is-invariant 𝓒)
           (kernel-cocycle-is-cocycle cem g descent zero-indicator-is-invariant
             𝓒)
           1ℝ
           0ℝ
           (kernel-pair-at-1-and-0 cem g descent zero-indicator-is-invariant 𝓒
             g-at-1-is-g-at-0)
           (kernel-cocycle-at-1-and-0 cem g descent zero-indicator-is-invariant
             𝓒
             g-at-1-is-g-at-0)

  not-every-subset-of-ℝ-has-set-shape-if-invariant
   : ¬ ((A : ℝ → Ω 𝓤₁) → is-set (○ (Σ x ꞉ ℝ , A x holds)))
  not-every-subset-of-ℝ-has-set-shape-if-invariant H =
   shape-of-the-image-is-not-a-set (H image-predicate)

\end{code}

The concrete theorem, for the dyadic function.

\begin{code}

 module _ (@♭ cem : Crisp-EM 𝓤₁)
          (@♭ continuity : Crisp-Real-Continuity)
          (@♭ descent : Unique-Boolean-Real-Path-Descent 𝓤₁)
          (r♭ : Singly-Generated-Punctual-Cohesion ℝ 0ℝ)
          (𝟚-is-♭-discrete : is-♭-discrete 𝟚)
          (B₂-is-modal : is-modal B₂)
        where

  shape-of-the-dyadic-image-is-not-a-set : ¬ is-set (○ dyadic-image)
  shape-of-the-dyadic-image-is-not-a-set =
   shape-of-the-image-is-not-a-set cem descent r♭ 𝟚-is-♭-discrete B₂-is-modal
    dyadic-g g-at-1-is-g-at-0
     (dyadic-zero-indicator-is-invariant cem continuity)

  subsets-of-ℝ-need-not-have-set-shape
   : ¬ ((A : ℝ → Ω 𝓤₁) → is-set (○ (Σ x ꞉ ℝ , A x holds)))
  subsets-of-ℝ-need-not-have-set-shape H =
   shape-of-the-dyadic-image-is-not-a-set (H dyadic-image-predicate)

\end{code}

The predicate dyadic-image-predicate is crisp, so the conjecture fails
already for crisp subsets.

\begin{code}

  crisp-subsets-of-ℝ-need-not-have-set-shape
   : ¬ ((@♭ A : ℝ → Ω 𝓤₁) → is-set (○ (Σ x ꞉ ℝ , A x holds)))
  crisp-subsets-of-ℝ-need-not-have-set-shape H =
   shape-of-the-dyadic-image-is-not-a-set (H dyadic-image-predicate)

\end{code}
