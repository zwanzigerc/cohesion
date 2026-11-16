Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 25 October 2026. See the AI disclosure in
gist.RealCohesion.index.

The finite-height obstruction to Shulman's continuity conjecture, in
real-cohesive terms.

Shulman's shape modality ʃ is nullification at the real line [1,
Definition 9.6], and his continuity conjecture [1, §10.3] says that,
assuming his Axioms R♭ and AC, the canonical map ʃ (A^S) → (ʃ A)^S is
an equivalence for every crisp set A and crisp discrete set S. Here
we instantiate gist.RealCohesion.FiniteHeightContinuity accordingly:

 * the interval is the real line ℝ of TypeTopology's Dedekind reals,
   with endpoints 0 and 1, so that the path quotient identifies the
   endpoints of real paths;

 * the reflective subuniverse is any one whose modal types are exactly
   the ℝ-null types. TypeTopology doesn't provide Shulman's
   higher-inductive construction of ʃ, so its existence, as a
   reflection onto the ℝ-null types, is a hypothesis. For ordinary,
   not necessarily crisp, types X, we ask that X be modal if and only
   if X is ℝ-null. The ℝ-null types themselves form a subuniverse,
   given below, whose reflectivity is precisely the existence of ʃ.

Under Axiom R♭, in the form of singly generated punctual cohesion with
generator ℝ pointed by 0 (gist.CohesiveApartness.Flat), the modal crisp
types are then exactly the ♭-discrete ones, as in Shulman's setting.

The resulting theorem: countable choice for crisp families, the
finite-height principle, and a tower of unbounded depth refute the
conjecture for S = ℕ and the crisp set A = Σ n ꞉ ℕ , B n. Axiom R♭ is
not used in the proof itself; it only identifies ʃ. Shulman's Axiom AC
gives the countable choice, and in gist.RealCohesion.FlatSplit we
derive it from the discrete axiom of choice of
gist.RealCohesion.CrispDiscreteness. The finite-height principle and
the tower are additional hypotheses, which hold in the countermodel of
[2, 3].

[1] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer
    Science 28(6), 856–941, 2018. https://arxiv.org/abs/1509.07584v3

[2] An ordinary real-cohesive countermodel to countable-power
    continuity. Research notes, 25 October 2026.
    references/C05-ordinary-countermodel.txt

[3] Internal real-path quotients and the finite-height principle.
    Research notes, 25 October 2026.
    references/C06-internal-real-path-quotients.txt

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.SetTrunc
open import UF.Subsingletons
open import Modal.Subuniverse
open import Quotient.Type

module gist.RealCohesion.RealShapeContinuity
        (@♭ fe : Fun-Ext)
        (@♭ pe : Prop-Ext)
        (@♭ pt : propositional-truncations-exist)
        (@♭ st : set-truncations-exist)
        (@♭ sq : set-quotients-exist)
       where

open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.Sets
open import DedekindReals.Type fe pe pt
open import gist.CohesiveApartness.Flat
open import gist.RealCohesion.CrispCountableChoice pt
open import gist.RealCohesion.RealNull fe pe pt public

open PropositionalTruncation pt

\end{code}

The subuniverse ℝ-null of the ℝ-null types is defined in
gist.RealCohesion.RealNull, and re-exported here.

We now assume a reflective subuniverse whose modal types are exactly
the ℝ-null types, such as ℝ-null itself if it is reflective. The
module is named, so that gist.RealCohesion.FlatSplit can instantiate
it.

\begin{code}

module RealShape
        {@♭ 𝓥 : Universe}
        (@♭ P : subuniverse 𝓤₁ 𝓥)
        (@♭ P-is-reflective : subuniverse-is-reflective P)
        (@♭ P-is-ℝ-null : (X : 𝓤₁ ̇ ) → subuniverse-contains P X ↔ is-null ℝ X)
       where

 open import gist.RealCohesion.ShapeContinuity fe pe pt st P P-is-reflective
  public
 open import gist.RealCohesion.RealPathQuotient pt sq ℝ 0ℝ 1ℝ
  public
 open import gist.RealCohesion.FiniteHeightContinuity
              fe pe pt st sq P P-is-reflective ℝ 0ℝ 1ℝ
  public

\end{code}

Under Axiom R♭, a crisp type is modal if and only if it is
♭-discrete.

\begin{code}

 R♭-gives-modal-iff-♭-discrete
  : Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → (@♭ X : 𝓤₁ ̇ ) → is-modal X ↔ is-♭-discrete X
 R♭-gives-modal-iff-♭-discrete = modal-iff-♭-discrete-under-R♭ P P-is-ℝ-null

\end{code}

The obstruction, for the countable comparison of the shape, with real
paths. It is the main theorem of gist.RealCohesion.FiniteHeightContinuity
for this instance, restated here with its hypotheses in full.

\begin{code}

 shape-continuity-fails
  : Crisp-Countable-Choice 𝓤₁
  → Finite-Height
  → (@♭ B : ℕ → 𝓤₁ ̇ )
    (@♭ B-is-set : (n : ℕ) → is-set (B n))
    (@♭ b t : (n : ℕ) → B n)
  → @♭ ((n : ℕ) → η₀ (B n) (b n) ＝ η₀ (B n) (t n))
  → ((k : ℕ) → ∃ n ꞉ ℕ , q[ k ] (b n) ≠ q[ k ] (t n))
  → ¬ is-equiv (κ (Σ n ꞉ ℕ , B n))
 shape-continuity-fails ccc fh B B-is-set b t h ud =
  κ-is-not-equiv B B-is-set b t ccc fh h ud

\end{code}
