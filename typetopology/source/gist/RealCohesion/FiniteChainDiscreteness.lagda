Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 10 November 2026; prose corrected 13 November 2026, after
the final audits; made a general module for Axiom C1, with Axiom R♭ as
an instance, and the constancy from C1 and a rising generator path
added, 13 November 2026, in the consolidation that followed (steps K4
and W1 of Claude Fable 5.2's plan [3], as corrected by its addendum
[4] and released by GPT-6 Astra). See the AI disclosure in
gist.RealCohesion.index.

Under Axiom R♭, the quotient Q of levels by finite chains is
♭-discrete, and therefore every map from ℝ to Q is constant. Since the
consolidation the proof is given for Axiom C1 with an arbitrary
ordinary family of generators (module under-C1): Q is then ♭-discrete,
and a map from a generator to ℝ that rises strictly somewhere, or
merely the existence of one, gives the constancy of maps ℝ → Q
(constancy-from-C1-and-NC). Axiom R♭ is the case of the one generator
ℝ, whose identity map rises, and keeps its names and types below.

This is Lemma 1.1 of the proof note [1], and the only place where the
proof of the approximate intermediate value theorem in
gist.RealCohesion.ApproximateIVT uses Axiom R♭: the rest of the proof
assumes only that maps ℝ → Q are constant. Both halves of the axiom
are used. We take
Axiom R♭ in the form of singly generated punctual cohesion with
generator ℝ pointed by 0 (gist.CohesiveApartness.Flat).

 1. Maps ℝ → 𝟚 are constant, because 𝟚 is ♭-discrete. So maps from ℝ
    to the type of levels, ℕ → 𝟚, are constant pointwise, hence
    constant by function extensionality, and the levels form a
    ♭-discrete type by the converse half of the axiom.

 2. The counit ♭ Q → Q is an embedding, because Q is a crisp set
    [2, Theorem 8.21]: maps from ℝ to a proposition are constant, so
    crisp propositions are ♭-discrete, and an identification of crisp
    elements of Q may therefore be taken to be crisp.

 3. The counit is a surjection: every element of Q is merely the
    class of a level, every level is the counit of a crisp level by
    step 1, and the class of a crisp level is crisp.

 4. So Q is ♭-discrete, and maps ℝ → Q are constant by the forward
    half of the axiom.

Under Axiom C1 the same steps hold generator by generator: a crisp
type all of whose maps from the generators are constant is ♭-discrete
by Axiom C0, and maps from each generator to the ♭-discrete type Q are
constant. To get from there to maps from ℝ, the general part uses a
generator path in ℝ that rises strictly, and the transfer lemma for
sets.

This is a special case of [2, Lemma 8.24]: a crisp quotient of a
discrete type is discrete. Proving Lemma 1.1 this way is GPT-6
Astra's shortening of the proof in [1]. Steps 2 and 3 follow the proof of
𝟚-mod-is-♭-discrete in gist.RealCohesion.CrispDiscreteness, which does
the same for a quotient of 𝟚. The two lemmas of step 2 are shared with
that module through gist.RealCohesion.CrispRationals, which takes the
♭-discreteness of crisp propositions as an ordinary hypothesis. Both
modules now derive it from gist.RealCohesion.PunctualCohesion, which
takes Axiom C1 as an ordinary hypothesis: that module passes its crisp
C1, and we pass an ordinary one, in particular the one that an
ordinary Axiom R♭ gives. (A crisp hypothesis would give a weaker
theorem.)

As in gist.RealCohesion.CrispDiscreteness, the one ingredient that
needs crisp identity induction, that the constructor of ♭ respects
crisp identifications, is the module parameter crisp-ap-^♭. The
♭-discreteness of 𝟚, which needs crisp induction on 𝟚, is a
hypothesis. Both are proved in --safe mode from the native ♯ of Agda
2.9.0 in gist.CohesiveApartness.CrispInduction, with which
gist.RealCohesion.Theorems instantiates them, and with --flat-split,
the route for Agda 2.8, in the FlatSplit modules, which are not
--safe.

[1] The approximate intermediate value theorem from real cohesion
    alone. Proof note by Claude Fable 5.2, revision 2, 10 November
    2026, audited by GPT-6 Astra.
    references/F17-aivt-proof-rev2.md

[2] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer
    Science 28(6), 856–941, 2018. https://arxiv.org/abs/1509.07584v3

[3] Claude Fable 5.2. Plan: consolidation of r3, and "C1 + NC in place
    of R♭" (G27(d)), 13 November 2026, steps K4 and W1.
    references/F02-consolidation-plan.md

[4] Claude Fable 5.2. Addendum 01 to the consolidation plan,
    13 November 2026. The general module follows its scratch check
    C1ConstancyOverLayerCheck.lagda (SHA-256 8188928f…).
    references/F03-consolidation-plan-addendum-01.md

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import gist.CohesiveApartness.Flat

module gist.RealCohesion.FiniteChainDiscreteness
        (@♭ fe : Fun-Ext)
        (@♭ pe : Prop-Ext)
        (@♭ pt : propositional-truncations-exist)
        (@♭ crisp-ap-^♭ : {@♭ 𝓤 : Universe} {@♭ A : 𝓤 ̇ } {@♭ x y : A}
                        → @♭ x ＝ y → x ^♭ ＝ y ^♭)
       where

open import UF.Embeddings
open import UF.Equiv
open import UF.ImageAndSurjection pt
open import UF.LeftCancellable
open import UF.Sets
open import DedekindReals.Type fe pe pt
open import gist.RealCohesion.FiniteChainLevels
open import gist.RealCohesion.FiniteChainQuotient fe pe pt
open import gist.RealCohesion.CrispRationals using (module counit-on-crisp-sets)
open import gist.RealCohesion.Constancy fe pe pt
 using (Constancy ; Constancy-is-prop ; Rising-Generator-Path ;
        identity-of-ℝ-rises ; module transfer)
import gist.RealCohesion.PunctualCohesion fe as PC

open PropositionalTruncation pt

\end{code}

The four steps, for an ordinary family R of generators with Axiom C1,
an ordinary hypothesis, and the ♭-discreteness of 𝟚. Step 1: maps
from the generators to 𝟚, and so to the levels, are constant, and the
levels form a ♭-discrete type. Step 2: crisp propositions are
♭-discrete, so the counit is an embedding on crisp sets. Steps 3 and 4:
Q is ♭-discrete, and maps from the generators to Q are constant.

Then W1: a strictly rising map g from some generator to ℝ gives the
constancy of maps ℝ → Q, by the transfer lemma for sets of
gist.RealCohesion.Constancy, with S the generator and A the set Q; and
so does the propositional truncation of such data, since Constancy is
a proposition. This is "C1 + NC in place of R♭", with NC used only
through its truncation.

\begin{code}

module under-C1 {𝓥 𝓦 : Universe} {J : 𝓥 ̇ } (R : J → 𝓦 ̇ ) (c1 : Axiom-C1 R)
                (𝟚-is-♭-discrete : is-♭-discrete 𝟚)
              where

 open Axiom-C1 c1

 generator-maps-to-𝟚-are-constant
  : (j : J) (f : R j → 𝟚) (r : R j) → f r ＝ f (base-point j)
 generator-maps-to-𝟚-are-constant =
  PC.generator-maps-are-constant R c1 𝟚 𝟚-is-♭-discrete

 generator-maps-to-levels-are-constant
  : (j : J) (f : R j → Level) (r : R j) → f r ＝ f (base-point j)
 generator-maps-to-levels-are-constant j f r =
  dfunext fe (λ k → generator-maps-to-𝟚-are-constant j (λ s → f s k) r)

 levels-are-♭-discrete : is-♭-discrete Level
 levels-are-♭-discrete =
  PC.types-null-for-the-generators-are-♭-discrete R c1 Level
   generator-maps-to-levels-are-constant

 crisp-props-are-♭-discrete
  : {@♭ 𝓣 : Universe} (@♭ P : 𝓣 ̇ ) → @♭ is-prop P → is-♭-discrete P
 crisp-props-are-♭-discrete P i = PC.crisp-propositions-are-♭-discrete R c1 P i

 open counit-on-crisp-sets crisp-ap-^♭ crisp-props-are-♭-discrete public

 ♭-counit-of-Q-is-surjection : is-surjection (♭-counit {𝓤₁} {Q})
 ♭-counit-of-Q-is-surjection =
  Q-induction (λ q → ∃ u ꞉ ♭ Q , ♭-counit u ＝ q) (λ q → ∃-is-prop) I
  where
   s : Level → ♭ Level
   s = pr₁ (pr₁ levels-are-♭-discrete)

   ε : ♭-counit ∘ s ∼ id
   ε = pr₂ (pr₁ levels-are-♭-discrete)

   I : (x : Level) → ∃ u ꞉ ♭ Q , ♭-counit u ＝ [ x ]
   I x = ∣ γ (s x) (ε x) ∣
    where
     γ : (u : ♭ Level) → ♭-counit u ＝ x → Σ w ꞉ ♭ Q , ♭-counit w ＝ [ x ]
     γ (v ^♭) e = [ v ] ^♭ , ap [_] e

 Q-is-♭-discrete : is-♭-discrete Q
 Q-is-♭-discrete =
  surjective-embeddings-are-equivs ♭-counit
   (♭-counit-is-embedding-on-crisp-sets Q Q-is-set)
   ♭-counit-of-Q-is-surjection

 generator-maps-to-Q-are-constant
  : (j : J) (f : R j → Q) (r : R j) → f r ＝ f (base-point j)
 generator-maps-to-Q-are-constant =
  PC.generator-maps-are-constant R c1 Q Q-is-♭-discrete

 constancy-from-a-rising-generator-path : Rising-Generator-Path R → Constancy
 constancy-from-a-rising-generator-path (j , g , x , y , l) h =
  transfer.constancy-transfers-along-a-strict-rise (base-point j) Q-is-set
   (generator-maps-to-Q-are-constant j) g x y h l

 constancy-from-C1-and-NC : ∥ Rising-Generator-Path R ∥ → Constancy
 constancy-from-C1-and-NC =
  ∥∥-rec Constancy-is-prop constancy-from-a-rising-generator-path

\end{code}

Under Axiom R♭, in the form of singly generated punctual cohesion with
generator ℝ pointed by 0, an ordinary hypothesis: the instance for the
one generator ℝ (singly-generated-punctual-cohesion-gives-Axiom-C1 of
gist.CohesiveApartness.Flat), whose rising path is the identity, with
0 < 1. The names and types of this part are those of the module before
the consolidation; each is a typed alias of the general part.

\begin{code}

module _ (r♭ : Singly-Generated-Punctual-Cohesion ℝ 0ℝ)
         (𝟚-is-♭-discrete : is-♭-discrete 𝟚)
       where

 private
  R♭-gives-C1 : Axiom-C1 (λ (_ : 𝟙 {𝓤₀}) → ℝ)
  R♭-gives-C1 = singly-generated-punctual-cohesion-gives-Axiom-C1 fe ℝ 0ℝ r♭

  module G = under-C1 (λ (_ : 𝟙 {𝓤₀}) → ℝ) R♭-gives-C1 𝟚-is-♭-discrete

 maps-from-ℝ-to-𝟚-are-constant : (f : ℝ → 𝟚) (r : ℝ) → f r ＝ f 0ℝ
 maps-from-ℝ-to-𝟚-are-constant = G.generator-maps-to-𝟚-are-constant ⋆

 maps-from-ℝ-to-levels-are-constant : (f : ℝ → Level) (r : ℝ) → f r ＝ f 0ℝ
 maps-from-ℝ-to-levels-are-constant = G.generator-maps-to-levels-are-constant ⋆

 levels-are-♭-discrete : is-♭-discrete Level
 levels-are-♭-discrete = G.levels-are-♭-discrete

 crisp-props-are-♭-discrete
  : {@♭ 𝓣 : Universe} (@♭ P : 𝓣 ̇ ) → @♭ is-prop P → is-♭-discrete P
 crisp-props-are-♭-discrete = G.crisp-props-are-♭-discrete

 open counit-on-crisp-sets crisp-ap-^♭ crisp-props-are-♭-discrete public

 ♭-counit-of-Q-is-surjection : is-surjection (♭-counit {𝓤₁} {Q})
 ♭-counit-of-Q-is-surjection = G.♭-counit-of-Q-is-surjection

 Q-is-♭-discrete : is-♭-discrete Q
 Q-is-♭-discrete = G.Q-is-♭-discrete

 maps-from-ℝ-to-Q-are-constant : (h : ℝ → Q) (u v : ℝ) → h u ＝ h v
 maps-from-ℝ-to-Q-are-constant =
  G.constancy-from-C1-and-NC identity-of-ℝ-rises

\end{code}
