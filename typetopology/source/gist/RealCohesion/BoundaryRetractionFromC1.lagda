Claude Fable 5.2, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. Starter module for gate G27 of the second
addendum to the formalization plan.

Added to the folder by Claude Opus 5.5 on 12 November 2026, for gate G27(b),
with the code unchanged and one sentence of the prose changed (the disc is now
in gist.RealCohesion.SphereRetractionFromC1), after GPT-6 Astra's review
released it (12 November 2026); see the AI disclosure in
gist.RealCohesion.index. On 13 November 2026, in the consolidation
after the final audits, Claude Opus 5.5 made the lemma
identifications-in-♯-from-sharp-ones of §1 a typed alias of the same
lemma in gist.CohesiveApartness.SharpProperties, the five lemmas of §3
on Q typed aliases of those of the general part of
gist.RealCohesion.FiniteChainDiscreteness, the two predicates of §3
typed aliases of those of gist.RealCohesion.Constancy, and the lemmas
of the module separator of §4a typed aliases of the transfer lemma of
gist.RealCohesion.Constancy, at the set 𝟚.

Shulman's Lemma 12.3 from crisp excluded middle and Axiom C1, without
Axiom T and without Axiom R♭, in the form for the cube [-1,1]ⁿ. The
theorem and its proof are due to GPT-6 Astra (12 November 2026;
audited on paper by Fable the same day).

The exact statement. [1, Lemma 12.3], which [1] tags with LEM, C1 and
T: if there is a map f : D² → D² with no fixed point, then S¹ is a
retract of D². Here D² is the unit disc of ℝ² and S¹ its boundary.

The formal statement, Lemma-12-3-for-the-cube, has the cube
[-1,1]ⁿ⁺¹ in place of D², and its boundary in place of S¹, for every
crisp n, relative to Kuhn's lemma in dimension n + 1; the map f need
not be crisp, and the conclusion is a retraction, not the mere
existence of one. Lemma-12-3-for-the-square is the case of the square,
where Kuhn's lemma is proved. The statement for the disc is in
gist.RealCohesion.SphereRetractionFromC1 (gate G27(c)).

Nothing is assumed beyond crisp excluded middle, Axiom C1, and the
standing hypotheses of function extensionality, propositional
extensionality and propositional truncations. The proof also gives, in
the same generality, the stronger statement
discrete-or-no-fixed-point-free-maps: either ℝ is ♭-discrete, or no
self-map of the cube is fixed-point free. So the crisp and the sharp
fixed-point theorems for the cube ([1, Corollary 12.5 and Theorem 12.4]
for the square) follow from crisp excluded middle, Axiom C1 and the
hypothesis that ℝ is not ♭-discrete, in place of Axiom R♭. These
hypotheses follow from crisp excluded middle and Axiom R♭, and are
strictly weaker.

The proof.

 * If a map e : ℝ → 𝟚 separates two real numbers, then ℝ is ♭-discrete.
   This is separators-make-ℝ-discrete, proved in §4a without
   multiplication or division of real numbers.

 * So if ℝ is not ♭-discrete, every map ℝ → 𝟚 is constant. Under Axiom
   C1 the quotient Q of gist.RealCohesion.FiniteChainQuotient is
   ♭-discrete, so it has decidable equality by crisp excluded middle,
   and every map ℝ → Q is constant. This part is GPT-6 Astra's module
   C1FiniteChainBridge, reproduced here.

 * The constancy of maps ℝ → Q is all that
   gist.RealCohesion.CubeFixedPoint needs of Axiom R♭, and it need not
   be crisp. So every crisp self-map of the cube has a fixed point.

 * The type of fixed-point-free self-maps of the cube is a crisp type,
   and it has no crisp element. Under Axiom C1 a crisp type without
   crisp elements is empty [1, Corollary 8.16]. This is proved here
   with the native ♯ of Agda 2.9.0, from the fact that ♯ 𝟘 is empty
   under Axiom C1 [1, Theorem 8.11].

 * If ℝ is ♭-discrete, it has decidable equality by crisp excluded
   middle, and a retraction of the cube onto its boundary is defined
   by cases: a point of the boundary is sent to itself, and every
   other point to the corner (1,...,1).

 * Crisp excluded middle decides whether ℝ is ♭-discrete.

Crisp excluded middle is used for propositions in 𝓤₀, as a crisp
hypothesis, and at one proposition in 𝓤₁: that ℝ is ♭-discrete. The
fixed-point theorems for the case that ℝ is not ♭-discrete, and the
retraction for the case that it is, need it for 𝓤₀ only: equality in Q
and in ℝ is decided on crisp representatives, where it is equivalent
to a proposition in 𝓤₀.

Theorem 8.32 of [1], the analytic Markov principle, keeps Axiom T. §8
records why the proof above does not remove it: under Axiom C1 the
analytic Markov principle, in the form that positivity is stable under
double negation, gives Axiom T back, so that removing Axiom T from
Theorem 8.32 would prove Axiom T; and the principle does hold if ℝ is
♭-discrete. That Axiom T does not follow from crisp excluded middle and
Axiom R♭ is a statement about models and is not formalized here.

[1] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer Science
    28(6), 2018. https://arxiv.org/abs/1509.07584v3
    Numbering as in version 3 of the arXiv preprint.

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import gist.CohesiveApartness.Flat

module gist.RealCohesion.BoundaryRetractionFromC1
        (@♭ fe : Fun-Ext)
        (@♭ pe : Prop-Ext)
        (@♭ pt : propositional-truncations-exist)
        {@♭ 𝓥 𝓦 : Universe} {@♭ J : 𝓥 ̇ }
        (@♭ R : J → 𝓦 ̇ )
        (@♭ c1 : Axiom-C1 R)
       where

open import Fin.Topology using (Fin-Compact)
open import Fin.Type
open import NotionsOfDecidability.Decidable
open import Notation.Order
open import Quotient.Large pt fe pe using (module large-quotient)
open import Rationals.Type
open import Rationals.Order
open import Rationals.Addition renaming (_+_ to _ℚ+_)
open import Rationals.Negation renaming (_-_ to _ℚ-_ ; -_ to ℚ-_)
open import UF.Base hiding (_≈_)
open import UF.DiscreteAndSeparated
open import UF.Embeddings
open import UF.Equiv
open import UF.Equiv-FunExt using (being-equiv-is-prop'')
open import UF.ImageAndSurjection pt
open import UF.Sets
open import UF.Subsingletons-FunExt
 using (Π-is-prop ; decidability-of-prop-is-prop)
open import DedekindReals.Order fe pe pt
open import DedekindReals.Type fe pe pt
open import gist.CohesiveApartness.CrispInduction
 using (crisp-ap-^♭ ; 𝟚-is-♭-discrete)
open import gist.CohesiveApartness.Sharp
import gist.CohesiveApartness.SharpProperties
import gist.RealCohesion.Constancy
import gist.RealCohesion.FiniteChainDiscreteness
open import gist.RealCohesion.NativeSharp using (native-sharp)
open import gist.CohesiveApartness.TightApartness fe pt
 using (decidable-predicates-spread)
open import gist.RealCohesion.AnalyticMarkovObstruction fe pe pt
 using (Positivity-Is-Stable)
open import gist.RealCohesion.AxiomTObstruction fe pe pt native-sharp
 using (Axiom-T)
open import gist.RealCohesion.BrouwerStatements fe pe pt
 using (ℝ^ ; in-cube ; Cube ; Crisp-Cube-Fixed-Point ;
        Sharp-Cube-Fixed-Point ; crisp-fixed-points-give-sharp-fixed-points)
open import gist.RealCohesion.CrispDiscreteness fe pe pt crisp-ap-^♭
 using (crisp-props-are-♭-discrete ; ♭-counit-is-embedding-on-crisp-sets)
open import gist.RealCohesion.CubeFixedPoint fe pe pt
 using (crisp-cube-fixed-point ; minus-one-below-one)
open import gist.RealCohesion.FiniteChainLevels using (Level)
open import gist.RealCohesion.FiniteChainQuotient fe pe pt
open import gist.RealCohesion.KuhnLemma using (Kuhn-Lemma ; kuhn-lemma-2)
open import gist.RealCohesion.Sharp
 using (props-with-a-map-from-sharp-are-codiscrete)
open import gist.RealCohesion.RationalArithmetic
 using (half ; add-difference ; minus-plus ; module halving-sequence)
open import gist.RealCohesion.RationalLimits fe pe pt
 using (module halving-sequence-bounds)
open import gist.RealCohesion.RationalPoints fe pe pt using (ιₐ)
open import gist.RealCohesion.RealLattice fe pe pt
 using (min ; clamp ; clamp-below ; clamp-above ; ≤-min ; min-≤-left ;
        min-≤-right ; below-min ; below-min-left ; below-min-right ; _+_ ;
        sum-≤ ; plus-zero ; translate-twice ; translate-above ;
        translate-below ; translate-strict ; below-translate⁻¹ ; ιₐ-sum ;
        ιₐ-≤-ιₐ ; <-gives-≤-ιₐ ; >-gives-ιₐ-≤)
open import gist.RealCohesion.RealOrder fe pe pt
 using (ℝ≤-refl ; cuts-are-ordered)
open import gist.RealCohesion.ShulmanWeakeningsStatements fe pe pt
 using (on-boundary ; is-retraction-onto-the-boundary)

open PropositionalTruncation pt
open Axiom-C1 c1

private
 module SP = gist.CohesiveApartness.SharpProperties fe
 module C = gist.RealCohesion.Constancy fe pe pt
 module FC = gist.RealCohesion.FiniteChainDiscreteness.under-C1
              fe pe pt crisp-ap-^♭ R c1 𝟚-is-♭-discrete

\end{code}

1. The modality ♯, without Axiom C1. Identifications in ♯ A can be
obtained from sharp ones: this is the codiscreteness of the identity
types of ♯ A [1, Theorem 3.7]. The two constant maps ♯ (u ＝ v) → ♯ A
with values u and v agree on the image of the unit, and rec-sharp,
which extends a map (u ＝ v) → ♯ A along the unit, sends the two
restrictions to the two constant maps, by the η rule for ♯. The proof
is in gist.CohesiveApartness.SharpProperties; the lemma is named here
by a typed alias, so that, as before, it takes the parameters of this
module.

\begin{code}

identifications-in-♯-from-sharp-ones
 : {𝓤 : Universe} {A : 𝓤 ̇ } (u v : ♯ A) → ♯ (u ＝ v) → u ＝ v
identifications-in-♯-from-sharp-ones = SP.identifications-in-♯-from-sharp-ones

♯𝟘-is-prop : is-prop (♯ (𝟘 {𝓤₀}))
♯𝟘-is-prop u v = identifications-in-♯-from-sharp-ones u v w
 where
  w : ♯ (u ＝ v)
  w .ε♯ = 𝟘-elim (u .ε♯)

\end{code}

2. Under Axiom C1, ♯ 𝟘 is empty [1, Theorem 8.11]: it is a crisp
proposition, hence ♭-discrete, so that an element of it comes from a
crisp one, from which the element of 𝟘 can be extracted. Hence ♭
detects emptiness [1, Corollary 8.16]: a crisp type without crisp
elements is empty. The refutation of ♭ A need not be crisp, because
the introduction rule of ♯ makes it so.

\begin{code}

♯𝟘-is-♭-discrete : is-♭-discrete (♯ (𝟘 {𝓤₀}))
♯𝟘-is-♭-discrete = crisp-props-are-♭-discrete R c1 (♯ 𝟘) ♯𝟘-is-prop

♯𝟘-is-empty : ♯ (𝟘 {𝓤₀}) → 𝟘 {𝓤₀}
♯𝟘-is-empty z = γ (pr₁ (pr₁ ♯𝟘-is-♭-discrete) z)
 where
  γ : ♭ (♯ (𝟘 {𝓤₀})) → 𝟘 {𝓤₀}
  γ (w ^♭) = crisp-elim-sharp w

♭-detects-emptiness : {@♭ 𝓣 : Universe} (@♭ A : 𝓣 ̇ ) → ¬ ♭ A → ¬ A
♭-detects-emptiness A ν a = ♯𝟘-is-empty w
 where
  w : ♯ (𝟘 {𝓤₀})
  w .ε♯ = ν (a ^♭)

\end{code}

3. The quotient Q under Axiom C1. This part is GPT-6 Astra's module
C1FiniteChainBridge of 12 November 2026, with the names changed in two
places. Maps from the generators to 𝟚, and so to Level = (ℕ → 𝟚), are
constant, so Level is ♭-discrete; the counit of Q is an embedding,
because Q is a crisp set, and a surjection, because the quotient map
is crisp; so Q is ♭-discrete [1, Lemma 8.24], and has decidable
equality by crisp excluded middle. Since the consolidation of
13 November 2026 the five lemmas up to Q-is-♭-discrete are typed
aliases of the general part (module under-C1) of
gist.RealCohesion.FiniteChainDiscreteness, which has the same proofs
for an ordinary family; this module passes its crisp R and c1.

\begin{code}

generator-maps-to-𝟚-are-constant
 : (j : J) (f : R j → 𝟚) (x : R j) → f x ＝ f (base-point j)
generator-maps-to-𝟚-are-constant = FC.generator-maps-to-𝟚-are-constant

generator-maps-to-levels-are-constant
 : (j : J) (f : R j → Level) (x : R j) → f x ＝ f (base-point j)
generator-maps-to-levels-are-constant = FC.generator-maps-to-levels-are-constant

levels-are-♭-discrete : is-♭-discrete Level
levels-are-♭-discrete = FC.levels-are-♭-discrete

♭-counit-of-Q-is-surjection : is-surjection (♭-counit {𝓤₁} {Q})
♭-counit-of-Q-is-surjection = FC.♭-counit-of-Q-is-surjection

Q-is-♭-discrete : is-♭-discrete Q
Q-is-♭-discrete = FC.Q-is-♭-discrete

Q-has-decidable-equality : Crisp-EM 𝓤₁ → is-discrete Q
Q-has-decidable-equality cem =
 ♭-discrete-sets-are-discrete cem Q Q-is-set Q-is-♭-discrete

\end{code}

Crisp excluded middle for 𝓤₀ is enough for the equality of Q, although
Q lives in 𝓤₁. Every element of Q is the class of a level, every level
is the value of the counit at a crisp one, and two crisp levels have
the same class if and only if they are related by a finite chain,
which is a crisp proposition in 𝓤₀. This refinement is Fable's.

\begin{code}

private
 module LQ = large-quotient Level chain-equivalence

Q-has-decidable-equality-from-𝓤₀ : Crisp-EM 𝓤₀ → is-discrete Q
Q-has-decidable-equality-from-𝓤₀ cem =
 Q-induction (λ q → (q' : Q) → is-decidable (q ＝ q'))
  (λ q → Π-is-prop fe (λ q' → decidability-of-prop-is-prop fe Q-is-set))
  (λ x → Q-induction (λ q' → is-decidable ([ x ] ＝ q'))
          (λ q' → decidability-of-prop-is-prop fe Q-is-set)
          (λ y → γ (s x) (s y) (ε x) (ε y)))
 where
  s : Level → ♭ Level
  s = pr₁ (pr₁ levels-are-♭-discrete)

  ε : ♭-counit ∘ s ∼ id
  ε = pr₂ (pr₁ levels-are-♭-discrete)

  δ : (@♭ v w : Level) → is-decidable ([ v ] ＝ [ w ])
  δ v w = cases (λ c → inl (LQ.η-identifies-related-points c))
                (λ ν → inr (λ e → ν (LQ.η-relates-identified-points e)))
                (cem (v ≈ w) ∥∥-is-prop)

  γ : (u u' : ♭ Level) {x y : Level}
    → ♭-counit u ＝ x → ♭-counit u' ＝ y → is-decidable ([ x ] ＝ [ y ])
  γ (v ^♭) (w ^♭) refl refl = δ v w

Maps-From-ℝ-To-𝟚-Are-Constant : 𝓤₁ ̇
Maps-From-ℝ-To-𝟚-Are-Constant = C.Maps-From-ℝ-To-𝟚-Are-Constant

Maps-From-ℝ-To-Q-Are-Constant : 𝓤₁ ̇
Maps-From-ℝ-To-Q-Are-Constant = C.Constancy

maps-to-Q-are-constant-if-maps-to-𝟚-are
 : Crisp-EM 𝓤₀
 → Maps-From-ℝ-To-𝟚-Are-Constant
 → Maps-From-ℝ-To-Q-Are-Constant
maps-to-Q-are-constant-if-maps-to-𝟚-are cem c k u v =
 decidable-predicates-spread (λ t → k t ＝ k v)
  (λ t → Q-has-decidable-equality-from-𝓤₀ cem (k t) (k v))
  v u (λ h → c h u v) refl

\end{code}

4. The separator lemma, and its first consequence. A separator is a
map e : ℝ → 𝟚 with two real numbers at which it takes different
values. The lemma, Separators-Make-ℝ-Discrete, is a statement of real
analysis under Axiom C1, with no excluded middle. It is proved in §4a;
its first consequence is stated here relative to it.

\begin{code}

Separators-Make-ℝ-Discrete : 𝓤₁ ̇
Separators-Make-ℝ-Discrete =
 (e : ℝ → 𝟚) (a b : ℝ) → e a ≠ e b → is-♭-discrete ℝ

maps-to-𝟚-are-constant-if-ℝ-is-not-♭-discrete
 : Separators-Make-ℝ-Discrete
 → ¬ is-♭-discrete ℝ
 → Maps-From-ℝ-To-𝟚-Are-Constant
maps-to-𝟚-are-constant-if-ℝ-is-not-♭-discrete sep ν k u v =
 γ (𝟚-is-discrete (k u) (k v))
 where
  γ : is-decidable (k u ＝ k v) → k u ＝ k v
  γ (inl e) = e
  γ (inr d) = 𝟘-elim (ν (sep k u v d))

\end{code}

4a. Proof of the separator lemma. Let e : ℝ → 𝟚, and let g be a map
from a generator to ℝ with g x < g y. We show that e is constant.
Choose rationals p < q with g x < p and q < g y. For a rational C, let
P C say that e s ＝ e t whenever s ≤ t ≤ s + C.

 * P (q - p) holds: for s ≤ t ≤ s + (q - p), the map
   τ ↦ clamp s t (s + (τ - p)) sends g x to s and g y to t, and its
   composite with g and e is a map from a generator to 𝟚, hence
   constant.

 * P C and P C' give P (C + C'), for C and C' ≥ 0, through the point
   min t (s + C).

 * So P N holds for every rational N ≥ 0: halve N until it is below
   q - p, and double back.

 * Two real numbers a and b have a common rational lower bound L, and
   rational upper bounds U and U'. Then e a ＝ e L by P (U - L), and
   e b ＝ e L by P (U' - L).

Neither multiplication nor division of real numbers is used; GPT-6
Astra's proof uses the quotient (g t - g x) / (g y - g x), which needs
them. This form of the argument is Fable's. Since the consolidation of
13 November 2026 its code is the module transfer of
gist.RealCohesion.Constancy, for any pointed type and any set in place
of the generator and 𝟚, and the lemmas below are typed aliases of it,
at the generator R j and the set 𝟚, with their names and types.

\begin{code}

module separator
        (j : J) (g : R j → ℝ) (x y : R j)
        (e : ℝ → 𝟚)
       where

 private
  module T = C.transfer (base-point j) 𝟚-is-set
              (generator-maps-to-𝟚-are-constant j) g x y e

 P : ℚ → 𝓤₁ ̇
 P = T.P

 ≤-translate : (s : ℝ) (C : ℚ) → 0ℚ ≤ C → s ≤ (s + ιₐ C)
 ≤-translate = T.≤-translate

 ≤-min-translate : (u v z : ℝ) (C : ℚ)
                 → z ≤ (u + ιₐ C) → z ≤ (v + ιₐ C) → z ≤ (min u v + ιₐ C)
 ≤-min-translate = T.≤-min-translate

 P-is-monotone : (C C' : ℚ) → C' ≤ C → P C → P C'
 P-is-monotone = T.P-is-monotone

 P-is-additive : (C C' : ℚ) → 0ℚ ≤ C → 0ℚ ≤ C' → P C → P C' → P (C ℚ+ C')
 P-is-additive = T.P-is-additive

 module _ (p q : ℚ) (l₁ : g x < p) (l₂ : q < g y) where

  base : P (q ℚ- p)
  base = T.base p q l₁ l₂

 all-constants : (c : ℚ) → 0ℚ < c → P c → (N : ℚ) → 0ℚ ≤ N → P N
 all-constants = T.all-constants

 hub : ((N : ℚ) → 0ℚ ≤ N → P N)
     → (a : ℝ) (L U : ℚ) → L < a → a < U → e (ιₐ L) ＝ e a
 hub = T.hub

 conclusion : g x < g y → (a b : ℝ) → e a ＝ e b
 conclusion = T.constancy-transfers-along-a-strict-rise

separators-make-ℝ-discrete : Separators-Make-ℝ-Discrete
separators-make-ℝ-discrete e a b d =
 rl-implication (axiom-C0 ℝ)
  (λ j → rl-implication
          (null-iff-maps-are-constant fe (R j) (base-point j) ℝ)
          (λ g x → ♯-is-tight (g x) (g (base-point j))
                    (∥∥-rec 𝟘-is-prop (γ j g x))))
 where
  γ : (j : J) (g : R j → ℝ) (x : R j)
    → (g x < g (base-point j)) ∔ (g (base-point j) < g x) → 𝟘
  γ j g x (inl l) = d (separator.conclusion j g x (base-point j) e l a b)
  γ j g x (inr l) = d (separator.conclusion j g (base-point j) x e l a b)

\end{code}

5. Fixed-point-free maps. If every crisp self-map of the cube has a
fixed point, then no self-map of the cube, crisp or not, is
fixed-point free: the type of fixed-point-free maps is crisp and has
no crisp element.

\begin{code}

Fixed-Point-Free-Maps : ℕ → 𝓤₁ ̇
Fixed-Point-Free-Maps n =
 Σ f ꞉ (Cube n → Cube n) , ((x : Cube n) → ¬ (f x ＝ x))

crisp-fixed-points-exclude-fixed-point-free-maps
 : (@♭ n : ℕ) → Crisp-Cube-Fixed-Point n → ¬ Fixed-Point-Free-Maps n
crisp-fixed-points-exclude-fixed-point-free-maps n φ =
 ♭-detects-emptiness (Fixed-Point-Free-Maps n) γ
 where
  γ : ¬ ♭ (Fixed-Point-Free-Maps n)
  γ (e ^♭) = ∥∥-rec 𝟘-is-prop (λ (x , p) → pr₂ e x p) (φ (pr₁ e))

\end{code}

6. The discrete branch. If ℝ is ♭-discrete, it has decidable equality
by crisp excluded middle for 𝓤₀: two crisp real numbers u and v are
equal if and only if u ≤ v and v ≤ u, a crisp proposition in 𝓤₀. If ℝ
has decidable equality, then it is decidable whether a point lies on
the boundary of the cube, and a retraction of the cube [-1,1]ⁿ⁺¹ onto
its boundary is defined by cases.

\begin{code}

ℝ-has-decidable-equality-if-♭-discrete
 : Crisp-EM 𝓤₀ → is-♭-discrete ℝ → is-discrete ℝ
ℝ-has-decidable-equality-if-♭-discrete cem ((s , ε) , _) x y =
 γ (s x) (s y) (ε x) (ε y)
 where
  δ : (@♭ u v : ℝ) → is-decidable (u ＝ v)
  δ u v = cases (λ (l , m) → inl (≤-ℝ-ℝ-antisym u v l m))
                (λ ν → inr (λ e → ν (transport (λ z → u ≤ z) e (ℝ≤-refl u) ,
                                      transport (λ z → z ≤ u) e (ℝ≤-refl u))))
                (cem ((u ≤ v) × (v ≤ u))
                     (×-is-prop (≤-is-prop u v) (≤-is-prop v u)))

  γ : (a b : ♭ ℝ) {x y : ℝ}
    → ♭-counit a ＝ x → ♭-counit b ＝ y → is-decidable (x ＝ y)
  γ (u ^♭) (v ^♭) refl refl = δ u v

Boundary-Retraction : ℕ → 𝓤₁ ̇
Boundary-Retraction n =
 Σ r ꞉ (Cube n → Cube n) , is-retraction-onto-the-boundary r

module _ (δ : is-discrete ℝ) where

 being-on-the-boundary-is-decidable
  : {n : ℕ} (x : ℝ^ n) → is-decidable (on-boundary x)
 being-on-the-boundary-is-decidable {n} x =
  γ (Fin-Compact (λ i → (x i ＝ embedding-ℚ-to-ℝ -1ℚ) ∔ (x i ＝ 1ℝ))
      (λ i → +-preserves-decidability
              (δ (x i) (embedding-ℚ-to-ℝ -1ℚ)) (δ (x i) 1ℝ)))
  where
   γ : is-decidable (Σ i ꞉ Fin n , (x i ＝ embedding-ℚ-to-ℝ -1ℚ) ∔ (x i ＝ 1ℝ))
     → is-decidable (on-boundary x)
   γ (inl σ) = inl ∣ σ ∣
   γ (inr ν) = inr (∥∥-rec 𝟘-is-prop ν)

 module _ {n : ℕ} where

  corner : Cube (succ n)
  corner = (λ _ → 1ℝ) , (λ _ → minus-one-below-one , ℝ≤-refl 1ℝ)

  corner-is-on-the-boundary : on-boundary (pr₁ corner)
  corner-is-on-the-boundary = ∣ 𝟎 , inr refl ∣

  by-cases : (x : Cube (succ n)) → is-decidable (on-boundary (pr₁ x))
           → Cube (succ n)
  by-cases x (inl _) = x
  by-cases x (inr _) = corner

  by-cases-lands : (x : Cube (succ n)) (d : is-decidable (on-boundary (pr₁ x)))
                 → on-boundary (pr₁ (by-cases x d))
  by-cases-lands x (inl b) = b
  by-cases-lands x (inr _) = corner-is-on-the-boundary

  by-cases-fixes : (x : Cube (succ n)) (d : is-decidable (on-boundary (pr₁ x)))
                 → on-boundary (pr₁ x) → by-cases x d ＝ x
  by-cases-fixes x (inl _) b = refl
  by-cases-fixes x (inr ν) b = 𝟘-elim (ν b)

  boundary-retraction-from-decidable-equality : Boundary-Retraction (succ n)
  boundary-retraction-from-decidable-equality =
   (λ x → by-cases x (being-on-the-boundary-is-decidable (pr₁ x))) ,
   (λ x → by-cases-lands x (being-on-the-boundary-is-decidable (pr₁ x))) ,
   (λ x → by-cases-fixes x (being-on-the-boundary-is-decidable (pr₁ x)))

\end{code}

7. The theorems. First the two branches, which need crisp excluded
middle for 𝓤₀ only.

\begin{code}

module _ (@♭ cem₀ : Crisp-EM 𝓤₀) where

 crisp-fixed-points-if-ℝ-is-not-♭-discrete
  : ¬ is-♭-discrete ℝ
  → {@♭ n : ℕ} (@♭ kuhn : Kuhn-Lemma n)
  → Crisp-Cube-Fixed-Point n
 crisp-fixed-points-if-ℝ-is-not-♭-discrete ν =
  crisp-cube-fixed-point cem₀
   (maps-to-Q-are-constant-if-maps-to-𝟚-are cem₀
     (maps-to-𝟚-are-constant-if-ℝ-is-not-♭-discrete
       separators-make-ℝ-discrete ν))

 sharp-fixed-points-if-ℝ-is-not-♭-discrete
  : ¬ is-♭-discrete ℝ
  → {@♭ n : ℕ} (@♭ kuhn : Kuhn-Lemma n)
  → Sharp-Cube-Fixed-Point native-sharp n
 sharp-fixed-points-if-ℝ-is-not-♭-discrete ν {n} kuhn =
  crisp-fixed-points-give-sharp-fixed-points native-sharp n
   (crisp-fixed-points-if-ℝ-is-not-♭-discrete ν kuhn)

 no-fixed-point-free-maps-if-ℝ-is-not-♭-discrete
  : ¬ is-♭-discrete ℝ
  → {@♭ n : ℕ} (@♭ kuhn : Kuhn-Lemma n)
  → ¬ Fixed-Point-Free-Maps n
 no-fixed-point-free-maps-if-ℝ-is-not-♭-discrete ν {n} kuhn =
  crisp-fixed-points-exclude-fixed-point-free-maps n
   (crisp-fixed-points-if-ℝ-is-not-♭-discrete ν kuhn)

 boundary-retraction-if-ℝ-is-♭-discrete
  : is-♭-discrete ℝ → {n : ℕ} → Boundary-Retraction (succ n)
 boundary-retraction-if-ℝ-is-♭-discrete d =
  boundary-retraction-from-decidable-equality
   (ℝ-has-decidable-equality-if-♭-discrete cem₀ d)

\end{code}

Crisp excluded middle for 𝓤₁ decides whether ℝ is ♭-discrete, and
gives the dichotomy and the lemma.

\begin{code}

 module _ (cem₁ : Crisp-EM 𝓤₁) where

  ℝ-is-♭-discrete-or-not : is-♭-discrete ℝ ∔ ¬ is-♭-discrete ℝ
  ℝ-is-♭-discrete-or-not =
   cem₁ (is-♭-discrete ℝ) (being-equiv-is-prop'' fe ♭-counit)

  discrete-or-no-fixed-point-free-maps
   : {@♭ n : ℕ} (@♭ kuhn : Kuhn-Lemma n)
   → is-♭-discrete ℝ ∔ ¬ Fixed-Point-Free-Maps n
  discrete-or-no-fixed-point-free-maps {n} kuhn = γ ℝ-is-♭-discrete-or-not
   where
    γ : is-♭-discrete ℝ ∔ ¬ is-♭-discrete ℝ
      → is-♭-discrete ℝ ∔ ¬ Fixed-Point-Free-Maps n
    γ (inl d) = inl d
    γ (inr ν) = inr (no-fixed-point-free-maps-if-ℝ-is-not-♭-discrete ν kuhn)

  Lemma-12-3-for-the-cube
   : {@♭ n : ℕ} (@♭ kuhn : Kuhn-Lemma (succ n))
   → Fixed-Point-Free-Maps (succ n)
   → Boundary-Retraction (succ n)
  Lemma-12-3-for-the-cube {n} kuhn e =
   γ (discrete-or-no-fixed-point-free-maps kuhn)
   where
    γ : is-♭-discrete ℝ ∔ ¬ Fixed-Point-Free-Maps (succ n)
      → Boundary-Retraction (succ n)
    γ (inl d) = boundary-retraction-if-ℝ-is-♭-discrete d
    γ (inr ν) = 𝟘-elim (ν e)

  Lemma-12-3-for-the-square
   : (f : Cube 2 → Cube 2)
   → ((x : Cube 2) → ¬ (f x ＝ x))
   → Boundary-Retraction 2
  Lemma-12-3-for-the-square f h =
   Lemma-12-3-for-the-cube (kuhn-lemma-2 fe) (f , h)

\end{code}

8. The analytic Markov principle [1, Theorem 8.32]. Under Axiom C1 an
element of ♯ P gives ¬¬ P, for any type P, because ♯ 𝟘 is empty. So if
positivity is stable under double negation, then Axiom T holds: the
analytic Markov principle without Axiom T is as strong as Axiom T.
Together with Axiom-T-gives-stability of
gist.RealCohesion.AxiomTObstruction, which needs crisp excluded middle
and not Axiom C1, this is the remark of [1, §8.3] that the two are
equivalent in the presence of excluded middle.

\begin{code}

♯-gives-¬¬ : {𝓤 : Universe} {P : 𝓤 ̇ } → ♯ P → ¬¬ P
♯-gives-¬¬ z ν = ♯𝟘-is-empty (♯-map ν z)

stability-of-positivity-gives-Axiom-T : Positivity-Is-Stable → Axiom-T
stability-of-positivity-gives-Axiom-T σ r =
 props-with-a-map-from-sharp-are-codiscrete native-sharp (<-is-prop 0ℝ r)
  (λ z → σ r (♯-gives-¬¬ z))

\end{code}

If ℝ is ♭-discrete, positivity is stable, by crisp excluded middle:
every real number is the value of the counit at a crisp one.

\begin{code}

positivity-is-stable-if-ℝ-is-♭-discrete
 : Crisp-EM 𝓤₀ → is-♭-discrete ℝ → Positivity-Is-Stable
positivity-is-stable-if-ℝ-is-♭-discrete cem ((s , ε) , _) r h =
 γ (s r) (ε r)
 where
  γ : (u : ♭ ℝ) → ♭-counit u ＝ r → 0ℝ < r
  γ (v ^♭) e = cases (λ l → transport (0ℝ <_) e l)
                     (λ ν → 𝟘-elim (h (λ l → ν (transport (0ℝ <_) (e ⁻¹) l))))
                     (cem (0ℝ < v) (<-is-prop 0ℝ v))

\end{code}
