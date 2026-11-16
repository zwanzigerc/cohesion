Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 25 October 2026; prose updated 27 October 2026. See the AI
disclosure in
gist.RealCohesion.index. The statements follow the plan [3], whose
Agda part was prepared by Codex (25 October 2026); the dense positive
family was proposed by Claude Opus in an earlier conversation. Both
obstructions are abstracted from the pointless-end countermodel of the
research notes [1, Theorem 2.5].

Conditional refutations of the analytic Markov principle and of the
full fan theorem, for TypeTopology's Dedekind reals.

The analytic Markov principle says that a real number that is not
≤ 0 is positive. Shulman derives it from Axioms LEM, C1 and T
[2, Theorem 8.32], and Axiom C1 is not needed for this form of it
(gist.RealCohesion.AxiomTObstruction). It is not provable from crisp
excluded middle and Axioms R♭ and AC [1, Theorem 2.5(i)], and neither
is the full fan theorem [1, Theorem 2.5(ii)]. Here we prove, constructively,
that two kinds of data refute these principles. Both kinds of data
are realized in the pointless-end countermodel, as explained at the
end of this file. This is not formalized.

1. A dense positive family: a type X and a map t : X → ℝ such that

     (x : X) → ¬¬ (0 < t x)        and        ¬ ((x : X) → 0 < t x).

   It refutes the analytic Markov principle, and its variant for the
   apartness of real numbers, because every t x is not ≤ 0. Only the
   incompatibility of 0 < r with r ≤ 0 is used.

2. The five conditions of a binary bar: a type X, a map t : X → ℝ and
   a family B of predicates on binary words, with

     B1 root:          B x [] ↔ 0 < t x,
     B2 splitting:     B x s ↔ (B x (s ⌢ ₀) × B x (s ⌢ ₁)),
     B3 sibling cover: B x (s ⌢ ₀) ∨ B x (s ⌢ ₁),
     B4 bar:           every binary sequence has an initial segment
                       in B x,
     B5 properness:    ¬ ((x : X) → 0 < t x),

   for all x : X and words s. They refute both principles. B1–B4 give
   the density of the first kind of data
   (gist.RealCohesion.BinaryBarObstruction), so it is derived here, not assumed.
   The refutation of the full fan theorem uses only B1 (one direction), B2, B4
   and B5.

All the displayed quantifiers are over ordinary variables. In the
countermodel the data X, t, B can be taken crisp, but the conditions,
and the principles that they refute, quantify over arbitrary elements.
For crisp elements, crisp excluded middle makes the dense family
positive (gist.RealCohesion.CrispBarObstruction).

The analytic Markov principle is equivalent to the stability of
positivity under double negation. This is the form that the route
through Axiom T uses (gist.RealCohesion.AxiomTObstruction).

[1] Answers to some open problems in real-cohesive homotopy type
    theory. Research notes, draft of 25 October 2026.
    references/C01-write-up-2026-10-25.tex

[2] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer
    Science 28(6), 856–941, 2018. https://arxiv.org/abs/1509.07584v3
    Numbering as in version 3 of the arXiv preprint.

[3] The ordinary pointless-end countermodel: a formalization plan,
    revision 3, 25 October 2026. In particular its parts
    OBSTRUCTION-VERIFICATION.md and AGDA-CONDITIONAL-REFUTATIONS.md.
    references/C09-pointless-end-gameplan-v3.md
    references/C09a-obstruction-verification.md
    references/C09b-agda-conditional-refutations.md

[4] The library PointlessEnd of the Lean package cohesion, with its
    report NLAB23.md, 26 October 2026.
    references/C10-NLAB23.md

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.AnalyticMarkovObstruction
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import DedekindReals.Order fe pe pt
open import DedekindReals.Type fe pe pt
open import MLTT.List hiding ([_])
open import Notation.Order
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import gist.RealCohesion.BinaryBarObstruction pt fe
open import gist.RealCohesion.Cylinders pt fe using (_⌢_ ; _↾_)
open import gist.RealCohesion.RealOrder fe pe pt
 using (ℝ<-gives-≤) renaming (ℝ≤-refl to ℝ≤-is-reflexive) public
open import gist.RealCohesion.RealLattice fe pe pt
 using (max ; ≤-max-left ; ≤-max-right ; ≤-from-difference ; <-from-difference ;
        positive-max)
 renaming (_+_ to _ℝ+_ ; -_ to ℝ-_)

open PropositionalTruncation pt

\end{code}

The principles.

\begin{code}

Analytic-Markov : 𝓤₁ ̇
Analytic-Markov = (r : ℝ) → ¬ (r ≤ 0ℝ) → 0ℝ < r

Analytic-Markov-For-Apartness : 𝓤₁ ̇
Analytic-Markov-For-Apartness = (x y : ℝ) → x ≠ y → x ♯ y

Positivity-Is-Stable : 𝓤₁ ̇
Positivity-Is-Stable = (r : ℝ) → ¬¬ (0ℝ < r) → 0ℝ < r

\end{code}

Two facts about the order of the reals, ℝ≤-refl and ℝ<-gives-≤ of
gist.RealCohesion.RealOrder, are re-exported here, the first under the
name ℝ≤-is-reflexive.

The analytic Markov principle is equivalent to the stability of
positivity, and to its version for apartness. For the last
equivalence: if x ≠ y, then max (x - y) (y - x) is not ≤ 0, because
otherwise x ≤ y and y ≤ x; so it is positive, and then x - y or y - x
is positive.

\begin{code}

analytic-Markov-gives-stability : Analytic-Markov → Positivity-Is-Stable
analytic-Markov-gives-stability amp r h =
 amp r (λ l → h (ℝ-less-than-or-equal-not-greater r 0ℝ l))

stability-gives-analytic-Markov : Positivity-Is-Stable → Analytic-Markov
stability-gives-analytic-Markov stable r ν =
 stable r (λ m → ν (ℝ-not-less-is-greater-or-equal 0ℝ r m))

apartness-version-gives-analytic-Markov : Analytic-Markov-For-Apartness
                                        → Analytic-Markov
apartness-version-gives-analytic-Markov amp r ν =
 ∨-elim (<-is-prop 0ℝ r)
  (λ (l : r < 0ℝ) → 𝟘-elim (ν (ℝ<-gives-≤ r 0ℝ l)))
  id
  (amp r 0ℝ r-is-not-0)
 where
  r-is-not-0 : r ≠ 0ℝ
  r-is-not-0 e = ν (transport (_≤ 0ℝ) (e ⁻¹) (ℝ≤-is-reflexive 0ℝ))

analytic-Markov-gives-apartness-version : Analytic-Markov
                                        → Analytic-Markov-For-Apartness
analytic-Markov-gives-apartness-version amp x y ν =
 ∥∥-functor γ (positive-max (x ℝ+ (ℝ- y)) (y ℝ+ (ℝ- x)) (amp r r-is-not-≤-0))
 where
  r : ℝ
  r = max (x ℝ+ (ℝ- y)) (y ℝ+ (ℝ- x))

  r-is-not-≤-0 : ¬ (r ≤ 0ℝ)
  r-is-not-≤-0 k =
   ν (≤-ℝ-ℝ-antisym x y
       (≤-from-difference x y
         (ℝ≤-trans (x ℝ+ (ℝ- y)) r 0ℝ (≤-max-left (x ℝ+ (ℝ- y)) (y ℝ+ (ℝ- x)))
           k))
       (≤-from-difference y x
         (ℝ≤-trans (y ℝ+ (ℝ- x)) r 0ℝ (≤-max-right (x ℝ+ (ℝ- y)) (y ℝ+ (ℝ- x)))
           k)))

  γ : (0ℝ < (x ℝ+ (ℝ- y))) + (0ℝ < (y ℝ+ (ℝ- x))) → (x < y) + (y < x)
  γ (inl l) = inr (<-from-difference x y l)
  γ (inr l) = inl (<-from-difference y x l)

\end{code}

1. A dense positive family refutes the analytic Markov principle.

\begin{code}

module _ {𝓤 : Universe}
         (X : 𝓤 ̇ )
         (t : X → ℝ)
         (dense-positive : (x : X) → ¬¬ (0ℝ < t x))
         (proper-positive : ¬ ((x : X) → 0ℝ < t x))
       where

 dense-positive-family-refutes-stability : ¬ Positivity-Is-Stable
 dense-positive-family-refutes-stability stable =
  proper-positive (λ x → stable (t x) (dense-positive x))

 dense-positive-family-refutes-analytic-Markov : ¬ Analytic-Markov
 dense-positive-family-refutes-analytic-Markov amp =
  dense-positive-family-refutes-stability (analytic-Markov-gives-stability amp)

 dense-positive-family-refutes-apartness-version
  : ¬ Analytic-Markov-For-Apartness
 dense-positive-family-refutes-apartness-version amp =
  dense-positive-family-refutes-analytic-Markov
   (apartness-version-gives-analytic-Markov amp)

\end{code}

2. The five conditions. They are data, so this record needn't be a
proposition. Density is not among the fields.

\begin{code}

record Five-Conditions {𝓤 𝓥 : Universe}
                       (X : 𝓤 ̇ )
                       (t : X → ℝ)
                       (B : X → List 𝟚 → Ω 𝓥)
                     : 𝓤 ⊔ 𝓥 ̇ where
 field
  root          : (x : X) → B x [] holds ↔ 0ℝ < t x
  splitting     : (x : X) → Splitting (B x)
  sibling-cover : (x : X) → Sibling-Cover (B x)
  bar           : (x : X) → Bar (B x)
  proper        : ¬ ((x : X) → 0ℝ < t x)

\end{code}

The refutation of the full fan theorem with exactly the conditions
that it uses: one direction of B1, and B2, B4 and B5.

\begin{code}

root-splitting-bar-and-properness-refute-full-FAN
 : {𝓤 𝓥 : Universe}
   (X : 𝓤 ̇ )
   (t : X → ℝ)
   (B : X → List 𝟚 → Ω 𝓥)
 → ((x : X) → B x [] holds → 0ℝ < t x)
 → ((x : X) → Splitting (B x))
 → ((x : X) → Bar (B x))
 → ¬ ((x : X) → 0ℝ < t x)
 → ¬ Full-FAN 𝓥
root-splitting-bar-and-properness-refute-full-FAN X t B root splits bar proper =
 family-of-splitting-bars-refutes-full-FAN X B splits bar
  (λ h → proper (λ x → root x (h x)))

\end{code}

The consequences of the five conditions.

\begin{code}

module _ {𝓤 𝓥 : Universe}
         {X : 𝓤 ̇ }
         {t : X → ℝ}
         {B : X → List 𝟚 → Ω 𝓥}
         (𝓑 : Five-Conditions X t B)
       where

 open Five-Conditions 𝓑

 five-conditions-give-dense-positive : (x : X) → ¬¬ (0ℝ < t x)
 five-conditions-give-dense-positive x =
  ¬¬-functor (lr-implication (root x))
   (empty-word-is-not-not-in-splitting-bar
     (B x) (splitting x) (sibling-cover x) (bar x))

 five-conditions-give-dense-proper-positive
  : ((x : X) → ¬¬ (0ℝ < t x)) × ¬ ((x : X) → 0ℝ < t x)
 five-conditions-give-dense-proper-positive =
  five-conditions-give-dense-positive , proper

 five-conditions-refute-analytic-Markov : ¬ Analytic-Markov
 five-conditions-refute-analytic-Markov =
  dense-positive-family-refutes-analytic-Markov
   X t five-conditions-give-dense-positive proper

 five-conditions-refute-full-FAN : ¬ Full-FAN 𝓥
 five-conditions-refute-full-FAN =
  root-splitting-bar-and-properness-refute-full-FAN X t B
   (λ x → lr-implication (root x)) splitting bar proper

 five-conditions-refute-both : ¬ Analytic-Markov × ¬ Full-FAN 𝓥
 five-conditions-refute-both = five-conditions-refute-analytic-Markov ,
                               five-conditions-refute-full-FAN

\end{code}

The same conclusions from the mere existence of the data.

\begin{code}

dense-positive-family-exists-refutes-analytic-Markov
 : {𝓤 : Universe}
 → (∃ X ꞉ 𝓤 ̇ , Σ t ꞉ (X → ℝ) , ((x : X) → ¬¬ (0ℝ < t x))
                              × ¬ ((x : X) → 0ℝ < t x))
 → ¬ Analytic-Markov
dense-positive-family-exists-refutes-analytic-Markov =
 ∥∥-rec (negations-are-props fe)
  (λ (X , t , d , p) → dense-positive-family-refutes-analytic-Markov X t d p)

five-conditions-exist-refute-both
 : {𝓤 𝓥 : Universe}
 → (∃ X ꞉ 𝓤 ̇ , Σ t ꞉ (X → ℝ) , Σ B ꞉ (X → List 𝟚 → Ω 𝓥) ,
                 Five-Conditions X t B)
 → ¬ Analytic-Markov × ¬ Full-FAN 𝓥
five-conditions-exist-refute-both =
 ∥∥-rec (×-is-prop (negations-are-props fe) (negations-are-props fe))
  (λ (X , t , B , 𝓑) → five-conditions-refute-both 𝓑)

\end{code}

Why the data are not arbitrary. The pointless-end countermodel
[1, Theorem 2.5] is an ∞-topos of sheaves on a site of locales; here
we use its 1-topos of sheaves of sets. Take X to be the sheaf
represented by the locale X_⊤, t its coordinate, and B_s the open
(𝟏 , cyl′ s) of the glued frame of gist.RealCohesion.PointlessEnd,
where cyl′ s is the complement of the cylinder of s. The frame-level
forms of B1–B4 are proved in gist.RealCohesion.BinaryBarFrame and
gist.RealCohesion.PointlessEnd, relative to the hypotheses on the
frames made there, and the collar is not 𝟏. The notes [1] argue that
the coordinate is positive exactly on the collar, that the collar is
dense, that the bar refutes the fan theorem at the stage X_⊤, and
that the only subterminal objects of the model are 0 and 1
[1, Proposition 2.4(ii)], from which properness follows as an internal
statement. The five conditions as internal statements, and the density
of the collar in the lattice of all subsheaves, are from the plan [3].
None of these semantic facts is formalized in Agda: neither the
transfer of the frame identities to internal statements about sheaves,
nor the interpretation of the quantifiers, nor the validity of Axiom
R♭ and crisp excluded middle in the model. They are formalized in Lean
[4], for the 1-topos of sheaves of sets on a smaller site of charts
(the point, ℝ and the locales X_e, without products): the five
conditions, the density of the collar and properness as internal
statements, Axiom R♭ and crisp excluded middle, and the failure of the
analytic Markov principle and of the full fan theorem. So the
theorems of this file are conditional internal results. They don't
show that crisp excluded middle and Axiom R♭ prove the negation of
either principle. The argument concerns sheaves of sets: it is a
(1,1)-categorical compatibility argument, not a model of univalent
real-cohesive type theory.
