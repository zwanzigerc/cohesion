Claude Fable 5.2, an AI model made by Anthropic, prompted by Colin
Zwanziger, 11 November 2026. Starter module: the statements to be
proved in the formalization of three results of the write-up
"Answers to some open problems in real-cohesive homotopy type theory"
(seventh revision of 11 November 2026). Only statements, the theorems to
be proved as types (the Target definitions at the end), and three
modal reductions, each a one-line application of the interface of
gist.RealCohesion.Sharp, and the transfer of Corollary 3.7 from the
cube to any crisp retract of it, which relates the cube form to the
exact statement; no other proofs.

Updated by Claude Opus 5.5 on 13 November 2026, after the final audits,
in the prose only: every target of this module is now proved in
gist.RealCohesion.Theorems, and three passages below that spoke of
work still to be done now say where it is done. Later that day, in the
consolidation that followed, Claude Opus 5.5 replaced the definitions
of bit, corner and Kuhn-Lemma by typed aliases of the same definitions
in gist.RealCohesion.KuhnStatement, which gist.RealCohesion.KuhnLemma
shares (step K2 of Claude Fable 5.2's consolidation plan).

 * Theorem 7.10 (Shulman's Theorem 11.7 [1] without crisp excluded
   middle): Axiom R♭ refutes the analytic lesser limited principle of
   omniscience. The theorem to prove is

     Singly-Generated-Punctual-Cohesion ℝ 0ℝ → ¬ Analytic-LLPO

 * Corollary 3.7 (Shulman's Theorem 12.4 and Corollary 12.5 without
   Axiom T and without univalence), in the form for the cube [-1,1]ⁿ:
   under crisp excluded middle and Axiom R♭, every crisp self-map of
   the cube has a fixed point (Crisp-Cube-Fixed-Point), and every
   self-map has one under ♯ (Sharp-Cube-Fixed-Point).

 * Theorem 4.3, in the form for the cube: under crisp excluded middle,
   Axiom R♭ and Axiom T, every self-map of the cube, crisp or not, has
   rational ε-fixed points (Approximate-Cube-Fixed-Point).

The write-up states the last two for the Euclidean unit ball. The
blueprint addendum of 11 November explains why the cube comes first:
it needs no multiplication of real numbers.

The combinatorial input is Kuhn's cubical lemma [2], in the form in
which it is proved in HOL Light and Isabelle/HOL [3] (kuhn_lemma). It
is a statement about functions on finite grids and involves neither
real numbers nor modalities. Here the grid {0,…,p+1}ⁿ has side p + 1,
so that it is never empty. A labelling ℓ gives every grid point a
vector of n bits. If the i-th bit is ₀ on the face where the i-th
coordinate is 0, and ₁ on the face where it is p + 1, then some unit
cube of the grid has, for every i, a corner whose i-th bit is ₀ and a
corner whose i-th bit is ₁.

Sequential hitting is stated for functionals on X → ℝ, for an
arbitrary type X. For X = 𝟙 it is Sequential-Hitting of
gist.RealCohesion.ApproximateIVTStatement, and for X = Fin n it is
Theorem 7.4 of the write-up for ℝⁿ with the supremum norm.

[1] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer
    Science 28(6), 856–941, 2018. https://arxiv.org/abs/1509.07584v3

[2] Harold W. Kuhn. Some combinatorial lemmas in topology. IBM Journal
    of Research and Development 4(5), 518–524, 1960.

[3] John Harrison's proof, translated from HOL Light to Isabelle/HOL by
    Robert Himmelmann: kuhn_lemma of Brouwer_Fixpoint.thy.

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.BrouwerStatements
        (@♭ fe : Fun-Ext)
        (@♭ pe : Prop-Ext)
        (@♭ pt : propositional-truncations-exist)
       where

open import Fin.Type
open import Naturals.Addition renaming (_+_ to _+ℕ_)
open import Naturals.Order
open import Notation.Order
open import Rationals.Type
open import Rationals.Order
open import Rationals.Addition renaming (_+_ to _+ℚ_)
open import Rationals.Negation renaming (_-_ to _-ℚ_)
open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import DedekindReals.Addition fe pe pt renaming (_+_ to _+ℝ_)
open import Rationals.Limits fe pe pt using (⟨1/2⟩^_)
open import gist.CohesiveApartness.Flat
open import gist.RealCohesion.Sharp
import gist.RealCohesion.KuhnStatement as KS

open PropositionalTruncation pt

\end{code}

The analytic lesser limited principle of omniscience.

\begin{code}

Analytic-LLPO : 𝓤₁ ̇
Analytic-LLPO = (x : ℝ) → (x ≤ 0ℝ) ∨ (0ℝ ≤ x)

\end{code}

Sequential hitting for functionals, and the form in which the
fixed-point argument uses it.

\begin{code}

2⁻ : ℕ → ℝ
2⁻ j = embedding-ℚ-to-ℝ (⟨1/2⟩^ j)

_is-within-2⁻_of_ : {𝓥 : Universe} {X : 𝓥 ̇ } → (X → ℝ) → ℕ → (X → ℝ) → 𝓥 ̇
_is-within-2⁻_of_ {𝓥} {X} z j a =
 (x : X) → (z x ≤ a x +ℝ 2⁻ j) × (a x ≤ z x +ℝ 2⁻ j)

Sequential-Hitting-For-Functionals : (𝓥 : Universe) → 𝓤₁ ⊔ (𝓥 ⁺) ̇
Sequential-Hitting-For-Functionals 𝓥 =
   (X : 𝓥 ̇ ) (h : (X → ℝ) → ℝ) (a : X → ℝ) (z : ℕ → X → ℝ)
 → ((j : ℕ) → z j is-within-2⁻ j of a)
 → 1ℝ ≤ h a
 → ∃ j ꞉ ℕ , 0ℝ < h (z j)

Closed-Half-Lines-Are-Sequentially-Closed : (𝓥 : Universe) → 𝓤₁ ⊔ (𝓥 ⁺) ̇
Closed-Half-Lines-Are-Sequentially-Closed 𝓥 =
   (X : 𝓥 ̇ ) (H : (X → ℝ) → ℝ) (a : X → ℝ) (z : ℕ → X → ℝ)
 → ((j : ℕ) → z j is-within-2⁻ j of a)
 → ((j : ℕ) → H (z j) ≤ 0ℝ)
 → H a ≤ 0ℝ

\end{code}

Kuhn's cubical lemma for dimension n, described in words above. The
statement is that of gist.RealCohesion.KuhnStatement, with the corners
of the unit cube at q written as corner q r. The three names are typed
aliases of the definitions there, so that, as before, they take the
parameters of this module.

\begin{code}

bit : 𝟚 → ℕ
bit = KS.bit

corner : {n : ℕ} → (Fin n → ℕ) → (Fin n → 𝟚) → Fin n → ℕ
corner = KS.corner

Kuhn-Lemma : ℕ → 𝓤₀ ̇
Kuhn-Lemma = KS.Kuhn-Lemma

\end{code}

The cube [-1,1]ⁿ and its rational points.

\begin{code}

ℝ^ : ℕ → 𝓤₁ ̇
ℝ^ n = Fin n → ℝ

in-cube : {n : ℕ} → ℝ^ n → 𝓤₀ ̇
in-cube {n} x = (i : Fin n) → (embedding-ℚ-to-ℝ -1ℚ ≤ x i) × (x i ≤ 1ℝ)

Cube : ℕ → 𝓤₁ ̇
Cube n = Σ x ꞉ ℝ^ n , in-cube x

rational-point : {n : ℕ} → (Fin n → ℚ) → ℝ^ n
rational-point q i = embedding-ℚ-to-ℝ (q i)

\end{code}

The three fixed-point statements. In the third, |f q - q| < ε in the
supremum norm is written as two strict inequalities for each
coordinate.

\begin{code}

Crisp-Cube-Fixed-Point : (@♭ n : ℕ) → 𝓤₁ ̇
Crisp-Cube-Fixed-Point n =
 (@♭ f : Cube n → Cube n) → ∃ x ꞉ Cube n , f x ＝ x

has-rational-approximate-fixed-point : {n : ℕ} → (Cube n → Cube n) → ℚ → 𝓤₀ ̇
has-rational-approximate-fixed-point {n} f ε =
   ∃ q ꞉ (Fin n → ℚ)
 , Σ c ꞉ in-cube (rational-point q)
 ,
 ((i : Fin n) → (pr₁ (f (rational-point q , c)) i < embedding-ℚ-to-ℝ (q i +ℚ ε))
              ×
              (embedding-ℚ-to-ℝ (q i -ℚ ε) < pr₁ (f (rational-point q , c)) i))

Approximate-Cube-Fixed-Point : ℕ → 𝓤₁ ̇
Approximate-Cube-Fixed-Point n =
   (f : Cube n → Cube n) (ε : ℚ)
 → 0ℚ < ε
 → has-rational-approximate-fixed-point f ε

module _ (S : Sharp-Modality) where

 open Sharp-Modality S

 Sharp-Cube-Fixed-Point : ℕ → 𝓤₁ ̇
 Sharp-Cube-Fixed-Point n =
  (f : Cube n → Cube n) → ♯ (∃ x ꞉ Cube n , f x ＝ x)

\end{code}

The second statement follows from the first by crisp induction for ♯,
with no further assumption. This is the last paragraph of the proof of
Corollary 3.7 in the write-up.

\begin{code}

 crisp-fixed-points-give-sharp-fixed-points
  : (@♭ n : ℕ) → Crisp-Cube-Fixed-Point n → Sharp-Cube-Fixed-Point n
 crisp-fixed-points-give-sharp-fixed-points n φ =
  crisp-ind-sharp (λ f → ∃ x ꞉ Cube n , f x ＝ x) φ

\end{code}

Lemma 4.1 of the write-up: under Axiom T, the statement that some term
of a sequence of real numbers is positive is codiscrete.

\begin{code}

 Positive-Terms-Are-Codiscrete : 𝓤₁ ̇
 Positive-Terms-Are-Codiscrete =
  (x : ℕ → ℝ) → is-codiscrete S (∃ k ꞉ ℕ , 0ℝ < x k)

\end{code}

Shulman's Theorem 3.3 (decrispify) then reduces
Approximate-Cube-Fixed-Point to crisp self-maps: it suffices to have,
for every self-map f and tolerance ε, a sequence of real numbers such
that a positive term yields a rational approximate fixed point, and
such that a term is positive whenever f is crisp. This is the first
step of the proof of Theorem 4.3 in the write-up. The tolerance ε is
not assumed crisp, and the sequence need not detect every rational
point; the blueprint addendum takes the k-th term to test the grid
points of side 2ᵏ.

\begin{code}

 approximate-fixed-points-from-crisp-maps
  : (@♭ n : ℕ)
    (x : (Cube n → Cube n) → ℚ → ℕ → ℝ)
  → Positive-Terms-Are-Codiscrete
  → ((f : Cube n → Cube n) (ε : ℚ)
        → (∃ k ꞉ ℕ , 0ℝ < x f ε k)
        → has-rational-approximate-fixed-point f ε)
  → ((@♭ f : Cube n → Cube n) (ε : ℚ) → 0ℚ < ε → ∃ k ꞉ ℕ , 0ℝ < x f ε k)
  → Approximate-Cube-Fixed-Point n
 approximate-fixed-points-from-crisp-maps n x κ α φ f ε l =
  α f ε (decrispify S (λ g → ∃ k ꞉ ℕ , 0ℝ < x g ε k)
          (λ g → κ (x g ε)) (λ g → φ g ε l) f)

\end{code}

The theorems to prove. Crisp excluded middle and Kuhn's lemma are
crisp hypotheses, because the fixed point is the limit of a sequence
constructed from them, and the propositions decided along the way
must be crisp. Kuhn's lemma is a theorem of Martin-Löf type theory.
When this module was written, it was a hypothesis here until it would
be proved in the library; it is now proved in every dimension
(gist.RealCohesion.KuhnLemmaGeneral). gist.RealCohesion.Theorems
proves each target below, and states the fixed-point theorems also
without that hypothesis, in the forms named …-in-every-dimension.

\begin{code}

Target-7-10 : 𝓤ω
Target-7-10 = Singly-Generated-Punctual-Cohesion ℝ 0ℝ → ¬ Analytic-LLPO

Target-hitting : (𝓥 : Universe) → 𝓤ω
Target-hitting 𝓥 = Singly-Generated-Punctual-Cohesion ℝ 0ℝ
                 → Sequential-Hitting-For-Functionals 𝓥

Target-3-7-crisp : (@♭ n : ℕ) → 𝓤ω
Target-3-7-crisp n = (@♭ cem : Crisp-EM 𝓤₀)
                   → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
                   → (@♭ kuhn : Kuhn-Lemma n)
                   → Crisp-Cube-Fixed-Point n

module _ (S : Sharp-Modality) where

 open Sharp-Modality S
 open import gist.RealCohesion.AxiomTObstruction fe pe pt S using (Axiom-T)
 open import gist.RealCohesion.AnalyticMarkovObstruction fe pe pt
       using (Analytic-Markov-For-Apartness)

 Target-3-7-sharp : (@♭ n : ℕ) → 𝓤ω
 Target-3-7-sharp n = (@♭ cem : Crisp-EM 𝓤₀)
                    → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
                    → (@♭ kuhn : Kuhn-Lemma n)
                    → Sharp-Cube-Fixed-Point S n

 Target-4-1 : 𝓤₁ ̇
 Target-4-1 = Axiom-T → Positive-Terms-Are-Codiscrete S

 Target-8-32 : 𝓤₁ ̇
 Target-8-32 = Crisp-EM 𝓤₀ → Axiom-T → Analytic-Markov-For-Apartness

 Target-4-3 : (@♭ n : ℕ) → 𝓤ω
 Target-4-3 n = (@♭ cem : Crisp-EM 𝓤₀)
              → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
              → Axiom-T
              → (@♭ kuhn : Kuhn-Lemma n)
              → Approximate-Cube-Fixed-Point n

\end{code}

Target-8-32 is Shulman's Theorem 8.32 in its apartness form, without
his Axiom C1. Its order form, for the same hypotheses, is
Axiom-T-gives-analytic-Markov of gist.RealCohesion.AxiomTObstruction.

The write-up also gives the second statement of Corollary 3.7 in the
form ¬¬ ∃. That form needs the empty type to be codiscrete, which is
Shulman's Theorem 8.11 and is not derivable from the interface of
gist.RealCohesion.Sharp. With it as a hypothesis the step is immediate.

\begin{code}

 ¬¬-fixed-points-from-sharp-fixed-points
  : (n : ℕ)
  → (♯ (𝟘 {𝓤₀}) → 𝟘 {𝓤₀})
  → Sharp-Cube-Fixed-Point S n
  → (f : Cube n → Cube n) → ¬¬ (∃ x ꞉ Cube n , f x ＝ x)
 ¬¬-fixed-points-from-sharp-fixed-points n e σ f ν =
  e (rec-sharp (λ a → 𝟘-elim (ν a)) (σ f))

\end{code}

The relation to the exact statement of Corollary 3.7. The write-up
states it for the Euclidean unit ball Dⁿ, which is a crisp retract of
the cube: the inclusion Dⁿ → [-1,1]ⁿ has the retraction
y ↦ y / max(1, ‖y‖). The two derivations below make the relation
formal. Every crisp retract K of the cube inherits both forms of the
corollary from the cube. The exact statement is the instance in which
K is the Euclidean ball. When this module was written, that
retraction was still to be formalized. It now is, without square
roots, as y ↦ y / max(1 , ‖y‖²) (gist.RealCohesion.EuclideanBall),
and gist.RealCohesion.Theorems states both forms for the ball in every
dimension.

\begin{code}

crisp-retracts-of-the-cube-have-fixed-points
 : (@♭ n : ℕ) {@♭ 𝓥 : Universe} (@♭ K : 𝓥 ̇ )
   (@♭ e : K → Cube n) (@♭ ρ : Cube n → K)
 → ((k : K) → ρ (e k) ＝ k)
 → Crisp-Cube-Fixed-Point n
 → (@♭ g : K → K) → ∃ k ꞉ K , g k ＝ k
crisp-retracts-of-the-cube-have-fixed-points n K e ρ η φ g =
 ∥∥-functor γ (φ (λ c → e (g (ρ c))))
 where
  γ : (Σ c ꞉ Cube n , e (g (ρ c)) ＝ c) → Σ k ꞉ K , g k ＝ k
  γ (c , p) = ρ c , (g (ρ c)         ＝⟨ (η (g (ρ c))) ⁻¹ ⟩
                     ρ (e (g (ρ c))) ＝⟨ ap ρ p ⟩
                     ρ c             ∎)

module _ (S : Sharp-Modality) where

 open Sharp-Modality S

 retracts-of-the-cube-have-sharp-fixed-points
  : (@♭ n : ℕ) {@♭ 𝓥 : Universe} (@♭ K : 𝓥 ̇ )
    (@♭ e : K → Cube n) (@♭ ρ : Cube n → K)
  → ((k : K) → ρ (e k) ＝ k)
  → Crisp-Cube-Fixed-Point n
  → (g : K → K) → ♯ (∃ k ꞉ K , g k ＝ k)
 retracts-of-the-cube-have-sharp-fixed-points n K e ρ η φ =
  crisp-ind-sharp (λ g → ∃ k ꞉ K , g k ＝ k)
   (crisp-retracts-of-the-cube-have-fixed-points n K e ρ η φ)

\end{code}

For Theorem 4.3, the exact statement could not be written down when
this module was written, because the Euclidean norm was not yet
available. Its relation to Approximate-Cube-Fixed-Point is recorded in
the blueprint addendum, Section 1a: the same proof gives it for the
ball from the retraction above, the decidability of membership of
rational points in the ball, and rational points of the ball
converging with modulus to a given crisp point of it. It is now stated
and proved for the ball in every dimension, with the squared Euclidean
distance, by another route: it is transferred from the cube form
through the retraction, which is nonexpansive
(gist.RealCohesion.EuclideanBall, and
R♭-and-T-give-approximate-fixed-points-on-the-ball-in-every-dimension
in gist.RealCohesion.Theorems).
