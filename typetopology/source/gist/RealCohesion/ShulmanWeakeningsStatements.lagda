Claude Fable 5.2, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. Starter module for the second addendum
to the formalization plan: the statements of the remaining weakened
forms of results of Shulman [1] that had no formalization gate. Only
statements; no proofs, except one reduction at the end.

Updated by Claude Opus 5.5 on 13 November 2026, after the final audits,
in the prose only. This is now the statement module of the second
addendum: gist.RealCohesion.Theorems proves every target defined here,
except three, which are not proved in this library. Two are the forms
of uniform continuity with both points arbitrary,
Target-uniform-continuity-on-the-cube and Target-uniform-continuity:
the first is the optional gate G17 of the addendum, and the second, its
form on boxes, belongs to the same optional proposal. The third is the
cube form of Lemma 12.2, Target-12-2-cube, which was not commissioned
(gate G22); the reduction at the end does not prove it, since it takes
a further fact of real analysis as a hypothesis.

Statements of [1] with strictly fewer of the axioms that [1] lists
for them:

  * The exact intermediate value theorem for crisp functions
    (Corollary 3.5 of the write-up; [1, Theorem 11.2] without Axiom T).

  * [1, Corollary 11.6] without Axiom T, in its own words, and in n
    variables (Theorem 3.3 of the write-up).

  * [1, Theorem 11.5] from Axiom R♭ alone, without Axiom T (12 November
    2026; audited on paper by GPT-6 Astra the same day).

  * The n-variable form of [1, Theorem 11.5] from Axiom R♭ alone, for
    every crisp n (GPT-6 Astra, 12 November 2026; audited on paper on
    Astra's side and by Fable). With rational detection it gives two of
    the three parts of Theorem 3.3 of the write-up without excluded
    middle.

Lemmas for these, and statements that are not weakenings in that
sense:

  * Strong extensionality of every function ℝ → ℝ, from Axiom R♭.

  * Rational detection (Corollary 7.6 of the write-up, due to GPT-6
    Astra), in one and in n variables, from Axiom R♭.

  * Continuity of crisp functions from crisp excluded middle and Axiom
    R♭: uniform continuity on the cube and on boxes (not proved in this
    library; see above), the n-variable form of [1, Theorem 11.5]
    (Remark 3.4 of the write-up), [1, Theorem 11.5] itself, and the
    continuity hypothesis Crisp-Real-Continuity of
    gist.RealCohesion.CrispRealAnalysis.
    Measured by the axioms that [1] lists for Theorem 11.5, which do
    not include excluded middle, this exchanges Axiom T for crisp
    excluded middle.

  * No retraction of the cube onto its boundary ([1, Lemma 12.2] in
    cube form and in every dimension; not proved in this library, see
    above). This exchanges univalence for crisp excluded middle.

  * The approximate Brouwer fixed-point theorem [1, Theorem 12.6] in
    the form for the square with the supremum norm, from univalence
    and Axiom R♭, which are the hypotheses of [1]. This is not a
    weakening; it is in the plan at Colin's request (12 November
    2026). The route proposed in the addendum was new and had not been
    audited when this was written; it has since been audited and
    formalized, for the square (gist.RealCohesion.ApproximateBrouwerSquare)
    and for the disc (gist.RealCohesion.ApproximateBrouwerDisc). Also
    its form in every dimension from crisp excluded middle and Axiom
    R♭, which exchanges univalence for crisp excluded middle.

The inequality |x - a| < δ is written as two strict inequalities, so
that no absolute value is needed, and the supremum norm is used on
ℝⁿ, as in gist.RealCohesion.BrouwerStatements.

[1] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer Science
    28(6), 2018. https://arxiv.org/abs/1509.07584v3

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Univalence

module gist.RealCohesion.ShulmanWeakeningsStatements
        (@♭ fe : Fun-Ext)
        (@♭ pe : Prop-Ext)
        (@♭ pt : propositional-truncations-exist)
       where

open import Fin.Type
open import Notation.Order
open import Rationals.Type
open import Rationals.Order
open import Rationals.Negation renaming (_-_ to _-ℚ_ ; -_ to -ℚ_)
open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import DedekindReals.Addition fe pe pt
             renaming (_+_ to _+ℝ_ ; -_ to -ℝ_ ; _-_ to _-ℝ_)
open import gist.CohesiveApartness.Flat
open import gist.RealCohesion.Sharp
open import gist.RealCohesion.CrispRealAnalysis fe pe pt
             using (Crisp-Real-Continuity)
open import gist.RealCohesion.BrouwerStatements fe pe pt
             using (ℝ^ ; in-cube ; Cube ; rational-point ; Kuhn-Lemma
                  ; Sharp-Cube-Fixed-Point)

open PropositionalTruncation pt

\end{code}

Axiom R♭, and notation.

\begin{code}

R♭ : 𝓤ω
R♭ = Singly-Generated-Punctual-Cohesion ℝ 0ℝ

ι : ℚ → ℝ
ι = embedding-ℚ-to-ℝ

_is-strictly-within_of_ : ℝ → ℚ → ℝ → 𝓤₀ ̇
x is-strictly-within δ of a = (x < a +ℝ ι δ) × (a < x +ℝ ι δ)

_is-coordinatewise-within_of_ : {n : ℕ} → ℝ^ n → ℚ → ℝ^ n → 𝓤₀ ̇
_is-coordinatewise-within_of_ {n} x δ a =
 (i : Fin n) → x i is-strictly-within δ of a i

\end{code}

Strong extensionality and rational detection. Neither the function
nor the points are crisp.

\begin{code}

Strongly-Extensional : (ℝ → ℝ) → 𝓤₁ ̇
Strongly-Extensional f = (u v : ℝ) → f u ♯ f v → u ♯ v

Rational-Detection : 𝓤₁ ̇
Rational-Detection =
 (h : ℝ → ℝ) → (∃ x ꞉ ℝ , 0ℝ < h x) → ∃ q ꞉ ℚ , 0ℝ < h (ι q)

Rational-Detection-In-Dimension : ℕ → 𝓤₁ ̇
Rational-Detection-In-Dimension n =
   (h : ℝ^ n → ℝ)
 → (∃ x ꞉ ℝ^ n , 0ℝ < h x)
 → ∃ q ꞉ (Fin n → ℚ) , 0ℝ < h (rational-point q)

\end{code}

The exact intermediate value theorem for crisp functions and crisp
values. The points a and b of the hypothesis are not crisp, as in
[1, Theorem 11.2].

\begin{code}

Crisp-Exact-IVT : 𝓤₁ ̇
Crisp-Exact-IVT =
   (@♭ f : ℝ → ℝ) (@♭ c : ℝ)
 → (∃ a ꞉ ℝ , f a < c)
 → (∃ b ꞉ ℝ , c < f b)
 → ∃ x ꞉ ℝ , f x ＝ c

\end{code}

Continuity. The first notion is that of [1, Theorem 11.5]: the
function and the point are crisp, and the nearby point x is
arbitrary. The second is its n-variable form.

\begin{code}

is-ε-δ-continuous-at : (ℝ → ℝ) → ℝ → 𝓤₁ ̇
is-ε-δ-continuous-at f a =
   (ε : ℚ)
 → 0ℚ < ε
 → ∃ δ ꞉ ℚ , (0ℚ < δ)
           × ((x : ℝ) → x is-strictly-within δ of a
                      → f x is-strictly-within ε of f a)

Shulman-11-5 : 𝓤₁ ̇
Shulman-11-5 = (@♭ f : ℝ → ℝ) (@♭ a : ℝ) → is-ε-δ-continuous-at f a

is-continuous-at : {n : ℕ} → (ℝ^ n → ℝ) → ℝ^ n → 𝓤₁ ̇
is-continuous-at {n} F p =
   (ε : ℚ)
 → 0ℚ < ε
 → ∃ δ ꞉ ℚ , (0ℚ < δ)
           × ((y : ℝ^ n) → y is-coordinatewise-within δ of p
                         → F y is-strictly-within ε of F p)

Remark-3-4 : (@♭ n : ℕ) → 𝓤₁ ̇
Remark-3-4 n = (@♭ F : ℝ^ n → ℝ) (@♭ p : ℝ^ n) → is-continuous-at F p

\end{code}

Uniform continuity of crisp functions, on the cube [-1,1]ⁿ and on
boxes [-M,M]ⁿ. Both points are arbitrary. The form for the cube was
the working lemma of the addendum: applied to x ↦ F (p + x) it gives
Remark-3-4 and Shulman-11-5. These two statements are not proved in
this library. Remark-3-4 and Shulman-11-5 are proved from Axiom R♭
alone by another route (gates G23 and G24), and the uniform
continuity that Theorem 3.3 needs, of a crisp continuous map at crisp
rational points, is the different statement proved in
gist.RealCohesion.CrispUniformContinuityOnBoxes (gate G21).

\begin{code}

Uniform-Continuity-On-The-Cube : (@♭ n : ℕ) → 𝓤₁ ̇
Uniform-Continuity-On-The-Cube n =
   (@♭ F : ℝ^ n → ℝ) (ε : ℚ)
 → 0ℚ < ε
 → ∃ δ ꞉ ℚ , (0ℚ < δ)
           × ((x y : ℝ^ n) → in-cube x
                           → in-cube y
                           → y is-coordinatewise-within δ of x
                           → F y is-strictly-within ε of F x)

in-box : {n : ℕ} → ℚ → ℝ^ n → 𝓤₀ ̇
in-box {n} M x = (i : Fin n) → (ι (-ℚ M) ≤ x i) × (x i ≤ ι M)

Uniform-Continuity-On-Boxes : (@♭ n : ℕ) → 𝓤₁ ̇
Uniform-Continuity-On-Boxes n =
   (@♭ F : ℝ^ n → ℝ) (M ε : ℚ)
 → 0ℚ < ε
 → ∃ δ ꞉ ℚ , (0ℚ < δ)
           × ((x y : ℝ^ n) → in-box M x
                           → in-box M y
                           → y is-coordinatewise-within δ of x
                           → F y is-strictly-within ε of F x)

\end{code}

Theorem 3.3 of the write-up. The canonical map from ♭ (ℝⁿ → ℝ) to
♭ ℝⁿ → ♭ ℝ is injective, and its image consists of the functions that
are ε-δ continuous in the discrete sense.

\begin{code}

♭-apply : {@♭ n : ℕ} → ♭ (ℝ^ n → ℝ) → ♭ (ℝ^ n) → ♭ ℝ
♭-apply (F ^♭) (x ^♭) = (F x) ^♭

is-♭-continuous : {@♭ n : ℕ} → (♭ (ℝ^ n) → ♭ ℝ) → 𝓤₁ ̇
is-♭-continuous {n} h =
   (x : ♭ (ℝ^ n)) (ε : ℚ)
 → 0ℚ < ε
 → ∃ δ ꞉ ℚ , (0ℚ < δ)
           × ((y : ♭ (ℝ^ n))
                 → ♭-counit y is-coordinatewise-within δ of ♭-counit x
                 → ♭-counit (h y) is-strictly-within ε of ♭-counit (h x))

♭-apply-is-injective : (@♭ n : ℕ) → 𝓤₁ ̇
♭-apply-is-injective n =
 (F G : ♭ (ℝ^ n → ℝ)) → ♭-apply F ＝ ♭-apply G → F ＝ G

♭-apply-has-continuous-values : (@♭ n : ℕ) → 𝓤₁ ̇
♭-apply-has-continuous-values n =
 (F : ♭ (ℝ^ n → ℝ)) → is-♭-continuous (♭-apply F)

continuous-maps-are-values-of-♭-apply : (@♭ n : ℕ) → 𝓤₁ ̇
continuous-maps-are-values-of-♭-apply n =
   (h : ♭ (ℝ^ n) → ♭ ℝ)
 → is-♭-continuous h
 → ∃ F ꞉ ♭ (ℝ^ n → ℝ) , ♭-apply F ＝ h

Theorem-3-3 : (@♭ n : ℕ) → 𝓤₁ ̇
Theorem-3-3 n = ♭-apply-is-injective n
              × ♭-apply-has-continuous-values n
              × continuous-maps-are-values-of-♭-apply n

\end{code}

[1, Corollary 11.6] in its own words, for functions of one variable:
the canonical function ♭ (ℝ → ℝ) → (♭ ℝ → ♭ ℝ) is an injection, and
its image consists of the ε-δ continuous functions.

\begin{code}

♭-apply₁ : ♭ (ℝ → ℝ) → ♭ ℝ → ♭ ℝ
♭-apply₁ (f ^♭) (x ^♭) = (f x) ^♭

is-♭-ε-δ-continuous : (♭ ℝ → ♭ ℝ) → 𝓤₁ ̇
is-♭-ε-δ-continuous h =
   (x : ♭ ℝ) (ε : ℚ)
 → 0ℚ < ε
 → ∃ δ ꞉ ℚ , (0ℚ < δ)
           × ((y : ♭ ℝ)
                 → ♭-counit y is-strictly-within δ of ♭-counit x
                 → ♭-counit (h y) is-strictly-within ε of ♭-counit (h x))

Shulman-11-6 : 𝓤₁ ̇
Shulman-11-6 =
   ((f g : ♭ (ℝ → ℝ)) → ♭-apply₁ f ＝ ♭-apply₁ g → f ＝ g)
 × ((h : ♭ ℝ → ♭ ℝ) → (∃ f ꞉ ♭ (ℝ → ℝ) , ♭-apply₁ f ＝ h)
                    ↔ is-♭-ε-δ-continuous h)

\end{code}

No retraction of the cube [-1,1]ⁿ onto its boundary. The retraction
is not assumed crisp.

\begin{code}

on-boundary : {n : ℕ} → ℝ^ n → 𝓤₁ ̇
on-boundary {n} x = ∃ i ꞉ Fin n , (x i ＝ ι -1ℚ) ∔ (x i ＝ 1ℝ)

is-retraction-onto-the-boundary : {n : ℕ} → (Cube n → Cube n) → 𝓤₁ ̇
is-retraction-onto-the-boundary {n} r =
   ((x : Cube n) → on-boundary (pr₁ (r x)))
 × ((x : Cube n) → on-boundary (pr₁ x) → r x ＝ x)

No-Retraction-Onto-The-Boundary : ℕ → 𝓤₁ ̇
No-Retraction-Onto-The-Boundary n =
 ¬ (Σ r ꞉ (Cube n → Cube n) , is-retraction-onto-the-boundary r)

\end{code}

The targets. Crisp excluded middle is a crisp hypothesis, as in
gist.RealCohesion.BrouwerStatements. The universe level 𝓤₀ is the one
that the proofs sketched in the addendum need; if a proof needs
Crisp-EM 𝓤₁, the statement must say so. gist.RealCohesion.Theorems
proves every target of the next block except two:
Target-uniform-continuity-on-the-cube and Target-uniform-continuity
are not proved in this library (optional gate G17; see above).

\begin{code}

Target-strong-extensionality : 𝓤ω
Target-strong-extensionality = R♭ → (f : ℝ → ℝ) → Strongly-Extensional f

Target-7-6 : 𝓤ω
Target-7-6 = R♭ → Rational-Detection

Target-7-6-in-dimension : ℕ → 𝓤ω
Target-7-6-in-dimension n = R♭ → Rational-Detection-In-Dimension n

Target-3-5 : 𝓤ω
Target-3-5 = (@♭ cem : Crisp-EM 𝓤₀) → R♭ → Crisp-Exact-IVT

Target-uniform-continuity-on-the-cube : (@♭ n : ℕ) → 𝓤ω
Target-uniform-continuity-on-the-cube n = (@♭ cem : Crisp-EM 𝓤₀)
                                        → R♭
                                        → Uniform-Continuity-On-The-Cube n

Target-uniform-continuity : (@♭ n : ℕ) → 𝓤ω
Target-uniform-continuity n = (@♭ cem : Crisp-EM 𝓤₀)
                            → R♭
                            → Uniform-Continuity-On-Boxes n

Target-3-4 : (@♭ n : ℕ) → 𝓤ω
Target-3-4 n = (@♭ cem : Crisp-EM 𝓤₀) → R♭ → Remark-3-4 n

Target-11-5 : 𝓤ω
Target-11-5 = (@♭ cem : Crisp-EM 𝓤₀) → R♭ → Shulman-11-5

Target-crisp-real-continuity : 𝓤ω
Target-crisp-real-continuity = (@♭ cem : Crisp-EM 𝓤₀)
                             → R♭
                             → Crisp-Real-Continuity

Target-3-3 : (@♭ n : ℕ) → 𝓤ω
Target-3-3 n = (@♭ cem : Crisp-EM 𝓤₀) → R♭ → Theorem-3-3 n

Target-11-6 : 𝓤ω
Target-11-6 = (@♭ cem : Crisp-EM 𝓤₀) → R♭ → Shulman-11-6

\end{code}

The new claim: [1, Theorem 11.5] from Axiom R♭ alone.

\begin{code}

Target-11-5-from-R♭-alone : 𝓤ω
Target-11-5-from-R♭-alone = R♭ → Shulman-11-5

\end{code}

Its n-variable form, also from Axiom R♭ alone (GPT-6 Astra). This is
Remark 3.4 of the write-up without crisp excluded middle, so
Target-3-4 follows from it by forgetting a hypothesis. With rational
detection in n variables it gives the first two parts of Theorem 3.3,
again without crisp excluded middle; the third part, that every
continuous map is a value, keeps that hypothesis.

\begin{code}

Target-3-4-from-R♭-alone : (@♭ n : ℕ) → 𝓤ω
Target-3-4-from-R♭-alone n = R♭ → Remark-3-4 n

Target-3-3-embedding-and-continuity-from-R♭-alone : (@♭ n : ℕ) → 𝓤ω
Target-3-3-embedding-and-continuity-from-R♭-alone n =
 R♭ → ♭-apply-is-injective n × ♭-apply-has-continuous-values n

Target-3-4-follows : (@♭ n : ℕ)
                   → Target-3-4-from-R♭-alone n
                   → Target-3-4 n
Target-3-4-follows n t cem r♭ = t r♭

\end{code}

The approximate Brouwer fixed-point theorem of [1, Theorem 12.6]: a
crisp self-map of the disc has, for every ε > 0, a point that it moves
by less than ε. Here it is stated for the cube [-1,1]ⁿ with the
supremum norm. For n = 2, from univalence and Axiom R♭, this is the
cube form of [1, Theorem 12.6] with the hypotheses of [1]; the
statement for the round disc follows from it by the retraction of the
plane onto the disc. For every n, from crisp excluded middle and Axiom
R♭, it is a consequence of the crisp fixed point on the cube.

\begin{code}

Approximate-Fixed-Points-Of-Crisp-Maps : (@♭ n : ℕ) → 𝓤₁ ̇
Approximate-Fixed-Points-Of-Crisp-Maps n =
   (@♭ f : Cube n → Cube n) (ε : ℚ)
 → 0ℚ < ε
 → ∃ x ꞉ Cube n , pr₁ (f x) is-coordinatewise-within ε of pr₁ x

Target-12-6-cube : 𝓤ω
Target-12-6-cube = Univalence
                 → R♭
                 → Approximate-Fixed-Points-Of-Crisp-Maps 2

Target-12-6-cube-from-LEM : (@♭ n : ℕ) → 𝓤ω
Target-12-6-cube-from-LEM n = (@♭ cem : Crisp-EM 𝓤₀)
                            → R♭
                            → Approximate-Fixed-Points-Of-Crisp-Maps n

\end{code}

The cube form of [1, Lemma 12.2]. That the empty type is codiscrete is
[1, Theorem 8.11]; the interface for ♯ does not provide it, so it is a
hypothesis here. This target is not proved in this library: it is
gate G22 of the addendum, which was not commissioned. The reduction
below does not inhabit it, since it also takes a fact of real
analysis as a hypothesis.

\begin{code}

module _ (S : Sharp-Modality) where

 open Sharp-Modality S

 Target-12-2-cube : (@♭ n : ℕ) → 𝓤ω
 Target-12-2-cube n = (@♭ cem : Crisp-EM 𝓤₀)
                    → R♭
                    → (@♭ kuhn : Kuhn-Lemma n)
                    → (♯ (𝟘 {𝓤₀}) → 𝟘 {𝓤₀})
                    → No-Retraction-Onto-The-Boundary n

\end{code}

The cube form of [1, Lemma 12.2] follows from the ♯ form of the
fixed-point theorem and one fact of real analysis: for a retraction r
onto the boundary, the map x ↦ - r x has no fixed point. With that
fact as a hypothesis the reduction is a few lines, and it is checked
here.

\begin{code}

 no-retraction-from-sharp-fixed-points
  : (n : ℕ)
  → (♯ (𝟘 {𝓤₀}) → 𝟘 {𝓤₀})
  → Sharp-Cube-Fixed-Point S n
  → ((r : Cube n → Cube n)
        → is-retraction-onto-the-boundary r
        → Σ f ꞉ (Cube n → Cube n) , ¬ (∃ x ꞉ Cube n , f x ＝ x))
  → No-Retraction-Onto-The-Boundary n
 no-retraction-from-sharp-fixed-points n e φ α (r , ρ) =
  e (rec-sharp (λ s → unit-sharp (pr₂ (α r ρ) s)) (φ (pr₁ (α r ρ))))

\end{code}
