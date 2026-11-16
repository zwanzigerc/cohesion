Claude Fable 5.2, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026, for part (c) of gate G27 of the second
addendum to the formalization plan, answering a point of GPT-6 Astra's
review of that gate. Added to the folder by Claude Opus 5.5 on
12 November 2026, after Astra's review released it, with §6 added at
Astra's request: the retraction of §5 gives the sphere as a retract of
the ball in the sense of gist.RealCohesion.EuclideanSphere, whose
statement Lemma-12-3-for-the-ball is the one of step E4 of gate G14.
§1 to §5 are unchanged. On 13 November 2026, in the consolidation
after the final audits, Claude Opus 5.5 added to §6 the forms with a
retraction of the inclusion sphere-to-ball as the conclusion. See the
AI disclosure in gist.RealCohesion.index.

Shulman's Lemma 12.3 for the Euclidean ball, and so for the disc as
he states it, from crisp excluded middle and Axiom C1. Neither Axiom T
nor Axiom R♭ is assumed, the map is not assumed crisp, and the
conclusion is a retraction.

  [1, Lemma 12.3]. If there is a map f : D² → D² with no fixed point,
  then S¹ is a retract of D².

Here Dⁿ is Ball n of gist.RealCohesion.EuclideanBall, the type of
points of ℝⁿ whose squared norm is at most 1, and the sphere consists
of the points of the ball whose squared norm is 1. A retraction onto
the sphere is a self-map of the ball that lands in the sphere and
fixes its points.

The module adds to gist.RealCohesion.BoundaryRetractionFromC1, which
has the lemma for the cube, only what the ball needs.

 * The sphere, and the unit vector (1 , 0 , … , 0) as a point of it
   in dimension n + 1. This uses the ring laws 1 · x = x and
   0 · x = 0 of gist.RealCohesion.RealMultiplication and nothing else
   about the product of reals: no square roots and no inverses. The
   option --lossy-unification, which gist.RealCohesion.EuclideanBall
   also uses, keeps Agda from unfolding the product of reals when it
   compares terms.

 * If ℝ has decidable equality, the ball of dimension n + 1 retracts
   onto its sphere: a point on the sphere stays, and every other
   point goes to the unit vector. Membership in the sphere is one
   equation between reals.

 * A fixed-point-free self-map of the ball gives one of the cube,
   because the ball is a retract of the cube
   (ball-is-a-retract-of-the-cube of gist.RealCohesion.EuclideanBall).

 * Hence the dichotomy, the lemma, and the crisp and sharp
   fixed-point theorems for the ball from crisp excluded middle,
   Axiom C1 and "ℝ is not ♭-discrete" ([1, Corollary 12.5 and Theorem
   12.4] for the disc). Kuhn's lemma is a hypothesis in dimension n
   and is proved in dimension 2, so that the disc is unconditional.

[1] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer Science
    28(6), 2018. https://arxiv.org/abs/1509.07584v3
    Numbering as in version 3 of the arXiv preprint.

\begin{code}

{-# OPTIONS --safe --without-K --cohesion --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import gist.CohesiveApartness.Flat

module gist.RealCohesion.SphereRetractionFromC1
        (@♭ fe : Fun-Ext)
        (@♭ pe : Prop-Ext)
        (@♭ pt : propositional-truncations-exist)
        {@♭ 𝓥 𝓦 : Universe} {@♭ J : 𝓥 ̇ }
        (@♭ R : J → 𝓦 ̇ )
        (@♭ c1 : Axiom-C1 R)
       where

open import Fin.Type
open import NotionsOfDecidability.Decidable
open import Notation.Order
open import Rationals.Type using (ℚ ; 0ℚ)
open import UF.Base
open import UF.DiscreteAndSeparated
open import DedekindReals.Order fe pe pt
open import DedekindReals.Type fe pe pt
open import gist.CohesiveApartness.Sharp
open import gist.RealCohesion.BrouwerStatements fe pe pt
 using (Cube ; crisp-retracts-of-the-cube-have-fixed-points)
open import gist.RealCohesion.EuclideanBall fe pe pt
 using (vector-sum ; squared-norm ; Ball ; ball-to-cube ; cube-to-ball ;
        ball-is-a-retract-of-the-cube ; zero-plus)
open import gist.RealCohesion.KuhnLemma using (Kuhn-Lemma ; kuhn-lemma-2)
open import gist.RealCohesion.RationalPoints fe pe pt using (ιₐ)
open import gist.RealCohesion.RealLattice fe pe pt using (_+_ ; plus-zero)
open import gist.RealCohesion.RealMultiplication fe pe pt
 using (_*_ ; *-left-unit ; *-left-zero ; 0ℝ-is-ιₐ)
open import gist.RealCohesion.RealOrder fe pe pt using (ℝ≤-refl)
import gist.RealCohesion.BoundaryRetractionFromC1
import gist.RealCohesion.EuclideanSphere fe pe pt as ES
open import UF.Retracts using (retract_of_)

open PropositionalTruncation pt

private
 module B = gist.RealCohesion.BoundaryRetractionFromC1 fe pe pt R c1

\end{code}

1. The sphere, and retractions onto it.

\begin{code}

on-the-sphere : {n : ℕ} → Ball n → 𝓤₁ ̇
on-the-sphere k = squared-norm (pr₁ k) ＝ 1ℝ

is-retraction-onto-the-sphere : {n : ℕ} → (Ball n → Ball n) → 𝓤₁ ̇
is-retraction-onto-the-sphere {n} r =
   ((k : Ball n) → on-the-sphere (r k))
 × ((k : Ball n) → on-the-sphere k → r k ＝ k)

Sphere-Retraction : ℕ → 𝓤₁ ̇
Sphere-Retraction n =
 Σ r ꞉ (Ball n → Ball n) , is-retraction-onto-the-sphere r

Fixed-Point-Free-Maps-Of-The-Ball : ℕ → 𝓤₁ ̇
Fixed-Point-Free-Maps-Of-The-Ball n =
 Σ f ꞉ (Ball n → Ball n) , ((k : Ball n) → ¬ (f k ＝ k))

\end{code}

2. The unit vector is on the sphere.

\begin{code}

unit-vector : {n : ℕ} → Fin (succ n) → ℝ
unit-vector 𝟎       = 1ℝ
unit-vector (suc i) = 0ℝ

vector-sum-of-zeros
 : {n : ℕ} (v : Fin n → ℝ) → ((i : Fin n) → v i ＝ ιₐ 0ℚ) → vector-sum v ＝ ιₐ 0ℚ
vector-sum-of-zeros {0}      v h = refl
vector-sum-of-zeros {succ n} v h =
 v 𝟎 + vector-sum (v ∘ suc) ＝⟨ I ⟩
 ιₐ 0ℚ + ιₐ 0ℚ              ＝⟨ zero-plus (ιₐ 0ℚ) ⟩
 ιₐ 0ℚ                      ∎
 where
  I = ap₂ _+_ (h 𝟎) (vector-sum-of-zeros (v ∘ suc) (λ i → h (suc i)))

squared-norm-of-a-unit-vector
 : {n : ℕ} (v : Fin (succ n) → ℝ)
 → v 𝟎 ＝ 1ℝ
 → ((i : Fin n) → v (suc i) ＝ 0ℝ)
 → squared-norm v ＝ 1ℝ
squared-norm-of-a-unit-vector {n} v a b =
 (v 𝟎 * v 𝟎) + vector-sum (λ (i : Fin n) → v (suc i) * v (suc i))
  ＝⟨ ap₂ _+_ I II ⟩
 1ℝ + ιₐ 0ℚ
  ＝⟨ plus-zero 1ℝ ⟩
 1ℝ                                                                ∎
 where
  I : v 𝟎 * v 𝟎 ＝ 1ℝ
  I = ap₂ _*_ a a ∙ *-left-unit 1ℝ

  II : vector-sum (λ (i : Fin n) → v (suc i) * v (suc i)) ＝ ιₐ 0ℚ
  II = vector-sum-of-zeros (λ (i : Fin n) → v (suc i) * v (suc i))
        (λ i → ap₂ _*_ (b i) (b i) ∙ *-left-zero 0ℝ ∙ 0ℝ-is-ιₐ)

unit-vector-has-norm-one : {n : ℕ} → squared-norm (unit-vector {n}) ＝ 1ℝ
unit-vector-has-norm-one {n} =
 squared-norm-of-a-unit-vector (unit-vector {n}) refl (λ i → refl)

unit-point : {n : ℕ} → Ball (succ n)
unit-point {n} =
 unit-vector {n} ,
 transport (_≤ 1ℝ) {1ℝ} {squared-norm (unit-vector {n})}
  (unit-vector-has-norm-one {n} ⁻¹) (ℝ≤-refl 1ℝ)

\end{code}

3. The retraction, if ℝ has decidable equality.

\begin{code}

module _ (δ : is-discrete ℝ) where

 sphere-retraction-from-decidable-equality
  : {n : ℕ} → Sphere-Retraction (succ n)
 sphere-retraction-from-decidable-equality {n} =
  (λ k → ρ k (dec k)) ,
  (λ k → ρ-lands k (dec k)) ,
  (λ k → ρ-fixes k (dec k))
  where
   dec : (k : Ball (succ n)) → is-decidable (on-the-sphere k)
   dec k = δ (squared-norm (pr₁ k)) 1ℝ

   ρ : (k : Ball (succ n)) → is-decidable (on-the-sphere k) → Ball (succ n)
   ρ k (inl _) = k
   ρ k (inr _) = unit-point

   ρ-lands : (k : Ball (succ n)) (d : is-decidable (on-the-sphere k))
           → on-the-sphere (ρ k d)
   ρ-lands k (inl p) = p
   ρ-lands k (inr _) = unit-vector-has-norm-one {n}

   ρ-fixes : (k : Ball (succ n)) (d : is-decidable (on-the-sphere k))
           → on-the-sphere k → ρ k d ＝ k
   ρ-fixes k (inl _) _ = refl
   ρ-fixes k (inr ν) p = 𝟘-elim (ν p)

\end{code}

4. From the ball to the cube.

\begin{code}

fixed-point-free-maps-of-the-ball-give-such-maps-of-the-cube
 : {n : ℕ} → Fixed-Point-Free-Maps-Of-The-Ball n → B.Fixed-Point-Free-Maps n
fixed-point-free-maps-of-the-ball-give-such-maps-of-the-cube {n} (f , φ) = g , ψ
 where
  g : Cube n → Cube n
  g c = ball-to-cube (f (cube-to-ball c))

  ψ : (c : Cube n) → ¬ (g c ＝ c)
  ψ c p = φ (cube-to-ball c)
           (ball-is-a-retract-of-the-cube (f (cube-to-ball c)) ⁻¹
            ∙ ap cube-to-ball p)

\end{code}

5. The theorems.

\begin{code}

module _ (@♭ cem₀ : Crisp-EM 𝓤₀) where

 no-fixed-point-free-maps-of-the-ball-if-ℝ-is-not-♭-discrete
  : ¬ is-♭-discrete ℝ
  → {@♭ n : ℕ} (@♭ kuhn : Kuhn-Lemma n)
  → ¬ Fixed-Point-Free-Maps-Of-The-Ball n
 no-fixed-point-free-maps-of-the-ball-if-ℝ-is-not-♭-discrete ν kuhn e =
  B.no-fixed-point-free-maps-if-ℝ-is-not-♭-discrete cem₀ ν kuhn
   (fixed-point-free-maps-of-the-ball-give-such-maps-of-the-cube e)

 crisp-fixed-points-on-the-ball-if-ℝ-is-not-♭-discrete
  : ¬ is-♭-discrete ℝ
  → {@♭ n : ℕ} (@♭ kuhn : Kuhn-Lemma n)
  → (@♭ f : Ball n → Ball n) → ∃ k ꞉ Ball n , f k ＝ k
 crisp-fixed-points-on-the-ball-if-ℝ-is-not-♭-discrete ν {n} kuhn =
  crisp-retracts-of-the-cube-have-fixed-points n (Ball n)
   ball-to-cube cube-to-ball ball-is-a-retract-of-the-cube
   (B.crisp-fixed-points-if-ℝ-is-not-♭-discrete cem₀ ν kuhn)

 sharp-fixed-points-on-the-ball-if-ℝ-is-not-♭-discrete
  : ¬ is-♭-discrete ℝ
  → {@♭ n : ℕ} (@♭ kuhn : Kuhn-Lemma n)
  → (f : Ball n → Ball n) → ♯ (∃ k ꞉ Ball n , f k ＝ k)
 sharp-fixed-points-on-the-ball-if-ℝ-is-not-♭-discrete ν {n} kuhn =
  crisp-ind-sharp (λ f → ∃ k ꞉ Ball n , f k ＝ k)
   (crisp-fixed-points-on-the-ball-if-ℝ-is-not-♭-discrete ν kuhn)

 crisp-fixed-points-on-the-disc-if-ℝ-is-not-♭-discrete
  : ¬ is-♭-discrete ℝ
  → (@♭ f : Ball 2 → Ball 2) → ∃ k ꞉ Ball 2 , f k ＝ k
 crisp-fixed-points-on-the-disc-if-ℝ-is-not-♭-discrete ν =
  crisp-fixed-points-on-the-ball-if-ℝ-is-not-♭-discrete ν (kuhn-lemma-2 fe)

 sharp-fixed-points-on-the-disc-if-ℝ-is-not-♭-discrete
  : ¬ is-♭-discrete ℝ
  → (f : Ball 2 → Ball 2) → ♯ (∃ k ꞉ Ball 2 , f k ＝ k)
 sharp-fixed-points-on-the-disc-if-ℝ-is-not-♭-discrete ν =
  sharp-fixed-points-on-the-ball-if-ℝ-is-not-♭-discrete ν (kuhn-lemma-2 fe)

 sphere-retraction-if-ℝ-is-♭-discrete
  : is-♭-discrete ℝ → {n : ℕ} → Sphere-Retraction (succ n)
 sphere-retraction-if-ℝ-is-♭-discrete d =
  sphere-retraction-from-decidable-equality
   (B.ℝ-has-decidable-equality-if-♭-discrete cem₀ d)

 module _ (cem₁ : Crisp-EM 𝓤₁) where

  discrete-or-no-fixed-point-free-maps-of-the-ball
   : {@♭ n : ℕ} (@♭ kuhn : Kuhn-Lemma n)
   → is-♭-discrete ℝ ∔ ¬ Fixed-Point-Free-Maps-Of-The-Ball n
  discrete-or-no-fixed-point-free-maps-of-the-ball {n} kuhn =
   γ (B.ℝ-is-♭-discrete-or-not cem₀ cem₁)
   where
    γ : is-♭-discrete ℝ ∔ ¬ is-♭-discrete ℝ
      → is-♭-discrete ℝ ∔ ¬ Fixed-Point-Free-Maps-Of-The-Ball n
    γ (inl d) = inl d
    γ (inr ν) =
     inr (no-fixed-point-free-maps-of-the-ball-if-ℝ-is-not-♭-discrete ν kuhn)

  Lemma-12-3-for-the-ball
   : {@♭ n : ℕ} (@♭ kuhn : Kuhn-Lemma (succ n))
   → Fixed-Point-Free-Maps-Of-The-Ball (succ n)
   → Sphere-Retraction (succ n)
  Lemma-12-3-for-the-ball {n} kuhn e =
   γ (discrete-or-no-fixed-point-free-maps-of-the-ball kuhn)
   where
    γ : is-♭-discrete ℝ ∔ ¬ Fixed-Point-Free-Maps-Of-The-Ball (succ n)
      → Sphere-Retraction (succ n)
    γ (inl d) = sphere-retraction-if-ℝ-is-♭-discrete d
    γ (inr ν) = 𝟘-elim (ν e)

  Lemma-12-3-for-the-disc
   : (f : Ball 2 → Ball 2)
   → ((k : Ball 2) → ¬ (f k ＝ k))
   → Sphere-Retraction 2
  Lemma-12-3-for-the-disc f h =
   Lemma-12-3-for-the-ball (kuhn-lemma-2 fe) (f , h)

\end{code}

6. The retraction as a retract. A retraction r of the ball onto its
sphere gives the sphere of gist.RealCohesion.EuclideanSphere as a
retract of the ball, with the inclusion sphere-to-ball as the section:
the composite fixes every point of the sphere, by the second property
of r. So Lemma 12.3 for the disc from crisp excluded middle and Axiom
C1 has the type Lemma-12-3-for-the-ball 2 of that module, which step
E4 of gate G14 proves from crisp excluded middle and Axiom T.

That type forgets that the section is the inclusion. The retraction r
gives more: a retraction of the inclusion, in the sense of
ES.Retraction-Of-The-Sphere-Inclusion
(sphere-retractions-give-retractions-of-the-inclusion), and
sphere-retractions-give-retracts is that map followed by the one that
forgets that the section is the inclusion. So the lemma also holds
with the conclusion of ES.Literal-Lemma-12-3-for-the-ball, the form of
Shulman's statement (literal-Lemma-12-3-for-the-ball and
literal-Lemma-12-3-for-the-disc), under exactly the hypotheses of the
two forms as a retract: crisp excluded middle for 𝓤₀ as a crisp
hypothesis and for 𝓤₁ as an ordinary one, and, for the ball, a crisp
positive dimension and Kuhn's lemma in that dimension as a crisp
hypothesis. As there, the dimension 0 is not covered.

\begin{code}

sphere-retractions-give-retractions-of-the-inclusion
 : {n : ℕ} → Sphere-Retraction n → ES.Retraction-Of-The-Sphere-Inclusion n
sphere-retractions-give-retractions-of-the-inclusion {n} (r , lands , fixes) =
 (λ k → pr₁ (r k) , lands k) , γ
 where
  γ : (x : ES.Sphere n)
    → (pr₁ (r (ES.sphere-to-ball x)) , lands (ES.sphere-to-ball x)) ＝ x
  γ (v , e) =
   to-subtype-＝ (λ _ → ℝ-is-set) (ap pr₁ (fixes (ES.sphere-to-ball (v , e)) e))

sphere-retractions-give-retracts
 : {n : ℕ} → Sphere-Retraction n → retract (ES.Sphere n) of (Ball n)
sphere-retractions-give-retracts ρ =
 ES.retractions-of-the-inclusion-give-retracts
  (sphere-retractions-give-retractions-of-the-inclusion ρ)

module _ (@♭ cem₀ : Crisp-EM 𝓤₀) (cem₁ : Crisp-EM 𝓤₁) where

 Lemma-12-3-for-the-ball-as-a-retract
  : {@♭ n : ℕ} (@♭ kuhn : Kuhn-Lemma (succ n))
  → ES.Lemma-12-3-for-the-ball (succ n)
 Lemma-12-3-for-the-ball-as-a-retract kuhn f h =
  sphere-retractions-give-retracts
   (Lemma-12-3-for-the-ball cem₀ cem₁ kuhn (f , h))

 Lemma-12-3-for-the-disc-as-a-retract : ES.Lemma-12-3-for-the-ball 2
 Lemma-12-3-for-the-disc-as-a-retract f h =
  sphere-retractions-give-retracts (Lemma-12-3-for-the-disc cem₀ cem₁ f h)

 literal-Lemma-12-3-for-the-ball
  : {@♭ n : ℕ} (@♭ kuhn : Kuhn-Lemma (succ n))
  → ES.Literal-Lemma-12-3-for-the-ball (succ n)
 literal-Lemma-12-3-for-the-ball kuhn f h =
  sphere-retractions-give-retractions-of-the-inclusion
   (Lemma-12-3-for-the-ball cem₀ cem₁ kuhn (f , h))

 literal-Lemma-12-3-for-the-disc : ES.Literal-Lemma-12-3-for-the-ball 2
 literal-Lemma-12-3-for-the-disc f h =
  sphere-retractions-give-retractions-of-the-inclusion
   (Lemma-12-3-for-the-disc cem₀ cem₁ f h)

\end{code}
