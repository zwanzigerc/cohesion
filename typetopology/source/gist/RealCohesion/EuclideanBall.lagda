Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026; prose corrected 13 November 2026, after
the final audits. See the AI disclosure in gist.RealCohesion.index.

The Euclidean unit ball as a retract of the cube (gate G14, step E2).

The ball of the write-up's Corollary 3.7, which for n = 2 is the disc
of Shulman's Theorem 12.4 and Corollary 12.5 [1], is
Dⁿ = {x : ℝⁿ | |x| ≤ 1} for the Euclidean norm. We write it as
{x : ℝⁿ | ‖x‖² ≤ 1}, with ‖x‖² = Σᵢ xᵢ², which is the same set because
|x| = √‖x‖² and both are nonnegative; square roots are not needed here.

 * Every point of Dⁿ lies in the cube [-1,1]ⁿ: if xᵢ > 1 or xᵢ < -1,
   then xᵢ² > 1, but xᵢ² ≤ ‖x‖² ≤ 1.

 * ρ x = x / max(1 , ‖x‖²) maps ℝⁿ into Dⁿ and fixes the points of Dⁿ.
   This is the square-root-free retraction of Fable's addendum
   (ADDENDUM-2, G14), which Codex audited on 12 November 2026; it
   uses the reciprocal of gist.RealCohesion.RealReciprocal.

So Dⁿ is a retract of the cube, by crisp maps, and
gist.RealCohesion.Theorems derives Corollary 3.7 for Dⁿ from the
fixed points on the cube, with crisp-retracts-of-the-cube-have-fixed-points
of gist.RealCohesion.BrouwerStatements. The inequalities between reals
come from inequalities between rationals, by continuity or by the cuts
of products; no case distinction on real numbers is used.

[1] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer
    Science 28(6), 856–941, 2018. https://arxiv.org/abs/1509.07584v3
    Numbering as in version 3 of the arXiv preprint.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.EuclideanBall
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import Fin.Type
open import Notation.CanonicalMap
open import Notation.Order
open import UF.Base
open import UF.Subsingletons-FunExt
open import Rationals.Type
open import Rationals.Order
open import Rationals.Multiplication renaming (_*_ to _ℚ*_)
open import Rationals.Negation renaming (_-_ to _ℚ-_ ; -_ to ℚ-_)
open import Rationals.Addition renaming (_+_ to _ℚ+_)
open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import gist.RealCohesion.ContinuityForms fe pe pt
 using (Coordinatewise-Strictly-Continuous)
open import gist.RealCohesion.RationalPoints fe pe pt
 using (ιₐ ; ιₐ-is-ι ; ιₐ-lower⁻¹ ; ιₐ-upper⁻¹ ; ιₐ-upper)
open import gist.RealCohesion.RationalProducts
 using (square-above-one ; square-below-minus-one ; minus-one-is-negative)
open import gist.RealCohesion.RealLattice fe pe pt
 using (_+_ ; -_ ; sum-≤ ; plus-zero ; ℚ<ℝ-is-prop ; <-≤-trans-ℚ ; ιₐ-sum ;
        ιₐ-≤-ιₐ ; ℝ<ℚ-is-prop ; translate-below ; translate-strict ;
         ≤-<-trans-ℚ ;
        <-gives-≤-ιₐ)
open import gist.RealCohesion.RealLattice fe pe pt using (zero-plus) public
open import gist.RealCohesion.RealAlgebra fe pe pt
 using (+-comm ; +-assoc ; interchange ; square-of-scaled) public
open import gist.RealCohesion.RealBalls fe pe pt
 using (halfₐ ; halfₐ-is-positive ; halfₐ-is-less)
open import gist.RealCohesion.RealOrder fe pe pt using (ℝ≤-refl)
open import gist.RealCohesion.RationalBoxExtension fe pe pt
 using (constant-is-continuous ; not-below-gives-≤ ; projection-is-continuous ;
        ≤-at-a-continuity-point)
open import gist.RealCohesion.RealMultiplication fe pe pt
 using
  (_*_ ; *-comm ; *-assoc ; *-right-unit ; *-left-zero ; *-right-distributive ;
   sum-is-continuous ; products-above ; products-of-negatives-above ;
   squares-are-nonneg ; 0ℝ-is-ιₐ ; 1ℝ-is-ιₐ ; ιₐ-* ; ιₐ-neg ;
    product-is-continuous ;
   products-below)
open import gist.RealCohesion.RealReciprocal fe pe pt
 using (reciprocal-ℝ ; reciprocal-ℝ-of-at-most-one ; reciprocal-ℝ-bound ;
         reciprocal-ℝ-agrees ;
        reciprocal-ℝ-is-continuous)
open import gist.RealCohesion.RationalProducts using (reciprocal)
open import gist.RealCohesion.RationalVectors
 using (vsum ; norm² ; retraction-ℚ ; retraction-ℚ-is-nonexpansive ; budget)

open PropositionalTruncation pt

\end{code}

Squares are at least ιₐ 0. (The commutativity of addition and the
square of a product, which this module used to prove, are now in
gist.RealCohesion.RealAlgebra, and 0 + x = x is RealLattice's
zero-plus; the module re-exports them.)

\begin{code}

squares-are-nonneg' : (x : ℝ) → ιₐ 0ℚ ≤ x * x
squares-are-nonneg' x =
 transport (_≤ x * x) {0ℝ} {ιₐ 0ℚ} 0ℝ-is-ιₐ (squares-are-nonneg x)

\end{code}

Finite sums and the squared norm.

\begin{code}

vector-sum : {n : ℕ} → (Fin n → ℝ) → ℝ
vector-sum {0}      v = ιₐ 0ℚ
vector-sum {succ n} v = v 𝟎 + vector-sum (v ∘ suc)

squared-norm : {n : ℕ} → (Fin n → ℝ) → ℝ
squared-norm x = vector-sum (λ i → x i * x i)

vector-sum-is-nonneg : {n : ℕ} (v : Fin n → ℝ)
                     → ((i : Fin n) → ιₐ 0ℚ ≤ v i) → ιₐ 0ℚ ≤ vector-sum v
vector-sum-is-nonneg {0}      v h = ℝ≤-refl (ιₐ 0ℚ)
vector-sum-is-nonneg {succ n} v h =
 transport (_≤ vector-sum {succ n} v) {ιₐ 0ℚ + ιₐ 0ℚ} {ιₐ 0ℚ}
  (plus-zero (ιₐ 0ℚ))
  (sum-≤ (ιₐ 0ℚ) (v 𝟎) (ιₐ 0ℚ) (vector-sum (v ∘ suc)) (h 𝟎)
    (vector-sum-is-nonneg (v ∘ suc) (h ∘ suc)))

term-≤-vector-sum : {n : ℕ} (v : Fin n → ℝ)
                  → ((i : Fin n) → ιₐ 0ℚ ≤ v i) → (i : Fin n)
                  → v i ≤ vector-sum v
term-≤-vector-sum {0}      v h i = 𝟘-elim i
term-≤-vector-sum {succ n} v h 𝟎 =
 transport (_≤ vector-sum {succ n} v) {v 𝟎 + ιₐ 0ℚ} {v 𝟎} (plus-zero (v 𝟎))
  (sum-≤ (v 𝟎) (v 𝟎) (ιₐ 0ℚ) (vector-sum (v ∘ suc)) (ℝ≤-refl (v 𝟎))
    (vector-sum-is-nonneg (v ∘ suc) (h ∘ suc)))
term-≤-vector-sum {succ n} v h (suc i) =
 ℝ≤-trans (v (suc i)) (vector-sum (v ∘ suc)) (vector-sum {succ n} v)
  (term-≤-vector-sum (v ∘ suc) (h ∘ suc) i)
  (transport (_≤ vector-sum {succ n} v) {ιₐ 0ℚ + vector-sum (v ∘ suc)}
    {vector-sum (v ∘ suc)}
    (zero-plus (vector-sum (v ∘ suc)))
    (sum-≤ (ιₐ 0ℚ) (v 𝟎) (vector-sum (v ∘ suc)) (vector-sum (v ∘ suc)) (h 𝟎)
      (ℝ≤-refl (vector-sum (v ∘ suc)))))

vector-sum-times : {n : ℕ} (v : Fin n → ℝ) (c : ℝ)
                 → vector-sum (λ i → v i * c) ＝ vector-sum v * c
vector-sum-times {0}      v c =
 0ℝ-is-ιₐ ⁻¹ ∙ *-left-zero c ⁻¹ ∙ ap (_* c) 0ℝ-is-ιₐ
vector-sum-times {succ n} v c =
 ap (v 𝟎 * c +_) (vector-sum-times (v ∘ suc) c)
 ∙ *-right-distributive (v 𝟎) (vector-sum (v ∘ suc)) c ⁻¹

vector-sum-plus : {n : ℕ} (v w : Fin n → ℝ)
                → vector-sum (λ i → v i + w i) ＝ vector-sum v + vector-sum w
vector-sum-plus {0}      v w = plus-zero (ιₐ 0ℚ) ⁻¹
vector-sum-plus {succ n} v w =
 ap ((v 𝟎 + w 𝟎) +_) (vector-sum-plus (v ∘ suc) (w ∘ suc))
 ∙ interchange (v 𝟎) (w 𝟎) (vector-sum (v ∘ suc)) (vector-sum (w ∘ suc))

vector-sum-is-continuous
 : {m n : ℕ} (A : Fin n → (Fin m → ℝ) → ℝ) (x : Fin m → ℝ)
 → ((i : Fin n) → Coordinatewise-Strictly-Continuous (A i) x)
 → Coordinatewise-Strictly-Continuous (λ y → vector-sum (λ i → A i y)) x
vector-sum-is-continuous {m} {0}      A x c = constant-is-continuous (ιₐ 0ℚ) x
vector-sum-is-continuous {m} {succ n} A x c =
 sum-is-continuous (A 𝟎) (λ y → vector-sum (λ i → A (suc i) y)) x (c 𝟎)
  (vector-sum-is-continuous (λ i → A (suc i)) x (λ i → c (suc i)))

\end{code}

The ball lies in the cube.

\begin{code}

coordinates-of-the-ball
 : {n : ℕ} (x : Fin n → ℝ) → squared-norm x ≤ 1ℝ
 → (i : Fin n) → (embedding-ℚ-to-ℝ -1ℚ ≤ x i) × (x i ≤ 1ℝ)
coordinates-of-the-ball x h i = lower , upper
 where
  square-≤-one : x i * x i ≤ 1ℝ
  square-≤-one = ℝ≤-trans (x i * x i) (squared-norm x) 1ℝ
                  (term-≤-vector-sum (λ j → x j * x j)
                    (λ j → squares-are-nonneg' (x j)) i) h

  square-below-one : (q : ℚ) → (q ℚ* q) < x i * x i → q ℚ* q < 1ℚ
  square-below-one q k =
   ιₐ-lower⁻¹ (q ℚ* q) 1ℚ
    (transport ((q ℚ* q) <_) {1ℝ} {ιₐ 1ℚ} 1ℝ-is-ιₐ
      (<-≤-trans-ℚ (x i * x i) 1ℝ (q ℚ* q) k square-≤-one))

  upper : x i ≤ 1ℝ
  upper = not-below-gives-≤ (x i) 1ℝ ν
   where
    ν : ¬ (1ℝ < x i)
    ν k = ∥∥-rec 𝟘-is-prop γ k
     where
      γ : (Σ q ꞉ ℚ , (1ℝ < q) × (q < x i)) → 𝟘
      γ (q , a , b) = ℚ<-irrefl (q ℚ* q)
       (ℚ<-trans (q ℚ* q) 1ℚ (q ℚ* q) I (square-above-one q 1<q))
       where
        1<q : 1ℚ < q
        1<q = ιₐ-upper⁻¹ 1ℚ q (transport (_< q) {1ℝ} {ιₐ 1ℚ} 1ℝ-is-ιₐ a)

        q-is-positive : 0ℚ < q
        q-is-positive = ℚ<-trans 0ℚ 1ℚ q 0<1 1<q

        I : q ℚ* q < 1ℚ
        I = square-below-one q
             (products-above q q (x i) (x i) q-is-positive q-is-positive b b)

  lower : embedding-ℚ-to-ℝ -1ℚ ≤ x i
  lower = not-below-gives-≤ (embedding-ℚ-to-ℝ -1ℚ) (x i) ν
   where
    ν : ¬ (x i < embedding-ℚ-to-ℝ -1ℚ)
    ν k = ∥∥-rec 𝟘-is-prop γ k
     where
      γ : (Σ q ꞉ ℚ , (x i < q) × (q < embedding-ℚ-to-ℝ -1ℚ)) → 𝟘
      γ (q , a , b) =
       ℚ<-irrefl (q ℚ* q)
        (ℚ<-trans (q ℚ* q) 1ℚ (q ℚ* q) I (square-below-minus-one q q<-1))
       where
        q<-1 : q < -1ℚ
        q<-1 = ιₐ-lower⁻¹ q -1ℚ
                (transport (q <_) {embedding-ℚ-to-ℝ -1ℚ} {ιₐ -1ℚ}
                  (ιₐ-is-ι -1ℚ ⁻¹) b)

        q-is-negative : q < 0ℚ
        q-is-negative = ℚ<-trans q -1ℚ 0ℚ q<-1 minus-one-is-negative

        I : q ℚ* q < 1ℚ
        I = square-below-one q
             (products-of-negatives-above q q (x i) (x i) q-is-negative
               q-is-negative a a)

\end{code}

The retraction ρ x = x / max(1 , ‖x‖²). With m the reciprocal of
max(1 , ‖x‖²), we have ‖ρ x‖² = ‖x‖² m² ≤ 1, and m = 1 if ‖x‖² ≤ 1.

\begin{code}

retraction : {n : ℕ} → (Fin n → ℝ) → (Fin n → ℝ)
retraction x i = x i * reciprocal-ℝ (squared-norm x)

squared-norm-of-retraction
 : {n : ℕ} (x : Fin n → ℝ)
 → squared-norm (retraction x)
   ＝ squared-norm x
   * (reciprocal-ℝ (squared-norm x) * reciprocal-ℝ (squared-norm x))
squared-norm-of-retraction x =
 ap vector-sum (dfunext fe (λ i → square-of-scaled (x i) m))
 ∙ vector-sum-times (λ i → x i * x i) (m * m)
 where
  m : ℝ
  m = reciprocal-ℝ (squared-norm x)

retraction-lands-in-the-ball : {n : ℕ} (x : Fin n → ℝ)
                             → squared-norm (retraction x) ≤ 1ℝ
retraction-lands-in-the-ball x =
 transport (_≤ 1ℝ)
  {squared-norm x
   * (reciprocal-ℝ (squared-norm x) * reciprocal-ℝ (squared-norm x))}
  {squared-norm (retraction x)}
  (squared-norm-of-retraction x ⁻¹) (reciprocal-ℝ-bound (squared-norm x))

retraction-fixes-the-ball : {n : ℕ} (x : Fin n → ℝ) → squared-norm x ≤ 1ℝ
                          → retraction x ＝ x
retraction-fixes-the-ball x h =
 dfunext fe (λ i → ap (x i *_) (reciprocal-ℝ-of-at-most-one (squared-norm x) h)
                  ∙ *-right-unit (x i))

\end{code}

The ball, the cube, and the retraction between them. The cube is
written as in gist.RealCohesion.BrouwerStatements, whose Cube n is the
same type; this module has no --cohesion, so it cannot import it.

\begin{code}

Ball : ℕ → 𝓤₁ ̇
Ball n = Σ x ꞉ (Fin n → ℝ) , squared-norm x ≤ 1ℝ

Unit-Cube : ℕ → 𝓤₁ ̇
Unit-Cube n =
 Σ x ꞉ (Fin n → ℝ) , ((i : Fin n) → (embedding-ℚ-to-ℝ -1ℚ ≤ x i) × (x i ≤ 1ℝ))

ball-to-cube : {n : ℕ} → Ball n → Unit-Cube n
ball-to-cube (x , h) = x , coordinates-of-the-ball x h

cube-to-ball : {n : ℕ} → Unit-Cube n → Ball n
cube-to-ball (x , _) = retraction x , retraction-lands-in-the-ball x

ball-is-a-retract-of-the-cube : {n : ℕ} (k : Ball n)
                              → cube-to-ball (ball-to-cube k) ＝ k
ball-is-a-retract-of-the-cube (x , h) =
 to-subtype-＝ (λ y → ≤-is-prop (squared-norm y) 1ℝ)
  (retraction-fixes-the-ball x h)

\end{code}

Rational points, and the nonexpansiveness of the retraction: for real
z and rational q, the squared distance of ρ z and ρ q is at most that
of z and q. At rational points this is
retraction-ℚ-is-nonexpansive of gist.RealCohesion.RationalVectors,
and both sides are continuous in z.

\begin{code}

vector-sum-of-rationals : {n : ℕ} (v : Fin n → ℚ)
                        → vector-sum (λ i → ιₐ (v i)) ＝ ιₐ (vsum v)
vector-sum-of-rationals {0}      v = refl
vector-sum-of-rationals {succ n} v =
 ap (ιₐ (v 𝟎) +_) (vector-sum-of-rationals (v ∘ suc))
  ∙ ιₐ-sum (v 𝟎) (vsum (v ∘ suc))

squared-norm-of-rationals : {n : ℕ} (v : Fin n → ℚ)
                          → squared-norm (λ i → ιₐ (v i)) ＝ ιₐ (norm² v)
squared-norm-of-rationals v =
 ap vector-sum (dfunext fe (λ i → ιₐ-* (v i) (v i)))
 ∙ vector-sum-of-rationals (λ i → v i ℚ* v i)

retraction-of-rationals : {n : ℕ} (p : Fin n → ℚ)
                        → retraction (λ i → ιₐ (p i))
                        ＝ (λ i → ιₐ (retraction-ℚ p i))
retraction-of-rationals p =
 dfunext fe
  (λ i → ap (ιₐ (p i) *_) (ap reciprocal-ℝ (squared-norm-of-rationals p)
                           ∙ reciprocal-ℝ-agrees (norm² p))
        ∙ ιₐ-* (p i) (reciprocal (norm² p)))

distance² : {n : ℕ} → (Fin n → ℝ) → (Fin n → ℝ) → ℝ
distance² x y = squared-norm (λ i → x i + (- y i))

distance²-of-rationals : {n : ℕ} (p q : Fin n → ℚ)
                       → distance² (λ i → ιₐ (p i)) (λ i → ιₐ (q i))
                       ＝ ιₐ (norm² (λ i → p i ℚ- q i))
distance²-of-rationals p q =
 ap squared-norm
  (dfunext fe (λ i → ap (ιₐ (p i) +_) (ιₐ-neg (q i)) ∙ ιₐ-sum (p i) (ℚ- q i)))
 ∙ squared-norm-of-rationals (λ i → p i ℚ- q i)

squared-norm-is-continuous
 : {m n : ℕ} (A : Fin n → (Fin m → ℝ) → ℝ) (x : Fin m → ℝ)
 → ((i : Fin n) → Coordinatewise-Strictly-Continuous (A i) x)
 → Coordinatewise-Strictly-Continuous (λ y → squared-norm (λ i → A i y)) x
squared-norm-is-continuous A x c =
 vector-sum-is-continuous (λ i y → A i y * A i y) x
  (λ i → product-is-continuous (A i) (A i) x (c i) (c i))

retraction-is-continuous : {n : ℕ} (x : Fin n → ℝ) (i : Fin n)
                         → Coordinatewise-Strictly-Continuous
                            (λ y → retraction y i) x
retraction-is-continuous x i =
 product-is-continuous (λ y → y i) (λ y → reciprocal-ℝ (squared-norm y)) x
  (projection-is-continuous i x)
  (reciprocal-ℝ-is-continuous (λ y → squared-norm y) x
    (squared-norm-is-continuous (λ j y → y j) x
      (λ j → projection-is-continuous j x)))

retraction-is-nonexpansive-towards-rationals
 : {n : ℕ} (z : Fin n → ℝ) (q : Fin n → ℚ)
 → distance² (retraction z) (retraction (λ i → ιₐ (q i)))
 ≤ distance² z (λ i → ιₐ (q i))
retraction-is-nonexpansive-towards-rationals {n} z q =
 ≤-at-a-continuity-point F G z cF cG h
 where
  r : Fin n → ℝ
  r = retraction (λ i → ιₐ (q i))

  F G : (Fin n → ℝ) → ℝ
  F y = distance² (retraction y) r
  G y = distance² y (λ i → ιₐ (q i))

  cF : Coordinatewise-Strictly-Continuous F z
  cF = squared-norm-is-continuous (λ i y → retraction y i + (- r i)) z
        (λ i → sum-is-continuous (λ y → retraction y i) (λ _ → - r i) z
                (retraction-is-continuous z i)
                 (constant-is-continuous (- r i) z))

  cG : Coordinatewise-Strictly-Continuous G z
  cG = squared-norm-is-continuous (λ i y → y i + (- ιₐ (q i))) z
        (λ i → sum-is-continuous (λ y → y i) (λ _ → - ιₐ (q i)) z
                (projection-is-continuous i z)
                 (constant-is-continuous (- ιₐ (q i)) z))

  h : (p : Fin n → ℚ) → F (λ i → ιₐ (p i)) ≤ G (λ i → ιₐ (p i))
  h p = transport₂ _≤_
         {ιₐ (norm² (λ i → retraction-ℚ p i ℚ- retraction-ℚ q i))}
          {F (λ i → ιₐ (p i))}
         {ιₐ (norm² (λ i → p i ℚ- q i))} {G (λ i → ιₐ (p i))}
         (e₁ ⁻¹) (e₂ ⁻¹)
         (ιₐ-≤-ιₐ (norm² (λ i → retraction-ℚ p i ℚ- retraction-ℚ q i))
                  (norm² (λ i → p i ℚ- q i))
                  (retraction-ℚ-is-nonexpansive p q))
   where
    e₁ : F (λ i → ιₐ (p i))
       ＝ ιₐ (norm² (λ i → retraction-ℚ p i ℚ- retraction-ℚ q i))
    e₁ = ap₂ distance² (retraction-of-rationals p) (retraction-of-rationals q)
       ∙ distance²-of-rationals (retraction-ℚ p) (retraction-ℚ q)

    e₂ : G (λ i → ιₐ (p i)) ＝ ιₐ (norm² (λ i → p i ℚ- q i))
    e₂ = distance²-of-rationals p q

\end{code}

Approximate fixed points: Theorem 4.3 of the write-up for the ball,
from the cube (step E3, by part E of Codex's audit). Given f on the
ball and ε > 0, take δ with n δ² < ε², and apply the cube theorem with
δ/2 to g = f ∘ ρ (with the inclusion of the ball in the cube). It gives
a rational point q of the cube with g q within δ/2 of q in every
coordinate. Then y = ρ q is a rational point of the ball, and
‖f y - y‖² = ‖ρ (f y) - ρ q‖² ≤ ‖f y - q‖² ≤ n δ² < ε², because f y
lies in the ball and ρ is nonexpansive (the middle bound is not strict
when n = 0). The cube statement is written
as gist.RealCohesion.BrouwerStatements unfolds it.

\begin{code}

below-embedding : (x : ℝ) (r : ℚ) → x < embedding-ℚ-to-ℝ r → x < r
below-embedding x r = ∥∥-rec (ℝ<ℚ-is-prop x r) γ
 where
  γ : (Σ s ꞉ ℚ , (x < s) × (s < embedding-ℚ-to-ℝ r)) → x < r
  γ (s , a , b) = use-rounded-real-R x s r b a

embedding-below : (x : ℝ) (r : ℚ) → embedding-ℚ-to-ℝ r < x → r < x
embedding-below x r = ∥∥-rec (ℚ<ℝ-is-prop r x) γ
 where
  γ : (Σ s ꞉ ℚ , (embedding-ℚ-to-ℝ r < s) × (s < x)) → r < x
  γ (s , a , b) = use-rounded-real-L x r s a b

coordinate-error
 : (t : ℝ) (q δ' δ : ℚ) → δ' < δ
 → t < q ℚ+ δ' → q ℚ- δ' < t
 → ((ℚ- δ) < t + (- ιₐ q)) × (t + (- ιₐ q) < δ)
coordinate-error t q δ' δ l a b = lower , upper
 where
  v-is : t + (- ιₐ q) ＝ t + ιₐ (ℚ- q)
  v-is = ap (t +_) (ιₐ-neg q)

  upper : t + (- ιₐ q) < δ
  upper = ≤-<-trans-ℚ (t + (- ιₐ q)) (ιₐ δ') δ
           (transport (_≤ ιₐ δ') {t + ιₐ (ℚ- q)} {t + (- ιₐ q)} (v-is ⁻¹)
             (translate-below t δ' q
               (transport (t <_) {q ℚ+ δ'} {δ' ℚ+ q} (ℚ+-comm q δ') a)))
           (ιₐ-upper δ' δ l)

  lower : (ℚ- δ) < t + (- ιₐ q)
  lower = use-rounded-real-L (t + (- ιₐ q)) (ℚ- δ) (ℚ- δ') (ℚ<-swap δ' δ l)
           (transport ((ℚ- δ') <_) {t + ιₐ (ℚ- q)} {t + (- ιₐ q)} (v-is ⁻¹)
             (translate-strict t (ℚ- δ') q
               (transport (_< t) {q ℚ+ (ℚ- δ')} {(ℚ- δ') ℚ+ q}
                 (ℚ+-comm q (ℚ- δ')) b)))

vector-sum-≤ : {n : ℕ} (v w : Fin n → ℝ) → ((i : Fin n) → v i ≤ w i)
             → vector-sum v ≤ vector-sum w
vector-sum-≤ {0}      v w h = ℝ≤-refl (ιₐ 0ℚ)
vector-sum-≤ {succ n} v w h =
 sum-≤ (v 𝟎) (w 𝟎) (vector-sum (v ∘ suc)) (vector-sum (w ∘ suc)) (h 𝟎)
  (vector-sum-≤ (v ∘ suc) (w ∘ suc) (h ∘ suc))

Approximate-Fixed-Points-On-The-Cube : ℕ → 𝓤₁ ̇
Approximate-Fixed-Points-On-The-Cube n =
   (g : Unit-Cube n → Unit-Cube n) (ε : ℚ)
 → 0ℚ < ε
 → ∃ q ꞉ (Fin n → ℚ)
 , Σ c ꞉ ((i : Fin n) → (embedding-ℚ-to-ℝ -1ℚ ≤ embedding-ℚ-to-ℝ (q i))
                      × (embedding-ℚ-to-ℝ (q i) ≤ 1ℝ))
 , ((i : Fin n) → (pr₁ (g ((λ j → embedding-ℚ-to-ℝ (q j)) , c)) i
                    < embedding-ℚ-to-ℝ (q i ℚ+ ε))
                × (embedding-ℚ-to-ℝ (q i ℚ- ε)
                    < pr₁ (g ((λ j → embedding-ℚ-to-ℝ (q j)) , c)) i))

Approximate-Fixed-Points-On-The-Ball : ℕ → 𝓤₁ ̇
Approximate-Fixed-Points-On-The-Ball n =
   (f : Ball n → Ball n) (ε : ℚ)
 → 0ℚ < ε
 → ∃ r ꞉ (Fin n → ℚ)
 , Σ m ꞉ squared-norm (λ i → ιₐ (r i)) ≤ 1ℝ
 , distance² (pr₁ (f ((λ i → ιₐ (r i)) , m))) (λ i → ιₐ (r i)) < ε ℚ* ε

approximate-fixed-points-on-the-ball
 : {n : ℕ} → Approximate-Fixed-Points-On-The-Cube n
 → Approximate-Fixed-Points-On-The-Ball n
approximate-fixed-points-on-the-ball {n} φ f ε l =
 ∥∥-functor γ (φ g (halfₐ δ) (halfₐ-is-positive δ δ-is-positive))
 where
  δ-data : Σ δ ꞉ ℚ , (0ℚ < δ) × (vsum {n} (λ _ → δ ℚ* δ) < ε ℚ* ε)
  δ-data = budget n ε l

  δ : ℚ
  δ = pr₁ δ-data

  δ-is-positive : 0ℚ < δ
  δ-is-positive = pr₁ (pr₂ δ-data)

  g : Unit-Cube n → Unit-Cube n
  g = ball-to-cube ∘ f ∘ cube-to-ball

  γ : (Σ q ꞉ (Fin n → ℚ)
      , Σ c ꞉ ((i : Fin n) → (embedding-ℚ-to-ℝ -1ℚ ≤ embedding-ℚ-to-ℝ (q i))
                           × (embedding-ℚ-to-ℝ (q i) ≤ 1ℝ))
      , ((i : Fin n) → (pr₁ (g ((λ j → embedding-ℚ-to-ℝ (q j)) , c)) i
                         < embedding-ℚ-to-ℝ (q i ℚ+ halfₐ δ))
                     × (embedding-ℚ-to-ℝ (q i ℚ- halfₐ δ)
                         < pr₁ (g ((λ j → embedding-ℚ-to-ℝ (q j)) , c)) i)))
    → Σ r ꞉ (Fin n → ℚ) , Σ m ꞉ squared-norm (λ i → ιₐ (r i)) ≤ 1ℝ
                        , distance² (pr₁ (f ((λ i → ιₐ (r i)) , m)))
                           (λ i → ιₐ (r i)) < ε ℚ* ε
  γ (q , c , bounds) = retraction-ℚ q , m , conclusion
   where
    x : Fin n → ℝ
    x j = embedding-ℚ-to-ℝ (q j)

    x-is : x ＝ (λ j → ιₐ (q j))
    x-is = dfunext fe (λ j → ιₐ-is-ι (q j) ⁻¹)

    r-vector : (λ i → ιₐ (retraction-ℚ q i)) ＝ retraction x
    r-vector = retraction-of-rationals q ⁻¹ ∙ ap retraction (x-is ⁻¹)

    m : squared-norm (λ i → ιₐ (retraction-ℚ q i)) ≤ 1ℝ
    m = transport (λ v → squared-norm v ≤ 1ℝ) (r-vector ⁻¹)
         (retraction-lands-in-the-ball x)

    y : Ball n
    y = cube-to-ball (x , c)

    same-point : ((λ i → ιₐ (retraction-ℚ q i)) , m) ＝ y
    same-point = to-subtype-＝ (λ v → ≤-is-prop (squared-norm v) 1ℝ) r-vector

    z : Fin n → ℝ
    z = pr₁ (f y)

    v : Fin n → ℝ
    v i = z i + (- ιₐ (q i))

    error : (i : Fin n) → ((ℚ- δ) < v i) × (v i < δ)
    error i =
     coordinate-error (z i) (q i) (halfₐ δ) δ (halfₐ-is-less δ δ-is-positive)
               (below-embedding (z i) (q i ℚ+ halfₐ δ) (pr₁ (bounds i)))
               (embedding-below (z i) (q i ℚ- halfₐ δ) (pr₂ (bounds i)))

    S : ℚ
    S = vsum {n} (λ _ → δ ℚ* δ)

    sum-bound : distance² z (λ i → ιₐ (q i)) ≤ ιₐ S
    sum-bound =
     transport (distance² z (λ i → ιₐ (q i)) ≤_)
      {vector-sum (λ _ → ιₐ (δ ℚ* δ))} {ιₐ S}
      (vector-sum-of-rationals (λ _ → δ ℚ* δ))
      (vector-sum-≤ (λ i → v i * v i) (λ _ → ιₐ (δ ℚ* δ))
        (λ i → <-gives-≤-ιₐ (v i * v i) (δ ℚ* δ)
                 (products-below δ (v i) (v i) (pr₁ (error i)) (pr₂ (error i))
                   (pr₁ (error i)) (pr₂ (error i)))))

    main : distance² (retraction z) (retraction (λ i → ιₐ (q i))) < ε ℚ* ε
    main = ≤-<-trans-ℚ (distance² (retraction z) (retraction (λ i → ιₐ (q i))))
            (ιₐ S) (ε ℚ* ε)
            (ℝ≤-trans (distance² (retraction z) (retraction (λ i → ιₐ (q i))))
                      (distance² z (λ i → ιₐ (q i))) (ιₐ S)
                      (retraction-is-nonexpansive-towards-rationals z q)
                       sum-bound)
            (ιₐ-upper S (ε ℚ* ε) (pr₂ (pr₂ δ-data)))

    LHS-is : distance² (pr₁ (f ((λ i → ιₐ (retraction-ℚ q i)) , m)))
             (λ i → ιₐ (retraction-ℚ q i))
           ＝ distance² (retraction z) (retraction (λ i → ιₐ (q i)))
    LHS-is = ap₂ distance² (ap (λ k → pr₁ (f k)) same-point
                            ∙ retraction-fixes-the-ball z (pr₂ (f y)) ⁻¹)
                           (r-vector ∙ ap retraction x-is)

    conclusion : distance² (pr₁ (f ((λ i → ιₐ (retraction-ℚ q i)) , m)))
                           (λ i → ιₐ (retraction-ℚ q i)) < ε ℚ* ε
    conclusion = transport (_< ε ℚ* ε)
                  {distance² (retraction z) (retraction (λ i → ιₐ (q i)))}
                  {distance² (pr₁ (f ((λ i → ιₐ (retraction-ℚ q i)) , m)))
                             (λ i → ιₐ (retraction-ℚ q i))}
                  (LHS-is ⁻¹) main

\end{code}
