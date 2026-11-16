Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. See the AI disclosure in
gist.RealCohesion.index.

Shulman's Theorem 12.6 for the disc (gate G26), from univalence and
Axiom R♭, by Corollary 4 of Fable's note [1], revision 2, which GPT-6
Astra audited on 12 November 2026.

Shulman's Theorem 12.6 [2], tagged UA and R♭: for a crisp
f :: D² → D² and ε > 0 there is x : D² with |f x - x| < ε, for the
Euclidean norm. Here D² is Ball 2 of gist.RealCohesion.EuclideanBall,
and |f x - x| < ε is written ‖f x - x‖² < ε², for every real ε > 0
(Approximate-Fixed-Points-Of-Crisp-Maps-Of-The-Disc-For-Real-ε). It
follows from the same statement for every rational ε > 0
(Approximate-Fixed-Points-Of-Crisp-Maps-Of-The-Disc): a positive
rational q below ε gives ‖f x - x‖² < q² < ε². The proof of the form
for rational ε:

 * The retraction ρ x = x / max(1 , ‖x‖²) of ℝⁿ onto the ball does not
   increase Euclidean distances (retraction-is-nonexpansive; Lemma 5 of
   the note, part D of Codex's audit). For b fixed both sides are
   continuous in a, and at rational a this is the case of step E3 of
   gate G14 with the roles exchanged, since the squared distance is
   symmetric. So the density principle of
   gist.RealCohesion.RationalBoxExtension gives it for all a and b.

 * Given f and ε, take δ with 2 δ² < ε² (budget of
   gist.RealCohesion.RationalVectors), and apply Shulman's Theorem 12.6
   for the square (gist.RealCohesion.ApproximateBrouwerSquare) to the
   crisp map g = f ∘ ρ, with values in the ball inside the square.
   It gives x with |g(x)ᵢ - xᵢ| < δ in each coordinate. For y = ρ x,
   f y lies in the ball, so ρ (f y) = f y, and
   ‖f y - y‖² = ‖ρ (f y) - ρ x‖² ≤ ‖f y - x‖² < 2 δ² < ε²
   (approximate-fixed-points-from-the-square).

Since the consolidation of 13 November 2026, by Claude Opus 5.5 (W4 of
Claude Fable 5.2's consolidation plan [3]), both forms are stated once,
from the theorem for the square (disc-form-from-the-square-form) and
from the form for rational ε (real-ε-form-from-the-rational-ε-form).
The theorems under univalence and Axiom R♭ keep their names and types;
gist.RealCohesion.TheoremsFromC1 applies the same two steps to the
theorem for the square under univalence, Axiom C1 and a merely rising
generator path.

[1] Claude Fable 5.2. Note: Shulman's approximate Brouwer theorem (12.6)
    without the shape modality. Revision 2, 12 November 2026, audited
    by GPT-6 Astra.
    references/F11-shulman-12-6-rev2.md

[2] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer Science
    28(6), 2018. https://arxiv.org/abs/1509.07584v3

[3] Claude Fable 5.2. Plan: consolidation of r3, and "C1 + NC in place
    of R♭" (G27(d)), 13 November 2026, Section 4.5, as incorporated by
    its addendum 01, Section 3, and released by GPT-6 Astra.
    references/F02-consolidation-plan.md

\begin{code}

{-# OPTIONS --safe --without-K --cohesion --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Univalence
open import gist.CohesiveApartness.Flat

module gist.RealCohesion.ApproximateBrouwerDisc
        (@♭ fe : Fun-Ext)
        (@♭ pe : Prop-Ext)
        (@♭ pt : propositional-truncations-exist)
       where

open import Fin.Type
open import Notation.CanonicalMap
open import Notation.Order
open import UF.Base
open import Rationals.Type
open import Rationals.Order
open import Rationals.Addition renaming (_+_ to _ℚ+_)
open import Rationals.Negation renaming (_-_ to _ℚ-_ ; -_ to ℚ-_)
open import Rationals.Multiplication renaming (_*_ to _ℚ*_)
open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import DedekindReals.Addition fe pe pt using () renaming (_+_ to _+ᵗ_)
open import gist.RealCohesion.ContinuityForms fe pe pt
 using (Coordinatewise-Strictly-Continuous)
open import gist.RealCohesion.RationalProducts using (negation-times-negation)
open import gist.RealCohesion.RationalPoints fe pe pt using (ιₐ ; ιₐ-is-ι)
open import gist.RealCohesion.RationalVectors using (vsum ; budget)
open import gist.RealCohesion.FinVectors using (Fin-pair)
open import gist.RealCohesion.RealOrder fe pe pt using (ℝ≤-refl)
open import gist.RealCohesion.RealLattice fe pe pt
 using
  (_+_ ; -_ ; +-is-+ᵗ ; ιₐ-sum ; <-gives-≤-ιₐ ; ≤-<-trans-ℚ ; ιₐ-zero-is-0ℝ)
open import gist.RealCohesion.RationalBoxExtension fe pe pt
 using (agree-at-a-continuity-point ; ≤-at-a-continuity-point ;
         projection-is-continuous ;
        constant-is-continuous)
open import gist.RealCohesion.RealMultiplication fe pe pt
 using (_*_ ; ιₐ-* ; ιₐ-neg ; product-is-continuous ; sum-is-continuous ;
        negative-is-continuous ; products-below ; products-above ;
        <-from-rational-between)
open import gist.RealCohesion.RealAlgebra fe pe pt
 using (+-comm ; plus-minus-cancel ; add-right-strict)
open import gist.RealCohesion.SquareEstimates fe pe pt using (shift-back)
open import gist.RealCohesion.EuclideanBall fe pe pt
 using
  (Ball ; Unit-Cube ; ball-to-cube ; cube-to-ball ; squared-norm ; vector-sum ;
   retraction ; retraction-fixes-the-ball ; retraction-is-continuous ;
   squared-norm-is-continuous ; distance² ; vector-sum-of-rationals ;
    vector-sum-≤ ;
   retraction-is-nonexpansive-towards-rationals ; below-embedding ;
    embedding-below)
open import gist.RealCohesion.BrouwerStatements fe pe pt using (Cube)
open import gist.RealCohesion.ShulmanWeakeningsStatements fe pe pt
 using (R♭ ; Approximate-Fixed-Points-Of-Crisp-Maps)
import gist.RealCohesion.ApproximateBrouwerSquare fe pe pt as ABS

open PropositionalTruncation pt

\end{code}

The squared distance is symmetric, and ρ does not increase it.

\begin{code}

difference-of-ιₐ : (p q : ℚ) → ιₐ p + (- ιₐ q) ＝ ιₐ (p ℚ- q)
difference-of-ιₐ p q = ap (ιₐ p +_) (ιₐ-neg q) ∙ ιₐ-sum p (ℚ- q)

squared-difference-is-symmetric
 : (x y : ℝ) → (x + (- y)) * (x + (- y)) ＝ (y + (- x)) * (y + (- x))
squared-difference-is-symmetric x y = agree-at-a-continuity-point F G t cF cG e
 where
  t : Fin 2 → ℝ
  t = Fin-pair x y

  F G : (Fin 2 → ℝ) → ℝ
  F v = (v 𝟎 + (- v 𝟏)) * (v 𝟎 + (- v 𝟏))
  G v = (v 𝟏 + (- v 𝟎)) * (v 𝟏 + (- v 𝟎))

  d : (i j : Fin 2) → Coordinatewise-Strictly-Continuous (λ v → v i + (- v j)) t
  d i j =
   sum-is-continuous (λ v → v i) (λ v → - v j) t (projection-is-continuous i t)
           (negative-is-continuous (λ v → v j) t (projection-is-continuous j t))

  cF : Coordinatewise-Strictly-Continuous F t
  cF = product-is-continuous (λ v → v 𝟎 + (- v 𝟏)) (λ v → v 𝟎 + (- v 𝟏)) t
        (d 𝟎 𝟏) (d 𝟎 𝟏)

  cG : Coordinatewise-Strictly-Continuous G t
  cG = product-is-continuous (λ v → v 𝟏 + (- v 𝟎)) (λ v → v 𝟏 + (- v 𝟎)) t
        (d 𝟏 𝟎) (d 𝟏 𝟎)

  e : (q : Fin 2 → ℚ) → F (λ i → ιₐ (q i)) ＝ G (λ i → ιₐ (q i))
  e q = ap₂ _*_ (difference-of-ιₐ a b) (difference-of-ιₐ a b)
      ∙ ιₐ-* (a ℚ- b) (a ℚ- b)
      ∙ ap ιₐ I
      ∙ ιₐ-* (b ℚ- a) (b ℚ- a) ⁻¹
      ∙ ap₂ _*_ (difference-of-ιₐ b a ⁻¹) (difference-of-ιₐ b a ⁻¹)
   where
    a b : ℚ
    a = q 𝟎
    b = q 𝟏

    I : (a ℚ- b) ℚ* (a ℚ- b) ＝ (b ℚ- a) ℚ* (b ℚ- a)
    I = negation-times-negation (a ℚ- b) (a ℚ- b) ⁻¹
      ∙ ap₂ _ℚ*_ (ℚ-minus-dist' a b) (ℚ-minus-dist' a b)

distance²-is-symmetric : {n : ℕ} (x y : Fin n → ℝ)
                       → distance² x y ＝ distance² y x
distance²-is-symmetric x y =
 ap vector-sum (dfunext fe (λ i → squared-difference-is-symmetric (x i) (y i)))

retraction-is-nonexpansive
 : {n : ℕ} (a b : Fin n → ℝ)
 → distance² (retraction a) (retraction b) ≤ distance² a b
retraction-is-nonexpansive {n} a b = ≤-at-a-continuity-point F G a cF cG h
 where
  r : Fin n → ℝ
  r = retraction b

  F G : (Fin n → ℝ) → ℝ
  F y = distance² (retraction y) r
  G y = distance² y b

  cF : Coordinatewise-Strictly-Continuous F a
  cF = squared-norm-is-continuous (λ i y → retraction y i + (- r i)) a
        (λ i → sum-is-continuous (λ y → retraction y i) (λ _ → - r i) a
                (retraction-is-continuous a i)
                 (constant-is-continuous (- r i) a))

  cG : Coordinatewise-Strictly-Continuous G a
  cG = squared-norm-is-continuous (λ i y → y i + (- b i)) a
        (λ i → sum-is-continuous (λ y → y i) (λ _ → - b i) a
                (projection-is-continuous i a)
                 (constant-is-continuous (- b i) a))

  h : (p : Fin n → ℚ) → F (λ i → ιₐ (p i)) ≤ G (λ i → ιₐ (p i))
  h p = transport₂ _≤_
         (distance²-is-symmetric (retraction b) (retraction (λ i → ιₐ (p i))))
         (distance²-is-symmetric b (λ i → ιₐ (p i)))
         (retraction-is-nonexpansive-towards-rationals b p)

\end{code}

From approximate fixed points on the square to the ball.

\begin{code}

coordinate-difference
 : (t z : ℝ) (δ : ℚ) → t < z + ιₐ δ → z < t + ιₐ δ
 → ((ℚ- δ) < t + (- z)) × (t + (- z) < δ)
coordinate-difference t z δ a b = lower , upper
 where
  upper : t + (- z) < δ
  upper = below-embedding (t + (- z)) δ
           (transport (t + (- z) <_) (I ∙ ιₐ-is-ι δ)
             (add-right-strict t (z + ιₐ δ) (- z) a))
   where
    I : (z + ιₐ δ) + (- z) ＝ ιₐ δ
    I = ap (_+ (- z)) (+-comm z (ιₐ δ)) ∙ plus-minus-cancel (ιₐ δ) z

  lower : (ℚ- δ) < t + (- z)
  lower = embedding-below (t + (- z)) (ℚ- δ)
           (transport (_< t + (- z)) (II ∙ ιₐ-is-ι (ℚ- δ))
             (add-right-strict (z + ιₐ (ℚ- δ)) t (- z)
               (transport (z + ιₐ (ℚ- δ) <_) (shift-back t δ)
                 (add-right-strict z (t + ιₐ δ) (ιₐ (ℚ- δ)) b))))
   where
    II : (z + ιₐ (ℚ- δ)) + (- z) ＝ ιₐ (ℚ- δ)
    II = ap (_+ (- z)) (+-comm z (ιₐ (ℚ- δ))) ∙ plus-minus-cancel (ιₐ (ℚ- δ)) z

approximate-fixed-points-from-the-square
 : {n : ℕ} (f : Ball n → Ball n) (δ ε : ℚ) → vsum {n} (λ _ → δ ℚ* δ) < ε ℚ* ε
 → (x : Unit-Cube n)
 → ((i : Fin n) → (pr₁ (f (cube-to-ball x)) i < pr₁ x i + ιₐ δ)
                × (pr₁ x i < pr₁ (f (cube-to-ball x)) i + ιₐ δ))
 → distance² (pr₁ (f (cube-to-ball x))) (pr₁ (cube-to-ball x)) < ε ℚ* ε
approximate-fixed-points-from-the-square {n} f δ ε small x bounds =
 transport (_< ε ℚ* ε) I main
 where
  y : Ball n
  y = cube-to-ball x

  t z : Fin n → ℝ
  t = pr₁ (f y)
  z = pr₁ x

  v : Fin n → ℝ
  v i = t i + (- z i)

  error : (i : Fin n) → ((ℚ- δ) < v i) × (v i < δ)
  error i =
   coordinate-difference (t i) (z i) δ (pr₁ (bounds i)) (pr₂ (bounds i))

  S : ℚ
  S = vsum {n} (λ _ → δ ℚ* δ)

  sum-bound : distance² t z ≤ ιₐ S
  sum-bound =
   transport (distance² t z ≤_) {vector-sum (λ _ → ιₐ (δ ℚ* δ))} {ιₐ S}
    (vector-sum-of-rationals (λ _ → δ ℚ* δ))
    (vector-sum-≤ (λ i → v i * v i) (λ _ → ιₐ (δ ℚ* δ))
      (λ i → <-gives-≤-ιₐ (v i * v i) (δ ℚ* δ)
               (products-below δ (v i) (v i) (pr₁ (error i)) (pr₂ (error i))
                 (pr₁ (error i)) (pr₂ (error i)))))

  main : distance² (retraction t) (retraction z) < ε ℚ* ε
  main = ≤-<-trans-ℚ (distance² (retraction t) (retraction z)) (ιₐ S) (ε ℚ* ε)
          (ℝ≤-trans (distance² (retraction t) (retraction z)) (distance² t z)
            (ιₐ S)
            (retraction-is-nonexpansive t z) sum-bound)
          (ιₐ-upper' S (ε ℚ* ε) small)
   where
    ιₐ-upper' : (p q : ℚ) → p < q → ιₐ p < q
    ιₐ-upper' p q l = transport (_< q) (ιₐ-is-ι p ⁻¹) (embedding-is-below p q l)
     where
      embedding-is-below : (p q : ℚ) → p < q → embedding-ℚ-to-ℝ p < q
      embedding-is-below p q l = l

  I : distance² (retraction t) (retraction z) ＝ distance² t (pr₁ y)
  I = ap (λ w → distance² w (retraction z))
       (retraction-fixes-the-ball t (pr₂ (f y)))

\end{code}

The statement and the theorem.

\begin{code}

on-the-square : (Ball 2 → Ball 2) → Cube 2 → Cube 2
on-the-square f = ball-to-cube ∘ f ∘ cube-to-ball

Approximate-Fixed-Points-Of-Crisp-Maps-Of-The-Disc : 𝓤₁ ̇
Approximate-Fixed-Points-Of-Crisp-Maps-Of-The-Disc =
   (@♭ f : Ball 2 → Ball 2) (ε : ℚ)
 → 0ℚ < ε
 → ∃ x ꞉ Ball 2 , distance² (pr₁ (f x)) (pr₁ x) < ε ℚ* ε

disc-form-from-the-square-form
 : Approximate-Fixed-Points-Of-Crisp-Maps 2
 → Approximate-Fixed-Points-Of-Crisp-Maps-Of-The-Disc
disc-form-from-the-square-form square f ε l =
 ∥∥-functor γ (square (on-the-square f) δ δ-is-positive)
 where
  δ-data : Σ δ ꞉ ℚ , (0ℚ < δ) × (vsum {2} (λ _ → δ ℚ* δ) < ε ℚ* ε)
  δ-data = budget 2 ε l

  δ : ℚ
  δ = pr₁ δ-data

  δ-is-positive : 0ℚ < δ
  δ-is-positive = pr₁ (pr₂ δ-data)

  from-target : {u v : ℝ} → u < v +ᵗ embedding-ℚ-to-ℝ δ → u < v + ιₐ δ
  from-target {u} {v} =
   transport (u <_) ((+-is-+ᵗ v (ιₐ δ) ∙ ap (v +ᵗ_) (ιₐ-is-ι δ)) ⁻¹)

  γ : (Σ x ꞉ Cube 2 ,
    ((i : Fin 2) → (pr₁ (on-the-square f x) i < pr₁ x i +ᵗ embedding-ℚ-to-ℝ δ)
                 × (pr₁ x i < pr₁ (on-the-square f x) i +ᵗ embedding-ℚ-to-ℝ δ)))
    → Σ y ꞉ Ball 2 , distance² (pr₁ (f y)) (pr₁ y) < ε ℚ* ε
  γ (x , w) = cube-to-ball x ,
              approximate-fixed-points-from-the-square f δ ε (pr₂ (pr₂ δ-data))
               x
               (λ i → from-target (pr₁ (w i)) , from-target (pr₂ (w i)))

UA-and-R♭-give-approximate-fixed-points-on-the-disc
 : Univalence → R♭ → Approximate-Fixed-Points-Of-Crisp-Maps-Of-The-Disc
UA-and-R♭-give-approximate-fixed-points-on-the-disc ua r♭ =
 disc-form-from-the-square-form (ABS.UA-and-R♭-give-Target-12-6-cube ua r♭)

\end{code}

The same for every real ε > 0, as Shulman states it. Since 0 < ε, there
is a rational q with 0 < q < ε; the form for rational ε gives x with
‖f x - x‖² < q², and q² < ε² because 0 < q < ε.

\begin{code}

Approximate-Fixed-Points-Of-Crisp-Maps-Of-The-Disc-For-Real-ε : 𝓤₁ ̇
Approximate-Fixed-Points-Of-Crisp-Maps-Of-The-Disc-For-Real-ε =
   (@♭ f : Ball 2 → Ball 2) (ε : ℝ)
 → 0ℝ < ε
 → ∃ x ꞉ Ball 2 , distance² (pr₁ (f x)) (pr₁ x) < ε * ε

real-ε-form-from-the-rational-ε-form
 : Approximate-Fixed-Points-Of-Crisp-Maps-Of-The-Disc
 → Approximate-Fixed-Points-Of-Crisp-Maps-Of-The-Disc-For-Real-ε
real-ε-form-from-the-rational-ε-form disc f ε l =
 ∥∥-rec ∃-is-prop γ l
 where
  γ : (Σ q ꞉ ℚ , (0ℝ < q) × (q < ε))
    → ∃ x ꞉ Ball 2 , distance² (pr₁ (f x)) (pr₁ x) < ε * ε
  γ (q , k , m) =
   ∥∥-functor δ (disc f q k)
   where
    δ : (Σ x ꞉ Ball 2 , distance² (pr₁ (f x)) (pr₁ x) < q ℚ* q)
      → Σ x ꞉ Ball 2 , distance² (pr₁ (f x)) (pr₁ x) < ε * ε
    δ (x , h) =
     x , <-from-rational-between (distance² (pr₁ (f x)) (pr₁ x)) (ε * ε)
                     (q ℚ* q) h (products-above q q ε ε k k m m)

UA-and-R♭-give-approximate-fixed-points-on-the-disc-for-real-ε
 : Univalence → R♭
 → Approximate-Fixed-Points-Of-Crisp-Maps-Of-The-Disc-For-Real-ε
UA-and-R♭-give-approximate-fixed-points-on-the-disc-for-real-ε ua r♭ =
 real-ε-form-from-the-rational-ε-form
  (UA-and-R♭-give-approximate-fixed-points-on-the-disc ua r♭)

\end{code}
