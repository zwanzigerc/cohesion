Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026; the form of the lemma with the inclusion
as the section added on 13 November 2026, in the consolidation after
the final audits. See the AI disclosure in gist.RealCohesion.index.

The sphere as a retract of the ball: Shulman's Lemma 12.3 from the
analytic Markov principle, in every dimension (gate G14, step E4).

Shulman's Lemma 12.3 [1], tagged LEM, C1 and T, says: if there is a map
f : D² → D² without a fixed point, then S¹ is a retract of D². Remark
3.8 of the write-up observes that his proof uses C1 only through his
Theorem 8.32, which needs only LEM and T, and that the proof works in
every dimension; GPT-6 Astra audited this on 12 November 2026 (part B
of references/A25-g14-audit.txt). Here: for
every n and every f : Dⁿ → Dⁿ with f x ≠ x for all x, the sphere
Sⁿ⁻¹ = {x : ℝⁿ | ‖x‖² = 1} is a retract of Dⁿ = {x : ℝⁿ | ‖x‖² ≤ 1}
(Analytic-Markov-gives-Lemma-12-3), assuming only the analytic Markov
principle in its order form, ¬ (r ≤ 0) → 0 < r (Analytic-Markov of
gist.RealCohesion.AnalyticMarkovObstruction). That is Shulman's
Theorem 8.32, which follows from crisp excluded middle and Axiom T
(Axiom-T-gives-analytic-Markov in gist.RealCohesion.Theorems, where
Lemma 12.3 is stated from those two hypotheses). The map f need not be
crisp. Retracts are TypeTopology's: retract (Sphere n) of (Ball n)
consists of maps r : Dⁿ → Sⁿ⁻¹ and s : Sⁿ⁻¹ → Dⁿ with r ∘ s = id; here
s is the inclusion. The sets Dⁿ and Sⁿ⁻¹ are those of Shulman's
statement, with |x| ≤ 1 and |x| = 1 written ‖x‖² ≤ 1 and ‖x‖² = 1.

That type does not say that the section is the inclusion. In
Shulman's proof the section is explicitly the standard inclusion of S¹
in D². So the lemma is also stated with a retraction of the
inclusion as its conclusion (decision D2 of Claude Fable 5.2's
consolidation plan [2]): Retraction-Of-The-Sphere-Inclusion n consists
of r : Dⁿ → Sⁿ⁻¹ with r ∘ sphere-to-ball = id, which is
is-section sphere-to-ball in the terms of TypeTopology's UF.Retracts,
and Literal-Lemma-12-3-for-the-ball n is the lemma with that
conclusion. The proof below constructs such an r, so it proves this
form (Analytic-Markov-gives-literal-Lemma-12-3), with the same
hypotheses; Analytic-Markov-gives-Lemma-12-3, with its type unchanged,
is that proof followed by retractions-of-the-inclusion-give-retracts,
which forgets that the section is the inclusion.

The retraction is the one of the audit. For z in Dⁿ, put u = f z,
v = z - u, A = ‖v‖², B = ⟨v , u⟩ and U = ‖u‖².

 * A > 0. If A ≤ 0, then every vᵢ² ≤ A ≤ 0, so v = 0 and f z = z; so
   ¬ (A ≤ 0), and the analytic Markov principle gives A > 0. This is the
   only nonconstructive step.

 * With a = 1/A (gist.RealCohesion.RealReciprocal), β = B a and
   γ = (1 - U) a ≥ 0, put t = √(β² + γ) - β
   (gist.RealCohesion.RealSquareRoot) and r z = u + t v, the point
   where the ray from u through z meets the sphere. This is the audit's
   t = (-B + √D)/A with D = B² + A (1 - U), divided through by A.

 * ‖u + t v‖² = U + B (t + t) + A t², and B (t + t) + A t² =
   A ((t + β)² - β²) = A γ = 1 - U; so ‖r z‖² = 1.

 * If ‖z‖² = 1, then ‖z‖² = U + B (1 + 1) + A gives γ = β (1 + 1) + 1,
   so (1 + β)² = β² + γ, and 1 + β ≥ 0 because its double is 1 + γ ≥ 0.
   By uniqueness of nonnegative square roots √(β² + γ) = 1 + β, so
   t = 1 and r z = u + v = z.

No case distinction on real numbers is made.

[1] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer
    Science 28(6), 856–941, 2018. https://arxiv.org/abs/1509.07584v3

[2] Claude Fable 5.2. Plan: consolidation of r3, and "C1 + NC in place
    of R♭" (G27(d)), 13 November 2026, decision D2 and step K6, as
    released by GPT-6 Astra on 13 November 2026.
    references/F02-consolidation-plan.md

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.EuclideanSphere
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import Fin.Type
open import Notation.Order
open import UF.Base
open import UF.Retracts using (retract_of_)
open import Rationals.Type
open import Rationals.Order
open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import gist.RealCohesion.RationalPoints fe pe pt using (ιₐ)
open import gist.RealCohesion.RealLattice fe pe pt
 using (_+_ ; -_ ; sum-≤ ; plus-zero ; zero-plus ; minus-plus-cancel ; ιₐ-≤-ιₐ)
open import gist.RealCohesion.RealOrder fe pe pt using (ℝ≤-refl)
open import gist.RealCohesion.RealMultiplication fe pe pt
 using
  (_*_ ; *-comm ; *-assoc ; *-right-unit ; *-left-unit ; *-left-distributive ;
   *-right-distributive ; 0ℝ-is-ιₐ ; 1ℝ-is-ιₐ)
open import gist.RealCohesion.RealAlgebra fe pe pt
 using
  (+-comm ; +-assoc ; +-right-inverse ; plus-minus-cancel ; plus-difference ;
   interchange ; nonneg-from-double ; square-of-shifted ; completing-the-square)
open import gist.RealCohesion.RealSquareRoot fe pe pt
 using (square-root ; square-root-is-nonneg ; square-root-squared ;
        nonneg-square-roots-are-unique ; products-of-nonnegatives-are-nonneg ;
        square-at-most-zero)
open import gist.RealCohesion.RealReciprocal fe pe pt
 using (inverse ; inverse-law ; inverse-is-nonneg)
open import gist.RealCohesion.EuclideanBall fe pe pt
 using (vector-sum ; squared-norm ; Ball ; vector-sum-plus ; vector-sum-times ;
        term-≤-vector-sum ; squares-are-nonneg')
open import gist.RealCohesion.AnalyticMarkovObstruction fe pe pt
 using (Analytic-Markov)

open PropositionalTruncation pt

\end{code}

The sphere, its inclusion into the ball, and the statement.

\begin{code}

Sphere : ℕ → 𝓤₁ ̇
Sphere n = Σ x ꞉ (Fin n → ℝ) , squared-norm x ＝ 1ℝ

sphere-to-ball : {n : ℕ} → Sphere n → Ball n
sphere-to-ball (x , e) = x , transport (_≤ 1ℝ) (e ⁻¹) (ℝ≤-refl 1ℝ)

Lemma-12-3-for-the-ball : ℕ → 𝓤₁ ̇
Lemma-12-3-for-the-ball n =
 (f : Ball n → Ball n) → ((x : Ball n) → ¬ (f x ＝ x))
  → retract (Sphere n) of (Ball n)

\end{code}

The statement with a retraction of the inclusion, and the map that
forgets that the section is the inclusion.

\begin{code}

Retraction-Of-The-Sphere-Inclusion : ℕ → 𝓤₁ ̇
Retraction-Of-The-Sphere-Inclusion n =
 Σ r ꞉ (Ball n → Sphere n) , r ∘ sphere-to-ball ∼ id

Literal-Lemma-12-3-for-the-ball : ℕ → 𝓤₁ ̇
Literal-Lemma-12-3-for-the-ball n =
 (f : Ball n → Ball n) → ((x : Ball n) → ¬ (f x ＝ x))
  → Retraction-Of-The-Sphere-Inclusion n

retractions-of-the-inclusion-give-retracts
 : {n : ℕ}
 → Retraction-Of-The-Sphere-Inclusion n → retract (Sphere n) of (Ball n)
retractions-of-the-inclusion-give-retracts (r , η) = r , sphere-to-ball , η

\end{code}

The expansion of ‖u + t v‖².

\begin{code}

squared-norm-of-shifted
 : {n : ℕ} (u v : Fin n → ℝ) (t : ℝ)
 → squared-norm (λ i → u i + t * v i)
   ＝ squared-norm u
   + (vector-sum (λ i → v i * u i) * (t + t) + squared-norm v * (t * t))
squared-norm-of-shifted u v t =
 ap vector-sum (dfunext fe (λ i → square-of-shifted (u i) (v i) t))
 ∙ vector-sum-plus (λ i → u i * u i)
    (λ i → (v i * u i) * (t + t) + (v i * v i) * (t * t))
 ∙ ap (squared-norm u +_)
     (vector-sum-plus (λ i → (v i * u i) * (t + t))
       (λ i → (v i * v i) * (t * t))
      ∙ ap₂ _+_ (vector-sum-times (λ i → v i * u i) (t + t))
                (vector-sum-times (λ i → v i * v i) (t * t)))

\end{code}

The retraction, for a map f without fixed points.

\begin{code}

module retraction-onto-the-sphere
        (markov : Analytic-Markov)
        {n : ℕ}
        (f : Ball n → Ball n)
        (h : (x : Ball n) → ¬ (f x ＝ x))
       where

 module at (z : Ball n) where

  w u v : Fin n → ℝ
  w = pr₁ z
  u = pr₁ (f z)
  v i = w i + (- u i)

  A B U : ℝ
  A = squared-norm v
  B = vector-sum (λ i → v i * u i)
  U = squared-norm u

  shifted-one : (λ i → u i + 1ℝ * v i) ＝ w
  shifted-one = dfunext fe
   (λ i → ap (u i +_) (*-left-unit (v i)) ∙ plus-difference (u i) (w i))

  fixed-if-A-is-at-most-zero : A ≤ 0ℝ → f z ＝ z
  fixed-if-A-is-at-most-zero k =
   to-subtype-＝ (λ x → ≤-is-prop (squared-norm x) 1ℝ)
    (dfunext fe equal-coordinate)
   where
    equal-coordinate : (i : Fin n) → u i ＝ w i
    equal-coordinate i =
     u i                   ＝⟨ zero-plus (u i) ⁻¹ ⟩
     ιₐ 0ℚ + u i           ＝⟨ ap (_+ u i) (v-is-zero ⁻¹) ⟩
     (w i + (- u i)) + u i ＝⟨ minus-plus-cancel (w i) (u i) ⟩
     w i                   ∎
     where
      square-is-at-most-zero : v i * v i ≤ 0ℝ
      square-is-at-most-zero =
       ℝ≤-trans (v i * v i) A 0ℝ
        (term-≤-vector-sum (λ j → v j * v j) (λ j → squares-are-nonneg' (v j))
          i) k

      v-is-zero : v i ＝ ιₐ 0ℚ
      v-is-zero = square-at-most-zero (v i) square-is-at-most-zero ∙ 0ℝ-is-ιₐ

  A-is-positive : 0ℝ < A
  A-is-positive = markov A (λ k → h z (fixed-if-A-is-at-most-zero k))

  a : ℝ
  a = inverse A A-is-positive

  scale-by-A : (X : ℝ) → (X * a) * A ＝ X
  scale-by-A X =
   *-assoc X a A ∙ ap (X *_) (inverse-law A A-is-positive) ∙ *-right-unit X

  β γ D s t : ℝ
  β = B * a
  γ = (1ℝ + (- U)) * a
  D = β * β + γ
  s = square-root D
  t = s + (- β)

  point : Fin n → ℝ
  point i = u i + t * v i

  one-minus-U-is-nonneg : 0ℝ ≤ 1ℝ + (- U)
  one-minus-U-is-nonneg =
   transport (_≤ 1ℝ + (- U)) (+-right-inverse U ∙ 0ℝ-is-ιₐ ⁻¹)
    (sum-≤ U 1ℝ (- U) (- U) (pr₂ (f z)) (ℝ≤-refl (- U)))

  γ-is-nonneg : 0ℝ ≤ γ
  γ-is-nonneg =
   products-of-nonnegatives-are-nonneg (1ℝ + (- U)) a one-minus-U-is-nonneg
                 (inverse-is-nonneg A A-is-positive)

  D-is-nonneg : 0ℝ ≤ D
  D-is-nonneg = transport (_≤ D) (plus-zero (ιₐ 0ℚ) ∙ 0ℝ-is-ιₐ ⁻¹)
                 (sum-≤ (ιₐ 0ℚ) (β * β) (ιₐ 0ℚ) γ (squares-are-nonneg' β)
                   (transport (_≤ γ) 0ℝ-is-ιₐ γ-is-nonneg))

  s-squared : s * s ＝ D
  s-squared = square-root-squared D D-is-nonneg

  on-the-sphere : squared-norm point ＝ 1ℝ
  on-the-sphere =
   squared-norm point              ＝⟨ squared-norm-of-shifted u v t ⟩
   U + (B * (t + t) + A * (t * t)) ＝⟨ ap (U +_) middle ⟩
   U + (1ℝ + (- U))                ＝⟨ plus-difference U 1ℝ ⟩
   1ℝ                              ∎
   where
    I : (β * A) * (t + t) ＝ A * (β * (t + t))
    I = ap (_* (t + t)) (*-comm β A) ∙ *-assoc A β (t + t)

    II : s * s + (- (β * β)) ＝ γ
    II = ap (_+ (- (β * β))) (s-squared ∙ +-comm (β * β) γ)
         ∙ plus-minus-cancel γ (β * β)

    middle : B * (t + t) + A * (t * t) ＝ 1ℝ + (- U)
    middle =
     B * (t + t) + A * (t * t)
      ＝⟨ ap (λ y → y * (t + t) + A * (t * t)) (scale-by-A B ⁻¹) ⟩
     (β * A) * (t + t) + A * (t * t)       ＝⟨ ap (_+ A * (t * t)) I ⟩
     A * (β * (t + t)) + A * (t * t)
      ＝⟨ *-left-distributive A (β * (t + t)) (t * t) ⁻¹ ⟩
     A * (β * (t + t) + t * t)
      ＝⟨ ap (A *_) (completing-the-square t β) ⟩
     A * ((t + β) * (t + β) + (- (β * β)))
      ＝⟨ ap (λ y → A * (y * y + (- (β * β))))
             (minus-plus-cancel s β) ⟩
     A * (s * s + (- (β * β)))             ＝⟨ ap (A *_) II ⟩
     A * γ
      ＝⟨ *-comm A γ ∙ scale-by-A (1ℝ + (- U)) ⟩
     1ℝ + (- U)                            ∎

  module _ (e : squared-norm w ＝ 1ℝ) where

   expansion : squared-norm w ＝ U + (B * (1ℝ + 1ℝ) + A * (1ℝ * 1ℝ))
   expansion = ap squared-norm (shifted-one ⁻¹) ∙ squared-norm-of-shifted u v 1ℝ

   E₁ : B * (1ℝ + 1ℝ) + A * (1ℝ * 1ℝ) ＝ 1ℝ + (- U)
   E₁ = X               ＝⟨ plus-minus-cancel X U ⁻¹ ⟩
        (X + U) + (- U) ＝⟨ ap (_+ (- U)) (+-comm X U ∙ expansion ⁻¹ ∙ e) ⟩
        1ℝ + (- U)      ∎
    where
     X : ℝ
     X = B * (1ℝ + 1ℝ) + A * (1ℝ * 1ℝ)

   E₂ : γ ＝ β * (1ℝ + 1ℝ) + 1ℝ * 1ℝ
   E₂ = (1ℝ + (- U)) * a                          ＝⟨ ap (_* a) (E₁ ⁻¹) ⟩
        (B * (1ℝ + 1ℝ) + A * (1ℝ * 1ℝ)) * a
         ＝⟨ *-right-distributive (B * (1ℝ + 1ℝ))
              (A * (1ℝ * 1ℝ)) a ⟩
        (B * (1ℝ + 1ℝ)) * a + (A * (1ℝ * 1ℝ)) * a ＝⟨ ap₂ _+_ I II ⟩
        β * (1ℝ + 1ℝ) + 1ℝ * 1ℝ                   ∎
    where
     I : (B * (1ℝ + 1ℝ)) * a ＝ β * (1ℝ + 1ℝ)
     I = *-assoc B (1ℝ + 1ℝ) a ∙ ap (B *_) (*-comm (1ℝ + 1ℝ) a)
         ∙ *-assoc B a (1ℝ + 1ℝ) ⁻¹

     II : (A * (1ℝ * 1ℝ)) * a ＝ 1ℝ * 1ℝ
     II =
      *-assoc A (1ℝ * 1ℝ) a ∙ *-comm A ((1ℝ * 1ℝ) * a) ∙ scale-by-A (1ℝ * 1ℝ)

   E₃ : (1ℝ + β) * (1ℝ + β) ＝ D
   E₃ = (1ℝ + β) * (1ℝ + β)
        ＝⟨ minus-plus-cancel ((1ℝ + β) * (1ℝ + β))
             (β * β) ⁻¹ ⟩
        ((1ℝ + β) * (1ℝ + β) + (- (β * β))) + β * β
         ＝⟨ ap (_+ β * β)
              (completing-the-square 1ℝ β ⁻¹) ⟩
        (β * (1ℝ + 1ℝ) + 1ℝ * 1ℝ) + β * β           ＝⟨ ap (_+ β * β) (E₂ ⁻¹) ⟩
        γ + β * β                                    ＝⟨ +-comm γ (β * β) ⟩
        D                                            ∎

   E₄ : 0ℝ ≤ 1ℝ + β
   E₄ =
    nonneg-from-double (1ℝ + β) (transport (0ℝ ≤_) double γ-plus-one-is-nonneg)
    where
     twice : (β * (1ℝ + 1ℝ) + 1ℝ * 1ℝ) + 1ℝ ＝ (1ℝ + β) + (1ℝ + β)
     twice =
      (β * (1ℝ + 1ℝ) + 1ℝ * 1ℝ) + 1ℝ ＝⟨ ap (λ y → (y + 1ℝ * 1ℝ) + 1ℝ)
                                            (*-left-distributive β 1ℝ 1ℝ
                                             ∙ ap₂ _+_ (*-right-unit β)
                                                (*-right-unit β)) ⟩
      ((β + β) + 1ℝ * 1ℝ) + 1ℝ
       ＝⟨ ap (λ y → ((β + β) + y) + 1ℝ) (*-right-unit 1ℝ) ⟩
      ((β + β) + 1ℝ) + 1ℝ            ＝⟨ +-assoc (β + β) 1ℝ 1ℝ ⟩
      (β + β) + (1ℝ + 1ℝ)            ＝⟨ interchange β β 1ℝ 1ℝ ⟩
      (β + 1ℝ) + (β + 1ℝ)            ＝⟨ ap₂ _+_ (+-comm β 1ℝ) (+-comm β 1ℝ) ⟩
      (1ℝ + β) + (1ℝ + β)            ∎

     double : γ + 1ℝ ＝ (1ℝ + β) + (1ℝ + β)
     double = ap (_+ 1ℝ) E₂ ∙ twice

     γ-plus-one-is-nonneg : 0ℝ ≤ γ + 1ℝ
     γ-plus-one-is-nonneg =
      transport (_≤ γ + 1ℝ) (plus-zero (ιₐ 0ℚ) ∙ 0ℝ-is-ιₐ ⁻¹)
       (sum-≤ (ιₐ 0ℚ) γ (ιₐ 0ℚ) 1ℝ (transport (_≤ γ) 0ℝ-is-ιₐ γ-is-nonneg)
         (transport (ιₐ 0ℚ ≤_) (1ℝ-is-ιₐ ⁻¹)
           (ιₐ-≤-ιₐ 0ℚ 1ℚ (ℚ<-coarser-than-≤ 0ℚ 1ℚ 0<1))))

   E₅ : s ＝ 1ℝ + β
   E₅ = nonneg-square-roots-are-unique s (1ℝ + β) (square-root-is-nonneg D) E₄
         (s-squared ∙ E₃ ⁻¹)

   E₆ : t ＝ 1ℝ
   E₆ = ap (_+ (- β)) E₅ ∙ plus-minus-cancel 1ℝ β

   fixes : point ＝ w
   fixes = dfunext fe (λ i → ap (λ y → u i + y * v i) E₆) ∙ shifted-one

 retraction : Ball n → Sphere n
 retraction z = at.point z , at.on-the-sphere z

 retraction-of-the-inclusion : Retraction-Of-The-Sphere-Inclusion n
 retraction-of-the-inclusion = retraction , γ
  where
   γ : (x : Sphere n) → retraction (sphere-to-ball x) ＝ x
   γ (x , e) =
    to-subtype-＝ (λ y → ℝ-is-set) (at.fixes (sphere-to-ball (x , e)) e)

 sphere-is-a-retract : retract (Sphere n) of (Ball n)
 sphere-is-a-retract =
  retractions-of-the-inclusion-give-retracts retraction-of-the-inclusion

Analytic-Markov-gives-literal-Lemma-12-3
 : Analytic-Markov → (n : ℕ) → Literal-Lemma-12-3-for-the-ball n
Analytic-Markov-gives-literal-Lemma-12-3 markov n f h =
 retraction-onto-the-sphere.retraction-of-the-inclusion markov f h

Analytic-Markov-gives-Lemma-12-3 : Analytic-Markov → (n : ℕ)
                                 → Lemma-12-3-for-the-ball n
Analytic-Markov-gives-Lemma-12-3 markov n f h =
 retractions-of-the-inclusion-give-retracts
  (Analytic-Markov-gives-literal-Lemma-12-3 markov n f h)

\end{code}
