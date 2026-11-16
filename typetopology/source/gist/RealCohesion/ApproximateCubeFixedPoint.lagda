Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. See the AI disclosure in
gist.RealCohesion.index.

Approximate fixed points on the cube: Theorem 4.3 of the write-up [1],
cube form, gate G12 of Claude Fable 5.2's blueprint addendum
[2, §6, D2 to D4].

The exact statement. Theorem 4.3: assume crisp excluded middle, Axiom
R♭ and Axiom T, let n ≥ 1 be crisp; then every map f : Dⁿ → Dⁿ, not
necessarily crisp, has rational approximate fixed points: for every
rational ε > 0 there merely is a rational point q of Dⁿ with
|f q - q| < ε.

The formal statement, cube-approximate-fixed-point, is that theorem
for the cube [-1,1]ⁿ in place of Dⁿ, with the supremum norm, for every
crisp n, relative to Kuhn's lemma in dimension n, a crisp hypothesis.
It is the target Target-4-3 of gist.RealCohesion.BrouwerStatements in
gist.RealCohesion.Theorems, for the native ♯, where it is also stated
in dimensions 0 and 1 with Kuhn's lemma discharged. The Euclidean ball
needs the retraction onto it; that, and Kuhn's lemma for general n,
are gate G14.

The proof is the write-up's, in the form of the addendum.

 * D2. For a map F from ℝⁿ to ℝⁿ and a rational ε, the margin of F at
   a point v is the minimum over i of (v i + ε) - F v i and
   F v i - (v i - ε); it is positive exactly when every coordinate of
   F v is within ε of that of v. The test sequence takes, at level m,
   the maximum of the margins at the grid points of level m. A
   positive finite maximum has a positive member, so a positive term
   of the test sequence of the clamped extension of f gives a rational
   approximate fixed point of f.

 * D3. If f is crisp, its clamped extension F has a fixed point x,
   with grid points of the levels μ j converging to x
   (gist.RealCohesion.CubeFixedPoint). The margin of F at x is
   positive, so by sequential hitting
   (gist.RealCohesion.FunctionalHitting) it is positive at one of
   these grid points, and then the test sequence is positive at its
   level. This uses Axiom R♭ and no crispness of ε.

 * D4. Under Axiom T, that some term of the test sequence is positive
   is codiscrete (Lemma 4.1, gist.RealCohesion.AxiomTObstruction), and
   Shulman's Theorem 3.3 (decrispify) passes from crisp maps to all
   maps (approximate-fixed-points-from-crisp-maps of
   gist.RealCohesion.BrouwerStatements).

The addendum scales the margin by a power of 2 for sequential hitting
with the hypothesis 1 ≤ h a; we use its form with the hypothesis
0 < h a, the remark after Theorem 7.4 of the write-up.

[1] Answers to some open problems in real-cohesive homotopy type
    theory. Research notes, seventh revision of 11 November 2026,
    Theorem 4.3 and its proof.
    references/C03-write-up-2026-11-11-seventh.tex
    references/C03a-write-up-seventh-README.txt

[2] Claude Fable 5.2. Formalization blueprint, addendum, revision 4 of
    11 November 2026.
    references/F14-brouwer-addendum-rev4.md

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import gist.CohesiveApartness.Flat
open import gist.RealCohesion.Sharp

module gist.RealCohesion.ApproximateCubeFixedPoint
        (@♭ fe : Fun-Ext)
        (@♭ pe : Prop-Ext)
        (@♭ pt : propositional-truncations-exist)
       where

open import Fin.Type
open import Naturals.Order hiding (max)
open import Notation.CanonicalMap
open import Notation.Order
open import Rationals.Addition renaming (_+_ to _ℚ+_)
open import Rationals.Negation renaming (_-_ to _ℚ-_ ; -_ to ℚ-_)
open import Rationals.Order
open import Rationals.Type
open import UF.Base using (happly)
open import DedekindReals.Order fe pe pt
open import DedekindReals.Type fe pe pt
open import gist.RealCohesion.BrouwerStatements fe pe pt
 using (ℝ^ ; in-cube ; Cube ; rational-point ; _is-within-2⁻_of_ ;
        has-rational-approximate-fixed-point ; Approximate-Cube-Fixed-Point ;
        approximate-fixed-points-from-crisp-maps)
open import gist.RealCohesion.CrispRationals
 using (Fin-cons ; Fin-cons-of-parts)
open import gist.RealCohesion.CubeFixedPoint fe pe pt
 using (on-ℝ^ ; on-ℝ^-is-in-cube ; on-ℝ^-agrees ; module function-form)
open import gist.RealCohesion.CubeGrid fe pe pt using (grid-points-are-in-cube)
open import gist.RealCohesion.FiniteChainQuotient fe pe pt using (Q)
open import gist.RealCohesion.FunctionalHitting fe pe pt
 using (positive-sequential-hitting-for-functionals)
open import gist.RealCohesion.KuhnLemma using (Kuhn-Lemma)
open import gist.RealCohesion.RationalGrid using (side ; grid-point)
open import gist.RealCohesion.RationalPoints fe pe pt using (ιₐ ; ιₐ-is-ι)
open import gist.RealCohesion.RealLattice fe pe pt
 using (max ; min ; ≤-max-left ; ≤-max-right ; ℝ≤-refl ; ιₐ-sum ; ιₐ-positive ;
        <-from-difference ; <-gives-positive-difference ; positive-max ;
         positive-min ;
        positive-min⁻¹ ; translate-up ; translate-down)
 renaming (_+_ to _ℝ+_ ; -_ to ℝ-_)

open PropositionalTruncation pt

\end{code}

Finite minima over Fin n, which gist.RealCohesion.RealLattice provides
since 12 November 2026 and this module re-exports, and finite maxima
over the index vectors a : Fin n → ℕ with a i ≤ N for all i. The
minimum over Fin 0 is 1/2, so that a positive minimum and positive
terms correspond in every dimension.

\begin{code}

open import gist.RealCohesion.RealLattice fe pe pt
 using (Fin-min ; Fin-min-is-positive ; positive-Fin-min) public

max-upto : (ℕ → ℝ) → ℕ → ℝ
max-upto h 0        = h 0
max-upto h (succ N) = max (max-upto h N) (h (succ N))

max-upto-is-above : (h : ℕ → ℝ) (N k : ℕ) → k ≤ N → h k ≤ max-upto h N
max-upto-is-above h 0        0 _ = ℝ≤-refl (h 0)
max-upto-is-above h 0 (succ k) l = 𝟘-elim l
max-upto-is-above h (succ N) k l = γ (≤-split k N l)
 where
  γ : (k ≤ N) ∔ (k ＝ succ N) → h k ≤ max-upto h (succ N)
  γ (inl m) = ℝ≤-trans (h k) (max-upto h N) (max-upto h (succ N))
               (max-upto-is-above h N k m)
                (≤-max-left (max-upto h N) (h (succ N)))
  γ (inr e) = transport (λ - → h - ≤ max-upto h (succ N)) (e ⁻¹)
               (≤-max-right (max-upto h N) (h (succ N)))

positive-max-upto : (h : ℕ → ℝ) (N : ℕ)
                  → 0ℝ < max-upto h N → ∃ k ꞉ ℕ , (k ≤ N) × (0ℝ < h k)
positive-max-upto h 0        l = ∣ 0 , ⋆ , l ∣
positive-max-upto h (succ N) l =
 ∥∥-rec ∃-is-prop γ (positive-max (max-upto h N) (h (succ N)) l)
 where
  γ : (0ℝ < max-upto h N) ∔ (0ℝ < h (succ N))
    → ∃ k ꞉ ℕ , (k ≤ succ N) × (0ℝ < h k)
  γ (inl m) = ∥∥-functor δ (positive-max-upto h N m)
   where
    δ : (Σ k ꞉ ℕ , (k ≤ N) × (0ℝ < h k)) → Σ k ꞉ ℕ , (k ≤ succ N) × (0ℝ < h k)
    δ (k , o , o') = k , ≤-trans k N (succ N) o (≤-succ N) , o'
  γ (inr m) = ∣ succ N , ≤-refl N , m ∣

vector-max : {n : ℕ} → ((Fin n → ℕ) → ℝ) → ℕ → ℝ
vector-max {0}      h N = h (λ i → 𝟘-elim i)
vector-max {succ n} h N =
 max-upto (λ c → vector-max (λ a → h (Fin-cons c a)) N) N

vector-max-is-above : {n : ℕ} (h : (Fin n → ℕ) → ℝ) (N : ℕ) (a : Fin n → ℕ)
                    → ((i : Fin n) → a i ≤ N) → h a ≤ vector-max h N
vector-max-is-above {0} h N a r =
 transport (λ - → h - ≤ h (λ i → 𝟘-elim i)) (dfunext fe (λ i → 𝟘-elim i))
  (ℝ≤-refl (h (λ i → 𝟘-elim i)))
vector-max-is-above {succ n} h N a r =
 ℝ≤-trans (h a) (vector-max (λ a' → h (Fin-cons (a 𝟎) a')) N) (vector-max h N)
  (transport (λ - → h - ≤ vector-max (λ a' → h (Fin-cons (a 𝟎) a')) N)
    (Fin-cons-of-parts fe a)
    (vector-max-is-above (λ a' → h (Fin-cons (a 𝟎) a')) N (a ∘ suc) (r ∘ suc)))
  (max-upto-is-above (λ c → vector-max (λ a' → h (Fin-cons c a')) N) N (a 𝟎)
    (r 𝟎))

positive-vector-max : {n : ℕ} (h : (Fin n → ℕ) → ℝ) (N : ℕ)
                    → 0ℝ < vector-max h N
                    → ∃ a ꞉ (Fin n → ℕ) , ((i : Fin n) → a i ≤ N) × (0ℝ < h a)
positive-vector-max {0}      h N l = ∣ (λ i → 𝟘-elim i) , (λ i → 𝟘-elim i) , l ∣
positive-vector-max {succ n} h N l =
 ∥∥-rec ∃-is-prop γ
  (positive-max-upto (λ c → vector-max (λ a → h (Fin-cons c a)) N) N l)
 where
  γ : (Σ c ꞉ ℕ , (c ≤ N) × (0ℝ < vector-max (λ a → h (Fin-cons c a)) N))
    → ∃ a ꞉ (Fin (succ n) → ℕ) , ((i : Fin (succ n)) → a i ≤ N) × (0ℝ < h a)
  γ (c , o , m) =
   ∥∥-functor δ (positive-vector-max (λ a → h (Fin-cons c a)) N m)
   where
    δ : (Σ a ꞉ (Fin n → ℕ) , ((i : Fin n) → a i ≤ N) × (0ℝ < h (Fin-cons c a)))
      → Σ a ꞉ (Fin (succ n) → ℕ) , ((i : Fin (succ n)) → a i ≤ N) × (0ℝ < h a)
    δ (a , r , m') = Fin-cons c a , ε , m'
     where
      ε : (i : Fin (succ n)) → Fin-cons c a i ≤ N
      ε 𝟎       = o
      ε (suc i) = r i

\end{code}

D2: the margin and the test sequence, for any map F from ℝⁿ to ℝⁿ and
any rational ε. At a rational point q, a positive margin gives the
two strict inequalities of has-rational-approximate-fixed-point.

\begin{code}

module _ {n : ℕ} (F : ℝ^ n → ℝ^ n) (ε : ℚ) where

 upper-gap lower-gap : ℝ^ n → Fin n → ℝ
 upper-gap v i = (v i ℝ+ ιₐ ε) ℝ+ (ℝ- F v i)
 lower-gap v i = F v i ℝ+ (ℝ- (v i ℝ+ ιₐ (ℚ- ε)))

 margin : ℝ^ n → ℝ
 margin v = Fin-min (λ i → min (upper-gap v i) (lower-gap v i))

 test : ℕ → ℝ
 test m =
  vector-max (λ a → margin (rational-point (grid-point m a))) (succ (side m))

 positive-margin-at-rational-points
  : (q : Fin n → ℚ) → 0ℝ < margin (rational-point q)
  → (i : Fin n) → (F (rational-point q) i < ι (q i ℚ+ ε))
                × (ι (q i ℚ- ε) < F (rational-point q) i)
 positive-margin-at-rational-points q l i =
  transport (F (rational-point q) i <_) I
   (<-from-difference (rational-point q i ℝ+ ιₐ ε) (F (rational-point q) i)
     (pr₁ (positive-min⁻¹ (upper-gap (rational-point q) i)
            (lower-gap (rational-point q) i) m))) ,
  transport (_< F (rational-point q) i) II
   (<-from-difference (F (rational-point q) i) (rational-point q i ℝ+ ιₐ (ℚ- ε))
     (pr₂ (positive-min⁻¹ (upper-gap (rational-point q) i)
            (lower-gap (rational-point q) i) m)))
  where
   m : 0ℝ
     < min (upper-gap (rational-point q) i) (lower-gap (rational-point q) i)
   m = positive-Fin-min (λ i →
     min (upper-gap (rational-point q) i) (lower-gap (rational-point q) i))
        l i

   I : rational-point q i ℝ+ ιₐ ε ＝ ι (q i ℚ+ ε)
   I = ap (_ℝ+ ιₐ ε) (ιₐ-is-ι (q i) ⁻¹) ∙ ιₐ-sum (q i) ε ∙ ιₐ-is-ι (q i ℚ+ ε)

   II : rational-point q i ℝ+ ιₐ (ℚ- ε) ＝ ι (q i ℚ- ε)
   II = ap (_ℝ+ ιₐ (ℚ- ε)) (ιₐ-is-ι (q i) ⁻¹) ∙ ιₐ-sum (q i) (ℚ- ε)
        ∙ ιₐ-is-ι (q i ℚ- ε)

approximate-fixed-points-from-positive-tests
 : {n : ℕ} (f : Cube n → Cube n) (ε : ℚ)
 → (∃ m ꞉ ℕ , 0ℝ < test (on-ℝ^ f) ε m)
 → has-rational-approximate-fixed-point f ε
approximate-fixed-points-from-positive-tests {n} f ε = ∥∥-rec ∃-is-prop γ
 where
  γ : (Σ m ꞉ ℕ , 0ℝ < test (on-ℝ^ f) ε m)
    → has-rational-approximate-fixed-point f ε
  γ (m , l) = ∥∥-functor δ
               (positive-vector-max
                 (λ a → margin (on-ℝ^ f) ε (rational-point (grid-point m a)))
                 (succ (side m)) l)
   where
    δ : (Σ a ꞉ (Fin n → ℕ) , ((i : Fin n) → a i ≤ succ (side m))
                            × (0ℝ < margin (on-ℝ^ f) ε
                                (rational-point (grid-point m a))))
      → Σ q ꞉ (Fin n → ℚ) , Σ c ꞉ in-cube (rational-point q)
          , ((i : Fin n) → (pr₁ (f (rational-point q , c)) i < ι (q i ℚ+ ε))
                         × (ι (q i ℚ- ε) < pr₁ (f (rational-point q , c)) i))
    δ (a , r , l') = grid-point m a , c , ε'
     where
      c : in-cube (rational-point (grid-point m a))
      c = grid-points-are-in-cube m a r

      ε' : (i : Fin n)
         → (pr₁ (f (rational-point (grid-point m a) , c)) i
            < ι (grid-point m a i ℚ+ ε))
         × (ι (grid-point m a i ℚ- ε)
            < pr₁ (f (rational-point (grid-point m a) , c)) i)
      ε' i = transport (λ w → (w i < ι (grid-point m a i ℚ+ ε))
                            × (ι (grid-point m a i ℚ- ε) < w i))
              (on-ℝ^-agrees f (rational-point (grid-point m a)) c)
              (positive-margin-at-rational-points (on-ℝ^ f) ε (grid-point m a)
                l' i)

\end{code}

D3, for any F with a fixed point y and grid points converging to y:
the margin at y is positive, so by sequential hitting it is positive
at one of the grid points, and then the test sequence is positive at
its level.

\begin{code}

module grid-hitting
        (ν : (k : ℝ → Q) (u v : ℝ) → k u ＝ k v)
        {n : ℕ}
        (F : ℝ^ n → ℝ^ n)
        (y : ℝ^ n)
        (y-is-fixed : F y ＝ y)
        (k : ℕ → ℕ)
        (b : ℕ → Fin n → ℕ)
        (b-in-range : (j : ℕ) (i : Fin n) → b j i ≤ succ (side (k j)))
        (converges : (j : ℕ)
         → rational-point (grid-point (k j) (b j)) is-within-2⁻ j of y)
       where

 margin-at-the-fixed-point : (ε : ℚ) → 0ℚ < ε → 0ℝ < margin F ε y
 margin-at-the-fixed-point ε l =
  Fin-min-is-positive (λ i → min (upper-gap F ε y i) (lower-gap F ε y i))
   (λ i → positive-min (upper-gap F ε y i) (lower-gap F ε y i) (I i) (II i))
  where
   I : (i : Fin n) → 0ℝ < upper-gap F ε y i
   I i = transport (λ w → 0ℝ < (y i ℝ+ ιₐ ε) ℝ+ (ℝ- w)) (happly y-is-fixed i ⁻¹)
          (<-gives-positive-difference (y i ℝ+ ιₐ ε) (y i)
            (translate-up (y i) ε l))

   II : (i : Fin n) → 0ℝ < lower-gap F ε y i
   II i =
    transport (λ w → 0ℝ < w ℝ+ (ℝ- (y i ℝ+ ιₐ (ℚ- ε)))) (happly y-is-fixed i ⁻¹)
           (<-gives-positive-difference (y i) (y i ℝ+ ιₐ (ℚ- ε))
             (translate-down (y i) ε l))

 tests-become-positive : (ε : ℚ) → 0ℚ < ε → ∃ m ꞉ ℕ , 0ℝ < test F ε m
 tests-become-positive ε l =
  ∥∥-functor γ
   (positive-sequential-hitting-for-functionals ν (Fin n) (margin F ε) y
     (λ j → rational-point (grid-point (k j) (b j))) converges
     (margin-at-the-fixed-point ε l))
  where
   γ : (Σ j ꞉ ℕ , 0ℝ < margin F ε (rational-point (grid-point (k j) (b j))))
     → Σ m ꞉ ℕ , 0ℝ < test F ε m
   γ (j , o) = k j ,
               ℝ<-≤-trans 0ℝ
                (margin F ε (rational-point (grid-point (k j) (b j))))
                (test F ε (k j)) o
                (vector-max-is-above
                  (λ a → margin F ε (rational-point (grid-point (k j) a)))
                  (succ (side (k j))) (b j) (b-in-range j))

\end{code}

D4: the theorem, for a sharp modality S, from crisp excluded middle,
the constancy of maps ℝ → Q, Axiom T and Kuhn's lemma in dimension n.
For a crisp map f the data of D3 are those of the crisp fixed point
of its clamped extension.

\begin{code}

module _ (S : Sharp-Modality) where

 open import gist.RealCohesion.AxiomTObstruction fe pe pt S
  using (Axiom-T ; Axiom-T-gives-positive-terms-are-codiscrete)

 cube-approximate-fixed-point
  : (@♭ cem : Crisp-EM 𝓤₀)
  → ((k : ℝ → Q) (u v : ℝ) → k u ＝ k v)
  → Axiom-T
  → {@♭ n : ℕ} (@♭ kuhn : Kuhn-Lemma n)
  → Approximate-Cube-Fixed-Point n
 cube-approximate-fixed-point cem ν T {n} kuhn =
  approximate-fixed-points-from-crisp-maps S n (λ f ε → test (on-ℝ^ f) ε)
   (Axiom-T-gives-positive-terms-are-codiscrete T)
   approximate-fixed-points-from-positive-tests
   φ
  where
   φ : (@♭ f : Cube n → Cube n) (ε : ℚ) → 0ℚ < ε
     → ∃ m ꞉ ℕ , 0ℝ < test (on-ℝ^ f) ε m
   φ f = grid-hitting.tests-become-positive ν (on-ℝ^ f)
          (function-form.x cem kuhn (on-ℝ^ f))
          (function-form.x-is-fixed cem kuhn (on-ℝ^ f) ν (on-ℝ^-is-in-cube f))
          (function-form.μ cem kuhn (on-ℝ^ f))
          (λ j → function-form.base cem kuhn (on-ℝ^ f)
                  (function-form.μ cem kuhn (on-ℝ^ f) j))
          (λ j → function-form.base-in-range cem kuhn (on-ℝ^ f)
                  (function-form.μ cem kuhn (on-ℝ^ f) j))
          (function-form.grid-points-converge cem kuhn (on-ℝ^ f))

\end{code}
