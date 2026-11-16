Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. See the AI disclosure in
gist.RealCohesion.index.

Extension to ℝⁿ of a function known at sample points of rational boxes.

Fix sample points u of some type P, each with a position in ℚⁿ and a
real value g u. Suppose that every open rational box around a real
point contains a sample point, that two such boxes contain a common
one, and that around every real point the values vary by less than any
given ε on the sample points of some box. Then a real number E x is
defined, for every real point x, by its Dedekind cuts:

 * p < E x if some open rational box (a , b) around x and some
   rational p' > p have p' < g u at every sample point u of (a , b);

 * E x < q if some open rational box (a , b) around x and some
   rational q' < q have g u < q' at every sample point u of (a , b).

The cuts are rounded by construction, disjoint because two boxes around
x have a common sample point, and inhabited and located by the small
oscillation. Two further facts hold for every such extension: E t is v
whenever the values at sample points near t tend to v
(extension-agrees-at), and E is continuous at every point, in the
coordinatewise strict form of gist.RealCohesion.ContinuityForms
(extension-is-continuous). And for any functions continuous at a
point, agreement at all rational points gives agreement at the point
(agree-at-a-continuity-point), and an inequality at all rational
points gives the inequality at the point (≤-at-a-continuity-point); it
is enough that the inequality holds at the rational points of some box
around the point (≤-near-a-continuity-point).

This is the construction of gist.RealCohesion.CrispExtensionOnBoxes
(gate G21), where the sample points are the crisp rational points and g
is a crisp map on them, made generic. That module is now an instance.
The other instances take all rational points as sample points and
extend operations on the rationals to the reals: multiplication
(gist.RealCohesion.RealMultiplication, gate G14). The module does not
use --cohesion, so that modules without it can use it.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.RationalBoxExtension
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import Fin.Type
open import Notation.CanonicalMap
open import Notation.Order
open import UF.Base
open import UF.Powerset
open import Rationals.Type
open import Rationals.Order
open import Rationals.Addition renaming (_+_ to _ℚ+_)
open import Rationals.Negation renaming (_-_ to _ℚ-_ ; -_ to ℚ-_)
open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import DedekindReals.Properties fe pe pt using (ℝ-arithmetically-located)
open import gist.RealCohesion.ContinuityForms fe pe pt
 using (Strictly-Within ; within-from-close ; close-from-within ;
        interval-gives-strictly-close ; strictly-close-below ;
         strictly-close-above ;
        below-by-less-than ; Coordinatewise-Strictly-Continuous)
open import gist.RealCohesion.FinVectors using (Fin-choice)
open import gist.RealCohesion.RationalArithmetic
 using (add-difference ; <-sub-right ; <-add-right ; ≤-sub-right ;
         widened-difference ;
        minus-plus)
open import gist.RealCohesion.RationalPoints fe pe pt
 using (ιₐ ; ιₐ-lower ; ιₐ-upper ; ιₐ-lower⁻¹ ; ιₐ-upper⁻¹)
open import gist.RealCohesion.RealLimits fe pe pt using (ρ ; ρ-is-positive)
open import gist.RealCohesion.RealOrder fe pe pt
 using (cuts-are-ordered ; not-below-and-above ; ℝ<-tight ; ℝ≤-refl)
open import gist.RealCohesion.RealLattice fe pe pt
 using (ℚ<ℝ-is-prop ; equal-if-lower-cuts-agree ; translate-up)
open import gist.RealCohesion.RealBalls fe pe pt

open PropositionalTruncation pt

\end{code}

Open rational boxes, as sets of rational points and as neighbourhoods
of real points. These were in gist.RealCohesion.CrispUniformContinuityOnBoxes
and gist.RealCohesion.CrispExtensionOnBoxes, which re-export them. Two
boxes around a real point have a common rational point; every real
point has boxes around it of any positive size, and the rational
points of such a box are strictly within its size of the point.

\begin{code}

In-Box : {n : ℕ} → (Fin n → ℚ) → (Fin n → ℚ) → (Fin n → ℚ) → 𝓤₀ ̇
In-Box {n} a b q = (i : Fin n) → (a i < q i) × (q i < b i)

Around : {n : ℕ} → (Fin n → ℚ) → (Fin n → ℚ) → (Fin n → ℝ) → 𝓤₀ ̇
Around {n} a b x = (i : Fin n) → (a i < x i) × (x i < b i)

common-point : {n : ℕ} (x : Fin n → ℝ) (a b a' b' : Fin n → ℚ)
             → Around a b x → Around a' b' x
             → ∃ r ꞉ (Fin n → ℚ) , In-Box a b r × In-Box a' b' r
common-point {n} x a b a' b' m m' =
 ∥∥-functor γ
  (Fin-choice pt n (λ i → common-rational-point (x i) (a i) (b i) (a' i) (b' i)
                            (pr₁ (m i)) (pr₂ (m i)) (pr₁ (m' i)) (pr₂ (m' i))))
 where
  γ :
   ((i : Fin n) → Σ r ꞉ ℚ , ((a i < r) × (r < b i)) × ((a' i < r) × (r < b' i)))
    → Σ r ꞉ (Fin n → ℚ) , In-Box a b r × In-Box a' b' r
  γ c = (λ i → pr₁ (c i)) , (λ i → pr₁ (pr₂ (c i))) , (λ i → pr₂ (pr₂ (c i)))

rational-point-in-box : {n : ℕ} (a b : Fin n → ℚ) (x : Fin n → ℝ) → Around a b x
                      → Σ r ꞉ (Fin n → ℚ) , In-Box a b r
rational-point-in-box {n} a b x m =
 (λ i → pr₁ (between i)) , (λ i → pr₂ (between i))
 where
  between : (i : Fin n) → Σ c ꞉ ℚ , (a i < c) × (c < b i)
  between i = ℚ-dense (a i) (b i)
               (cuts-are-ordered (x i) (a i) (b i) (pr₁ (m i)) (pr₂ (m i)))

Small-Box : {n : ℕ} → (Fin n → ℝ) → ℚ → 𝓤₀ ̇
Small-Box {n} x δ = Σ (a , b) ꞉ (Fin n → ℚ) × (Fin n → ℚ)
                  , Around a b x × ((i : Fin n) → b i ℚ- a i < δ)

small-box-around : {n : ℕ} (x : Fin n → ℝ) (δ : ℚ) → 0ℚ < δ → ∥ Small-Box x δ ∥
small-box-around {n} x δ l =
 ∥∥-functor γ (Fin-choice pt n (λ i → ℝ-arithmetically-located (x i) (δ , l)))
 where
  γ : ((i : Fin n) → Σ (c , e) ꞉ ℚ × ℚ , (c < x i < e) × (e ℚ- c < δ))
    → Small-Box x δ
  γ c = ((λ i → pr₁ (pr₁ (c i))) , (λ i → pr₂ (pr₁ (c i)))) ,
        (λ i → pr₁ (pr₂ (c i))) , (λ i → pr₂ (pr₂ (c i)))

within-in-a-small-box : {n : ℕ} (δ : ℚ) (a b r : Fin n → ℚ) (x : Fin n → ℝ)
                      → Around a b x → In-Box a b r
                      → ((i : Fin n) → b i ℚ- a i < δ)
                      → (i : Fin n) → Strictly-Within δ (ιₐ (r i)) (x i)
within-in-a-small-box δ a b r x m k w i =
 within-from-close δ (ιₐ (r i)) (x i)
  (interval-gives-strictly-close δ (a i) (b i) (ιₐ (r i)) (x i)
    (ιₐ-lower (a i) (r i) (pr₁ (k i))) (ιₐ-upper (r i) (b i) (pr₂ (k i)))
    (pr₁ (m i)) (pr₂ (m i)) (w i))

\end{code}

A rational interval around a real point t, of length less than
2⁻⁽ᴷ⁺¹⁾, whose rational points lie in a given interval (r , s) around
t. This was in gist.RealCohesion.CrispUniformContinuityOnBoxes, which
keeps its names for it.

\begin{code}

Box-Inside : (r s : ℚ) (t : ℝ) (K : ℕ) → 𝓤₀ ̇
Box-Inside r s t K =
 Σ (a , b) ꞉ ℚ × ℚ , (a < t) × (t < b) × (b ℚ- a < ρ K)
                   × ((q : ℚ) → a < q → q < b → (r < q) × (q < s))

box-inside : (r s : ℚ) (t : ℝ) (K : ℕ) → r < t → t < s → ∥ Box-Inside r s t K ∥
box-inside r s t K l l' = ∥∥-rec ∥∥-is-prop γ (ball-inside-interval r s t l l')
 where
  γ : (Σ δ₀ ꞉ ℚ , Ball-Inside r s t δ₀) → ∥ Box-Inside r s t K ∥
  γ (δ₀ , o₀ , f) =
   ∥∥-functor δ
    (ℝ-arithmetically-located t
      (minₐ (ρ K) δ₀ , minₐ-is-positive (ρ K) δ₀ (ρ-is-positive K) o₀))
   where
    δ : (Σ (a , b) ꞉ ℚ × ℚ , (a < t < b) × (b ℚ- a < minₐ (ρ K) δ₀))
      → Box-Inside r s t K
    δ ((a , b) , (m , m') , w) =
     (a , b) , m , m' ,
     ℚ<-≤-trans (b ℚ- a) (minₐ (ρ K) δ₀) (ρ K) w (minₐ-≤-left (ρ K) δ₀) ,
     (λ q o o' → ζ q (f (ιₐ q) (Close-from-interval δ₀ a b (ιₐ q) t
                                 (ιₐ-lower a q o) (ιₐ-upper q b o') m m'
                                 (ℚ<-≤-trans (b ℚ- a) (minₐ (ρ K) δ₀) δ₀ w
                                   (minₐ-≤-right (ρ K) δ₀)))))
     where
      ζ : (q : ℚ) → (r < ιₐ q) × (ιₐ q < s) → (r < q) × (q < s)
      ζ q (k , k') = ιₐ-lower⁻¹ r q k , ιₐ-upper⁻¹ q s k'

close-gives-within : (η : ℚ) (x y : ℝ) → Close η x y → Strictly-Within η x y
close-gives-within η x y c =
 ∥∥-rec (×-is-prop ∃-is-prop ∃-is-prop) γ (interval-from-Close η x y c)
 where
  γ : Common-Interval η x y → Strictly-Within η x y
  γ ((p , q) , k , k' , o , o' , w) =
   within-from-close η x y (interval-gives-strictly-close η p q x y k k' o o' w)

\end{code}

Continuous functions on ℝⁿ, in the coordinatewise strict form of
gist.RealCohesion.ContinuityForms. A larger tolerance is weaker;
projections and constants are continuous, and so are composites; and
two functions continuous at a point that agree at all rational points
agree at that point. The argument uses only the rational points of
some box around the point, so we give it in that form.

\begin{code}

margin-shifts : (p q δ δ' : ℚ) → q ℚ- p < δ' ℚ- δ
              → ((q ℚ+ δ) ℚ- p < δ') × (q ℚ- (p ℚ- δ) < δ')
margin-shifts p q δ δ' l =
 transport (_< δ') (I ⁻¹) II , transport (_< δ') (III ⁻¹) II
 where
  I : (q ℚ+ δ) ℚ- p ＝ (q ℚ- p) ℚ+ δ
  I =
   ℚ+-assoc q δ (ℚ- p) ∙ ap (q ℚ+_) (ℚ+-comm δ (ℚ- p)) ∙ ℚ+-assoc q (ℚ- p) δ ⁻¹

  II : (q ℚ- p) ℚ+ δ < δ'
  II = transport ((q ℚ- p) ℚ+ δ <_) (minus-plus δ' δ)
        (ℚ<-addition-preserves-order (q ℚ- p) (δ' ℚ- δ) δ l)

  III : q ℚ- (p ℚ- δ) ＝ (q ℚ- p) ℚ+ δ
  III =
   ap (q ℚ+_) (ℚ-minus-dist' p δ ∙ ℚ+-comm δ (ℚ- p)) ∙ ℚ+-assoc q (ℚ- p) δ ⁻¹

within-weakens : (δ δ' : ℚ) (y x : ℝ) → δ ≤ δ' → Strictly-Within δ y x
               → Strictly-Within δ' y x
within-weakens δ δ' y x l w =
 Cases (ℚ≤-split δ δ' l) strict
  (λ e → transport (λ - → Strictly-Within - y x) e w)
 where
  strict : δ < δ' → Strictly-Within δ' y x
  strict m = ∥∥-rec (×-is-prop ∃-is-prop ∃-is-prop) γ
              (ℝ-arithmetically-located x
                ((δ' ℚ- δ) , ℚ<-difference-positive δ δ' m))
   where
    γ : (Σ (p , q) ꞉ ℚ × ℚ , (p < x < q) × (q ℚ- p < δ' ℚ- δ))
      → Strictly-Within δ' y x
    γ ((p , q) , (k , k') , w') =
     within-from-close δ' y x
      (below-by-less-than δ' p (q ℚ+ δ) y x
        (strictly-close-above δ y x (pr₁ (close-from-within δ y x w)) q k') k
        (pr₁ (margin-shifts p q δ δ' w')) ,
       below-by-less-than δ' (p ℚ- δ) q x y k'
        (strictly-close-below δ y x (pr₂ (close-from-within δ y x w)) p k)
        (pr₂ (margin-shifts p q δ δ' w')))

projection-is-continuous : {m : ℕ} (i : Fin m) (x : Fin m → ℝ)
                         → Coordinatewise-Strictly-Continuous (λ y → y i) x
projection-is-continuous i x ε l = ∣ ε , l , (λ y w → w i) ∣

constant-is-continuous : {m : ℕ} (c : ℝ) (x : Fin m → ℝ)
                       → Coordinatewise-Strictly-Continuous (λ _ → c) x
constant-is-continuous c x ε l =
 ∣ ε , l ,
  (λ y w → within-from-close ε c c (translate-up c ε l , translate-up c ε l)) ∣

composition-is-continuous
 : {k m : ℕ} (F : (Fin k → ℝ) → ℝ) (G : Fin k → (Fin m → ℝ) → ℝ) (x : Fin m → ℝ)
 → Coordinatewise-Strictly-Continuous F (λ j → G j x)
 → ((j : Fin k) → Coordinatewise-Strictly-Continuous (G j) x)
 → Coordinatewise-Strictly-Continuous (λ y → F (λ j → G j y)) x
composition-is-continuous {k} {m} F G x cF cG ε l = ∥∥-rec ∃-is-prop γ (cF ε l)
 where
  γ : (Σ δ ꞉ ℚ , (0ℚ < δ)
               × ((y : Fin k → ℝ)
                  → ((j : Fin k) → Strictly-Within δ (y j) (G j x))
                                  → Strictly-Within ε (F y) (F (λ j → G j x))))
    → ∃ δ ꞉ ℚ , (0ℚ < δ)
              × ((y : Fin m → ℝ) → ((i : Fin m) → Strictly-Within δ (y i) (x i))
                                 → Strictly-Within ε (F (λ j → G j y))
                                    (F (λ j → G j x)))
  γ (δ , d , f) = ∥∥-functor ζ (Fin-choice pt k (λ j → cG j δ d))
   where
    ζ : ((j : Fin k) → Σ δⱼ ꞉ ℚ , (0ℚ < δⱼ)
                                × ((y : Fin m → ℝ) →
                                  ((i : Fin m) → Strictly-Within δⱼ (y i) (x i))
                                                   → Strictly-Within δ (G j y)
                                                      (G j x)))
      → Σ δ' ꞉ ℚ , (0ℚ < δ')
                 × ((y : Fin m → ℝ)
                    → ((i : Fin m) → Strictly-Within δ' (y i) (x i))
                                    → Strictly-Within ε (F (λ j → G j y))
                                       (F (λ j → G j x)))
    ζ c = Fin-minₐ (λ j → pr₁ (c j)) ,
          Fin-minₐ-is-positive (λ j → pr₁ (c j)) (λ j → pr₁ (pr₂ (c j))) ,
          (λ y w → f (λ j → G j y)
                     (λ j → pr₂ (pr₂ (c j)) y
                              (λ i → within-weakens (Fin-minₐ (λ j → pr₁ (c j)))
                                      (pr₁ (c j))
                                       (y i) (x i) (Fin-minₐ-≤ (λ j → pr₁ (c j))
                                                     j) (w i))))

margin-below : (r q η : ℚ) → η ≤ q ℚ- r → r ℚ+ η ≤ q
margin-below r q η l = transport ((r ℚ+ η) ≤_) (add-difference r q)
                        (ℚ≤-addition-preserves-order-left η (q ℚ- r) r l)

margin-above : (q s η : ℚ) → η ≤ s ℚ- q → q ≤ s ℚ- η
margin-above q s η l = ≤-sub-right q s η (margin-below q s η l)

separated-values-in-a-box
 : {n : ℕ} (F G : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (A B : Fin n → ℚ)
   (q r s η : ℚ)
 → Around A B x
 → F x < r → r < q → q < s → s < G x → 0ℚ < η → η ≤ q ℚ- r → η ≤ s ℚ- q
 → Coordinatewise-Strictly-Continuous F x
 → Coordinatewise-Strictly-Continuous G x
 → ((q : Fin n → ℚ) → In-Box A B q → G (λ i → ιₐ (q i)) ≤ F (λ i → ιₐ (q i)))
 → 𝟘 {𝓤₀}
separated-values-in-a-box {n} F G x A B q r s η around k m o o' l a b cF cG e =
 ∥∥-rec 𝟘-is-prop γ (binary-choice (cF η l) (cG η l))
 where
  γ : (Σ δ ꞉ ℚ , (0ℚ < δ)
               ×
               ((y : Fin n → ℝ) → ((i : Fin n) → Strictly-Within δ (y i) (x i))
                                → Strictly-Within η (F y) (F x)))
    × (Σ δ' ꞉ ℚ , (0ℚ < δ')
                × ((y : Fin n → ℝ)
                   → ((i : Fin n) → Strictly-Within δ' (y i) (x i))
                                   → Strictly-Within η (G y) (G x)))
    → 𝟘
  γ ((δ , d , f) , (δ' , d' , f')) =
   ∥∥-rec 𝟘-is-prop ζ
    (small-box-around x (minₐ δ δ') (minₐ-is-positive δ δ' d d'))
   where
    ζ : Small-Box x (minₐ δ δ') → 𝟘
    ζ ((a' , b') , mm , w) =
     ∥∥-rec 𝟘-is-prop θ (common-point x a' b' A B mm around)
     where
      θ : (Σ q' ꞉ (Fin n → ℚ) , In-Box a' b' q' × In-Box A B q') → 𝟘
      θ (q' , in-small , in-box) =
        not-below-and-above (F (λ i → ιₐ (q' i))) q
         (e q' in-box q
           (use-rounded-real-L' (G (λ i → ιₐ (q' i))) q (s ℚ- η)
             (margin-above q s η b)
             (strictly-close-below η (G (λ i → ιₐ (q' i))) (G x)
               (pr₂ (close-from-within η (G (λ i → ιₐ (q' i))) (G x)
                      (f' (λ i → ιₐ (q' i))
                        (λ i → within-weakens (minₐ δ δ') δ' (ιₐ (q' i)) (x i)
                                 (minₐ-≤-right δ δ') (near i)))))
               s o')))
         (use-rounded-real-R' (F (λ i → ιₐ (q' i))) (r ℚ+ η) q
           (margin-below r q η a)
           (strictly-close-above η (F (λ i → ιₐ (q' i))) (F x)
             (pr₁ (close-from-within η (F (λ i → ιₐ (q' i))) (F x)
                    (f (λ i → ιₐ (q' i))
                      (λ i → within-weakens (minₐ δ δ') δ (ιₐ (q' i)) (x i)
                                (minₐ-≤-left δ δ') (near i)))))
             r k))
         where
          near : (i : Fin n) → Strictly-Within (minₐ δ δ') (ιₐ (q' i)) (x i)
          near = within-in-a-small-box (minₐ δ δ') a' b' q' x mm in-small w

separated-values
 : {n : ℕ} (F G : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (q r s η : ℚ)
 → F x < r → r < q → q < s → s < G x → 0ℚ < η → η ≤ q ℚ- r → η ≤ s ℚ- q
 → Coordinatewise-Strictly-Continuous F x
 → Coordinatewise-Strictly-Continuous G x
 → ((q : Fin n → ℚ) → G (λ i → ιₐ (q i)) ≤ F (λ i → ιₐ (q i)))
 → 𝟘 {𝓤₀}
separated-values F G x q r s η k m o o' l a b cF cG e =
 ∥∥-rec 𝟘-is-prop γ (small-box-around x 1ℚ 0<1)
 where
  γ : Small-Box x 1ℚ → 𝟘
  γ ((A , B) , around , _) =
   separated-values-in-a-box F G x A B q r s η around k m o o' l a b cF cG
    (λ q' _ → e q')

not-below-near-a-continuity-point
 : {n : ℕ} (F G : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (A B : Fin n → ℚ)
 → Around A B x
 → Coordinatewise-Strictly-Continuous F x
 → Coordinatewise-Strictly-Continuous G x
 → ((q : Fin n → ℚ) → In-Box A B q → G (λ i → ιₐ (q i)) ≤ F (λ i → ιₐ (q i)))
 → ¬ (F x < G x)
not-below-near-a-continuity-point F G x A B around cF cG e l =
 ∥∥-rec 𝟘-is-prop γ l
 where
  γ : (Σ q ꞉ ℚ , (F x < q) × (q < G x)) → 𝟘
  γ (q , k , k') =
   ∥∥-rec 𝟘-is-prop δ
    (binary-choice
      (rounded-right-b (upper-cut-of (F x)) (rounded-from-real-R (F x)) q k)
                   (rounded-left-d (G x) q k'))
   where
    δ : (Σ r ꞉ ℚ , (r < q) × (F x < r)) × (Σ s ꞉ ℚ , q < s < G x) → 𝟘
    δ ((r , m , m') , (s , o , o')) =
     separated-values-in-a-box F G x A B q r s (minₐ (q ℚ- r) (s ℚ- q)) around
      m' m o o'
      (minₐ-is-positive (q ℚ- r) (s ℚ- q) (ℚ<-difference-positive r q m)
        (ℚ<-difference-positive q s o))
      (minₐ-≤-left (q ℚ- r) (s ℚ- q)) (minₐ-≤-right (q ℚ- r) (s ℚ- q)) cF cG e

not-below-at-a-continuity-point
 : {n : ℕ} (F G : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
 → Coordinatewise-Strictly-Continuous F x
 → Coordinatewise-Strictly-Continuous G x
 → ((q : Fin n → ℚ) → G (λ i → ιₐ (q i)) ≤ F (λ i → ιₐ (q i)))
 → ¬ (F x < G x)
not-below-at-a-continuity-point F G x cF cG e l =
 ∥∥-rec 𝟘-is-prop γ (small-box-around x 1ℚ 0<1)
 where
  γ : Small-Box x 1ℚ → 𝟘
  γ ((A , B) , around , _) =
   not-below-near-a-continuity-point F G x A B around cF cG (λ q _ → e q) l

agree-at-a-continuity-point
 : {n : ℕ} (F G : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
 → Coordinatewise-Strictly-Continuous F x
 → Coordinatewise-Strictly-Continuous G x
 → ((q : Fin n → ℚ) → F (λ i → ιₐ (q i)) ＝ G (λ i → ιₐ (q i)))
 → F x ＝ G x
agree-at-a-continuity-point F G x cF cG e =
 ℝ<-tight (F x) (G x)
  (not-below-at-a-continuity-point F G x cF cG (λ q → ＝-gives-≤ (e q ⁻¹)))
  (not-below-at-a-continuity-point G F x cG cF (λ q → ＝-gives-≤ (e q)))
 where
  ＝-gives-≤ : {y z : ℝ} → y ＝ z → y ≤ z
  ＝-gives-≤ {y} refl = ℝ≤-refl y

\end{code}

A real that is not below another is at most it (TypeTopology's
ℝ-not-less-is-greater-or-equal); so continuous functions that are
ordered at rational points are ordered at every point, and so are
continuous functions that are ordered at the rational points of some box
around the point.

\begin{code}

not-below-gives-≤ : (x y : ℝ) → ¬ (y < x) → x ≤ y
not-below-gives-≤ x y = ℝ-not-less-is-greater-or-equal y x

≤-at-a-continuity-point
 : {n : ℕ} (F G : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
 → Coordinatewise-Strictly-Continuous F x
 → Coordinatewise-Strictly-Continuous G x
 → ((q : Fin n → ℚ) → F (λ i → ιₐ (q i)) ≤ G (λ i → ιₐ (q i)))
 → F x ≤ G x
≤-at-a-continuity-point F G x cF cG h =
 not-below-gives-≤ (F x) (G x) (not-below-at-a-continuity-point G F x cG cF h)

≤-near-a-continuity-point
 : {n : ℕ} (F G : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (A B : Fin n → ℚ)
 → Around A B x
 → Coordinatewise-Strictly-Continuous F x
 → Coordinatewise-Strictly-Continuous G x
 → ((q : Fin n → ℚ) → In-Box A B q → F (λ i → ιₐ (q i)) ≤ G (λ i → ιₐ (q i)))
 → F x ≤ G x
≤-near-a-continuity-point F G x A B around cF cG h =
 not-below-gives-≤ (F x) (G x)
  (not-below-near-a-continuity-point G F x A B around cG cF h)

\end{code}

A rational bound used for continuity: an interval widened by e at both
ends twice, around a rational interval of length less than e, is
shorter than 8e.

\begin{code}

twice-widened-is-short
 : (s s' ε : ℚ) → 0ℚ < ε → s' ℚ- s < halfₐ (halfₐ (halfₐ ε))
 → ((s' ℚ+ halfₐ (halfₐ (halfₐ ε))) ℚ+ halfₐ (halfₐ (halfₐ ε)))
   ℚ- ((s ℚ- halfₐ (halfₐ (halfₐ ε))) ℚ- halfₐ (halfₐ (halfₐ ε))) < ε
twice-widened-is-short s s' ε l w =
 transport (_< ε) (I ⁻¹)
  (ℚ<-trans (((s' ℚ- s) ℚ+ halfₐ (halfₐ ε)) ℚ+ halfₐ (halfₐ ε))
            (halfₐ ε ℚ+ halfₐ (halfₐ ε)) ε
    (ℚ<-addition-preserves-order ((s' ℚ- s) ℚ+ halfₐ (halfₐ ε)) (halfₐ ε)
      (halfₐ (halfₐ ε))
      (transport (((s' ℚ- s) ℚ+ halfₐ (halfₐ ε)) <_) (halvesₐ-add-up (halfₐ ε))
        (ℚ<-addition-preserves-order (s' ℚ- s) (halfₐ (halfₐ ε))
          (halfₐ (halfₐ ε))
          (ℚ<-trans (s' ℚ- s) (halfₐ (halfₐ (halfₐ ε))) (halfₐ (halfₐ ε)) w
            (halfₐ-is-less (halfₐ (halfₐ ε)) q₄)))))
    (transport (halfₐ ε ℚ+ halfₐ (halfₐ ε) <_) (halvesₐ-add-up ε)
      (ℚ<-addition-preserves-order''' (halfₐ (halfₐ ε)) (halfₐ ε) (halfₐ ε)
        (halfₐ-is-less (halfₐ ε) q₂))))
 where
  q₂ : 0ℚ < halfₐ ε
  q₂ = halfₐ-is-positive ε l

  q₄ : 0ℚ < halfₐ (halfₐ ε)
  q₄ = halfₐ-is-positive (halfₐ ε) q₂

  I : ((s' ℚ+ halfₐ (halfₐ (halfₐ ε))) ℚ+ halfₐ (halfₐ (halfₐ ε)))
      ℚ- ((s ℚ- halfₐ (halfₐ (halfₐ ε))) ℚ- halfₐ (halfₐ (halfₐ ε)))
    ＝ ((s' ℚ- s) ℚ+ halfₐ (halfₐ ε)) ℚ+ halfₐ (halfₐ ε)
  I = widened-difference (s ℚ- halfₐ (halfₐ (halfₐ ε)))
       (s' ℚ+ halfₐ (halfₐ (halfₐ ε)))
       (halfₐ (halfₐ (halfₐ ε)))
    ∙ ap₂ _ℚ+_ (widened-difference s s' (halfₐ (halfₐ (halfₐ ε)))
                ∙ ap ((s' ℚ- s) ℚ+_) (halvesₐ-add-up (halfₐ (halfₐ ε))))
               (halvesₐ-add-up (halfₐ (halfₐ ε)))

\end{code}

The extension. We fix the sample points, their positions and values,
and the two facts about boxes; then the small oscillation.

\begin{code}

module extension-from-samples
        {n : ℕ}
        (P : 𝓤₀ ̇ )
        (position : P → Fin n → ℚ)
        (g : P → ℝ)
        (sample-in-box : (a b : Fin n → ℚ) (x : Fin n → ℝ) → Around a b x
                       → Σ u ꞉ P , In-Box a b (position u))
        (common-sample : (x : Fin n → ℝ) (a b a' b' : Fin n → ℚ)
                       → Around a b x → Around a' b' x
                       → ∃ u ꞉ P ,
                           In-Box a b (position u) × In-Box a' b' (position u))
       where

 Small-Oscillation : ℚ → (Fin n → ℚ) → (Fin n → ℚ) → 𝓤₀ ̇
 Small-Oscillation ε a b =
    (u v : P)
  → In-Box a b (position u) → In-Box a b (position v)
  → Close ε (g u) (g v)

 Has-Small-Oscillation : 𝓤₁ ̇
 Has-Small-Oscillation =
    (x : Fin n → ℝ) (ε : ℚ) → 0ℚ < ε
  →
  ∃ (a , b) ꞉ (Fin n → ℚ) × (Fin n → ℚ) , Around a b x × Small-Oscillation ε a b

 Lower-Bound Upper-Bound : (Fin n → ℚ) → (Fin n → ℚ) → ℚ → 𝓤₀ ̇
 Lower-Bound a b p = (u : P) → In-Box a b (position u) → p < g u
 Upper-Bound a b q = (u : P) → In-Box a b (position u) → g u < q

 lower-bound-from-oscillation
  : (ε : ℚ) (a b : Fin n → ℚ) (s : ℚ) (u : P)
  → Small-Oscillation ε a b → In-Box a b (position u) → s < g u
  → Lower-Bound a b (s ℚ- ε)
 lower-bound-from-oscillation ε a b s u osc m k v o =
  Close-below ε (g v) (g u) (osc v u o m) s k

 upper-bound-from-oscillation
  : (ε : ℚ) (a b : Fin n → ℚ) (s : ℚ) (u : P)
  → Small-Oscillation ε a b → In-Box a b (position u) → g u < s
  → Upper-Bound a b (s ℚ+ ε)
 upper-bound-from-oscillation ε a b s u osc m k v o =
  Close-above ε (g v) (g u) (osc v u o m) s k

 Below-Witness Above-Witness : (Fin n → ℝ) → ℚ → 𝓤₀ ̇
 Below-Witness x p = Σ (a , b , p') ꞉ (Fin n → ℚ) × (Fin n → ℚ) × ℚ
                   , Around a b x × (p < p') × Lower-Bound a b p'
 Above-Witness x q = Σ (a , b , q') ꞉ (Fin n → ℚ) × (Fin n → ℚ) × ℚ
                   , Around a b x × (q' < q) × Upper-Bound a b q'

 Below Above : (Fin n → ℝ) → ℚ → 𝓤₀ ̇
 Below x p = ∥ Below-Witness x p ∥
 Above x q = ∥ Above-Witness x q ∥

\end{code}

As in gist.RealCohesion.CrispExtension, witnesses are built by
functions whose rational arguments are variables, so that Agda does not
unfold rational arithmetic in their components.

\begin{code}

 below-witness : (x : Fin n → ℝ) (p : ℚ) (a b : Fin n → ℚ) (p' : ℚ)
               → Around a b x → p < p' → Lower-Bound a b p' → Below-Witness x p
 below-witness x p a b p' m o k = (a , b , p') , m , o , k

 above-witness : (x : Fin n → ℝ) (q : ℚ) (a b : Fin n → ℚ) (q' : ℚ)
               → Around a b x → q' < q → Upper-Bound a b q' → Above-Witness x q
 above-witness x q a b q' m o k = (a , b , q') , m , o , k

 below-by-one : (x : Fin n → ℝ) (a b : Fin n → ℚ) (s : ℚ) → Around a b x
              → Lower-Bound a b (s ℚ- 1ℚ) → Σ p ꞉ ℚ , Below x p
 below-by-one x a b s m k =
  (s ℚ- 1ℚ) ℚ- 1ℚ ,
  ∣ below-witness x ((s ℚ- 1ℚ) ℚ- 1ℚ) a b (s ℚ- 1ℚ) m
     (minus-positive-is-below (s ℚ- 1ℚ) 1ℚ 0<1) k ∣

 above-by-one : (x : Fin n → ℝ) (a b : Fin n → ℚ) (s : ℚ) → Around a b x
              → Upper-Bound a b (s ℚ+ 1ℚ) → Σ q ꞉ ℚ , Above x q
 above-by-one x a b s m k =
  (s ℚ+ 1ℚ) ℚ+ 1ℚ ,
  ∣ above-witness x ((s ℚ+ 1ℚ) ℚ+ 1ℚ) a b (s ℚ+ 1ℚ) m
     (ℚ<-addition-preserves-order'' (s ℚ+ 1ℚ) 1ℚ 0<1) k ∣

 below-from-margin : (x : Fin n → ℝ) (p : ℚ) (a b : Fin n → ℚ) (s ε : ℚ)
                   → Around a b x
                   → (p ℚ+ ε) < s → Lower-Bound a b (s ℚ- ε) → Below-Witness x p
 below-from-margin x p a b s ε m d k =
  below-witness x p a b (s ℚ- ε) m (<-sub-right p s ε d) k

 above-from-margin : (x : Fin n → ℝ) (q : ℚ) (a b : Fin n → ℚ) (s ε : ℚ)
                   → Around a b x
                   → s < (q ℚ- ε) → Upper-Bound a b (s ℚ+ ε) → Above-Witness x q
 above-from-margin x q a b s ε m d k =
  above-witness x q a b (s ℚ+ ε) m (<-add-right s q ε d) k

 below-from-oscillation
  : (x : Fin n → ℝ) (a b : Fin n → ℚ) → Around a b x → Small-Oscillation 1ℚ a b
  → ∃ p ꞉ ℚ , Below x p
 below-from-oscillation x a b m osc = γ (sample-in-box a b x m)
  where
   γ : (Σ u ꞉ P , In-Box a b (position u)) → ∃ p ꞉ ℚ , Below x p
   γ (u , o) = ∥∥-functor δ (inhabited-from-real-L (g u))
    where
     δ : (Σ s ꞉ ℚ , s < g u) → Σ p ꞉ ℚ , Below x p
     δ (s , k) =
      below-by-one x a b s m (lower-bound-from-oscillation 1ℚ a b s u osc o k)

 above-from-oscillation
  : (x : Fin n → ℝ) (a b : Fin n → ℚ) → Around a b x → Small-Oscillation 1ℚ a b
  → ∃ q ꞉ ℚ , Above x q
 above-from-oscillation x a b m osc = γ (sample-in-box a b x m)
  where
   γ : (Σ u ꞉ P , In-Box a b (position u)) → ∃ q ꞉ ℚ , Above x q
   γ (u , o) = ∥∥-functor δ (inhabited-from-real-R (g u))
    where
     δ : (Σ s ꞉ ℚ , g u < s) → Σ q ꞉ ℚ , Above x q
     δ (s , k) =
      above-by-one x a b s m (upper-bound-from-oscillation 1ℚ a b s u osc o k)

 Below-is-rounded : (x : Fin n → ℝ) (p : ℚ)
                  → Below x p ↔ (∃ p'' ꞉ ℚ , (p < p'') × Below x p'')
 Below-is-rounded x p = α , β
  where
   α : Below x p → ∃ p'' ꞉ ℚ , (p < p'') × Below x p''
   α = ∥∥-functor γ
    where
     γ : Below-Witness x p → Σ p'' ꞉ ℚ , (p < p'') × Below x p''
     γ ((a , b , p') , m , o , k) = δ (ℚ-dense p p' o)
      where
       δ : (Σ p'' ꞉ ℚ , (p < p'') × (p'' < p'))
         → Σ p'' ꞉ ℚ , (p < p'') × Below x p''
       δ (p'' , c , d) = p'' , c , ∣ below-witness x p'' a b p' m d k ∣

   β : (∃ p'' ꞉ ℚ , (p < p'') × Below x p'') → Below x p
   β = ∥∥-rec ∃-is-prop γ
    where
     γ : (Σ p'' ꞉ ℚ , (p < p'') × Below x p'') → Below x p
     γ (p'' , o , l) = ∥∥-functor δ l
      where
       δ : Below-Witness x p'' → Below-Witness x p
       δ ((a , b , p') , m , o' , k) =
        below-witness x p a b p' m (ℚ<-trans p p'' p' o o') k

 Above-is-rounded : (x : Fin n → ℝ) (q : ℚ)
                  → Above x q ↔ (∃ q'' ꞉ ℚ , (q'' < q) × Above x q'')
 Above-is-rounded x q = α , β
  where
   α : Above x q → ∃ q'' ꞉ ℚ , (q'' < q) × Above x q''
   α = ∥∥-functor γ
    where
     γ : Above-Witness x q → Σ q'' ꞉ ℚ , (q'' < q) × Above x q''
     γ ((a , b , q') , m , o , k) = δ (ℚ-dense q' q o)
      where
       δ : (Σ q'' ꞉ ℚ , (q' < q'') × (q'' < q))
         → Σ q'' ꞉ ℚ , (q'' < q) × Above x q''
       δ (q'' , c , d) = q'' , d , ∣ above-witness x q'' a b q' m c k ∣

   β : (∃ q'' ꞉ ℚ , (q'' < q) × Above x q'') → Above x q
   β = ∥∥-rec ∃-is-prop γ
    where
     γ : (Σ q'' ꞉ ℚ , (q'' < q) × Above x q'') → Above x q
     γ (q'' , o , l) = ∥∥-functor δ l
      where
       δ : Above-Witness x q'' → Above-Witness x q
       δ ((a , b , q') , m , o' , k) =
        above-witness x q a b q' m (ℚ<-trans q' q'' q o' o) k

 sample-bounds-are-ordered
  : (p q : ℚ) (a b : Fin n → ℚ) (p' : ℚ) (a' b' : Fin n → ℚ) (q' : ℚ)
  → p < p' → q' < q
  → Lower-Bound a b p' → Upper-Bound a' b' q'
  → (Σ u ꞉ P , In-Box a b (position u) × In-Box a' b' (position u))
  → p < q
 sample-bounds-are-ordered p q a b p' a' b' q' o o' k k' (u , c , c') =
  ℚ<-trans p p' q o
   (ℚ<-trans p' q' q (cuts-are-ordered (g u) p' q' (k u c) (k' u c')) o')

 Below-Above-disjoint : (x : Fin n → ℝ) (p q : ℚ) → Below x p × Above x q
                      → p < q
 Below-Above-disjoint x p q (l , r) =
  ∥∥-rec (ℚ<-is-prop p q) γ (binary-choice l r)
  where
   γ : Below-Witness x p × Above-Witness x q → p < q
   γ (((a , b , p') , m , o , k) , ((a' , b' , q') , m' , o' , k')) =
    ∥∥-rec (ℚ<-is-prop p q)
     (sample-bounds-are-ordered p q a b p' a' b' q' o o' k k')
     (common-sample x a b a' b' m m')

 located-from-oscillation
  : (x : Fin n → ℝ) (p q ε : ℚ) (a b : Fin n → ℚ)
  → (p ℚ+ ε) < (q ℚ- ε)
  → Around a b x
  → Small-Oscillation ε a b
  → Below x p ∨ Above x q
 located-from-oscillation x p q ε a b gap m osc = γ (sample-in-box a b x m)
  where
   γ : (Σ u ꞉ P , In-Box a b (position u)) → Below x p ∨ Above x q
   γ (u , o) = ∥∥-functor δ (ℝ-locatedness (g u) (p ℚ+ ε) (q ℚ- ε) gap)
    where
     δ : ((p ℚ+ ε) < g u) ∔ (g u < (q ℚ- ε)) → Below x p ∔ Above x q
     δ (inl c) = inl (∥∥-functor ζ (rounded-left-d (g u) (p ℚ+ ε) c))
      where
       ζ : (Σ s ꞉ ℚ , (p ℚ+ ε) < s < g u) → Below-Witness x p
       ζ (s , d , d') = below-from-margin x p a b s ε m d
                         (lower-bound-from-oscillation ε a b s u osc o d')
     δ (inr c) = inr (∥∥-functor ζ (rounded-right-b (upper-cut-of (g u))
                                     (rounded-from-real-R (g u)) (q ℚ- ε) c))
      where
       ζ : (Σ s ꞉ ℚ , (s < q ℚ- ε) × (g u < s)) → Above-Witness x q
       ζ (s , d , d') = above-from-margin x q a b s ε m d
                         (upper-bound-from-oscillation ε a b s u osc o d')

\end{code}

From now on, the small oscillation.

\begin{code}

 module with-small-oscillation
  (small-oscillation-around : Has-Small-Oscillation) where

  Below-is-inhabited : (x : Fin n → ℝ) → ∃ p ꞉ ℚ , Below x p
  Below-is-inhabited x = ∥∥-rec ∃-is-prop γ (small-oscillation-around x 1ℚ 0<1)
   where
    γ : (Σ (a , b) ꞉ (Fin n → ℚ) × (Fin n → ℚ) ,
          Around a b x × Small-Oscillation 1ℚ a b)
      → ∃ p ꞉ ℚ , Below x p
    γ ((a , b) , m , osc) = below-from-oscillation x a b m osc

  Above-is-inhabited : (x : Fin n → ℝ) → ∃ q ꞉ ℚ , Above x q
  Above-is-inhabited x = ∥∥-rec ∃-is-prop γ (small-oscillation-around x 1ℚ 0<1)
   where
    γ : (Σ (a , b) ꞉ (Fin n → ℚ) × (Fin n → ℚ) ,
          Around a b x × Small-Oscillation 1ℚ a b)
      → ∃ q ꞉ ℚ , Above x q
    γ ((a , b) , m , osc) = above-from-oscillation x a b m osc

  Below-Above-located : (x : Fin n → ℝ) (p q : ℚ) → p < q
                      → Below x p ∨ Above x q
  Below-Above-located x p q l =
   ∥∥-rec ∨-is-prop γ
    (small-oscillation-around x (halfₐ (halfₐ (q ℚ- p)))
      (quarter-is-positive (q ℚ- p) (ℚ<-difference-positive p q l)))
   where
    γ : (Σ (a , b) ꞉ (Fin n → ℚ) × (Fin n → ℚ)
                   , Around a b x
                   × Small-Oscillation (halfₐ (halfₐ (q ℚ- p))) a b)
      → Below x p ∨ Above x q
    γ ((a , b) , m , osc) =
     located-from-oscillation x p q (halfₐ (halfₐ (q ℚ- p))) a b
      (quarters-leave-a-gap p q l) m osc

  extension : (Fin n → ℝ) → ℝ
  extension x =
   ((λ p → Below x p , ∃-is-prop) , (λ q → Above x q , ∃-is-prop)) ,
                Below-is-inhabited x , Above-is-inhabited x ,
                Below-is-rounded x , Above-is-rounded x ,
                Below-Above-disjoint x , Below-Above-located x

\end{code}

Agreement. If, for every η > 0, the values at sample points within some
δ of t are within η of v, then the extension takes the value v at t.

\begin{code}

  Converges-To : (Fin n → ℝ) → ℝ → 𝓤₀ ̇
  Converges-To t v =
     (η : ℚ) → 0ℚ < η
   → ∃ δ ꞉ ℚ , (0ℚ < δ)
             × ((u : P)
                → ((i : Fin n) → Strictly-Within δ (ιₐ (position u i)) (t i))
                        → Strictly-Within η (g u) v)

  sample-near
   : (t : Fin n → ℝ) (a b : Fin n → ℚ) (δ : ℚ) → Around a b t → 0ℚ < δ
   → ∃ u ꞉ P , In-Box a b (position u)
             × ((i : Fin n) → Strictly-Within δ (ιₐ (position u i)) (t i))
  sample-near t a b δ m l = ∥∥-rec ∃-is-prop γ (small-box-around t δ l)
   where
    γ : Small-Box t δ
      → ∃ u ꞉ P , In-Box a b (position u)
                × ((i : Fin n) → Strictly-Within δ (ιₐ (position u i)) (t i))
    γ ((c , e) , m' , w) = ∥∥-functor ζ (common-sample t a b c e m m')
     where
      ζ : (Σ u ꞉ P , In-Box a b (position u) × In-Box c e (position u))
        → Σ u ꞉ P , In-Box a b (position u)
                  × ((i : Fin n) → Strictly-Within δ (ιₐ (position u i)) (t i))
      ζ (u , k , k') =
       u , k , within-in-a-small-box δ c e (position u) t m' k' w

  sample-contradiction
   : (t : Fin n → ℝ) (v : ℝ) (a b : Fin n → ℚ) (p' s δ : ℚ)
   → Lower-Bound a b p' → v < s
   → ((u : P) → ((i : Fin n) → Strictly-Within δ (ιₐ (position u i)) (t i))
              → Strictly-Within (p' ℚ- s) (g u) v)
   → (Σ u ꞉ P , In-Box a b (position u)
              × ((i : Fin n) → Strictly-Within δ (ιₐ (position u i)) (t i)))
   → 𝟘 {𝓤₀}
  sample-contradiction t v a b p' s δ k c f (u , o , cl) =
   not-below-and-above (g u) p' (k u o)
    (transport (g u <_) (add-difference s p')
      (strictly-close-above (p' ℚ- s) (g u) v
        (pr₁ (close-from-within (p' ℚ- s) (g u) v (f u cl))) s c))

  lower-cut-below-the-limit
   : (t : Fin n → ℝ) (v : ℝ) → Converges-To t v → (p : ℚ) → Below t p → p < v
  lower-cut-below-the-limit t v cv p = ∥∥-rec (ℚ<ℝ-is-prop p v) γ
   where
    γ : Below-Witness t p → p < v
    γ ((a , b , p') , m , o , k) =
     ∥∥-rec (ℚ<ℝ-is-prop p v) δ (ℝ-locatedness v p p' o)
     where
      δ : (p < v) ∔ (v < p') → p < v
      δ (inl c) = c
      δ (inr c) = 𝟘-elim (∥∥-rec 𝟘-is-prop ζ
                           (rounded-right-b (upper-cut-of v)
                             (rounded-from-real-R v) p' c))
       where
        ζ : (Σ s ꞉ ℚ , (s < p') × (v < s)) → 𝟘
        ζ (s , d , c') =
         ∥∥-rec 𝟘-is-prop θ (cv (p' ℚ- s) (ℚ<-difference-positive s p' d))
         where
          θ : (Σ δ ꞉ ℚ , (0ℚ < δ)
                       × ((u : P) → ((i : Fin n)
                         → Strictly-Within δ (ιₐ (position u i)) (t i))
                                  → Strictly-Within (p' ℚ- s) (g u) v))
            → 𝟘
          θ (δ , l , f) =
           ∥∥-rec 𝟘-is-prop (sample-contradiction t v a b p' s δ k c' f)
                           (sample-near t a b δ m l)

  lower-bound-near-the-limit
   : (t : Fin n → ℝ) (v : ℝ) (p p₂ δ : ℚ)
   → p < p₂ → p₂ < v
   → ((u : P) → ((i : Fin n) → Strictly-Within δ (ιₐ (position u i)) (t i))
              → Strictly-Within (halfₐ (p₂ ℚ- p)) (g u) v)
   → Small-Box t δ
   → Below-Witness t p
  lower-bound-near-the-limit t v p p₂ δ o o' f ((a , b) , m , w) =
   below-witness t p a b (p₂ ℚ- halfₐ (p₂ ℚ- p)) m (below-by-half-margin p p₂ o)
    (λ u e → strictly-close-below (halfₐ (p₂ ℚ- p)) (g u) v
              (pr₂ (close-from-within (halfₐ (p₂ ℚ- p)) (g u) v
                     (f u (within-in-a-small-box δ a b (position u) t m e w))))
              p₂ o')

  lower-cut-from-the-limit
   : (t : Fin n → ℝ) (v : ℝ) → Converges-To t v → (p : ℚ) → p < v → Below t p
  lower-cut-from-the-limit t v cv p l =
   ∥∥-rec ∃-is-prop γ (rounded-left-d v p l)
   where
    γ : (Σ p₂ ꞉ ℚ , p < p₂ < v) → Below t p
    γ (p₂ , o , o') =
     ∥∥-rec ∃-is-prop δ
      (cv (halfₐ (p₂ ℚ- p))
        (halfₐ-is-positive (p₂ ℚ- p) (ℚ<-difference-positive p p₂ o)))
     where
      δ : (Σ δ ꞉ ℚ , (0ℚ < δ)
                   × ((u : P) →
                     ((i : Fin n) → Strictly-Within δ (ιₐ (position u i)) (t i))
                              → Strictly-Within (halfₐ (p₂ ℚ- p)) (g u) v))
        → Below t p
      δ (δ' , l' , f) =
       ∥∥-functor (lower-bound-near-the-limit t v p p₂ δ' o o' f)
                         (small-box-around t δ' l')

  extension-agrees-at : (t : Fin n → ℝ) (v : ℝ) → Converges-To t v
                      → extension t ＝ v
  extension-agrees-at t v cv = equal-if-lower-cuts-agree (extension t) v
                                (lower-cut-below-the-limit t v cv)
                                 (lower-cut-from-the-limit t v cv)

\end{code}

Continuity. Around x, a box on which the values vary by less than ε/8;
inside it, a smaller box around x given by a rational margin in each
coordinate; the values of the extension at points of the smaller box lie
in a rational interval of length less than ε.

\begin{code}

  Margins : (Fin n → ℝ) → (Fin n → ℚ) → (Fin n → ℚ) → 𝓤₀ ̇
  Margins x a b = (i : Fin n) → Σ (a' , b') ꞉ ℚ × ℚ
                               , (a i < a') × (a' < x i) × (x i < b')
                               × (b' < b i)

  margins : (x : Fin n → ℝ) (a b : Fin n → ℚ) → Around a b x → ∥ Margins x a b ∥
  margins x a b m = Fin-choice pt n γ
   where
    γ : (i : Fin n) → ∥
     Σ (a' , b') ꞉ ℚ × ℚ , (a i < a') × (a' < x i) × (x i < b') × (b' < b i) ∥
    γ i = ∥∥-functor δ
           (binary-choice (rounded-left-d (x i) (a i) (pr₁ (m i)))
                          (rounded-right-b (upper-cut-of (x i))
                            (rounded-from-real-R (x i))
                            (b i) (pr₂ (m i))))
     where
      δ : (Σ a' ꞉ ℚ , a i < a' < x i) × (Σ b' ꞉ ℚ , (b' < b i) × (x i < b'))
        →
        Σ (a' , b') ꞉ ℚ × ℚ , (a i < a') × (a' < x i) × (x i < b') × (b' < b i)
      δ ((a' , k , k') , (b' , l , l')) = (a' , b') , k , k' , l' , l

  margin : {x : Fin n → ℝ} {a b : Fin n → ℚ} → Margins x a b → Fin n → ℚ
  margin {x} {a} {b} c i =
   minₐ (pr₁ (pr₁ (c i)) ℚ- a i) (b i ℚ- pr₂ (pr₁ (c i)))

  margin-is-positive : {x : Fin n → ℝ} {a b : Fin n → ℚ} (c : Margins x a b)
                     → (i : Fin n) → 0ℚ < margin c i
  margin-is-positive {x} {a} {b} c i =
   minₐ-is-positive (pr₁ (pr₁ (c i)) ℚ- a i) (b i ℚ- pr₂ (pr₁ (c i)))
    (ℚ<-difference-positive (a i) (pr₁ (pr₁ (c i))) (pr₁ (pr₂ (c i))))
    (ℚ<-difference-positive (pr₂ (pr₁ (c i))) (b i)
      (pr₂ (pr₂ (pr₂ (pr₂ (c i))))))

  inside-one-margin
   : (t r : ℝ) (aᵢ bᵢ a' b' δ : ℚ)
   → δ ≤ minₐ (a' ℚ- aᵢ) (bᵢ ℚ- b')
   → a' < t → t < b'
   → Strictly-Within δ r t
   → (aᵢ < r) × (r < bᵢ)
  inside-one-margin t r aᵢ bᵢ a' b' δ k o o' w =
   use-rounded-real-L' r aᵢ (a' ℚ- δ)
    (≤-sub-right aᵢ a' δ
      (transport ((aᵢ ℚ+ δ) ≤_) (add-difference aᵢ a')
        (ℚ≤-addition-preserves-order-left δ (a' ℚ- aᵢ) aᵢ
          (ℚ≤-trans δ (minₐ (a' ℚ- aᵢ) (bᵢ ℚ- b')) (a' ℚ- aᵢ) k
            (minₐ-≤-left (a' ℚ- aᵢ) (bᵢ ℚ- b'))))))
    (strictly-close-below δ r t (pr₂ (close-from-within δ r t w)) a' o) ,
   use-rounded-real-R' r (b' ℚ+ δ) bᵢ
    (transport ((b' ℚ+ δ) ≤_) (add-difference b' bᵢ)
      (ℚ≤-addition-preserves-order-left δ (bᵢ ℚ- b') b'
        (ℚ≤-trans δ (minₐ (a' ℚ- aᵢ) (bᵢ ℚ- b')) (bᵢ ℚ- b') k
          (minₐ-≤-right (a' ℚ- aᵢ) (bᵢ ℚ- b')))))
    (strictly-close-above δ r t (pr₁ (close-from-within δ r t w)) b' o')

  inside-the-margins
   : (x y : Fin n → ℝ) (a b : Fin n → ℚ) (c : Margins x a b)
   → ((i : Fin n) → Strictly-Within (Fin-minₐ (margin c)) (y i) (x i))
   → Around a b y
  inside-the-margins x y a b c w i =
   inside-one-margin (x i) (y i) (a i) (b i) (pr₁ (pr₁ (c i))) (pr₂ (pr₁ (c i)))
    (Fin-minₐ (margin c)) (Fin-minₐ-≤ (margin c) i)
    (pr₁ (pr₂ (pr₂ (c i)))) (pr₁ (pr₂ (pr₂ (pr₂ (c i))))) (w i)

  bounds-of-extension
   : (z : Fin n → ℝ) (a b : Fin n → ℚ) (s s' e : ℚ) → 0ℚ < e
   → Around a b z → Lower-Bound a b (s ℚ- e) → Upper-Bound a b (s' ℚ+ e)
   → ((s ℚ- e) ℚ- e < extension z) × (extension z < (s' ℚ+ e) ℚ+ e)
  bounds-of-extension z a b s s' e l m lb ub =
   ∣ below-witness z ((s ℚ- e) ℚ- e) a b (s ℚ- e) m
    (minus-positive-is-below (s ℚ- e) e l) lb ∣ ,
   ∣ above-witness z ((s' ℚ+ e) ℚ+ e) a b (s' ℚ+ e) m
    (ℚ<-addition-preserves-order'' (s' ℚ+ e) e l) ub ∣

  continuity-in-a-box
   : (x : Fin n → ℝ) (ε : ℚ) → 0ℚ < ε
   → (a b : Fin n → ℚ) → Around a b x
   → Small-Oscillation (halfₐ (halfₐ (halfₐ ε))) a b
   → (c : Margins x a b)
   → (y : Fin n → ℝ)
   → ((i : Fin n) → Strictly-Within (Fin-minₐ (margin c)) (y i) (x i))
   → Strictly-Within ε (extension y) (extension x)
  continuity-in-a-box x ε l a b m osc c y w =
   ∥∥-rec (×-is-prop ∃-is-prop ∃-is-prop) γ
    (ℝ-arithmetically-located (g (pr₁ u₀)) (halfₐ (halfₐ (halfₐ ε)) , e-pos))
   where
    e-pos : 0ℚ < halfₐ (halfₐ (halfₐ ε))
    e-pos = halfₐ-is-positive (halfₐ (halfₐ ε)) (quarter-is-positive ε l)

    u₀ : Σ u ꞉ P , In-Box a b (position u)
    u₀ = sample-in-box a b x m

    γ : (Σ (s , s') ꞉ ℚ × ℚ ,
          (s < g (pr₁ u₀) < s') × (s' ℚ- s < halfₐ (halfₐ (halfₐ ε))))
      → Strictly-Within ε (extension y) (extension x)
    γ ((s , s') , (k , k') , w') =
     within-from-close ε (extension y) (extension x)
      (interval-gives-strictly-close ε
        ((s ℚ- halfₐ (halfₐ (halfₐ ε))) ℚ- halfₐ (halfₐ (halfₐ ε)))
        ((s' ℚ+ halfₐ (halfₐ (halfₐ ε))) ℚ+ halfₐ (halfₐ (halfₐ ε)))
        (extension y) (extension x)
        (pr₁ by) (pr₂ by) (pr₁ bx) (pr₂ bx)
        (twice-widened-is-short s s' ε l w'))
     where
      lb : Lower-Bound a b (s ℚ- halfₐ (halfₐ (halfₐ ε)))
      lb = lower-bound-from-oscillation (halfₐ (halfₐ (halfₐ ε))) a b s (pr₁ u₀)
            osc (pr₂ u₀) k

      ub : Upper-Bound a b (s' ℚ+ halfₐ (halfₐ (halfₐ ε)))
      ub = upper-bound-from-oscillation (halfₐ (halfₐ (halfₐ ε))) a b s'
            (pr₁ u₀) osc (pr₂ u₀) k'

      by = bounds-of-extension y a b s s' (halfₐ (halfₐ (halfₐ ε))) e-pos
            (inside-the-margins x y a b c w) lb ub
      bx =
       bounds-of-extension x a b s s' (halfₐ (halfₐ (halfₐ ε))) e-pos m lb ub

  extension-is-continuous : (x : Fin n → ℝ)
                          → Coordinatewise-Strictly-Continuous extension x
  extension-is-continuous x ε l =
   ∥∥-rec ∃-is-prop γ
    (small-oscillation-around x (halfₐ (halfₐ (halfₐ ε)))
      (halfₐ-is-positive (halfₐ (halfₐ ε)) (quarter-is-positive ε l)))
   where
    γ : (Σ (a , b) ꞉ (Fin n → ℚ) × (Fin n → ℚ)
                   , Around a b x
                   × Small-Oscillation (halfₐ (halfₐ (halfₐ ε))) a b)
      → ∃ δ ꞉ ℚ , (0ℚ < δ)
                ×
                ((y : Fin n → ℝ) → ((i : Fin n) → Strictly-Within δ (y i) (x i))
                                 → Strictly-Within ε (extension y)
                                    (extension x))
    γ ((a , b) , m , osc) = ∥∥-functor δ (margins x a b m)
     where
      δ : Margins x a b
        → Σ δ ꞉ ℚ , (0ℚ < δ)
                  × ((y : Fin n → ℝ)
                     → ((i : Fin n) → Strictly-Within δ (y i) (x i))
                                     → Strictly-Within ε (extension y)
                                        (extension x))
      δ c = Fin-minₐ (margin c) ,
             Fin-minₐ-is-positive (margin c) (margin-is-positive c) ,
            continuity-in-a-box x ε l a b m osc c

  in-box-from-around : (u : P) (a b : Fin n → ℚ)
                     → Around a b (λ i → ιₐ (position u i))
                     → In-Box a b (position u)
  in-box-from-around u a b m i =
   ιₐ-lower⁻¹ (a i) (position u i) (pr₁ (m i)) ,
    ιₐ-upper⁻¹ (position u i) (b i) (pr₂ (m i))

  converges-at-a-sample : (u₀ : P)
                        → Converges-To (λ i → ιₐ (position u₀ i)) (g u₀)
  converges-at-a-sample u₀ η l =
   ∥∥-rec ∃-is-prop γ (small-oscillation-around (λ i → ιₐ (position u₀ i)) η l)
   where
    γ : (Σ (a , b) ꞉ (Fin n → ℚ) × (Fin n → ℚ)
                   , Around a b (λ i → ιₐ (position u₀ i))
                   × Small-Oscillation η a b)
      → ∃ δ ꞉ ℚ , (0ℚ < δ)
                × ((u : P) → ((i : Fin n)
                  → Strictly-Within δ (ιₐ (position u i)) (ιₐ (position u₀ i)))
                           → Strictly-Within η (g u) (g u₀))
    γ ((a , b) , m , osc) =
     ∥∥-functor ζ (margins (λ i → ιₐ (position u₀ i)) a b m)
     where
      ζ : Margins (λ i → ιₐ (position u₀ i)) a b
        → Σ δ ꞉ ℚ , (0ℚ < δ)
                  × ((u : P) → ((i : Fin n) → Strictly-Within δ
                                 (ιₐ (position u i)) (ιₐ (position u₀ i)))
                             → Strictly-Within η (g u) (g u₀))
      ζ c = Fin-minₐ (margin c) ,
             Fin-minₐ-is-positive (margin c) (margin-is-positive c) ,
            (λ u w → close-gives-within η (g u) (g u₀)
                      (osc u u₀
                        (in-box-from-around u a b
                          (inside-the-margins (λ i → ιₐ (position u₀ i))
                            (λ i → ιₐ (position u i))
                            a b c w))
                        (in-box-from-around u₀ a b m)))

  extension-at-samples : (u : P) → extension (λ i → ιₐ (position u i)) ＝ g u
  extension-at-samples u =
   extension-agrees-at (λ i → ιₐ (position u i)) (g u) (converges-at-a-sample u)

\end{code}
