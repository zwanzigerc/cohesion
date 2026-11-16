Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. See the AI disclosure in
gist.RealCohesion.index.

Multiplication of real numbers (gate G14, step E1).

At TypeTopology commit 52ed2eb, DedekindReals.Multiplication begins
the definition of the HoTT book and leaves it unfinished, commented
out. Fable's plan (ADDENDUM-2, G14) suggests transcribing the
definition from agda-unimath instead; there it rests on the arithmetic
of closed rational intervals, about 4200 lines with the module itself.
We define the product as a continuous extension instead, with the
construction of gist.RealCohesion.RationalBoxExtension, which the
library already has (gate G21):

 * the sample points are all points c of ℚ², with value c₀ c₁;

 * around every point of ℝ², the products of rational points vary by
   less than any ε > 0 on some small enough box
   (gist.RealCohesion.RationalProducts).

So p < x y if some open rational box around (x , y) and some p' > p
have p' < c₀ c₁ at every rational point c of the box, and dually for
x y < q. This agrees with the product of rationals, and is continuous.
The laws of a commutative ring follow: both sides of each law are
continuous functions of the variables that agree at rational points,
so they agree everywhere (agree-at-a-continuity-point).

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.RealMultiplication
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import Fin.Type
open import Notation.Order
open import UF.Base
open import UF.Powerset using (_⊆_)
open import Rationals.Type
open import Rationals.Abs
open import Rationals.Order
open import Rationals.Addition renaming (_+_ to _ℚ+_)
open import Rationals.Negation renaming (_-_ to _ℚ-_ ; -_ to ℚ-_)
open import Rationals.Multiplication renaming (_*_ to _ℚ*_)
open import Rationals.MinMax
 using (max ; max≤ ; max≤' ; min ; min≤ ; min≤' ; max-to-≤ ; min-to-≤)
open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import gist.RealCohesion.ContinuityForms fe pe pt
 using (Coordinatewise-Strictly-Continuous ; Box-Continuous ;
         box-gives-coordinatewise-strict ;
        Strictly-Close ; strictly-close-below ; strictly-close-above)
open import gist.RealCohesion.FinVectors using (Fin-cons ; Fin-pair)
open import gist.RealCohesion.RationalArithmetic using (abs-gives-ball)
open import gist.RealCohesion.RationalPoints fe pe pt
 using (ιₐ ; ιₐ-is-ι ; ιₐ-lower ; ιₐ-upper ; ιₐ-lower⁻¹ ; ιₐ-upper⁻¹)
open import gist.RealCohesion.RationalProducts
open import gist.RealCohesion.RealBalls fe pe pt
 using
  (Close-from-interval ; minₐ ; minₐ-≤-left ; minₐ-≤-right ; minₐ-is-positive ;
   halfₐ ; halfₐ-is-positive ; halfₐ-is-less ; quarter-is-positive ;
    twice-a-quarter)
open import gist.RealCohesion.RealOrder fe pe pt using (cuts-are-ordered)
open import gist.RealCohesion.RealLattice fe pe pt
 using (_+_ ; below-sum' ; sum-below' ; below-sum⁻¹ ; sum-below⁻¹ ; ιₐ-sum ;
         ιₐ-≤-ιₐ ;
        ℚ<ℝ-is-prop ; ℝ<ℚ-is-prop ; -_ ; below-neg ; neg-below ; below-neg⁻¹ ;
         neg-below⁻¹ ;
        equal-if-lower-cuts-agree)
open import gist.RealCohesion.RationalBoxExtension fe pe pt
 using (In-Box ; Around ; Small-Box ; small-box-around ; rational-point-in-box ;
        common-point ; module extension-from-samples ;
         composition-is-continuous ;
        projection-is-continuous ; constant-is-continuous ;
        agree-at-a-continuity-point ; ≤-at-a-continuity-point ; margin-below ;
         margin-above)

open PropositionalTruncation pt

\end{code}

The sample points and their values.

\begin{code}

product-at : (Fin 2 → ℚ) → ℝ
product-at c = ιₐ (c 𝟎 ℚ* c 𝟏)

open extension-from-samples {2} (Fin 2 → ℚ) id product-at rational-point-in-box
 common-point

\end{code}

The small oscillation. Around x, a first box (a , b) bounds the
coordinates by M; inside it, the products at two rational points of a
box with sides shorter than δ and than 1 differ by at most δ M + M δ,
which is less than η = ε/4 for δ small; and the products at the
rational points of that box then lie in an interval of length 2η < ε.

\begin{code}

products-vary-little : Has-Small-Oscillation
products-vary-little x ε l = ∥∥-rec ∃-is-prop γ (small-box-around x 1ℚ 0<1)
 where
  η : ℚ
  η = halfₐ (halfₐ ε)

  η-is-positive : 0ℚ < η
  η-is-positive = quarter-is-positive ε l

  γ : Small-Box x 1ℚ
    → ∃ (a' , b') ꞉ (Fin 2 → ℚ) × (Fin 2 → ℚ) ,
        Around a' b' x × Small-Oscillation ε a' b'
  γ ((a , b) , m , _) =
   ∥∥-functor ζ
    (small-box-around x (minₐ δ 1ℚ) (minₐ-is-positive δ 1ℚ δ-is-positive 0<1))
   where
    M : ℚ
    M = box-bound a b

    small : Σ δ ꞉ ℚ , (0ℚ < δ) × ((δ ℚ* M) ℚ+ (M ℚ* δ) < η)
    small = small-enough M η (box-bound-is-nonneg a b) η-is-positive

    δ : ℚ
    δ = pr₁ small

    δ-is-positive : 0ℚ < δ
    δ-is-positive = pr₁ (pr₂ small)

    δ-is-small : (δ ℚ* M) ℚ+ (M ℚ* δ) < η
    δ-is-small = pr₂ (pr₂ small)

    ζ : Small-Box x (minₐ δ 1ℚ)
      → Σ (a' , b') ꞉ (Fin 2 → ℚ) × (Fin 2 → ℚ) ,
          Around a' b' x × Small-Oscillation ε a' b'
    ζ ((a' , b') , m' , w) = (a' , b') , m' , oscillation
     where
      k : (i : Fin 2) → a' i < b i
      k i = cuts-are-ordered (x i) (a' i) (b i) (pr₁ (m' i)) (pr₂ (m i))

      k' : (i : Fin 2) → a i < b' i
      k' i = cuts-are-ordered (x i) (a i) (b' i) (pr₁ (m i)) (pr₂ (m' i))

      w₁ : (i : Fin 2) → b' i ℚ- a' i < 1ℚ
      w₁ i = ℚ<-≤-trans (b' i ℚ- a' i) (minₐ δ 1ℚ) 1ℚ (w i) (minₐ-≤-right δ 1ℚ)

      wδ : (i : Fin 2) → b' i ℚ- a' i < δ
      wδ i = ℚ<-≤-trans (b' i ℚ- a' i) (minₐ δ 1ℚ) δ (w i) (minₐ-≤-left δ 1ℚ)

      oscillation : Small-Oscillation ε a' b'
      oscillation u v mu mv =
       Close-from-interval ε (r ℚ- η) (r ℚ+ η) (ιₐ r) (ιₐ s)
        (ιₐ-lower (r ℚ- η) r (ℚ<-subtraction-preserves-order r η η-is-positive))
        (ιₐ-upper r (r ℚ+ η) (ℚ<-addition-preserves-order'' r η η-is-positive))
        (ιₐ-lower (r ℚ- η) s (pr₁ II))
        (ιₐ-upper s (r ℚ+ η) (pr₂ II))
        (widened-point r η ε (twice-a-quarter η ε l (ℚ≤-refl η)))
       where
        r s : ℚ
        r = u 𝟎 ℚ* u 𝟏
        s = v 𝟎 ℚ* v 𝟏

        I : abs (s ℚ- r) < η
        I = ℚ≤-<-trans (abs (s ℚ- r)) ((δ ℚ* M) ℚ+ (M ℚ* δ)) η
             (products-in-a-short-box a b a' b' δ k k' w₁ wδ v u mv mu)
              δ-is-small

        II : (r ℚ- η < s) × (s < r ℚ+ η)
        II = abs-gives-ball s r η I

open with-small-oscillation products-vary-little
 using (extension ; extension-is-continuous ; extension-at-samples)

\end{code}

The product, its agreement with the product of rationals, and its
continuity.

\begin{code}

infixl 36 _*_

_*_ : ℝ → ℝ → ℝ
x * y = extension (Fin-pair x y)

ιₐ-* : (p q : ℚ) → ιₐ p * ιₐ q ＝ ιₐ (p ℚ* q)
ιₐ-* p q = ap extension (dfunext fe γ) ∙ extension-at-samples (Fin-pair p q)
 where
  γ : Fin-pair (ιₐ p) (ιₐ q) ∼ (λ i → ιₐ (Fin-pair p q i))
  γ 𝟎             = refl
  γ 𝟏             = refl
  γ (suc (suc i)) = 𝟘-elim i

pair-is-continuous
 : {m : ℕ} (A B : (Fin m → ℝ) → ℝ) (x : Fin m → ℝ)
 → Coordinatewise-Strictly-Continuous A x
 → Coordinatewise-Strictly-Continuous B x
 → (j : Fin 2)
 → Coordinatewise-Strictly-Continuous (λ y → Fin-pair (A y) (B y) j) x
pair-is-continuous A B x cA cB 𝟎             = cA
pair-is-continuous A B x cA cB 𝟏             = cB
pair-is-continuous A B x cA cB (suc (suc i)) = 𝟘-elim i

product-is-continuous
 : {m : ℕ} (A B : (Fin m → ℝ) → ℝ) (x : Fin m → ℝ)
 → Coordinatewise-Strictly-Continuous A x
 → Coordinatewise-Strictly-Continuous B x
 → Coordinatewise-Strictly-Continuous (λ y → A y * B y) x
product-is-continuous A B x cA cB =
 composition-is-continuous extension (λ j y → Fin-pair (A y) (B y) j) x
  (extension-is-continuous (Fin-pair (A x) (B x)))
   (pair-is-continuous A B x cA cB)

\end{code}

Addition is continuous too. We prove the box form of continuity of
gist.RealCohesion.ContinuityForms: given u < t₀ + t₁ < v, the cuts of
the sum give u = r₀ + s₀ and v = r₁ + s₁ with r₀ < t₀ < r₁ and
s₀ < t₁ < s₁, and points strictly close enough to t₀ and t₁ stay
between these bounds.

\begin{code}

addition-is-box-continuous : (t : Fin 2 → ℝ)
                           → Box-Continuous (λ v → v 𝟎 + v 𝟏) t
addition-is-box-continuous t u v l l' =
 ∥∥-rec ∃-is-prop γ
  (binary-choice (below-sum⁻¹ (t 𝟎) (t 𝟏) u l) (sum-below⁻¹ (t 𝟎) (t 𝟏) v l'))
 where
  margins : (y : ℝ) (p q : ℚ) → p < y → y < q
          → ∃ (p' , q') ꞉ ℚ × ℚ , (p < p') × (p' < y) × (y < q') × (q' < q)
  margins y p q k k' =
   ∥∥-functor ζ (binary-choice (rounded-left-d y p k)
                  (rounded-right-b (upper-cut-of y) (rounded-from-real-R y) q
                    k'))
   where
    ζ : (Σ p' ꞉ ℚ , p < p' < y) × (Σ q' ꞉ ℚ , (q' < q) × (y < q'))
      → Σ (p' , q') ꞉ ℚ × ℚ , (p < p') × (p' < y) × (y < q') × (q' < q)
    ζ ((p' , a , b) , (q' , c , d)) = (p' , q') , a , b , d , c

  γ : (Σ (r₀ , s₀) ꞉ ℚ × ℚ , (r₀ < t 𝟎) × (s₀ < t 𝟏) × (u ＝ r₀ ℚ+ s₀))
    × (Σ (r₁ , s₁) ꞉ ℚ × ℚ , (t 𝟎 < r₁) × (t 𝟏 < s₁) × (v ＝ r₁ ℚ+ s₁))
    → ∃ r ꞉ ℚ , (0ℚ < r)
              × ((x : Fin 2 → ℝ) → ((j : Fin 2) → Strictly-Close r (x j) (t j))
                                 → (u < x 𝟎 + x 𝟏) × (x 𝟎 + x 𝟏 < v))
  γ (((r₀ , s₀) , a₀ , b₀ , e₀) , ((r₁ , s₁) , a₁ , b₁ , e₁)) =
   ∥∥-functor δ
    (binary-choice (margins (t 𝟎) r₀ r₁ a₀ a₁) (margins (t 𝟏) s₀ s₁ b₀ b₁))
   where
    δ : (Σ (r₀' , r₁') ꞉ ℚ × ℚ ,
          (r₀ < r₀') × (r₀' < t 𝟎) × (t 𝟎 < r₁') × (r₁' < r₁))
      × (Σ (s₀' , s₁') ꞉ ℚ × ℚ ,
          (s₀ < s₀') × (s₀' < t 𝟏) × (t 𝟏 < s₁') × (s₁' < s₁))
      → Σ r ꞉ ℚ , (0ℚ < r)
                ×
                ((x : Fin 2 → ℝ) → ((j : Fin 2) → Strictly-Close r (x j) (t j))
                                 → (u < x 𝟎 + x 𝟏) × (x 𝟎 + x 𝟏 < v))
    δ (((r₀' , r₁') , c₀ , d₀ , c₁ , d₁) , ((s₀' , s₁') , f₀ , g₀ , f₁ , g₁)) =
     r , r-is-positive , bounds
     where
      ρ₀ ρ₁ σ₀ σ₁ : ℚ
      ρ₀ = r₀' ℚ- r₀
      ρ₁ = r₁ ℚ- r₁'
      σ₀ = s₀' ℚ- s₀
      σ₁ = s₁ ℚ- s₁'

      r : ℚ
      r = minₐ (minₐ ρ₀ ρ₁) (minₐ σ₀ σ₁)

      r-is-positive : 0ℚ < r
      r-is-positive =
       minₐ-is-positive (minₐ ρ₀ ρ₁) (minₐ σ₀ σ₁)
        (minₐ-is-positive ρ₀ ρ₁ (ℚ<-difference-positive r₀ r₀' c₀)
          (ℚ<-difference-positive r₁' r₁ d₁))
        (minₐ-is-positive σ₀ σ₁ (ℚ<-difference-positive s₀ s₀' f₀)
          (ℚ<-difference-positive s₁' s₁ g₁))

      r≤ρ₀ : r ≤ ρ₀
      r≤ρ₀ = ℚ≤-trans r (minₐ ρ₀ ρ₁) ρ₀ (minₐ-≤-left (minₐ ρ₀ ρ₁) (minₐ σ₀ σ₁))
              (minₐ-≤-left ρ₀ ρ₁)

      r≤ρ₁ : r ≤ ρ₁
      r≤ρ₁ = ℚ≤-trans r (minₐ ρ₀ ρ₁) ρ₁ (minₐ-≤-left (minₐ ρ₀ ρ₁) (minₐ σ₀ σ₁))
              (minₐ-≤-right ρ₀ ρ₁)

      r≤σ₀ : r ≤ σ₀
      r≤σ₀ = ℚ≤-trans r (minₐ σ₀ σ₁) σ₀ (minₐ-≤-right (minₐ ρ₀ ρ₁) (minₐ σ₀ σ₁))
              (minₐ-≤-left σ₀ σ₁)

      r≤σ₁ : r ≤ σ₁
      r≤σ₁ = ℚ≤-trans r (minₐ σ₀ σ₁) σ₁ (minₐ-≤-right (minₐ ρ₀ ρ₁) (minₐ σ₀ σ₁))
              (minₐ-≤-right σ₀ σ₁)

      bounds : (x : Fin 2 → ℝ) → ((j : Fin 2) → Strictly-Close r (x j) (t j))
             → (u < x 𝟎 + x 𝟏) × (x 𝟎 + x 𝟏 < v)
      bounds x c = below-sum' (x 𝟎) (x 𝟏) u r₀ s₀ lower₀ lower₁ e₀ ,
                   sum-below' (x 𝟎) (x 𝟏) v r₁ s₁ upper₀ upper₁ e₁
       where
        lower₀ : r₀ < x 𝟎
        lower₀ =
         use-rounded-real-L' (x 𝟎) r₀ (r₀' ℚ- r) (margin-above r₀ r₀' r r≤ρ₀)
                  (strictly-close-below r (x 𝟎) (t 𝟎) (pr₂ (c 𝟎)) r₀' d₀)

        lower₁ : s₀ < x 𝟏
        lower₁ =
         use-rounded-real-L' (x 𝟏) s₀ (s₀' ℚ- r) (margin-above s₀ s₀' r r≤σ₀)
                  (strictly-close-below r (x 𝟏) (t 𝟏) (pr₂ (c 𝟏)) s₀' g₀)

        upper₀ : x 𝟎 < r₁
        upper₀ =
         use-rounded-real-R' (x 𝟎) (r₁' ℚ+ r) r₁ (margin-below r₁' r₁ r r≤ρ₁)
                  (strictly-close-above r (x 𝟎) (t 𝟎) (pr₁ (c 𝟎)) r₁' c₁)

        upper₁ : x 𝟏 < s₁
        upper₁ =
         use-rounded-real-R' (x 𝟏) (s₁' ℚ+ r) s₁ (margin-below s₁' s₁ r r≤σ₁)
                  (strictly-close-above r (x 𝟏) (t 𝟏) (pr₁ (c 𝟏)) s₁' f₁)

addition-is-continuous
 : (t : Fin 2 → ℝ) → Coordinatewise-Strictly-Continuous (λ v → v 𝟎 + v 𝟏) t
addition-is-continuous t =
 box-gives-coordinatewise-strict (λ v → v 𝟎 + v 𝟏) t
  (addition-is-box-continuous t)

sum-is-continuous
 : {m : ℕ} (A B : (Fin m → ℝ) → ℝ) (x : Fin m → ℝ)
 → Coordinatewise-Strictly-Continuous A x
 → Coordinatewise-Strictly-Continuous B x
 → Coordinatewise-Strictly-Continuous (λ y → A y + B y) x
sum-is-continuous A B x cA cB =
 composition-is-continuous (λ v → v 𝟎 + v 𝟏) (λ j y → Fin-pair (A y) (B y) j) x
  (addition-is-continuous (Fin-pair (A x) (B x)))
   (pair-is-continuous A B x cA cB)

\end{code}

The laws. Each side is a continuous function of the variables, by
product-is-continuous, and the two sides agree at rational points by
ιₐ-* and the law for the rationals.

\begin{code}

*-comm : (x y : ℝ) → x * y ＝ y * x
*-comm x y = agree-at-a-continuity-point F G t cF cG e
 where
  t : Fin 2 → ℝ
  t = Fin-pair x y

  F G : (Fin 2 → ℝ) → ℝ
  F v = v 𝟎 * v 𝟏
  G v = v 𝟏 * v 𝟎

  cF : Coordinatewise-Strictly-Continuous F t
  cF = product-is-continuous (λ v → v 𝟎) (λ v → v 𝟏) t
        (projection-is-continuous 𝟎 t) (projection-is-continuous 𝟏 t)

  cG : Coordinatewise-Strictly-Continuous G t
  cG = product-is-continuous (λ v → v 𝟏) (λ v → v 𝟎) t
        (projection-is-continuous 𝟏 t) (projection-is-continuous 𝟎 t)

  e : (q : Fin 2 → ℚ) → F (λ i → ιₐ (q i)) ＝ G (λ i → ιₐ (q i))
  e q = ιₐ-* (q 𝟎) (q 𝟏)
      ∙ ap ιₐ (ℚ*-comm (q 𝟎) (q 𝟏))
      ∙ ιₐ-* (q 𝟏) (q 𝟎) ⁻¹

*-assoc : (x y z : ℝ) → (x * y) * z ＝ x * (y * z)
*-assoc x y z = agree-at-a-continuity-point F G t cF cG e
 where
  t : Fin 3 → ℝ
  t = Fin-cons x (Fin-pair y z)

  F G : (Fin 3 → ℝ) → ℝ
  F v = (v 𝟎 * v 𝟏) * v 𝟐
  G v = v 𝟎 * (v 𝟏 * v 𝟐)

  p : (i : Fin 3) → Coordinatewise-Strictly-Continuous (λ v → v i) t
  p i = projection-is-continuous i t

  cF : Coordinatewise-Strictly-Continuous F t
  cF = product-is-continuous (λ v → v 𝟎 * v 𝟏) (λ v → v 𝟐) t
        (product-is-continuous (λ v → v 𝟎) (λ v → v 𝟏) t (p 𝟎) (p 𝟏)) (p 𝟐)

  cG : Coordinatewise-Strictly-Continuous G t
  cG = product-is-continuous (λ v → v 𝟎) (λ v → v 𝟏 * v 𝟐) t
        (p 𝟎) (product-is-continuous (λ v → v 𝟏) (λ v → v 𝟐) t (p 𝟏) (p 𝟐))

  e : (q : Fin 3 → ℚ) → F (λ i → ιₐ (q i)) ＝ G (λ i → ιₐ (q i))
  e q = ap (_* ιₐ (q 𝟐)) (ιₐ-* (q 𝟎) (q 𝟏))
      ∙ ιₐ-* (q 𝟎 ℚ* q 𝟏) (q 𝟐)
      ∙ ap ιₐ (ℚ*-assoc (q 𝟎) (q 𝟏) (q 𝟐))
      ∙ ιₐ-* (q 𝟎) (q 𝟏 ℚ* q 𝟐) ⁻¹
      ∙ ap (ιₐ (q 𝟎) *_) (ιₐ-* (q 𝟏) (q 𝟐) ⁻¹)

\end{code}

The units and zeros. Here the functions have one variable.

\begin{code}

1ℝ-is-ιₐ : 1ℝ ＝ ιₐ 1ℚ
1ℝ-is-ιₐ = ιₐ-is-ι 1ℚ ⁻¹

0ℝ-is-ιₐ : 0ℝ ＝ ιₐ 0ℚ
0ℝ-is-ιₐ = ιₐ-is-ι 0ℚ ⁻¹

*-right-unit : (x : ℝ) → x * 1ℝ ＝ x
*-right-unit x = agree-at-a-continuity-point F G t cF cG e
 where
  t : Fin 1 → ℝ
  t _ = x

  F G : (Fin 1 → ℝ) → ℝ
  F v = v 𝟎 * 1ℝ
  G v = v 𝟎

  cF : Coordinatewise-Strictly-Continuous F t
  cF = product-is-continuous (λ v → v 𝟎) (λ _ → 1ℝ) t
        (projection-is-continuous 𝟎 t) (constant-is-continuous 1ℝ t)

  cG : Coordinatewise-Strictly-Continuous G t
  cG = projection-is-continuous 𝟎 t

  e : (q : Fin 1 → ℚ) → F (λ i → ιₐ (q i)) ＝ G (λ i → ιₐ (q i))
  e q = ap (ιₐ (q 𝟎) *_) 1ℝ-is-ιₐ
      ∙ ιₐ-* (q 𝟎) 1ℚ
      ∙ ap ιₐ (ℚ-mult-right-id (q 𝟎))

*-left-unit : (x : ℝ) → 1ℝ * x ＝ x
*-left-unit x = *-comm 1ℝ x ∙ *-right-unit x

*-right-zero : (x : ℝ) → x * 0ℝ ＝ 0ℝ
*-right-zero x = agree-at-a-continuity-point F G t cF cG e
 where
  t : Fin 1 → ℝ
  t _ = x

  F G : (Fin 1 → ℝ) → ℝ
  F v = v 𝟎 * 0ℝ
  G v = 0ℝ

  cF : Coordinatewise-Strictly-Continuous F t
  cF = product-is-continuous (λ v → v 𝟎) (λ _ → 0ℝ) t
        (projection-is-continuous 𝟎 t) (constant-is-continuous 0ℝ t)

  cG : Coordinatewise-Strictly-Continuous G t
  cG = constant-is-continuous 0ℝ t

  e : (q : Fin 1 → ℚ) → F (λ i → ιₐ (q i)) ＝ G (λ i → ιₐ (q i))
  e q = ap (ιₐ (q 𝟎) *_) 0ℝ-is-ιₐ
      ∙ ιₐ-* (q 𝟎) 0ℚ
      ∙ ap ιₐ (ℚ-zero-right-is-zero (q 𝟎))
      ∙ 0ℝ-is-ιₐ ⁻¹

*-left-zero : (x : ℝ) → 0ℝ * x ＝ 0ℝ
*-left-zero x = *-comm 0ℝ x ∙ *-right-zero x

\end{code}

Distributivity, with the addition of gist.RealCohesion.RealLattice
(TypeTopology's, there made abstract).

\begin{code}

*-left-distributive : (x y z : ℝ) → x * (y + z) ＝ x * y + x * z
*-left-distributive x y z = agree-at-a-continuity-point F G t cF cG e
 where
  t : Fin 3 → ℝ
  t = Fin-cons x (Fin-pair y z)

  F G : (Fin 3 → ℝ) → ℝ
  F v = v 𝟎 * (v 𝟏 + v 𝟐)
  G v = v 𝟎 * v 𝟏 + v 𝟎 * v 𝟐

  p : (i : Fin 3) → Coordinatewise-Strictly-Continuous (λ v → v i) t
  p i = projection-is-continuous i t

  cF : Coordinatewise-Strictly-Continuous F t
  cF = product-is-continuous (λ v → v 𝟎) (λ v → v 𝟏 + v 𝟐) t
        (p 𝟎) (sum-is-continuous (λ v → v 𝟏) (λ v → v 𝟐) t (p 𝟏) (p 𝟐))

  cG : Coordinatewise-Strictly-Continuous G t
  cG = sum-is-continuous (λ v → v 𝟎 * v 𝟏) (λ v → v 𝟎 * v 𝟐) t
        (product-is-continuous (λ v → v 𝟎) (λ v → v 𝟏) t (p 𝟎) (p 𝟏))
        (product-is-continuous (λ v → v 𝟎) (λ v → v 𝟐) t (p 𝟎) (p 𝟐))

  e : (q : Fin 3 → ℚ) → F (λ i → ιₐ (q i)) ＝ G (λ i → ιₐ (q i))
  e q = ap (ιₐ (q 𝟎) *_) (ιₐ-sum (q 𝟏) (q 𝟐))
      ∙ ιₐ-* (q 𝟎) (q 𝟏 ℚ+ q 𝟐)
      ∙ ap ιₐ (ℚ-distributivity (q 𝟎) (q 𝟏) (q 𝟐))
      ∙ ιₐ-sum (q 𝟎 ℚ* q 𝟏) (q 𝟎 ℚ* q 𝟐) ⁻¹
      ∙ ap₂ _+_ (ιₐ-* (q 𝟎) (q 𝟏) ⁻¹) (ιₐ-* (q 𝟎) (q 𝟐) ⁻¹)

*-right-distributive : (x y z : ℝ) → (x + y) * z ＝ x * z + y * z
*-right-distributive x y z =
 *-comm (x + y) z ∙ *-left-distributive z x y
  ∙ ap₂ _+_ (*-comm z x) (*-comm z y)

\end{code}

Order. If 0 < a₀ < x and 0 < a₁ < y for rationals a₀ and a₁, then
a₀ a₁ < x y: for rationals a₀' and a₁' with a₀ < a₀' < x and
a₁ < a₁' < y, the product a₀' a₁' is a lower bound of the products at
the rational points of a box around (x , y). Likewise if x < b₀ < 0 and
y < b₁ < 0. So a product of positive reals is positive. Squares are
nonnegative, because they are at rational points.

\begin{code}

<-from-rational-between : (x y : ℝ) (q : ℚ) → x < q → q < y → x < y
<-from-rational-between x y q k l = ∣ q , k , l ∣

products-above
 : (a₀ a₁ : ℚ) (x y : ℝ) → 0ℚ < a₀ → 0ℚ < a₁ → a₀ < x → a₁ < y
 → (a₀ ℚ* a₁) < x * y
products-above a₀ a₁ x y k₀ k₁ l₀ l₁ =
 ∥∥-rec (ℚ<ℝ-is-prop (a₀ ℚ* a₁) (x * y)) γ
  (binary-choice
    (binary-choice (rounded-left-d x a₀ l₀) (rounded-left-d y a₁ l₁))
    (binary-choice (inhabited-from-real-R x) (inhabited-from-real-R y)))
 where
  γ : ((Σ a₀' ꞉ ℚ , a₀ < a₀' < x) × (Σ a₁' ꞉ ℚ , a₁ < a₁' < y))
    × ((Σ b₀ ꞉ ℚ , x < b₀) × (Σ b₁ ꞉ ℚ , y < b₁))
    → (a₀ ℚ* a₁) < x * y
  γ (((a₀' , m₀ , n₀) , (a₁' , m₁ , n₁)) , ((b₀ , o₀) , (b₁ , o₁))) =
   ∣ witness ∣
   where
    a b : Fin 2 → ℚ
    a = Fin-pair a₀' a₁'
    b = Fin-pair b₀ b₁

    around : Around a b (Fin-pair x y)
    around 𝟎             = n₀ , o₀
    around 𝟏             = n₁ , o₁
    around (suc (suc i)) = 𝟘-elim i

    k₀' : 0ℚ < a₀'
    k₀' = ℚ<-trans 0ℚ a₀ a₀' k₀ m₀

    k₁' : 0ℚ < a₁'
    k₁' = ℚ<-trans 0ℚ a₁ a₁' k₁ m₁

    closer : (a₀ ℚ* a₁) < (a₀' ℚ* a₁')
    closer = products-of-positives-are-monotone a₀ a₁ a₀' a₁' k₀ k₁ m₀ m₁

    lower-bound : Lower-Bound a b (a₀' ℚ* a₁')
    lower-bound u o =
     ιₐ-lower (a₀' ℚ* a₁') (u 𝟎 ℚ* u 𝟏)
      (products-of-positives-are-monotone a₀' a₁' (u 𝟎) (u 𝟏) k₀' k₁'
        (pr₁ (o 𝟎)) (pr₁ (o 𝟏)))

    witness : Below-Witness (Fin-pair x y) (a₀ ℚ* a₁)
    witness = (a , b , a₀' ℚ* a₁') , around , closer , lower-bound

products-of-negatives-above
 : (b₀ b₁ : ℚ) (x y : ℝ) → b₀ < 0ℚ → b₁ < 0ℚ → x < b₀ → y < b₁
 → (b₀ ℚ* b₁) < x * y
products-of-negatives-above b₀ b₁ x y k₀ k₁ l₀ l₁ =
 ∥∥-rec (ℚ<ℝ-is-prop (b₀ ℚ* b₁) (x * y)) γ
  (binary-choice
    (binary-choice
      (rounded-right-b (upper-cut-of x) (rounded-from-real-R x) b₀ l₀)
                   (rounded-right-b (upper-cut-of y) (rounded-from-real-R y) b₁
                     l₁))
    (binary-choice (inhabited-from-real-L x) (inhabited-from-real-L y)))
 where
  γ :
   ((Σ b₀' ꞉ ℚ , (b₀' < b₀) × (x < b₀')) × (Σ b₁' ꞉ ℚ , (b₁' < b₁) × (y < b₁')))
    × ((Σ a₀ ꞉ ℚ , a₀ < x) × (Σ a₁ ꞉ ℚ , a₁ < y))
    → (b₀ ℚ* b₁) < x * y
  γ (((b₀' , m₀ , n₀) , (b₁' , m₁ , n₁)) , ((a₀ , o₀) , (a₁ , o₁))) =
   ∣ witness ∣
   where
    a b : Fin 2 → ℚ
    a = Fin-pair a₀ a₁
    b = Fin-pair b₀' b₁'

    around : Around a b (Fin-pair x y)
    around 𝟎             = o₀ , n₀
    around 𝟏             = o₁ , n₁
    around (suc (suc i)) = 𝟘-elim i

    k₀' : b₀' < 0ℚ
    k₀' = ℚ<-trans b₀' b₀ 0ℚ m₀ k₀

    k₁' : b₁' < 0ℚ
    k₁' = ℚ<-trans b₁' b₁ 0ℚ m₁ k₁

    closer : (b₀ ℚ* b₁) < (b₀' ℚ* b₁')
    closer = products-of-negatives-are-monotone b₀ b₁ b₀' b₁' k₀ k₁ m₀ m₁

    lower-bound : Lower-Bound a b (b₀' ℚ* b₁')
    lower-bound u o =
     ιₐ-lower (b₀' ℚ* b₁') (u 𝟎 ℚ* u 𝟏)
      (products-of-negatives-are-monotone b₀' b₁' (u 𝟎) (u 𝟏) k₀' k₁'
        (pr₂ (o 𝟎)) (pr₂ (o 𝟏)))

    witness : Below-Witness (Fin-pair x y) (b₀ ℚ* b₁)
    witness = (a , b , b₀' ℚ* b₁') , around , closer , lower-bound

product-of-positives-is-positive : (x y : ℝ) → 0ℝ < x → 0ℝ < y → 0ℝ < x * y
product-of-positives-is-positive x y lx ly =
 ∥∥-rec ∃-is-prop γ (binary-choice lx ly)
 where
  γ : (Σ a₀ ꞉ ℚ , (0ℝ < a₀) × (a₀ < x)) × (Σ a₁ ꞉ ℚ , (0ℝ < a₁) × (a₁ < y))
    → 0ℝ < x * y
  γ ((a₀ , k₀ , l₀) , (a₁ , k₁ , l₁)) =
   <-from-rational-between 0ℝ (x * y) (a₀ ℚ* a₁)
    (transport (_< a₀ ℚ* a₁) {ιₐ 0ℚ} {0ℝ} (0ℝ-is-ιₐ ⁻¹)
      (ιₐ-upper 0ℚ (a₀ ℚ* a₁) (ℚ<-pos-multiplication-preserves-order a₀ a₁
                                a₀-is-positive a₁-is-positive)))
    (products-above a₀ a₁ x y a₀-is-positive a₁-is-positive l₀ l₁)
   where
    a₀-is-positive : 0ℚ < a₀
    a₀-is-positive =
     ιₐ-upper⁻¹ 0ℚ a₀ (transport (_< a₀) {0ℝ} {ιₐ 0ℚ} 0ℝ-is-ιₐ k₀)

    a₁-is-positive : 0ℚ < a₁
    a₁-is-positive =
     ιₐ-upper⁻¹ 0ℚ a₁ (transport (_< a₁) {0ℝ} {ιₐ 0ℚ} 0ℝ-is-ιₐ k₁)

squares-are-nonneg : (x : ℝ) → 0ℝ ≤ x * x
squares-are-nonneg x = transport (_≤ x * x) {ιₐ 0ℚ} {0ℝ} (0ℝ-is-ιₐ ⁻¹)
                        (≤-at-a-continuity-point F G t cF cG h)
 where
  t : Fin 1 → ℝ
  t _ = x

  F G : (Fin 1 → ℝ) → ℝ
  F v = ιₐ 0ℚ
  G v = v 𝟎 * v 𝟎

  cF : Coordinatewise-Strictly-Continuous F t
  cF = constant-is-continuous (ιₐ 0ℚ) t

  cG : Coordinatewise-Strictly-Continuous G t
  cG = product-is-continuous (λ v → v 𝟎) (λ v → v 𝟎) t
        (projection-is-continuous 𝟎 t) (projection-is-continuous 𝟎 t)

  h : (q : Fin 1 → ℚ) → F (λ i → ιₐ (q i)) ≤ G (λ i → ιₐ (q i))
  h q = transport (ιₐ 0ℚ ≤_) {ιₐ (q 𝟎 ℚ* q 𝟎)} {ιₐ (q 𝟎) * ιₐ (q 𝟎)}
         (ιₐ-* (q 𝟎) (q 𝟎) ⁻¹)
         (ιₐ-≤-ιₐ 0ℚ (q 𝟎 ℚ* q 𝟎) (rational-squares-are-nonneg (q 𝟎)))

\end{code}

The cuts of a square, by intervals. If q < x x, the products at the
rational points of some box around (x , x) exceed a rational above q;
the rational points m of the intersection (a , b) of the box's two
intervals give points (m , m) of the box, so q < m m for every rational
m in (a , b), an interval around x. Likewise if x x < q. The square root
of gist.RealCohesion.RealSquareRoot uses these, as agda-unimath's proof
of its square law uses the enclosing intervals of its products.

\begin{code}

Interval-Above-Square Interval-Below-Square : ℚ → ℝ → 𝓤₀ ̇
Interval-Above-Square q x =
 Σ a ꞉ ℚ , Σ b ꞉ ℚ , (a < x) × (x < b) × ((m : ℚ) → a < m → m < b → q < m ℚ* m)
Interval-Below-Square q x =
 Σ a ꞉ ℚ , Σ b ꞉ ℚ , (a < x) × (x < b) × ((m : ℚ) → a < m → m < b → m ℚ* m < q)

below-square⁻¹ : (q : ℚ) (x : ℝ) → q < x * x → ∥ Interval-Above-Square q x ∥
below-square⁻¹ q x l = ∥∥-functor γ l
 where
  γ : Below-Witness (Fin-pair x x) q → Interval-Above-Square q x
  γ ((a , b , p') , around , q<p' , lower) =
   max (a 𝟎) (a 𝟏) , min (b 𝟎) (b 𝟏) , left , right , δ
   where
    left : max (a 𝟎) (a 𝟏) < x
    left = Cases (max-to-≤ (a 𝟎) (a 𝟏))
            (λ (_ , e) →
              transport (_< x) {a 𝟏} {max (a 𝟎) (a 𝟏)} (e ⁻¹) (pr₁ (around 𝟏)))
            (λ (_ , e) →
              transport (_< x) {a 𝟎} {max (a 𝟎) (a 𝟏)} (e ⁻¹) (pr₁ (around 𝟎)))

    right : x < min (b 𝟎) (b 𝟏)
    right = Cases (min-to-≤ (b 𝟎) (b 𝟏))
             (λ (_ , e) →
               transport (x <_) {b 𝟎} {min (b 𝟎) (b 𝟏)} (e ⁻¹) (pr₂ (around 𝟎)))
             (λ (_ , e) →
               transport (x <_) {b 𝟏} {min (b 𝟎) (b 𝟏)} (e ⁻¹) (pr₂ (around 𝟏)))

    δ : (m : ℚ) → max (a 𝟎) (a 𝟏) < m → m < min (b 𝟎) (b 𝟏) → q < m ℚ* m
    δ m l l' = ℚ<-trans q p' (m ℚ* m) q<p'
                (ιₐ-lower⁻¹ p' (m ℚ* m) (lower (Fin-pair m m) in-box))
     where
      in-box : In-Box a b (Fin-pair m m)
      in-box 𝟎             =
       ℚ≤-<-trans (a 𝟎) (max (a 𝟎) (a 𝟏)) m (max≤ (a 𝟎) (a 𝟏)) l ,
                             ℚ<-≤-trans m (min (b 𝟎) (b 𝟏)) (b 𝟎) l'
                              (min≤ (b 𝟎) (b 𝟏))
      in-box 𝟏             =
       ℚ≤-<-trans (a 𝟏) (max (a 𝟎) (a 𝟏)) m (max≤' (a 𝟎) (a 𝟏)) l ,
                             ℚ<-≤-trans m (min (b 𝟎) (b 𝟏)) (b 𝟏) l'
                              (min≤' (b 𝟎) (b 𝟏))
      in-box (suc (suc i)) = 𝟘-elim i

square-below⁻¹ : (q : ℚ) (x : ℝ) → x * x < q → ∥ Interval-Below-Square q x ∥
square-below⁻¹ q x l = ∥∥-functor γ l
 where
  γ : Above-Witness (Fin-pair x x) q → Interval-Below-Square q x
  γ ((a , b , q') , around , q'<q , upper) =
   max (a 𝟎) (a 𝟏) , min (b 𝟎) (b 𝟏) , left , right , δ
   where
    left : max (a 𝟎) (a 𝟏) < x
    left = Cases (max-to-≤ (a 𝟎) (a 𝟏))
            (λ (_ , e) →
              transport (_< x) {a 𝟏} {max (a 𝟎) (a 𝟏)} (e ⁻¹) (pr₁ (around 𝟏)))
            (λ (_ , e) →
              transport (_< x) {a 𝟎} {max (a 𝟎) (a 𝟏)} (e ⁻¹) (pr₁ (around 𝟎)))

    right : x < min (b 𝟎) (b 𝟏)
    right = Cases (min-to-≤ (b 𝟎) (b 𝟏))
             (λ (_ , e) →
               transport (x <_) {b 𝟎} {min (b 𝟎) (b 𝟏)} (e ⁻¹) (pr₂ (around 𝟎)))
             (λ (_ , e) →
               transport (x <_) {b 𝟏} {min (b 𝟎) (b 𝟏)} (e ⁻¹) (pr₂ (around 𝟏)))

    δ : (m : ℚ) → max (a 𝟎) (a 𝟏) < m → m < min (b 𝟎) (b 𝟏) → m ℚ* m < q
    δ m l l' = ℚ<-trans (m ℚ* m) q' q
                (ιₐ-upper⁻¹ (m ℚ* m) q' (upper (Fin-pair m m) in-box)) q'<q
     where
      in-box : In-Box a b (Fin-pair m m)
      in-box 𝟎             =
       ℚ≤-<-trans (a 𝟎) (max (a 𝟎) (a 𝟏)) m (max≤ (a 𝟎) (a 𝟏)) l ,
                             ℚ<-≤-trans m (min (b 𝟎) (b 𝟏)) (b 𝟎) l'
                              (min≤ (b 𝟎) (b 𝟏))
      in-box 𝟏             =
       ℚ≤-<-trans (a 𝟏) (max (a 𝟎) (a 𝟏)) m (max≤' (a 𝟎) (a 𝟏)) l ,
                             ℚ<-≤-trans m (min (b 𝟎) (b 𝟏)) (b 𝟏) l'
                              (min≤' (b 𝟎) (b 𝟏))
      in-box (suc (suc i)) = 𝟘-elim i

\end{code}

Negation, the abstract negation of gist.RealCohesion.RealLattice: it
agrees with the negation of rationals, and it is continuous. For the
continuity, points strictly close enough to t stay between any
rational bounds p < t < q.

\begin{code}

ιₐ-neg : (q : ℚ) → - ιₐ q ＝ ιₐ (ℚ- q)
ιₐ-neg q = equal-if-lower-cuts-agree (- ιₐ q) (ιₐ (ℚ- q)) I II
 where
  I : lower-cut-of (- ιₐ q) ⊆ lower-cut-of (ιₐ (ℚ- q))
  I p l = ιₐ-lower p (ℚ- q)
           (transport (_< ℚ- q) {ℚ- (ℚ- p)} {p} (ℚ-minus-minus p ⁻¹)
             (ℚ<-swap q (ℚ- p) (ιₐ-upper⁻¹ q (ℚ- p) (below-neg⁻¹ (ιₐ q) p l))))

  II : lower-cut-of (ιₐ (ℚ- q)) ⊆ lower-cut-of (- ιₐ q)
  II p l = transport (_< (- ιₐ q)) {ℚ- (ℚ- p)} {p} (ℚ-minus-minus p ⁻¹)
            (below-neg (ιₐ q) (ℚ- p)
              (ιₐ-upper q (ℚ- p)
                (transport (_< ℚ- p) {ℚ- (ℚ- q)} {q} (ℚ-minus-minus q ⁻¹)
                  (ℚ<-swap p (ℚ- q) (ιₐ-lower⁻¹ p (ℚ- q) l)))))

close-points-stay-between
 : (t : ℝ) (p q : ℚ) → p < t → t < q
 → ∃ r ꞉ ℚ , (0ℚ < r) × ((y : ℝ) → Strictly-Close r y t → (p < y) × (y < q))
close-points-stay-between t p q k k' =
 ∥∥-functor γ (binary-choice (rounded-left-d t p k)
                (rounded-right-b (upper-cut-of t) (rounded-from-real-R t) q k'))
 where
  γ : (Σ p' ꞉ ℚ , p < p' < t) × (Σ q' ꞉ ℚ , (q' < q) × (t < q'))
    → Σ r ꞉ ℚ , (0ℚ < r) × ((y : ℝ) → Strictly-Close r y t → (p < y) × (y < q))
  γ ((p' , a , b) , (q' , c , d)) = r , r-is-positive , between
   where
    r : ℚ
    r = minₐ (p' ℚ- p) (q ℚ- q')

    r-is-positive : 0ℚ < r
    r-is-positive = minₐ-is-positive (p' ℚ- p) (q ℚ- q')
                     (ℚ<-difference-positive p p' a)
                      (ℚ<-difference-positive q' q c)

    between : (y : ℝ) → Strictly-Close r y t → (p < y) × (y < q)
    between y e =
     use-rounded-real-L' y p (p' ℚ- r)
      (margin-above p p' r (minₐ-≤-left (p' ℚ- p) (q ℚ- q')))
      (strictly-close-below r y t (pr₂ e) p' b) ,
     use-rounded-real-R' y (q' ℚ+ r) q
      (margin-below q' q r (minₐ-≤-right (p' ℚ- p) (q ℚ- q')))
      (strictly-close-above r y t (pr₁ e) q' d)

negation-is-box-continuous : (t : Fin 1 → ℝ) → Box-Continuous (λ v → - v 𝟎) t
negation-is-box-continuous t u v l l' =
 ∥∥-functor γ (close-points-stay-between (t 𝟎) (ℚ- v) (ℚ- u)
                (neg-below⁻¹ (t 𝟎) v l') (below-neg⁻¹ (t 𝟎) u l))
 where
  γ : (Σ r ꞉ ℚ ,
    (0ℚ < r) × ((y : ℝ) → Strictly-Close r y (t 𝟎) → (ℚ- v < y) × (y < ℚ- u)))
    → Σ r ꞉ ℚ , (0ℚ < r)
              × ((x : Fin 1 → ℝ) → ((j : Fin 1) → Strictly-Close r (x j) (t j))
                                 → (u < (- x 𝟎)) × ((- x 𝟎) < v))
  γ (r , r-is-positive , between) = r , r-is-positive , δ
   where
    δ : (x : Fin 1 → ℝ) → ((j : Fin 1) → Strictly-Close r (x j) (t j))
      → (u < (- x 𝟎)) × ((- x 𝟎) < v)
    δ x c = transport (_< (- x 𝟎)) {ℚ- (ℚ- u)} {u} (ℚ-minus-minus u ⁻¹)
             (below-neg (x 𝟎) (ℚ- u) (pr₂ (between (x 𝟎) (c 𝟎)))) ,
            transport ((- x 𝟎) <_) {ℚ- (ℚ- v)} {v} (ℚ-minus-minus v ⁻¹)
             (neg-below (x 𝟎) (ℚ- v) (pr₁ (between (x 𝟎) (c 𝟎))))

negative-is-continuous
 : {m : ℕ} (A : (Fin m → ℝ) → ℝ) (x : Fin m → ℝ)
 → Coordinatewise-Strictly-Continuous A x
 → Coordinatewise-Strictly-Continuous (λ y → - A y) x
negative-is-continuous A x cA =
 composition-is-continuous (λ v → - v 𝟎) (λ _ y → A y) x
  (box-gives-coordinatewise-strict (λ v → - v 𝟎) (λ _ → A x)
    (negation-is-box-continuous (λ _ → A x)))
  (λ _ → cA)

\end{code}

Products bounded above: if -m < x < m and -m < y < m for a rational m,
then x y < m m. The rational points of a box around (x , y) inside
(-m , m)² have coordinates of absolute value below some M < m.

\begin{code}

products-below
 : (m : ℚ) (x y : ℝ) → (ℚ- m) < x → x < m → (ℚ- m) < y → y < m → x * y < m ℚ* m
products-below m x y k₀ l₀ k₁ l₁ =
 ∥∥-rec (ℝ<ℚ-is-prop (x * y) (m ℚ* m)) γ
  (binary-choice
    (binary-choice (rounded-left-d x (ℚ- m) k₀)
                   (rounded-right-b (upper-cut-of x) (rounded-from-real-R x) m
                     l₀))
    (binary-choice (rounded-left-d y (ℚ- m) k₁)
                   (rounded-right-b (upper-cut-of y) (rounded-from-real-R y) m
                     l₁)))
 where
  minus-below : (a : ℚ) → (ℚ- m) < a → (ℚ- a) < m
  minus-below a h = transport ((ℚ- a) <_) {ℚ- (ℚ- m)} {m} (ℚ-minus-minus m ⁻¹)
                     (ℚ<-swap (ℚ- m) a h)

  γ : ((Σ a₀ ꞉ ℚ , (ℚ- m) < a₀ < x) × (Σ b₀ ꞉ ℚ , (b₀ < m) × (x < b₀)))
    × ((Σ a₁ ꞉ ℚ , (ℚ- m) < a₁ < y) × (Σ b₁ ꞉ ℚ , (b₁ < m) × (y < b₁)))
    → x * y < m ℚ* m
  γ (((a₀ , p₀ , q₀) , (b₀ , r₀ , s₀)) , ((a₁ , p₁ , q₁) , (b₁ , r₁ , s₁))) =
   ∣ witness ∣
   where
    M₀ M₁ M : ℚ
    M₀ = max (ℚ- a₀) b₀
    M₁ = max (ℚ- a₁) b₁
    M  = max M₀ M₁

    a b : Fin 2 → ℚ
    a = Fin-pair a₀ a₁
    b = Fin-pair b₀ b₁

    around : Around a b (Fin-pair x y)
    around 𝟎             = q₀ , s₀
    around 𝟏             = q₁ , s₁
    around (suc (suc i)) = 𝟘-elim i

    M<m : M < m
    M<m = max-below M₀ M₁ m (max-below (ℚ- a₀) b₀ m (minus-below a₀ p₀) r₀)
                            (max-below (ℚ- a₁) b₁ m (minus-below a₁ p₁) r₁)

    -a₀≤M : (ℚ- a₀) ≤ M
    -a₀≤M = ℚ≤-trans (ℚ- a₀) M₀ M (max≤ (ℚ- a₀) b₀) (max≤ M₀ M₁)

    b₀≤M : b₀ ≤ M
    b₀≤M = ℚ≤-trans b₀ M₀ M (max≤' (ℚ- a₀) b₀) (max≤ M₀ M₁)

    -a₁≤M : (ℚ- a₁) ≤ M
    -a₁≤M = ℚ≤-trans (ℚ- a₁) M₁ M (max≤ (ℚ- a₁) b₁) (max≤' M₀ M₁)

    b₁≤M : b₁ ≤ M
    b₁≤M = ℚ≤-trans b₁ M₁ M (max≤' (ℚ- a₁) b₁) (max≤' M₀ M₁)

    M-is-nonneg : 0ℚ ≤ M
    M-is-nonneg = Cases (ℚ-dichotomous 0ℚ b₀)
     (λ h → ℚ≤-trans 0ℚ b₀ M h b₀≤M)
     (λ h → ℚ≤-trans 0ℚ (ℚ- a₀) M
              (ℚ<-coarser-than-≤ 0ℚ (ℚ- a₀)
                (negative-gives-positive a₀
                  (ℚ<-≤-trans a₀ b₀ 0ℚ (cuts-are-ordered x a₀ b₀ q₀ s₀) h)))
              -a₀≤M)

    upper : Upper-Bound a b (M ℚ* M)
    upper u o =
     ιₐ-upper (u 𝟎 ℚ* u 𝟏) (M ℚ* M)
      (products-below-square M (u 𝟎) (u 𝟏)
        (abs-below a₀ b₀ (u 𝟎) M (pr₁ (o 𝟎)) (pr₂ (o 𝟎)) -a₀≤M b₀≤M)
        (abs-below a₁ b₁ (u 𝟏) M (pr₁ (o 𝟏)) (pr₂ (o 𝟏)) -a₁≤M b₁≤M))

    witness : Above-Witness (Fin-pair x y) (m ℚ* m)
    witness =
     (a , b , M ℚ* M) , around , square-below-square M m M-is-nonneg M<m , upper

\end{code}
