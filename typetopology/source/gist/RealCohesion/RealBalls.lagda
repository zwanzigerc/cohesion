Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 11 November 2026. See the AI disclosure in
gist.RealCohesion.index.

Rational balls of real numbers.

TypeTopology measures the distance of two reals by rational balls
(MetricSpaces.DedekindReals): B-ℝ x y ε says that x and y lie in a
common rational interval (p , q) with |p - q| < ε, which is to say
|x - y| < ε. We write Close ε x y for the same proposition with ε an
arbitrary rational, without a proof that ε is positive; for such a
proof l, B-ℝ x y (ε , l) is Close ε x y by definition. This lets crisp
predicates mention Close ε for a crisp rational ε whose positivity is
known only non-crisply.

We collect the facts about closeness used in
gist.RealCohesion.CrispUniformContinuity, gist.RealCohesion.CrispExtension
and gist.RealCohesion.FlatRealFunctions:

 * closeness from a common interval, and bounds from closeness;
 * symmetry, monotonicity and the triangle inequality;
 * every rational interval around a real t contains a ball around t;
 * every rational interval around t contains rationals arbitrarily
   close to t, and two such intervals have a common rational point.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.RealBalls
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import Fin.Type using (Fin ; 𝟎 ; suc)
open import Notation.CanonicalMap
open import Notation.Order
open import UF.Base
open import Rationals.Type
open import Rationals.Abs
open import Rationals.Order
open import Rationals.MinMax
open import Rationals.Addition renaming (_+_ to _ℚ+_)
open import Rationals.Negation renaming (_-_ to _ℚ-_ ; -_ to ℚ-_)
open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import DedekindReals.Properties fe pe pt using (ℝ-arithmetically-located)
open import MetricSpaces.DedekindReals fe pe pt using (B-ℝ ; ℝ-m4)
open import gist.RealCohesion.RationalArithmetic
 using (half ; halves-add-up ; half-is-positive ; half-is-less ;
        add-difference ; <-move-left ; <-move-right ; ≤-sub-right ;
         min-is-positive ;
        <-sub-right)
open import gist.RealCohesion.RationalPoints fe pe pt
open import gist.RealCohesion.RealOrder fe pe pt using (cuts-are-ordered)
open import gist.RealCohesion.RealLattice fe pe pt
 using (ℚ<ℝ-is-prop ; ℝ<ℚ-is-prop)
open import gist.RealCohesion.RealLimits fe pe pt using (ℚ<-add-left)

open PropositionalTruncation pt

\end{code}

Abstract copies of the minimum and of halving. Agda cannot unfold
them, so it compares, say, minₐ δ₁ δ₂ with minₐ δ₁ δ₂ syntactically.
Without this, it unfolds TypeTopology's min, which is defined by
trichotomy on the representations of rationals, whenever a local name
for a minimum has to be compared with its definition, and checking
takes minutes. The same device is used for ιₐ
(gist.RealCohesion.RationalPoints) and for multiples
(gist.RealCohesion.Quantizers).

\begin{code}

abstract
 minₐ : ℚ → ℚ → ℚ
 minₐ = min

 minₐ-≤-left : (p q : ℚ) → minₐ p q ≤ p
 minₐ-≤-left = min≤

 minₐ-≤-right : (p q : ℚ) → minₐ p q ≤ q
 minₐ-≤-right = min≤'

 minₐ-is-positive : (p q : ℚ) → 0ℚ < p → 0ℚ < q → 0ℚ < minₐ p q
 minₐ-is-positive = min-is-positive

 halfₐ : ℚ → ℚ
 halfₐ = half

 halfₐ-is-positive : (d : ℚ) → 0ℚ < d → 0ℚ < halfₐ d
 halfₐ-is-positive = half-is-positive

 halfₐ-is-less : (d : ℚ) → 0ℚ < d → halfₐ d < d
 halfₐ-is-less = half-is-less

 halvesₐ-add-up : (d : ℚ) → halfₐ d ℚ+ halfₐ d ＝ d
 halvesₐ-add-up = halves-add-up

\end{code}

Closeness, and its agreement with TypeTopology's balls.

\begin{code}

Close : ℚ → ℝ → ℝ → 𝓤₀ ̇
Close ε x y = ∃ (p , q) ꞉ ℚ × ℚ , (p < x < q) × (p < y < q) × (abs (p ℚ- q) < ε)

Close-is-B-ℝ : (ε : ℚ) (l : 0ℚ < ε) (x y : ℝ) → B-ℝ x y (ε , l) ＝ Close ε x y
Close-is-B-ℝ ε l x y = refl

Close-is-prop : (ε : ℚ) (x y : ℝ) → is-prop (Close ε x y)
Close-is-prop ε x y = ∃-is-prop

\end{code}

Closeness from a common interval, and back.

\begin{code}

Close-from-interval : (ε p q : ℚ) (x y : ℝ)
                    → p < x → x < q → p < y → y < q
                    → q ℚ- p < ε
                    → Close ε x y
Close-from-interval ε p q x y a b c d e =
 ∣ (p , q) , (a , b) , (c , d) ,
   transport (_< ε) (ℚ<-to-abs' p q (cuts-are-ordered x p q a b) ⁻¹) e ∣

Common-Interval : ℚ → ℝ → ℝ → 𝓤₀ ̇
Common-Interval ε x y =
 Σ (p , q) ꞉ ℚ × ℚ , (p < x) × (x < q) × (p < y) × (y < q) × (q ℚ- p < ε)

interval-from-Close : (ε : ℚ) (x y : ℝ) → Close ε x y
                    → ∥ Common-Interval ε x y ∥
interval-from-Close ε x y = ∥∥-functor γ
 where
  γ : (Σ (p , q) ꞉ ℚ × ℚ , (p < x < q) × (p < y < q) × (abs (p ℚ- q) < ε))
    → Common-Interval ε x y
  γ ((p , q) , (a , b) , (c , d) , e) =
   (p , q) , a , b , c , d ,
   transport (_< ε) (ℚ<-to-abs' p q (cuts-are-ordered x p q a b)) e

\end{code}

Bounds from closeness: if x is within ε of y, then x is above every
lower bound of y minus ε, and below every upper bound of y plus ε.

\begin{code}

Close-below : (ε : ℚ) (x y : ℝ) → Close ε x y → (s : ℚ) → s < y → (s ℚ- ε) < x
Close-below ε x y c s l =
 ∥∥-rec (ℚ<ℝ-is-prop (s ℚ- ε) x) γ (interval-from-Close ε x y c)
 where
  γ : Common-Interval ε x y → (s ℚ- ε) < x
  γ ((p , q) , a , b , c' , d , e) = use-rounded-real-L x (s ℚ- ε) p I a
   where
    II : s < ε ℚ+ p
    II =
     ℚ<-trans s q (ε ℚ+ p) (cuts-are-ordered y s q l d) (<-move-right q ε p e)

    I : (s ℚ- ε) < p
    I = <-move-left s p ε (transport (s <_) (ℚ+-comm ε p) II)

Close-above : (ε : ℚ) (x y : ℝ) → Close ε x y → (s : ℚ) → y < s → x < (s ℚ+ ε)
Close-above ε x y c s l =
 ∥∥-rec (ℝ<ℚ-is-prop x (s ℚ+ ε)) γ (interval-from-Close ε x y c)
 where
  γ : Common-Interval ε x y → x < (s ℚ+ ε)
  γ ((p , q) , a , b , c' , d , e) = use-rounded-real-R x q (s ℚ+ ε) I b
   where
    II : q < ε ℚ+ s
    II = ℚ<-trans q (ε ℚ+ p) (ε ℚ+ s) (<-move-right q ε p e)
          (ℚ<-add-left ε p s (cuts-are-ordered y p s c' l))

    I : q < s ℚ+ ε
    I = transport (q <_) (ℚ+-comm ε s) II

\end{code}

Symmetry, monotonicity and the triangle inequality. The last is
TypeTopology's ℝ-m4.

\begin{code}

Close-sym : (ε : ℚ) (x y : ℝ) → Close ε x y → Close ε y x
Close-sym ε x y = ∥∥-functor γ
 where
  γ : (Σ (p , q) ꞉ ℚ × ℚ , (p < x < q) × (p < y < q) × (abs (p ℚ- q) < ε))
    → Σ (p , q) ꞉ ℚ × ℚ , (p < y < q) × (p < x < q) × (abs (p ℚ- q) < ε)
  γ ((p , q) , a , b , e) = (p , q) , b , a , e

Close-weaken : (ε δ : ℚ) (x y : ℝ) → ε ≤ δ → Close ε x y → Close δ x y
Close-weaken ε δ x y k = ∥∥-functor γ
 where
  γ : (Σ (p , q) ꞉ ℚ × ℚ , (p < x < q) × (p < y < q) × (abs (p ℚ- q) < ε))
    → Σ (p , q) ꞉ ℚ × ℚ , (p < x < q) × (p < y < q) × (abs (p ℚ- q) < δ)
  γ ((p , q) , a , b , e) = (p , q) , a , b , ℚ<-≤-trans (abs (p ℚ- q)) ε δ e k

Close-trans : (ε δ : ℚ) (x y z : ℝ)
            → 0ℚ < ε → 0ℚ < δ
            → Close ε x y → Close δ y z → Close (ε ℚ+ δ) x z
Close-trans ε δ x y z l m = ℝ-m4 x y z (ε , l) (δ , m)

\end{code}

Every rational interval around t contains a ball around t: if
r < r₁ < t < r₂ < r', the ball of radius min (r₁ - r) (r' - r₂)
around t lies in (r , r').

We avoid local definitions of rationals, such as δ = min δ₁ δ₂ in a
where clause. Agda compares such a name with its definition by
unfolding the rational arithmetic, which takes minutes. Instead, the
rationals are arguments of top-level lemmas or bound by patterns.

\begin{code}

≤-add-left : (a b c : ℚ) → b ≤ c → a ℚ+ b ≤ a ℚ+ c
≤-add-left a b c = ℚ≤-addition-preserves-order-left b c a

below-by-margin : (r r₁ δ δ₁ : ℚ) → δ ≤ δ₁ → r ℚ+ δ₁ ＝ r₁ → r ≤ r₁ ℚ- δ
below-by-margin r r₁ δ δ₁ k e =
 ≤-sub-right r r₁ δ (transport (r ℚ+ δ ≤_) e (≤-add-left r δ δ₁ k))

above-by-margin : (r₂ r' δ δ₂ : ℚ) → δ ≤ δ₂ → r₂ ℚ+ δ₂ ＝ r' → r₂ ℚ+ δ ≤ r'
above-by-margin r₂ r' δ δ₂ k e = transport (r₂ ℚ+ δ ≤_) e (≤-add-left r₂ δ δ₂ k)

ball-by-margins : (r r₁ r₂ r' δ : ℚ) (t : ℝ)
                → r₁ < t → t < r₂
                → r ≤ r₁ ℚ- δ → r₂ ℚ+ δ ≤ r'
                → (s : ℝ) → Close δ s t → (r < s) × (s < r')
ball-by-margins r r₁ r₂ r' δ t b d I II s k =
 use-rounded-real-L' s r (r₁ ℚ- δ) I (Close-below δ s t k r₁ b) ,
 use-rounded-real-R' s (r₂ ℚ+ δ) r' II (Close-above δ s t k r₂ d)

Ball-Inside : ℚ → ℚ → ℝ → ℚ → 𝓤₁ ̇
Ball-Inside r r' t δ = (0ℚ < δ) × ((s : ℝ) → Close δ s t → (r < s) × (s < r'))

ball-from-bounds : (r r₁ r₂ r' : ℚ) (t : ℝ)
                 → r < r₁ → r₁ < t → t < r₂ → r₂ < r'
                 → Ball-Inside r r' t (minₐ (r₁ ℚ- r) (r' ℚ- r₂))
ball-from-bounds r r₁ r₂ r' t a b d c =
 minₐ-is-positive (r₁ ℚ- r) (r' ℚ- r₂)
  (ℚ<-difference-positive r r₁ a) (ℚ<-difference-positive r₂ r' c) ,
 ball-by-margins r r₁ r₂ r' (minₐ (r₁ ℚ- r) (r' ℚ- r₂)) t b d
  (below-by-margin r r₁ (minₐ (r₁ ℚ- r) (r' ℚ- r₂)) (r₁ ℚ- r)
    (minₐ-≤-left (r₁ ℚ- r) (r' ℚ- r₂)) (add-difference r r₁))
  (above-by-margin r₂ r' (minₐ (r₁ ℚ- r) (r' ℚ- r₂)) (r' ℚ- r₂)
    (minₐ-≤-right (r₁ ℚ- r) (r' ℚ- r₂)) (add-difference r₂ r'))

ball-inside-interval : (r r' : ℚ) (t : ℝ) → r < t → t < r'
                     → ∃ δ ꞉ ℚ , Ball-Inside r r' t δ
ball-inside-interval r r' t l m =
 ∥∥-functor γ
  (binary-choice (rounded-left-d t r l)
                 (rounded-right-b (upper-cut-of t) (rounded-from-real-R t) r'
                   m))
 where
  γ : (Σ r₁ ꞉ ℚ , r < r₁ < t) × (Σ r₂ ꞉ ℚ , (r₂ < r') × (t < r₂))
    → Σ δ ꞉ ℚ , Ball-Inside r r' t δ
  γ ((r₁ , a , b) , (r₂ , c , d)) =
   minₐ (r₁ ℚ- r) (r' ℚ- r₂) , ball-from-bounds r r₁ r₂ r' t a b d c

\end{code}

Rational points. Every rational interval around t contains rationals
arbitrarily close to t, and two rational intervals around t contain a
common rational.

\begin{code}

rational-in-small-interval
 : (t : ℝ) (a b δ δ₀ : ℚ)
 → ((s : ℝ) → Close δ₀ s t → (a < s) × (s < b))
 → (Σ (u , v) ꞉ ℚ × ℚ , (u < t < v) × (v ℚ- u < minₐ δ δ₀))
 → Σ r ꞉ ℚ , (a < r) × (r < b) × Close δ (ιₐ r) t
rational-in-small-interval t a b δ δ₀ f ((u , v) , (c , d) , w) =
 γ (ℚ-dense u v (cuts-are-ordered t u v c d))
 where
  γ : (Σ r ꞉ ℚ , (u < r) × (r < v))
    → Σ r ꞉ ℚ , (a < r) × (r < b) × Close δ (ιₐ r) t
  γ (r , e , e') = r , ιₐ-lower⁻¹ a r (pr₁ II) , ιₐ-upper⁻¹ r b (pr₂ II) ,
                   Close-weaken (minₐ δ δ₀) δ (ιₐ r) t (minₐ-≤-left δ δ₀) I
   where
    I : Close (minₐ δ δ₀) (ιₐ r) t
    I = Close-from-interval (minₐ δ δ₀) u v (ιₐ r) t (ιₐ-lower u r e)
         (ιₐ-upper r v e') c d w

    II : (a < ιₐ r) × (ιₐ r < b)
    II = f (ιₐ r) (Close-weaken (minₐ δ δ₀) δ₀ (ιₐ r) t (minₐ-≤-right δ δ₀) I)

rational-near : (t : ℝ) (a b δ : ℚ) → a < t → t < b → 0ℚ < δ
              → ∃ r ꞉ ℚ , (a < r) × (r < b) × Close δ (ιₐ r) t
rational-near t a b δ l m o =
 ∥∥-rec ∃-is-prop γ (ball-inside-interval a b t l m)
 where
  γ : (Σ δ₀ ꞉ ℚ , Ball-Inside a b t δ₀)
    → ∃ r ꞉ ℚ , (a < r) × (r < b) × Close δ (ιₐ r) t
  γ (δ₀ , o₀ , f) =
   ∥∥-functor (rational-in-small-interval t a b δ δ₀ f)
    (ℝ-arithmetically-located t (minₐ δ δ₀ , minₐ-is-positive δ δ₀ o o₀))

common-rational-point : (t : ℝ) (a b a' b' : ℚ)
                      → a < t → t < b → a' < t → t < b'
                      → ∃ r ꞉ ℚ , ((a < r) × (r < b)) × ((a' < r) × (r < b'))
common-rational-point t a b a' b' l m l' m' =
 ∥∥-rec ∃-is-prop γ (ball-inside-interval a' b' t l' m')
 where
  γ : (Σ δ ꞉ ℚ , Ball-Inside a' b' t δ)
    → ∃ r ꞉ ℚ , ((a < r) × (r < b)) × ((a' < r) × (r < b'))
  γ (δ , o , f) = ∥∥-functor ζ (rational-near t a b δ l m o)
   where
    ζ : (Σ r ꞉ ℚ , (a < r) × (r < b) × Close δ (ιₐ r) t)
      → Σ r ꞉ ℚ , ((a < r) × (r < b)) × ((a' < r) × (r < b'))
    ζ (r , c , d , k) = r , (c , d) ,
                        (ιₐ-lower⁻¹ a' r (pr₁ (f (ιₐ r) k)) ,
                          ιₐ-upper⁻¹ r b' (pr₂ (f (ιₐ r) k)))

\end{code}

Rational facts about margins, shared by the extensions of
gist.RealCohesion.CrispExtension and gist.RealCohesion.RationalBoxExtension.
They were in gist.RealCohesion.CrispUniformContinuity and
gist.RealCohesion.CrispExtension, which re-export them.

\begin{code}

minus-positive-is-below : (p ε : ℚ) → 0ℚ < ε → p ℚ- ε < p
minus-positive-is-below = ℚ<-subtraction-preserves-order

gap-from-margin : (c d₁ δ : ℚ) → δ ℚ+ δ < d₁ ℚ- c → (c ℚ+ δ) < (d₁ ℚ- δ)
gap-from-margin c d₁ δ l = <-sub-right (c ℚ+ δ) d₁ δ
                            (transport₂ _<_ (ℚ+-assoc c δ δ ⁻¹)
                              (add-difference c d₁)
                              (ℚ<-add-left c (δ ℚ+ δ) (d₁ ℚ- c) l))

twice-a-quarter : (δ w : ℚ) → 0ℚ < w → δ ≤ halfₐ (halfₐ w) → δ ℚ+ δ < w
twice-a-quarter δ w l k =
 ℚ≤-<-trans (δ ℚ+ δ) (halfₐ (halfₐ w) ℚ+ halfₐ (halfₐ w)) w
  (ℚ≤-adding δ (halfₐ (halfₐ w)) δ (halfₐ (halfₐ w)) k k)
  (transport (_< w) (halvesₐ-add-up (halfₐ w) ⁻¹) (halfₐ-is-less w l))

quarter-is-positive : (w : ℚ) → 0ℚ < w → 0ℚ < halfₐ (halfₐ w)
quarter-is-positive w l = halfₐ-is-positive (halfₐ w) (halfₐ-is-positive w l)

below-by-half-margin : (p p₂ : ℚ) → p < p₂ → p < p₂ ℚ- halfₐ (p₂ ℚ- p)
below-by-half-margin p p₂ o =
 <-sub-right p p₂ (halfₐ (p₂ ℚ- p))
  (transport (p ℚ+ halfₐ (p₂ ℚ- p) <_) (add-difference p p₂)
    (ℚ<-add-left p (halfₐ (p₂ ℚ- p)) (p₂ ℚ- p)
      (halfₐ-is-less (p₂ ℚ- p) (ℚ<-difference-positive p p₂ o))))

quarters-leave-a-gap : (p q : ℚ) → p < q
                     → (p ℚ+ halfₐ (halfₐ (q ℚ- p)))
                     < (q ℚ- halfₐ (halfₐ (q ℚ- p)))
quarters-leave-a-gap p q l = gap-from-margin p q (halfₐ (halfₐ (q ℚ- p)))
                              (twice-a-quarter (halfₐ (halfₐ (q ℚ- p))) (q ℚ- p)
                                (ℚ<-difference-positive p q l)
                                (ℚ≤-refl (halfₐ (halfₐ (q ℚ- p)))))

\end{code}

The minimum of finitely many rationals, positive if they all are, and
below each of them.

\begin{code}

Fin-minₐ : {n : ℕ} → (Fin n → ℚ) → ℚ
Fin-minₐ {0}      t = 1ℚ
Fin-minₐ {succ n} t = minₐ (t 𝟎) (Fin-minₐ (t ∘ suc))

Fin-minₐ-is-positive : {n : ℕ} (t : Fin n → ℚ) → ((i : Fin n) → 0ℚ < t i)
                     → 0ℚ < Fin-minₐ t
Fin-minₐ-is-positive {0}      t h = 0<1
Fin-minₐ-is-positive {succ n} t h =
 minₐ-is-positive (t 𝟎) (Fin-minₐ (t ∘ suc)) (h 𝟎)
  (Fin-minₐ-is-positive (t ∘ suc) (h ∘ suc))

Fin-minₐ-≤ : {n : ℕ} (t : Fin n → ℚ) (i : Fin n) → Fin-minₐ t ≤ t i
Fin-minₐ-≤ {0}      t i       = 𝟘-elim i
Fin-minₐ-≤ {succ n} t 𝟎       = minₐ-≤-left (t 𝟎) (Fin-minₐ (t ∘ suc))
Fin-minₐ-≤ {succ n} t (suc i) =
 ℚ≤-trans (Fin-minₐ t) (Fin-minₐ (t ∘ suc)) (t (suc i))
  (minₐ-≤-right (t 𝟎) (Fin-minₐ (t ∘ suc))) (Fin-minₐ-≤ (t ∘ suc) i)

\end{code}
