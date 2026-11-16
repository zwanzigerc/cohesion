Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 11 November 2026. See the AI disclosure in
gist.RealCohesion.index.

ε-δ continuous maps on the crisp reals, and their uniform continuity
on bounded intervals.

Shulman's Corollary 11.6 [1] concerns the maps h : ♭ ℝ → ♭ ℝ that are
ε-δ continuous: for every x : ♭ ℝ and every rational ε > 0 there is a
rational δ > 0 such that |y - x| < δ implies |h y - h x| < ε for every
y : ♭ ℝ, where y and h y are read as real numbers through the counit
of ♭ [2, §3]. We state |u - v| < ε with TypeTopology's rational balls
B-ℝ (gist.RealCohesion.RealBalls).

To show that such a map comes from a crisp function ℝ → ℝ, Shulman's
proof uses excluded middle in the discrete world, which makes h
uniformly continuous on every bounded interval, as Fable's note
describes it [3, Part A.4]. We prove this for crisp h from crisp
excluded middle, through the classical connectedness of crisp rational
intervals (gist.RealCohesion.CrispConnectedness), in place of the
usual compactness argument.

Fix crisp rationals a and ε, and let U t say that h is uniformly
continuous with tolerance ε on the crisp points of (a , t).

 * U holds at a, vacuously.

 * U and its negation are open at crisp points. By continuity at a
   crisp point t, h oscillates by less than ε on the crisp points of
   some rational interval (c , e) around t. If U holds at a point s of
   that interval, gluing (a , s) to (c , e) gives uniform continuity
   on (a , e), hence U at every point below e. This moves U from t to
   the points of (c , e), and from any point of (c , e) to t.

So U holds at every crisp rational b > a. Crisp representatives of
rationals carry this to all rationals a < b and ε > 0, and give
around every real x, crisp or not, a rational interval on whose crisp
points h oscillates by less than ε. That is what the extension in
gist.RealCohesion.CrispExtension uses.

[1] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer
    Science 28(6), 856–941, 2018. https://arxiv.org/abs/1509.07584v3

[2] Answers to some open problems in real-cohesive homotopy type
    theory. Research notes, revised 10 November 2026, §3.
    references/C02-write-up-2026-11-10.tex

[3] Fable. Shulman's stated questions: three updates, Part A.
    Working note, 10 November 2026, audited by GPT-6 Astra.
    references/F18-shulman-three-updates.md

\begin{code}

{-# OPTIONS --safe --without-K --cohesion --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import gist.CohesiveApartness.Flat

module gist.RealCohesion.CrispUniformContinuity
        (@♭ fe : Fun-Ext)
        (@♭ pe : Prop-Ext)
        (@♭ pt : propositional-truncations-exist)
       where

open import Notation.CanonicalMap
open import Notation.Order
open import UF.Base
open import UF.Subsingletons-FunExt
open import Rationals.Type
open import Rationals.Order
open import Rationals.Addition renaming (_+_ to _ℚ+_)
open import Rationals.Negation renaming (_-_ to _ℚ-_ ; -_ to ℚ-_)
open import Rationals.Positive using (ℚ₊)
open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import DedekindReals.Properties fe pe pt using (ℝ-arithmetically-located)
open import MetricSpaces.DedekindReals fe pe pt using (B-ℝ)
open import gist.RealCohesion.RationalArithmetic
 using (add-difference ; <-sub-right)
open import gist.RealCohesion.RationalPoints fe pe pt
open import gist.RealCohesion.RealOrder fe pe pt
 using (below-a-real ; above-a-real ; cuts-are-ordered)
open import gist.RealCohesion.RealLattice fe pe pt using (ℝ<ℚ-is-prop)
open import gist.RealCohesion.RealLimits fe pe pt
 using (plus-minus ; minus-plus ; ℚ<-add-left)
open import gist.RealCohesion.RealBalls fe pe pt
 hiding (minus-positive-is-below ; gap-from-margin ; twice-a-quarter ;
          quarter-is-positive ;
         below-by-half-margin ; quarters-leave-a-gap)
open import gist.RealCohesion.RealBalls fe pe pt
 using (minus-positive-is-below ; gap-from-margin ; twice-a-quarter ;
         quarter-is-positive)
 public
open import gist.RealCohesion.CrispRationals
 using (ℚ-has-crisp-representatives ; crisp-elim ; crisp-elim₂)
open import gist.RealCohesion.CrispConnectedness fe pe pt
 using (Open-At-Crisp-Points ; crisp-interval-is-connected)

open PropositionalTruncation pt

\end{code}

ε-δ continuity of maps ♭ ℝ → ♭ ℝ.

\begin{code}

is-ε-δ-continuous : (♭ ℝ → ♭ ℝ) → 𝓤₁ ̇
is-ε-δ-continuous h =
   (x : ♭ ℝ) (ε : ℚ₊)
 → ∃ δ ꞉ ℚ₊ , ((y : ♭ ℝ) → B-ℝ (♭-counit y) (♭-counit x) δ
                         → B-ℝ (♭-counit (h y)) (♭-counit (h x)) ε)

being-ε-δ-continuous-is-prop : (h : ♭ ℝ → ♭ ℝ) → is-prop (is-ε-δ-continuous h)
being-ε-δ-continuous-is-prop h =
 Π-is-prop fe (λ x → Π-is-prop fe (λ ε → ∃-is-prop))

\end{code}

Facts about the order used below.

\begin{code}

below-ιₐ⁻¹ : (x : ℝ) (e : ℚ) → x < ιₐ e → x < e
below-ιₐ⁻¹ x e = ∥∥-rec (ℝ<ℚ-is-prop x e) γ
 where
  γ : (Σ q ꞉ ℚ , (x < q) × (q < ιₐ e)) → x < e
  γ (q , m , n) = use-rounded-real-R x q e (ιₐ-lower⁻¹ q e n) m

below-ιₐ : (x : ℝ) (e : ℚ) → x < e → x < ιₐ e
below-ιₐ x e l =
 ∥∥-functor γ (rounded-right-b (upper-cut-of x) (rounded-from-real-R x) e l)
 where
  γ : (Σ q ꞉ ℚ , (q < e) × (x < q)) → Σ q ꞉ ℚ , (x < q) × (q < ιₐ e)
  γ (q , m , n) = q , n , ιₐ-lower q e m

below-through : (x : ℝ) (q : ℚ) (d : ℝ) → x < q → q < d → x < d
below-through x q d m n = ∣ q , m , n ∣

below-below : (x s : ℝ) (e : ℚ) → x < s → s < e → x < ιₐ e
below-below x s e l m = ∥∥-functor γ l
 where
  γ : (Σ q ꞉ ℚ , (x < q) × (q < s)) → Σ q ꞉ ℚ , (x < q) × (q < ιₐ e)
  γ (q , n , o) = q , n , ιₐ-lower q e (cuts-are-ordered s q e o m)

nothing-between : (a : ℚ) (x : ℝ) → a < x → x < ι a → 𝟘 {𝓤₀}
nothing-between a x l m = ∥∥-rec 𝟘-is-prop γ m
 where
  γ : (Σ q ꞉ ℚ , (x < q) × (q < ι a)) → 𝟘
  γ (q , n , o) = ℚ<-irrefl a (ℚ<-trans a q a (cuts-are-ordered x a q l n) o)


\end{code}

We now fix a crisp ε-δ continuous map h, and assume crisp excluded
middle.

\begin{code}

module uniform-continuity
        (@♭ cem : Crisp-EM 𝓤₁)
        (@♭ h : ♭ ℝ → ♭ ℝ)
        (@♭ h-is-continuous : is-ε-δ-continuous h)
       where

 g : ♭ ℝ → ℝ
 g y = ♭-counit (h y)

 Small-Oscillation : ℚ → ℚ → ℚ → 𝓤₁ ̇
 Small-Oscillation ε a b =
    (y z : ♭ ℝ)
  → a < ♭-counit y → ♭-counit y < b
  → a < ♭-counit z → ♭-counit z < b
  → Close ε (g y) (g z)

 UC-Condition : ℚ → ℚ → ℝ → ℚ → 𝓤₁ ̇
 UC-Condition ε a t δ =
    (y z : ♭ ℝ)
  → a < ♭-counit y → ♭-counit y < t
  → a < ♭-counit z → ♭-counit z < t
  → Close δ (♭-counit y) (♭-counit z)
  → Close ε (g y) (g z)

 Uniformly-Continuous-Below : ℚ → ℚ → ℝ → 𝓤₁ ̇
 Uniformly-Continuous-Below ε a t = ∃ δ ꞉ ℚ , (0ℚ < δ) × UC-Condition ε a t δ

\end{code}

Small oscillation near crisp points.

\begin{code}

 oscillation-from-center
  : (t v : ℝ) (ε δ c e : ℚ)
  → 0ℚ < ε
  → ((y : ♭ ℝ) → Close δ (♭-counit y) t → Close (halfₐ ε) (g y) v)
  → c < t → t < e → e ℚ- c < δ
  → Small-Oscillation ε c e
 oscillation-from-center t v ε δ c e l f a b w y z p q p' q' =
  transport (λ - → Close - (g y) (g z)) (halvesₐ-add-up ε)
   (Close-trans (halfₐ ε) (halfₐ ε) (g y) v (g z)
     (halfₐ-is-positive ε l) (halfₐ-is-positive ε l)
     (f y (Close-from-interval δ c e (♭-counit y) t p q a b w))
     (Close-sym (halfₐ ε) (g z) v
       (f z (Close-from-interval δ c e (♭-counit z) t p' q' a b w))))

 local-small-oscillation : (@♭ t : ℝ) (ε : ℚ) → 0ℚ < ε
                         → ∃ (c , e) ꞉ ℚ × ℚ ,
                             (c < t) × (t < e) × Small-Oscillation ε c e
 local-small-oscillation t ε l =
  ∥∥-rec ∃-is-prop γ (h-is-continuous (t ^♭) (halfₐ ε , halfₐ-is-positive ε l))
  where
   γ : (Σ δ ꞉ ℚ₊ , ((y : ♭ ℝ) → B-ℝ (♭-counit y) t δ
                              → B-ℝ (g y) (g (t ^♭))
                                 (halfₐ ε , halfₐ-is-positive ε l)))
     → ∃ (c , e) ꞉ ℚ × ℚ , (c < t) × (t < e) × Small-Oscillation ε c e
   γ ((δ , m) , f) = ∥∥-functor ζ (ℝ-arithmetically-located t (δ , m))
    where
     ζ : (Σ (c , e) ꞉ ℚ × ℚ , (c < t < e) × (e ℚ- c < δ))
       → Σ (c , e) ꞉ ℚ × ℚ , (c < t) × (t < e) × Small-Oscillation ε c e
     ζ ((c , e) , (a , b) , w) =
      (c , e) , a , b , oscillation-from-center t (g (t ^♭)) ε δ c e l f a b w

\end{code}

Gluing and restricting.

\begin{code}

 glue-with-radius
  : (ε a c e δ₁ d₁ δ : ℚ) (d : ℝ)
  → d₁ < d
  → 0ℚ < δ → δ ≤ δ₁
  → (c ℚ+ δ) < (d₁ ℚ- δ)
  → UC-Condition ε a d δ₁
  → Small-Oscillation ε c e
  → UC-Condition ε a (ιₐ e) δ
 glue-with-radius ε a c e δ₁ d₁ δ d n o k gap F osc y z p q p' q' cl =
  ∥∥-rec (Close-is-prop ε (g y) (g z)) H
   (ℝ-locatedness (♭-counit y) (c ℚ+ δ) (d₁ ℚ- δ) gap)
  where
   cl' : Close δ (♭-counit z) (♭-counit y)
   cl' = Close-sym δ (♭-counit y) (♭-counit z) cl

   H : ((c ℚ+ δ) < ♭-counit y) ∔ (♭-counit y < (d₁ ℚ- δ)) → Close ε (g y) (g z)
   H (inl r) = osc y z
                (below-a-real (♭-counit y) c (c ℚ+ δ)
                  (ℚ<-addition-preserves-order'' c δ o) r)
                (below-ιₐ⁻¹ (♭-counit y) e q)
                (transport (_< ♭-counit z) (plus-minus c δ)
                  (Close-below δ (♭-counit z) (♭-counit y) cl' (c ℚ+ δ) r))
                (below-ιₐ⁻¹ (♭-counit z) e q')
   H (inr r) = F y z p (below-through (♭-counit y) d₁ d y-below n)
                     p' (below-through (♭-counit z) d₁ d z-below n)
                     (Close-weaken δ δ₁ (♭-counit y) (♭-counit z) k cl)
    where
     y-below : ♭-counit y < d₁
     y-below =
      above-a-real (♭-counit y) (d₁ ℚ- δ) d₁ (minus-positive-is-below d₁ δ o) r

     z-below : ♭-counit z < d₁
     z-below = transport (♭-counit z <_) (minus-plus d₁ δ)
                (Close-above δ (♭-counit z) (♭-counit y) cl' (d₁ ℚ- δ) r)

 glue-radius-is-positive : (c d₁ δ₁ : ℚ) → c < d₁ → 0ℚ < δ₁
                         → 0ℚ < minₐ δ₁ (halfₐ (halfₐ (d₁ ℚ- c)))
 glue-radius-is-positive c d₁ δ₁ n l₁ =
  minₐ-is-positive δ₁ (halfₐ (halfₐ (d₁ ℚ- c))) l₁
   (quarter-is-positive (d₁ ℚ- c) (ℚ<-difference-positive c d₁ n))

 glued : (ε a c e δ₁ d₁ : ℚ) (d : ℝ)
       → c < d₁ → d₁ < d → 0ℚ < δ₁
       → UC-Condition ε a d δ₁
       → Small-Oscillation ε c e
       → Σ δ ꞉ ℚ , (0ℚ < δ) × UC-Condition ε a (ιₐ e) δ
 glued ε a c e δ₁ d₁ d n n' l₁ F osc =
  minₐ δ₁ (halfₐ (halfₐ (d₁ ℚ- c))) ,
  glue-radius-is-positive c d₁ δ₁ n l₁ ,
  glue-with-radius ε a c e δ₁ d₁ (minₐ δ₁ (halfₐ (halfₐ (d₁ ℚ- c)))) d n'
   (glue-radius-is-positive c d₁ δ₁ n l₁)
   (minₐ-≤-left δ₁ (halfₐ (halfₐ (d₁ ℚ- c))))
   (gap-from-margin c d₁ (minₐ δ₁ (halfₐ (halfₐ (d₁ ℚ- c))))
     (twice-a-quarter (minₐ δ₁ (halfₐ (halfₐ (d₁ ℚ- c)))) (d₁ ℚ- c)
       (ℚ<-difference-positive c d₁ n)
       (minₐ-≤-right δ₁ (halfₐ (halfₐ (d₁ ℚ- c))))))
   F osc

 glue : (ε a c e : ℚ) (d : ℝ)
      → c < d
      → Uniformly-Continuous-Below ε a d
      → Small-Oscillation ε c e
      → Uniformly-Continuous-Below ε a (ιₐ e)
 glue ε a c e d m uc osc =
  ∥∥-functor γ (binary-choice uc (rounded-left-d d c m))
  where
   γ : (Σ δ₁ ꞉ ℚ , (0ℚ < δ₁) × UC-Condition ε a d δ₁) × (Σ d₁ ꞉ ℚ , c < d₁ < d)
     → Σ δ ꞉ ℚ , (0ℚ < δ) × UC-Condition ε a (ιₐ e) δ
   γ ((δ₁ , l₁ , F) , (d₁ , n , n')) = glued ε a c e δ₁ d₁ d n n' l₁ F osc

 restrict : (ε a δ : ℚ) (t s : ℝ)
          → ((x : ℝ) → x < s → x < t)
          → UC-Condition ε a t δ
          → UC-Condition ε a s δ
 restrict ε a δ t s k F y z p q p' q' =
  F y z p (k (♭-counit y) q) p' (k (♭-counit z) q')

 restrict-UC : (ε a : ℚ) (t s : ℝ)
             → ((x : ℝ) → x < s → x < t)
             → Uniformly-Continuous-Below ε a t
             → Uniformly-Continuous-Below ε a s
 restrict-UC ε a t s k = ∥∥-functor γ
  where
   γ : (Σ δ ꞉ ℚ , (0ℚ < δ) × UC-Condition ε a t δ)
     → Σ δ ꞉ ℚ , (0ℚ < δ) × UC-Condition ε a s δ
   γ (δ , l , F) = δ , l , restrict ε a δ t s k F

\end{code}

Uniform continuity and its failure are open at crisp points.

\begin{code}

 UC-is-open
  : (ε a : ℚ) → 0ℚ < ε
  → (@♭ t : ℝ) → Uniformly-Continuous-Below ε a t
  → ∃ (r , r') ꞉ ℚ × ℚ , (r < t) × (t < r')
                       × ((@♭ s : ℝ) → r < s → s < r'
                          → Uniformly-Continuous-Below ε a s)
 UC-is-open ε a l t u = ∥∥-functor γ (local-small-oscillation t ε l)
  where
   γ : (Σ (c , e) ꞉ ℚ × ℚ , (c < t) × (t < e) × Small-Oscillation ε c e)
     → Σ (r , r') ꞉ ℚ × ℚ , (r < t) × (t < r')
                          × ((@♭ s : ℝ) → r < s → s < r'
                             → Uniformly-Continuous-Below ε a s)
   γ ((c , e) , p , q , osc) = (c , e) , p , q , δ
    where
     δ : (@♭ s : ℝ) → c < s → s < e → Uniformly-Continuous-Below ε a s
     δ s _ m = restrict-UC ε a (ιₐ e) s (λ x n → below-below x s e n m)
                (glue ε a c e t p u osc)

 UC-failure-is-open
  : (ε a : ℚ) → 0ℚ < ε
  → (@♭ t : ℝ) → ¬ Uniformly-Continuous-Below ε a t
  → ∃ (r , r') ꞉ ℚ × ℚ , (r < t) × (t < r')
                       × ((@♭ s : ℝ) → r < s → s < r'
                          → ¬ Uniformly-Continuous-Below ε a s)
 UC-failure-is-open ε a l t ν = ∥∥-functor γ (local-small-oscillation t ε l)
  where
   γ : (Σ (c , e) ꞉ ℚ × ℚ , (c < t) × (t < e) × Small-Oscillation ε c e)
     → Σ (r , r') ꞉ ℚ × ℚ , (r < t) × (t < r')
                          × ((@♭ s : ℝ) → r < s → s < r'
                             → ¬ Uniformly-Continuous-Below ε a s)
   γ ((c , e) , p , q , osc) = (c , e) , p , q , δ
    where
     δ : (@♭ s : ℝ) → c < s → s < e → ¬ Uniformly-Continuous-Below ε a s
     δ s m _ u = ν (restrict-UC ε a (ιₐ e) t (λ x n → below-below x t e n q)
                     (glue ε a c e s m u osc))

 UC-at-left-end : (ε a : ℚ) → Uniformly-Continuous-Below ε a (ι a)
 UC-at-left-end ε a = ∣ 1ℚ , 0<1 , vacuous ∣
  where
   vacuous : UC-Condition ε a (ι a) 1ℚ
   vacuous y z p q _ _ _ = 𝟘-elim (nothing-between a (♭-counit y) p q)

\end{code}

Uniform continuity on crisp rational intervals, by connectedness, and
then on all rational intervals.

\begin{code}

 uniformly-continuous-on-crisp-intervals
  : (@♭ ε a b : ℚ) → 0ℚ < ε → a < b → Uniformly-Continuous-Below ε a (ι b)
 uniformly-continuous-on-crisp-intervals ε a b l m =
  lr-implication
   (crisp-interval-is-connected cem (Uniformly-Continuous-Below ε a)
     (λ t → ∃-is-prop)
     a b m open-U open-¬U)
   (UC-at-left-end ε a)
  where
   open-U : Open-At-Crisp-Points cem (Uniformly-Continuous-Below ε a)
            (λ t → ∃-is-prop) a b
             (Uniformly-Continuous-Below ε a)
   open-U t _ _ = UC-is-open ε a l t

   open-¬U : Open-At-Crisp-Points cem (Uniformly-Continuous-Below ε a)
             (λ t → ∃-is-prop) a b
              (λ t → ¬ Uniformly-Continuous-Below ε a t)
   open-¬U t _ _ = UC-failure-is-open ε a l t

 uniformly-continuous-on-intervals
  : (ε a b : ℚ) → 0ℚ < ε → a < b → Uniformly-Continuous-Below ε a (ιₐ b)
 uniformly-continuous-on-intervals ε a b =
  crisp-elim₂ ℚ-has-crisp-representatives ℚ-has-crisp-representatives
   (λ ε a → 0ℚ < ε → a < b → Uniformly-Continuous-Below ε a (ιₐ b))
   (λ ε₀ a₀ → crisp-elim ℚ-has-crisp-representatives
               (λ b →
                 0ℚ < ε₀ → a₀ < b → Uniformly-Continuous-Below ε₀ a₀ (ιₐ b))
               (λ b₀ l m →
                 transport (Uniformly-Continuous-Below ε₀ a₀) (ιₐ-is-ι b₀ ⁻¹)
                            (uniformly-continuous-on-crisp-intervals ε₀ a₀ b₀ l
                              m))
               b)
   ε a

\end{code}

Small oscillation around every real number, crisp or not.

\begin{code}

 oscillation-from-uniform-continuity
  : (ε c d δ₁ δ₀ a b : ℚ) (x : ℝ)
  → UC-Condition ε c (ιₐ d) δ₁
  → ((s : ℝ) → Close δ₀ s x → (c < s) × (s < d))
  → a < x → x < b → b ℚ- a < minₐ δ₁ δ₀
  → Small-Oscillation ε a b
 oscillation-from-uniform-continuity ε c d δ₁ δ₀ a b x F f m n w y z o o' r r' =
  F y z (pr₁ (inside y o o')) (below-ιₐ (♭-counit y) d (pr₂ (inside y o o')))
        (pr₁ (inside z r r')) (below-ιₐ (♭-counit z) d (pr₂ (inside z r r')))
        (Close-weaken (minₐ δ₁ δ₀) δ₁ (♭-counit y) (♭-counit z)
          (minₐ-≤-left δ₁ δ₀)
          (Close-from-interval (minₐ δ₁ δ₀) a b (♭-counit y) (♭-counit z) o o' r
            r' w))
  where
   inside : (u : ♭ ℝ) → a < ♭-counit u → ♭-counit u < b
          → (c < ♭-counit u) × (♭-counit u < d)
   inside u k k' = f (♭-counit u)
                    (Close-weaken (minₐ δ₁ δ₀) δ₀ (♭-counit u) x
                      (minₐ-≤-right δ₁ δ₀)
                      (Close-from-interval (minₐ δ₁ δ₀) a b (♭-counit u) x k k'
                        m n w))

 interval-with-small-oscillation
  : (ε c d δ₁ δ₀ : ℚ) (x : ℝ)
  → UC-Condition ε c (ιₐ d) δ₁
  → ((s : ℝ) → Close δ₀ s x → (c < s) × (s < d))
  → (Σ (a , b) ꞉ ℚ × ℚ , (a < x < b) × (b ℚ- a < minₐ δ₁ δ₀))
  → Σ (a , b) ꞉ ℚ × ℚ , (a < x) × (x < b) × Small-Oscillation ε a b
 interval-with-small-oscillation ε c d δ₁ δ₀ x F f ((a , b) , (m , n) , w) =
  (a , b) , m , n ,
   oscillation-from-uniform-continuity ε c d δ₁ δ₀ a b x F f m n w

 small-oscillation-around
  : (x : ℝ) (ε : ℚ) → 0ℚ < ε
  → ∃ (a , b) ꞉ ℚ × ℚ , (a < x) × (x < b) × Small-Oscillation ε a b
 small-oscillation-around x ε l =
  ∥∥-rec ∃-is-prop γ
   (binary-choice (inhabited-from-real-L x) (inhabited-from-real-R x))
  where
   γ : (Σ c ꞉ ℚ , c < x) × (Σ d ꞉ ℚ , x < d)
     → ∃ (a , b) ꞉ ℚ × ℚ , (a < x) × (x < b) × Small-Oscillation ε a b
   γ ((c , p) , (d , q)) =
    ∥∥-rec ∃-is-prop δ
     (binary-choice
       (uniformly-continuous-on-intervals ε c d l (cuts-are-ordered x c d p q))
                    (ball-inside-interval c d x p q))
    where
     δ : (Σ δ₁ ꞉ ℚ , (0ℚ < δ₁) × UC-Condition ε c (ιₐ d) δ₁)
       × (Σ δ₀ ꞉ ℚ , Ball-Inside c d x δ₀)
       → ∃ (a , b) ꞉ ℚ × ℚ , (a < x) × (x < b) × Small-Oscillation ε a b
     δ ((δ₁ , l₁ , F) , (δ₀ , l₀ , f)) =
      ∥∥-functor (interval-with-small-oscillation ε c d δ₁ δ₀ x F f)
       (ℝ-arithmetically-located x (minₐ δ₁ δ₀ , minₐ-is-positive δ₁ δ₀ l₁ l₀))

\end{code}
