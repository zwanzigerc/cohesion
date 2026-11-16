Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 11 November 2026. See the AI disclosure in
gist.RealCohesion.index.

Rational detection, from Axiom R♭ alone (GPT-6 Astra).

For any function h : ℝ → ℝ, not necessarily crisp: if h x > 0 for some
real x, then h q > 0 for some rational q [1, §3], [2, Corollary 7.6].
We assume only that every map ℝ → Q is constant, which follows from
Axiom R♭ (gist.RealCohesion.FiniteChainDiscreteness).

The proof is Astra's. First translate x by a rational, so that it lies
between 1/2 and 1/2 + 2⁻⁵. At each level j, the two staircase
quantizers of gist.RealCohesion.Quantizers have values within
2⁻⁽ʲ⁺¹⁾ of x, and merely one of the two values is rational. Scale h so
that it exceeds 1 at x. Sequential hitting along the pair of
sequences (gist.RealCohesion.PairHitting), applied to
H u v = min (h u , h v), gives a level at which h is positive at both
values, one of which is rational. The rational approximations and the
rational values are never chosen for all levels at once, so no
countable choice is used.

With the same hypothesis we derive:

 * rational detection for a window u < f < v, and for two functions
   at once;

 * the approximate intermediate value theorem with a rational witness
   [2, Theorem 4.2];

 * rational detection in n variables: for h : ℝⁿ → ℝ, not necessarily
   crisp, if h x > 0 at some point x, then h q > 0 at some rational
   point q. This was added by Claude Opus 5.5 on 12 November 2026, as
   gate G16(b) of Claude Fable 5.2's second addendum [3, §3]. It is
   the first step of the proof of Lemma 7.15 of the write-up [4],
   dyadic detection (GPT-6 Astra), which then passes from the rational
   point to a dyadic one.

[1] GPT-6 Astra. Positive rational detection, 10 November 2026.
    references/A11-positive-rational-detection.txt

[2] Answers to some open problems in real-cohesive homotopy type
    theory. Research notes, revised 10 November 2026.
    references/C02-write-up-2026-11-10.tex

[3] Claude Fable 5.2. Second addendum to the formalization plan,
    revision 4 of 12 November 2026.
    references/F13b-second-addendum-rev4-as-amended.md

[4] Answers to some open problems in real-cohesive homotopy type
    theory. Research notes, revision of 12 November 2026.
    references/C04-write-up-2026-11-12.tex

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.RationalDetection
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import Fin.Type
open import Notation.CanonicalMap
open import Notation.Order
open import UF.Base
open import Rationals.Type
open import Rationals.Order
open import Rationals.Addition renaming (_+_ to _ℚ+_)
open import Rationals.Negation renaming (_-_ to _ℚ-_ ; -_ to ℚ-_)
open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import DedekindReals.Properties fe pe pt using (ℝ-arithmetically-located)
open import gist.RealCohesion.RationalArithmetic
 using (add-difference ; minus-zero ; <-move-right)
open import gist.RealCohesion.RationalPoints fe pe pt
open import gist.RealCohesion.RealLattice fe pe pt
open import gist.RealCohesion.RealLimits fe pe pt
 using (ρ ; ρ-is-positive ; ρ-becomes-small ; within ; plus-minus)
open import gist.RealCohesion.FiniteChainQuotient fe pe pt using (Q)
open import gist.RealCohesion.IntervalHitting fe pe pt
 using (window ; window-is-positive⁻¹)
open import gist.RealCohesion.ApproximateIVTReduction fe pe pt
 using (dbl^ ; dbl^-is-monotone ; dbl^-of-ρ ; dbl^-of-zero ; dbl-ℝ ;
        below-dbl-ℝ ; below-dbl-ℝ⁻¹ ; approximate-IVT-from-constancy)
open import gist.RealCohesion.Quantizers fe pe pt using (module level)
open import gist.RealCohesion.PairHitting fe pe pt using (pair-hitting)
open import gist.RealCohesion.FinVectors using (Fin-cons ; Fin-cons-of-parts)

open PropositionalTruncation pt

\end{code}

Translating a strict upper bound or a strict lower bound, and the
positivity of a window. The translation of lower bounds was added on
12 November 2026, for gist.RealCohesion.CrispFunctionsOfSeveralVariables.

\begin{code}

translation-identity : (q q' c : ℚ) → q ℚ+ c ＝ q' ℚ+ (c ℚ+ (q ℚ- q'))
translation-identity q q' c = ℚ+-comm q c
                            ∙ ap (c ℚ+_) (add-difference q' q ⁻¹)
                            ∙ ℚ+-assoc c q' (q ℚ- q') ⁻¹
                            ∙ ap (_ℚ+ (q ℚ- q')) (ℚ+-comm c q')
                            ∙ ℚ+-assoc q' c (q ℚ- q')

translate-upper : (t : ℝ) (q c : ℚ) → t < q → (t + ιₐ c) < (q ℚ+ c)
translate-upper t q c l =
 ∥∥-rec (ℝ<ℚ-is-prop (t + ιₐ c) (q ℚ+ c)) γ
  (rounded-right-b (upper-cut-of t) (rounded-from-real-R t) q l)
 where
  γ : (Σ q' ꞉ ℚ , (q' < q) × (t < q')) → (t + ιₐ c) < (q ℚ+ c)
  γ (q' , k , l') = sum-below' t (ιₐ c) (q ℚ+ c) q' (c ℚ+ (q ℚ- q')) l'
                     (ιₐ-upper c (c ℚ+ (q ℚ- q'))
                       (ℚ<-addition-preserves-order'' c (q ℚ- q')
                         (ℚ<-difference-positive q' q k)))
                     (translation-identity q q' c)

translate-lower : (t : ℝ) (q c : ℚ) → q < t → (q ℚ+ c) < (t + ιₐ c)
translate-lower t q c l =
 ∥∥-rec (ℚ<ℝ-is-prop (q ℚ+ c) (t + ιₐ c)) γ (rounded-left-d t q l)
 where
  γ : (Σ q' ꞉ ℚ , (q < q') × (q' < t)) → (q ℚ+ c) < (t + ιₐ c)
  γ (q' , k , l') = below-sum' t (ιₐ c) (q ℚ+ c) q' (c ℚ+ (q ℚ- q')) l'
                     (ιₐ-lower (c ℚ+ (q ℚ- q')) c
                       (transport₂ _<_ (ℚ+-comm (q ℚ- q') c)
                         (ℚ-zero-left-neutral c)
                         (ℚ<-addition-preserves-order (q ℚ- q') 0ℚ c
                           (ℚ<-difference-positive' q q' k))))
                     (translation-identity q q' c)

window-is-positive : (f : ℝ → ℝ) (y : ℝ) (u v : ℚ)
                   → u < f y → f y < v → 0ℚ < window 0 f u v y
window-is-positive f y u v l m =
 transport (_< window 0 f u v y) (dbl^-of-zero 1)
  (below-dbl-ℝ 1 (min (f y + ιₐ (ℚ- u)) (ιₐ v + (- f y))) 0ℚ
    (below-min (f y + ιₐ (ℚ- u)) (ιₐ v + (- f y)) 0ℚ
      (translate-strict (f y) 0ℚ u
        (transport (_< f y) (ℚ-zero-left-neutral u ⁻¹) l))
      (reflect-strict (f y) 0ℚ v (transport (f y <_) (minus-zero v ⁻¹) m))))

\end{code}

From now on we assume that every map ℝ → Q is constant.

\begin{code}

module _ (ν : (k : ℝ → Q) (u v : ℝ) → k u ＝ k v) where

 rational-detection : (h : ℝ → ℝ) (x : ℝ) → 0ℚ < h x → ∃ q ꞉ ℚ , 0ℚ < h (ιₐ q)
 rational-detection h x h-positive =
  ∥∥-rec ∃-is-prop γ (ℝ-arithmetically-located x (ρ 4 , ρ-is-positive 4))
  where
   γ : (Σ (a , b) ꞉ ℚ × ℚ , ((a < x) × (x < b)) × (b ℚ- a < ρ 4))
     → ∃ q ꞉ ℚ , 0ℚ < h (ιₐ q)
   γ ((a , b) , (l , m') , d) =
    ∥∥-rec ∃-is-prop δ (rounded-left-d (h x) 0ℚ h-positive)
    where
     c : ℚ
     c = 1/2 ℚ- a

     x' : ℝ
     x' = x + ιₐ c

     h' : ℝ → ℝ
     h' s = h (s + ιₐ (ℚ- c))

     x'-above : 1/2 < x'
     x'-above = transport₂ (λ (u : ℚ) (v : ℝ) → u < v)
                 (add-difference a 1/2)
                 (ap (λ - → x + ιₐ -) (ℚ-minus-minus c ⁻¹))
                 (translate-strict x (a ℚ+ c) (ℚ- c)
                   (transport (_< x) (plus-minus a c ⁻¹) l))

     x-below : x < a ℚ+ ρ 4
     x-below = use-rounded-real-R x b (a ℚ+ ρ 4)
                (transport (b <_) (ℚ+-comm (ρ 4) a) (<-move-right b (ρ 4) a d))
                 m'

     x'-below : x' < 1/2 ℚ+ ρ 4
     x'-below =
      transport (x' <_) identity (translate-upper x (a ℚ+ ρ 4) c x-below)
      where
       identity : (a ℚ+ ρ 4) ℚ+ c ＝ 1/2 ℚ+ ρ 4
       identity = ℚ+-assoc a (ρ 4) c
                ∙ ap (a ℚ+_) (ℚ+-comm (ρ 4) c)
                ∙ ℚ+-assoc a c (ρ 4) ⁻¹
                ∙ ap (_ℚ+ ρ 4) (add-difference a 1/2)

     h'-at-x' : h' x' ＝ h x
     h'-at-x' = ap h (translate-twice x c (ℚ- c)
                      ∙ ap (λ - → x + ιₐ -) (ℚ-inverse-sum-to-zero c)
                      ∙ plus-zero x)

     δ : (Σ c₀ ꞉ ℚ , (0ℚ < c₀) × (c₀ < h x)) → ∃ q ꞉ ℚ , 0ℚ < h (ιₐ q)
     δ (c₀ , p₀ , q₀) =
      ∥∥-rec ∃-is-prop ε (pair-hitting ν H x' y⁰ y¹ close⁰ close¹ H-at-x')
      where
       small : Σ n ꞉ ℕ , ρ n < c₀
       small = ρ-becomes-small c₀ p₀

       M : ℕ
       M = succ (pr₁ small)

       H : ℝ → ℝ → ℝ
       H u v = min (dbl-ℝ M (h' u)) (dbl-ℝ M (h' v))

       large : 1ℚ < dbl-ℝ M (h' x')
       large = transport (λ - → 1ℚ < dbl-ℝ M -) (h'-at-x' ⁻¹)
                (use-rounded-real-L (dbl-ℝ M (h x)) 1ℚ (dbl^ M c₀)
                  (transport (_< dbl^ M c₀) (dbl^-of-ρ (pr₁ small))
                    (dbl^-is-monotone M (ρ (pr₁ small)) c₀ (pr₂ small)))
                  (below-dbl-ℝ M (h x) c₀ q₀))

       H-at-x' : ιₐ 1ℚ ≤ H x' x'
       H-at-x' = >-gives-ιₐ-≤ (H x' x') 1ℚ
                  (below-min (dbl-ℝ M (h' x')) (dbl-ℝ M (h' x')) 1ℚ large large)

       y⁰ y¹ : ℕ → ℝ
       y⁰ j = level.Q⁰ j x'
       y¹ j = level.Q¹ j x'

       close⁰ : (j : ℕ) → within (ρ j) (y⁰ j) x'
       close⁰ j = level.Q⁰-close j x' x'-above x'-below

       close¹ : (j : ℕ) → within (ρ j) (y¹ j) x'
       close¹ j = level.Q¹-close j x' x'-above x'-below

       positive : (u : ℝ) → 0ℚ < dbl-ℝ M (h' u) → 0ℚ < h' u
       positive u p = below-dbl-ℝ⁻¹ M (h' u) 0ℚ
                       (transport (_< dbl-ℝ M (h' u)) (dbl^-of-zero M ⁻¹) p)

       rational-point : (q : ℚ) → 0ℚ < h' (ιₐ q) → ∃ q' ꞉ ℚ , 0ℚ < h (ιₐ q')
       rational-point q p =
        ∣ q ℚ+ (ℚ- c) , transport (λ - → 0ℚ < h -) (ιₐ-sum q (ℚ- c)) p ∣

       ε : (Σ k ꞉ ℕ , 0ℚ < H (y⁰ k) (y¹ k)) → ∃ q ꞉ ℚ , 0ℚ < h (ιₐ q)
       ε (k , p) =
        ∥∥-rec ∃-is-prop ζ (level.Q-is-rational k x' x'-above x'-below)
        where
         p⁰ : 0ℚ < h' (y⁰ k)
         p⁰ = positive (y⁰ k)
               (below-min-left (dbl-ℝ M (h' (y⁰ k))) (dbl-ℝ M (h' (y¹ k))) 0ℚ p)

         p¹ : 0ℚ < h' (y¹ k)
         p¹ = positive (y¹ k)
               (below-min-right (dbl-ℝ M (h' (y⁰ k))) (dbl-ℝ M (h' (y¹ k))) 0ℚ
                 p)

         ζ : (Σ q ꞉ ℚ , y⁰ k ＝ ιₐ q) ∔ (Σ q ꞉ ℚ , y¹ k ＝ ιₐ q)
           → ∃ q ꞉ ℚ , 0ℚ < h (ιₐ q)
         ζ (inl (q , e)) = rational-point q (transport (λ - → 0ℚ < h' -) e p⁰)
         ζ (inr (q , e)) = rational-point q (transport (λ - → 0ℚ < h' -) e p¹)

\end{code}

Rational detection for windows.

\begin{code}

 rational-detection-window : (f : ℝ → ℝ) (y : ℝ) (u v : ℚ)
                           → u < f y → f y < v
                           → ∃ q ꞉ ℚ , (u < f (ιₐ q)) × (f (ιₐ q) < v)
 rational-detection-window f y u v l m =
  ∥∥-functor γ
   (rational-detection (window 0 f u v) y (window-is-positive f y u v l m))
  where
   γ : (Σ q ꞉ ℚ , 0ℚ < window 0 f u v (ιₐ q))
     → Σ q ꞉ ℚ , (u < f (ιₐ q)) × (f (ιₐ q) < v)
   γ (q , p) = q , window-is-positive⁻¹ 0 f u v (ιₐ q) p

 rational-detection-window₂
  : (f g : ℝ → ℝ) (y : ℝ) (u v u' v' : ℚ)
  → u < f y → f y < v → u' < g y → g y < v'
  → ∃ q ꞉ ℚ ,
      ((u < f (ιₐ q)) × (f (ιₐ q) < v)) × ((u' < g (ιₐ q)) × (g (ιₐ q) < v'))
 rational-detection-window₂ f g y u v u' v' l m l' m' =
  ∥∥-functor γ (rational-detection h y
                 (below-min (window 0 f u v y) (window 0 g u' v' y) 0ℚ
                   (window-is-positive f y u v l m)
                    (window-is-positive g y u' v' l' m')))
  where
   h : ℝ → ℝ
   h w = min (window 0 f u v w) (window 0 g u' v' w)

   γ : (Σ q ꞉ ℚ , 0ℚ < h (ιₐ q))
     → Σ q ꞉ ℚ ,
         ((u < f (ιₐ q)) × (f (ιₐ q) < v)) × ((u' < g (ιₐ q)) × (g (ιₐ q) < v'))
   γ (q , p) = q ,
               window-is-positive⁻¹ 0 f u v (ιₐ q)
                (below-min-left (window 0 f u v (ιₐ q))
                  (window 0 g u' v' (ιₐ q)) 0ℚ p) ,
               window-is-positive⁻¹ 0 g u' v' (ιₐ q)
                (below-min-right (window 0 f u v (ιₐ q))
                  (window 0 g u' v' (ιₐ q)) 0ℚ p)

\end{code}

The approximate intermediate value theorem with a rational witness.

\begin{code}

 approximate-IVT-with-rational-witness-from-constancy
  : (f : ℝ → ℝ) (p q a b : ℝ)
  → p < q → f a < q → p < f b
  → ∃ r ꞉ ℚ , (p < f (ι r)) × (f (ι r) < q)
 approximate-IVT-with-rational-witness-from-constancy f p q a b l m n =
  ∥∥-rec ∃-is-prop γ (approximate-IVT-from-constancy ν f p q a b l m n)
  where
   γ : (Σ x ꞉ ℝ , (p < f x) × (f x < q))
     → ∃ r ꞉ ℚ , (p < f (ι r)) × (f (ι r) < q)
   γ (x , o , o') = ∥∥-rec ∃-is-prop δ (binary-choice o o')
    where
     δ : (Σ s ꞉ ℚ , (p < s) × (s < f x)) × (Σ t ꞉ ℚ , (f x < t) × (t < q))
       → ∃ r ꞉ ℚ , (p < f (ι r)) × (f (ι r) < q)
     δ ((s , ps , sf) , (t , ft , tq)) =
      ∥∥-functor ε (rational-detection-window f x s t sf ft)
      where
       ε : (Σ r ꞉ ℚ , (s < f (ιₐ r)) × (f (ιₐ r) < t))
         → Σ r ꞉ ℚ , (p < f (ι r)) × (f (ι r) < q)
       ε (r , sr , rt) = r ,
                         ∣ s , ps , transport (λ - → s < f -) (ιₐ-is-ι r) sr ∣ ,
                         ∣ t , transport (λ - → f - < t) (ιₐ-is-ι r) rt , tq ∣

\end{code}

Rational detection in n variables, by induction on n, one coordinate
at a time, as the second addendum proposes [3, §3]. For n + 1: the
function t ↦ h (t , x ∘ suc) is positive at the first coordinate of x,
so at some rational q₀; then y ↦ h (q₀ , y) is positive at x ∘ suc,
and the induction hypothesis applies to it.

\begin{code}

 rational-detection-in-dimension
  : (n : ℕ) (h : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
  → 0ℚ < h x → ∃ q ꞉ (Fin n → ℚ) , 0ℚ < h (λ i → ιₐ (q i))
 rational-detection-in-dimension 0 h x l =
  ∣ 𝟘-elim , transport (λ - → 0ℚ < h -) (dfunext fe (λ i → 𝟘-elim i)) l ∣
 rational-detection-in-dimension (succ n) h x l =
  ∥∥-rec ∃-is-prop γ
   (rational-detection (λ t → h (Fin-cons t (x ∘ suc))) (x 𝟎)
     (transport (λ - → 0ℚ < h -) (Fin-cons-of-parts fe x ⁻¹) l))
  where
   γ : (Σ q₀ ꞉ ℚ , 0ℚ < h (Fin-cons (ιₐ q₀) (x ∘ suc)))
     → ∃ q ꞉ (Fin (succ n) → ℚ) , 0ℚ < h (λ i → ιₐ (q i))
   γ (q₀ , m) = ∥∥-functor δ
                 (rational-detection-in-dimension n
                   (λ y → h (Fin-cons (ιₐ q₀) y)) (x ∘ suc) m)
    where
     δ : (Σ q' ꞉ (Fin n → ℚ) , 0ℚ < h (Fin-cons (ιₐ q₀) (λ i → ιₐ (q' i))))
       → Σ q ꞉ (Fin (succ n) → ℚ) , 0ℚ < h (λ i → ιₐ (q i))
     δ (q' , m') = Fin-cons q₀ q' , transport (λ - → 0ℚ < h -) (dfunext fe I) m'
      where
       I : Fin-cons (ιₐ q₀) (λ i → ιₐ (q' i)) ∼ (λ i → ιₐ (Fin-cons q₀ q' i))
       I 𝟎       = refl
       I (suc i) = refl

\end{code}
