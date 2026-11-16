Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. See the AI disclosure in
gist.RealCohesion.index.

Three forms of continuity at a point, and their equivalence.

The library states continuity in two ways: by rational intervals, as
in gist.RealCohesion.CrispFunctionsEverywhere (for rationals u < f a < v,
there is a rational interval around a on which u < f < v), and by
TypeTopology's rational balls B-ℝ, as in
gist.RealCohesion.CrispUniformContinuity. The starter module of Claude
Fable 5.2's second addendum, gist.RealCohesion.ShulmanWeakeningsStatements,
uses a third: x is strictly within δ of a if x < a + δ and a < x + δ,
and f is continuous at a if for every rational ε > 0 there is a
rational δ > 0 such that every x strictly within δ of a has f x
strictly within ε of f a. This module shows that the three forms are
equivalent, so that the theorems of the library can be stated with the
types of the starter module.

The forms are stated for maps e g : X → ℝ and a point x₀ : X of an
arbitrary type: e gives the position of a point and g its value. For
continuity of f : ℝ → ℝ at a, X is ℝ, e is the identity and g is f;
for Shulman's Corollary 11.6, X is ♭ ℝ, e is the counit, and g is the
counit after a map ♭ ℝ → ♭ ℝ.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Fin.Type using (Fin)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.ContinuityForms
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import Notation.CanonicalMap
open import Notation.Order
open import Rationals.Type
open import Rationals.Order
open import Rationals.Positive using (ℚ₊)
open import Rationals.Addition renaming (_+_ to _ℚ+_)
open import Rationals.Negation renaming (_-_ to _ℚ-_ ; -_ to ℚ-_)
open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import DedekindReals.Properties fe pe pt using (ℝ-arithmetically-located)
open import DedekindReals.Addition fe pe pt using () renaming (_+_ to _+ᵗ_)
open import MetricSpaces.DedekindReals fe pe pt using (B-ℝ)
open import gist.RealCohesion.RationalArithmetic
 using (add-difference ; <-move-left ; <-move-right)
open import gist.RealCohesion.RationalPoints fe pe pt
open import gist.RealCohesion.RealOrder fe pe pt using (cuts-are-ordered)
open import gist.RealCohesion.RealLattice fe pe pt
 using (ℚ<ℝ-is-prop ; ℝ<ℚ-is-prop ; below-sum⁻¹ ; translate-strict ; +-is-+ᵗ)
 renaming (_+_ to _ℝ+_)
open import gist.RealCohesion.RealLimits fe pe pt using (ℚ<-add-left)
open import gist.RealCohesion.RealBalls fe pe pt
 using (minₐ ; minₐ-≤-left ; minₐ-≤-right ; minₐ-is-positive ; Close ;
         Close-from-interval ;
        below-by-margin ; above-by-margin ; ball-inside-interval)

open PropositionalTruncation pt

\end{code}

Strict closeness, in the starter's terms (TypeTopology's sum and
embedding) and in the abstract terms of gist.RealCohesion.RealLattice.

\begin{code}

Strictly-Within : ℚ → ℝ → ℝ → 𝓤₀ ̇
Strictly-Within δ x a = (x < a +ᵗ ι δ) × (a < x +ᵗ ι δ)

Strictly-Close : ℚ → ℝ → ℝ → 𝓤₀ ̇
Strictly-Close δ x a = (x < a ℝ+ ιₐ δ) × (a < x ℝ+ ιₐ δ)

plus-ιₐ-is-plus-ι : (x : ℝ) (δ : ℚ) → x ℝ+ ιₐ δ ＝ x +ᵗ ι δ
plus-ιₐ-is-plus-ι x δ = +-is-+ᵗ x (ιₐ δ) ∙ ap (x +ᵗ_) (ιₐ-is-ι δ)

within-from-close : (δ : ℚ) (x a : ℝ) → Strictly-Close δ x a
                  → Strictly-Within δ x a
within-from-close δ x a (k , k') = transport (x <_) (plus-ιₐ-is-plus-ι a δ) k ,
                                   transport (a <_) (plus-ιₐ-is-plus-ι x δ) k'

close-from-within : (δ : ℚ) (x a : ℝ) → Strictly-Within δ x a
                  → Strictly-Close δ x a
close-from-within δ x a (k , k') =
 transport (x <_) (plus-ιₐ-is-plus-ι a δ ⁻¹) k ,
                                   transport (a <_) (plus-ιₐ-is-plus-ι x δ ⁻¹)
                                    k'

\end{code}

Two points of a rational interval of length less than ε are strictly
within ε of each other. A point strictly within δ of t is above every
lower bound of t minus δ, and below every upper bound of t plus δ.

\begin{code}

below-by-less-than : (ε u v : ℚ) (y z : ℝ)
                   → y < v → u < z → v ℚ- u < ε → y < z ℝ+ ιₐ ε
below-by-less-than ε u v y z b c w = ∣ v , b , II ∣
 where
  I : (v ℚ- ε) < z
  I = use-rounded-real-L z (v ℚ- ε) u
       (<-move-left v u ε
         (transport (v <_) (ℚ+-comm ε u) (<-move-right v ε u w))) c

  II : v < z ℝ+ ιₐ ε
  II = transport (λ - → v < z ℝ+ ιₐ -) (ℚ-minus-minus ε ⁻¹)
        (translate-strict z v (ℚ- ε) I)

interval-gives-strictly-close : (ε u v : ℚ) (y z : ℝ)
                              → u < y → y < v → u < z → z < v → v ℚ- u < ε
                              → Strictly-Close ε y z
interval-gives-strictly-close ε u v y z a b c d w =
 below-by-less-than ε u v y z b c w , below-by-less-than ε u v z y d a w

strictly-close-below : (δ : ℚ) (x t : ℝ) → t < x ℝ+ ιₐ δ → (s : ℚ) → s < t
                     → (s ℚ- δ) < x
strictly-close-below δ x t k s l = ∥∥-rec (ℚ<ℝ-is-prop (s ℚ- δ) x) γ k
 where
  γ : (Σ q ꞉ ℚ , (t < q) × (q < x ℝ+ ιₐ δ)) → (s ℚ- δ) < x
  γ (q , m , n) = ∥∥-rec (ℚ<ℝ-is-prop (s ℚ- δ) x) δ'
                   (below-sum⁻¹ x (ιₐ δ) s (use-rounded-real-L (x ℝ+ ιₐ δ) s q
                                             (cuts-are-ordered t s q l m) n))
   where
    δ' : (Σ (r , r') ꞉ ℚ × ℚ , (r < x) × (r' < ιₐ δ) × (s ＝ r ℚ+ r'))
       → (s ℚ- δ) < x
    δ' ((r , r') , o , o' , e) =
     use-rounded-real-L x (s ℚ- δ) r
      (<-move-left s r δ (transport (_< r ℚ+ δ) (e ⁻¹)
                           (ℚ<-add-left r r' δ (ιₐ-lower⁻¹ r' δ o'))))
      o

strictly-close-above : (δ : ℚ) (x t : ℝ) → x < t ℝ+ ιₐ δ → (s : ℚ) → t < s
                     → x < (s ℚ+ δ)
strictly-close-above δ x t k s l = ∥∥-rec (ℝ<ℚ-is-prop x (s ℚ+ δ)) γ k
 where
  γ : (Σ q ꞉ ℚ , (x < q) × (q < t ℝ+ ιₐ δ)) → x < (s ℚ+ δ)
  γ (q , m , n) = ∥∥-rec (ℝ<ℚ-is-prop x (s ℚ+ δ)) δ' (below-sum⁻¹ t (ιₐ δ) q n)
   where
    δ' : (Σ (r , r') ꞉ ℚ × ℚ , (r < t) × (r' < ιₐ δ) × (q ＝ r ℚ+ r'))
       → x < (s ℚ+ δ)
    δ' ((r , r') , o , o' , e) =
     use-rounded-real-R x q (s ℚ+ δ)
      (transport (_< s ℚ+ δ) (e ⁻¹)
        (ℚ<-adding r s r' δ (cuts-are-ordered t r s o l) (ιₐ-lower⁻¹ r' δ o')))
      m

\end{code}

Every rational interval around t contains all points strictly within
some δ of t, as in gist.RealCohesion.RealBalls for its balls.

\begin{code}

Strict-Ball-Inside : ℚ → ℚ → ℝ → ℚ → 𝓤₁ ̇
Strict-Ball-Inside r r' t δ =
 (0ℚ < δ) × ((s : ℝ) → Strictly-Close δ s t → (r < s) × (s < r'))

strict-ball-by-margins : (r r₁ r₂ r' δ : ℚ) (t : ℝ)
                       → r₁ < t → t < r₂
                       → r ≤ r₁ ℚ- δ → r₂ ℚ+ δ ≤ r'
                       → (s : ℝ) → Strictly-Close δ s t → (r < s) × (s < r')
strict-ball-by-margins r r₁ r₂ r' δ t b d I II s (k , k') =
 use-rounded-real-L' s r (r₁ ℚ- δ) I (strictly-close-below δ s t k' r₁ b) ,
 use-rounded-real-R' s (r₂ ℚ+ δ) r' II (strictly-close-above δ s t k r₂ d)

strict-ball-inside-interval : (r r' : ℚ) (t : ℝ) → r < t → t < r'
                            → ∃ δ ꞉ ℚ , Strict-Ball-Inside r r' t δ
strict-ball-inside-interval r r' t l m =
 ∥∥-functor γ
  (binary-choice (rounded-left-d t r l)
                 (rounded-right-b (upper-cut-of t) (rounded-from-real-R t) r'
                   m))
 where
  γ : (Σ r₁ ꞉ ℚ , r < r₁ < t) × (Σ r₂ ꞉ ℚ , (r₂ < r') × (t < r₂))
    → Σ δ ꞉ ℚ , Strict-Ball-Inside r r' t δ
  γ ((r₁ , a , b) , (r₂ , c , d)) =
   minₐ (r₁ ℚ- r) (r' ℚ- r₂) ,
   minₐ-is-positive (r₁ ℚ- r) (r' ℚ- r₂)
    (ℚ<-difference-positive r r₁ a) (ℚ<-difference-positive r₂ r' c) ,
   strict-ball-by-margins r r₁ r₂ r' (minₐ (r₁ ℚ- r) (r' ℚ- r₂)) t b d
    (below-by-margin r r₁ (minₐ (r₁ ℚ- r) (r' ℚ- r₂)) (r₁ ℚ- r)
      (minₐ-≤-left (r₁ ℚ- r) (r' ℚ- r₂)) (add-difference r r₁))
    (above-by-margin r₂ r' (minₐ (r₁ ℚ- r) (r' ℚ- r₂)) (r' ℚ- r₂)
      (minₐ-≤-right (r₁ ℚ- r) (r' ℚ- r₂)) (add-difference r₂ r'))

\end{code}

The three forms of continuity of g at x₀, with positions e.

\begin{code}

module _ {𝓥 : Universe} {X : 𝓥 ̇ } (e g : X → ℝ) (x₀ : X) where

 Interval-Continuous : 𝓥 ̇
 Interval-Continuous =
    (u v : ℚ) → u < g x₀ → g x₀ < v
  → ∃ (r , r') ꞉ ℚ × ℚ , (r < e x₀) × (e x₀ < r')
                       × ((y : X) → r < e y → e y < r' → (u < g y) × (g y < v))

 Ball-Continuous : 𝓥 ̇
 Ball-Continuous =
    (ε : ℚ₊)
  → ∃ δ ꞉ ℚ₊ , ((y : X) → B-ℝ (e y) (e x₀) δ → B-ℝ (g y) (g x₀) ε)

 Strictly-Continuous : 𝓥 ̇
 Strictly-Continuous =
    (ε : ℚ)
  → 0ℚ < ε
  → ∃ δ ꞉ ℚ , (0ℚ < δ)
            × ((y : X) → Strictly-Within δ (e y) (e x₀)
               → Strictly-Within ε (g y) (g x₀))

\end{code}

From intervals to the strict form, and back. For ε, take rationals
u < g x₀ < v with v - u < ε, an interval around e x₀ for them, and a
strict ball inside that interval. For u < g x₀ < v, take ε with a
strict ball around g x₀ inside (u , v), the δ for it, and an interval
around e x₀ of length less than δ.

\begin{code}

 interval-gives-strict : Interval-Continuous → Strictly-Continuous
 interval-gives-strict c ε o =
  ∥∥-rec ∃-is-prop γ (ℝ-arithmetically-located (g x₀) (ε , o))
  where
   γ : (Σ (u , v) ꞉ ℚ × ℚ , ((u < g x₀) × (g x₀ < v)) × (v ℚ- u < ε))
     → ∃ δ ꞉ ℚ , (0ℚ < δ)
               × ((y : X) → Strictly-Within δ (e y) (e x₀)
                  → Strictly-Within ε (g y) (g x₀))
   γ ((u , v) , (a , b) , w) = ∥∥-rec ∃-is-prop δ' (c u v a b)
    where
     δ' : (Σ (r , r') ꞉ ℚ × ℚ , (r < e x₀) × (e x₀ < r')
                              × ((y : X) → r < e y → e y < r'
                                 → (u < g y) × (g y < v)))
        → ∃ δ ꞉ ℚ , (0ℚ < δ)
                  × ((y : X) → Strictly-Within δ (e y) (e x₀)
                     → Strictly-Within ε (g y) (g x₀))
     δ' ((r , r') , l , m , h) =
      ∥∥-functor ζ (strict-ball-inside-interval r r' (e x₀) l m)
      where
       ζ : (Σ δ ꞉ ℚ , Strict-Ball-Inside r r' (e x₀) δ)
         → Σ δ ꞉ ℚ , (0ℚ < δ)
                   × ((y : X) → Strictly-Within δ (e y) (e x₀)
                      → Strictly-Within ε (g y) (g x₀))
       ζ (δ , p , k) = δ , p , θ
        where
         θ : (y : X) → Strictly-Within δ (e y) (e x₀)
           → Strictly-Within ε (g y) (g x₀)
         θ y n = within-from-close ε (g y) (g x₀)
                  (interval-gives-strictly-close ε u v (g y) (g x₀)
                    (pr₁ (h y (pr₁ I) (pr₂ I))) (pr₂ (h y (pr₁ I) (pr₂ I))) a b
                     w)
          where
           I : (r < e y) × (e y < r')
           I = k (e y) (close-from-within δ (e y) (e x₀) n)

 strict-gives-interval : Strictly-Continuous → Interval-Continuous
 strict-gives-interval c u v a b =
  ∥∥-rec ∃-is-prop γ (strict-ball-inside-interval u v (g x₀) a b)
  where
   γ : (Σ ε ꞉ ℚ , Strict-Ball-Inside u v (g x₀) ε)
     → ∃ (r , r') ꞉ ℚ × ℚ , (r < e x₀) × (e x₀ < r')
                          ×
                          ((y : X) → r < e y → e y < r' → (u < g y) × (g y < v))
   γ (ε , o , k) = ∥∥-rec ∃-is-prop δ' (c ε o)
    where
     δ' : (Σ δ ꞉ ℚ , (0ℚ < δ)
                   × ((y : X) → Strictly-Within δ (e y) (e x₀)
                      → Strictly-Within ε (g y) (g x₀)))
        → ∃ (r , r') ꞉ ℚ × ℚ , (r < e x₀) × (e x₀ < r')
                             × ((y : X) → r < e y → e y < r'
                                → (u < g y) × (g y < v))
     δ' (δ , p , h) = ∥∥-functor ζ (ℝ-arithmetically-located (e x₀) (δ , p))
      where
       ζ : (Σ (r , r') ꞉ ℚ × ℚ , ((r < e x₀) × (e x₀ < r')) × (r' ℚ- r < δ))
         → Σ (r , r') ꞉ ℚ × ℚ , (r < e x₀) × (e x₀ < r')
                              × ((y : X) → r < e y → e y < r'
                                 → (u < g y) × (g y < v))
       ζ ((r , r') , (l , m) , w) = (r , r') , l , m , θ
        where
         θ : (y : X) → r < e y → e y < r' → (u < g y) × (g y < v)
         θ y n n' = k (g y)
                     (close-from-within ε (g y) (g x₀)
                       (h y (within-from-close δ (e y) (e x₀)
                              (interval-gives-strictly-close δ r r' (e y) (e x₀)
                                n n' l m w))))

\end{code}

From intervals to balls, and back, in the same way, with the balls of
gist.RealCohesion.RealBalls. For a positive rational ε, Close ε is
B-ℝ with radius ε by definition.

\begin{code}

 interval-gives-ball : Interval-Continuous → Ball-Continuous
 interval-gives-ball c (ε , o) =
  ∥∥-rec ∃-is-prop γ (ℝ-arithmetically-located (g x₀) (ε , o))
  where
   γ : (Σ (u , v) ꞉ ℚ × ℚ , ((u < g x₀) × (g x₀ < v)) × (v ℚ- u < ε))
     → ∃ δ ꞉ ℚ₊ , ((y : X) → B-ℝ (e y) (e x₀) δ → B-ℝ (g y) (g x₀) (ε , o))
   γ ((u , v) , (a , b) , w) = ∥∥-rec ∃-is-prop δ' (c u v a b)
    where
     δ' : (Σ (r , r') ꞉ ℚ × ℚ , (r < e x₀) × (e x₀ < r')
                              × ((y : X) → r < e y → e y < r'
                                 → (u < g y) × (g y < v)))
        → ∃ δ ꞉ ℚ₊ , ((y : X) → B-ℝ (e y) (e x₀) δ → B-ℝ (g y) (g x₀) (ε , o))
     δ' ((r , r') , l , m , h) =
      ∥∥-functor ζ (ball-inside-interval r r' (e x₀) l m)
      where
       ζ :
        (Σ δ ꞉ ℚ , (0ℚ < δ) × ((s : ℝ) → Close δ s (e x₀) → (r < s) × (s < r')))
         → Σ δ ꞉ ℚ₊ , ((y : X) → B-ℝ (e y) (e x₀) δ → B-ℝ (g y) (g x₀) (ε , o))
       ζ (δ , p , k) = (δ , p) , θ
        where
         θ : (y : X) → B-ℝ (e y) (e x₀) (δ , p) → B-ℝ (g y) (g x₀) (ε , o)
         θ y n = Close-from-interval ε u v (g y) (g x₀)
                  (pr₁ (h y (pr₁ (k (e y) n)) (pr₂ (k (e y) n))))
                  (pr₂ (h y (pr₁ (k (e y) n)) (pr₂ (k (e y) n))))
                  a b w

 ball-gives-interval : Ball-Continuous → Interval-Continuous
 ball-gives-interval c u v a b =
  ∥∥-rec ∃-is-prop γ (ball-inside-interval u v (g x₀) a b)
  where
   γ : (Σ ε ꞉ ℚ , (0ℚ < ε) × ((s : ℝ) → Close ε s (g x₀) → (u < s) × (s < v)))
     → ∃ (r , r') ꞉ ℚ × ℚ , (r < e x₀) × (e x₀ < r')
                          ×
                          ((y : X) → r < e y → e y < r' → (u < g y) × (g y < v))
   γ (ε , o , k) = ∥∥-rec ∃-is-prop δ' (c (ε , o))
    where
     δ' : (Σ δ ꞉ ℚ₊ , ((y : X) → B-ℝ (e y) (e x₀) δ → B-ℝ (g y) (g x₀) (ε , o)))
        → ∃ (r , r') ꞉ ℚ × ℚ , (r < e x₀) × (e x₀ < r')
                             × ((y : X) → r < e y → e y < r'
                                → (u < g y) × (g y < v))
     δ' ((δ , p) , h) = ∥∥-functor ζ (ℝ-arithmetically-located (e x₀) (δ , p))
      where
       ζ : (Σ (r , r') ꞉ ℚ × ℚ , ((r < e x₀) × (e x₀ < r')) × (r' ℚ- r < δ))
         → Σ (r , r') ꞉ ℚ × ℚ , (r < e x₀) × (e x₀ < r')
                              × ((y : X) → r < e y → e y < r'
                                 → (u < g y) × (g y < v))
       ζ ((r , r') , (l , m) , w) = (r , r') , l , m , θ
        where
         θ : (y : X) → r < e y → e y < r' → (u < g y) × (g y < v)
         θ y n n' =
          k (g y) (h y (Close-from-interval δ r r' (e y) (e x₀) n n' l m w))

 ball-gives-strict : Ball-Continuous → Strictly-Continuous
 ball-gives-strict c = interval-gives-strict (ball-gives-interval c)

 strict-gives-ball : Strictly-Continuous → Ball-Continuous
 strict-gives-ball c = interval-gives-ball (strict-gives-interval c)

\end{code}

Functions of n variables, with the supremum norm: continuity by
boxes, in which every coordinate is strictly within r of that of the
point, gives the strict ε-δ form of the starter module, as for one
variable. Added for gate G24
(gist.RealCohesion.CrispFunctionsOfSeveralVariables).

\begin{code}

module _ {n : ℕ} (F : (Fin n → ℝ) → ℝ) (a : Fin n → ℝ) where

 Box-Continuous : 𝓤₁ ̇
 Box-Continuous =
    (u v : ℚ) → u < F a → F a < v
  → ∃ r ꞉ ℚ , (0ℚ < r)
            × ((x : Fin n → ℝ) → ((j : Fin n) → Strictly-Close r (x j) (a j))
                               → (u < F x) × (F x < v))

 Coordinatewise-Strictly-Continuous : 𝓤₁ ̇
 Coordinatewise-Strictly-Continuous =
    (ε : ℚ)
  → 0ℚ < ε
  → ∃ δ ꞉ ℚ , (0ℚ < δ)
            × ((y : Fin n → ℝ) → ((i : Fin n) → Strictly-Within δ (y i) (a i))
                               → Strictly-Within ε (F y) (F a))

 box-gives-coordinatewise-strict : Box-Continuous
                                 → Coordinatewise-Strictly-Continuous
 box-gives-coordinatewise-strict c ε o =
  ∥∥-rec ∃-is-prop γ (ℝ-arithmetically-located (F a) (ε , o))
  where
   γ : (Σ (u , v) ꞉ ℚ × ℚ , ((u < F a) × (F a < v)) × (v ℚ- u < ε))
     → ∃ δ ꞉ ℚ , (0ℚ < δ)
               ×
               ((y : Fin n → ℝ) → ((i : Fin n) → Strictly-Within δ (y i) (a i))
                                → Strictly-Within ε (F y) (F a))
   γ ((u , v) , (l , m) , w) = ∥∥-functor δ (c u v l m)
    where
     δ : (Σ r ꞉ ℚ , (0ℚ < r)
                  × ((x : Fin n → ℝ)
                     → ((j : Fin n) → Strictly-Close r (x j) (a j))
                                     → (u < F x) × (F x < v)))
       → Σ δ ꞉ ℚ , (0ℚ < δ)
                 × ((y : Fin n → ℝ)
                    → ((i : Fin n) → Strictly-Within δ (y i) (a i))
                                    → Strictly-Within ε (F y) (F a))
     δ (r , p , h) = r , p , θ
      where
       θ : (y : Fin n → ℝ) → ((i : Fin n) → Strictly-Within r (y i) (a i))
         → Strictly-Within ε (F y) (F a)
       θ y b = within-from-close ε (F y) (F a)
                (interval-gives-strictly-close ε u v (F y) (F a)
                  (pr₁ I) (pr₂ I) l m w)
        where
         I : (u < F y) × (F y < v)
         I = h y (λ i → close-from-within r (y i) (a i) (b i))

\end{code}
