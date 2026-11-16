Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. See the AI disclosure in
gist.RealCohesion.index.

The estimates on the plane in the proof of Shulman's Theorem 12.6 for
the square (gate G25), §2.5 of Fable's note [1]. No multiplication of
reals occurs: only the order, addition and the lattice operations of
gist.RealCohesion.RealLattice.

For a rational ε with 0 < ε < 1 put η = ε/2, δ = ε/4 and c = 1 - η, and
let clamp-c t clamp t to [-c , c]. For a point z of the plane and the
modified map g, the proof compares zᵢ with gᵢ:

 * zᵢ is east or west of gᵢ by more than δ, or within η of it
   (margin-or-inside); being east (west) by more than δ puts
   zᵢ - gᵢ in the half-plane zᵢ - gᵢ > 0 (< 0) of the double cover
   (positive-from-margin, negative-from-margin);

 * clamp-c moves a point of [-1 , 1] by at most η (clamp-close-above,
   clamp-close-below), and its values lie in [-c , c];

 * on the lines x = ±2 and y = ±2 the margins hold, because the values
   of g lie in [-c , c] (east-margin, west-margin);

 * a point z with every |zᵢ - gᵢ| < η lies in the cube, and if
   gᵢ = clamp-c tᵢ for a point t of the cube, then |tᵢ - zᵢ| < ε
   (inside-gives-cube, within-from-inside).

[1] Claude Fable 5.2. Note: Shulman's approximate Brouwer theorem (12.6)
    without the shape modality. Revision 2, 12 November 2026, audited
    by GPT-6 Astra.
    references/F11-shulman-12-6-rev2.md

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.SquareEstimates
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import Notation.Order
open import UF.Base
open import Rationals.Type
open import Rationals.Order
open import Rationals.Addition renaming (_+_ to _ℚ+_)
open import Rationals.Negation renaming (_-_ to _ℚ-_ ; -_ to ℚ-_)
open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import gist.RealCohesion.RationalArithmetic
 using (half ; half-is-positive ; half-is-less ; halves-add-up ; minus-plus ;
         neg-is-negative)
open import gist.RealCohesion.RationalPoints fe pe pt
 using (ιₐ ; ιₐ-is-ι ; ιₐ-lower ; ιₐ-upper)
open import gist.RealCohesion.RealOrder fe pe pt using (ℝ<-gives-≤ ; ℝ≤-refl)
open import gist.RealCohesion.RealLattice fe pe pt
 using
  (_+_ ; -_ ; +-is-+ᵗ ; sum-≤ ; plus-zero ; ιₐ-sum ; ιₐ-≤-ιₐ ; ιₐ-positive ;
   ιₐ-zero-is-0ℝ ; translate-up ; translate-down ; max ; min ; clamp ; max-≤ ;
   ≤-max-right ; min-≤-right ; ≤-min ; clamp-is-above-lo ; clamp-is-below-hi)
open import gist.RealCohesion.RealAlgebra fe pe pt
 using
  (+-comm ; +-assoc ; +-right-inverse ; plus-minus-cancel ; add-right-strict ;
   add-left-strict)

open PropositionalTruncation pt

\end{code}

Strict inequalities between embedded rationals, and shifting back. The
rational between two others is taken from an abstract copy of ℚ-dense,
so that Agda does not unfold its arithmetic inside comparisons of reals.

\begin{code}

abstract
 rational-between : (p q : ℚ) → p < q → Σ r ꞉ ℚ , (p < r) × (r < q)
 rational-between = ℚ-dense

ιₐ-strict : (p q : ℚ) → p < q → ιₐ p < ιₐ q
ιₐ-strict p q l =
 ∣ pr₁ m , ιₐ-upper p (pr₁ m) (pr₁ (pr₂ m)) , ιₐ-lower (pr₁ m) q (pr₂ (pr₂ m)) ∣
 where
  m : Σ r ꞉ ℚ , (p < r) × (r < q)
  m = rational-between p q l

shift-back : (x : ℝ) (a : ℚ) → (x + ιₐ a) + ιₐ (ℚ- a) ＝ x
shift-back x a = +-assoc x (ιₐ a) (ιₐ (ℚ- a))
               ∙ ap (x +_) (ιₐ-sum a (ℚ- a) ∙ ap ιₐ (ℚ-inverse-sum-to-zero a))
               ∙ plus-zero x

twice-shift : (x : ℝ) (a b : ℚ) → (x + ιₐ a) + ιₐ b ＝ x + ιₐ (a ℚ+ b)
twice-shift x a b = +-assoc x (ιₐ a) (ιₐ b) ∙ ap (x +_) (ιₐ-sum a b)

shift-back' : (x : ℝ) (a : ℚ) → (x + ιₐ (ℚ- a)) + ιₐ a ＝ x
shift-back' x a =
 ap (λ y → (x + ιₐ (ℚ- a)) + ιₐ y) (ℚ-minus-minus a) ∙ shift-back x (ℚ- a)

within-weakens : (t z : ℝ) (a b : ℚ) → a ≤ b → t < z + ιₐ a → t < z + ιₐ b
within-weakens t z a b k l = ℝ<-≤-trans t (z + ιₐ a) (z + ιₐ b) l
                              (sum-≤ z z (ιₐ a) (ιₐ b) (ℝ≤-refl z)
                                (ιₐ-≤-ιₐ a b k))

\end{code}

Margins: comparing a point z with g.

\begin{code}

margin-or-inside : (z g : ℝ) (δ η : ℚ) → δ < η → (g + ιₐ δ < z) ∨ (z < g + ιₐ η)
margin-or-inside z g δ η l =
 weak-linearity (g + ιₐ δ) (g + ιₐ η) z
  (add-left-strict (ιₐ δ) (ιₐ η) g (ιₐ-strict δ η l))

positive-from-margin : (z g : ℝ) (δ : ℚ) → 0ℚ < δ → g + ιₐ δ < z
                     → 0ℝ < z + (- g)
positive-from-margin z g δ k l =
 ℝ<-trans 0ℝ (ιₐ δ) (z + (- g)) (ιₐ-positive δ k)
  (transport (_< z + (- g)) I (add-right-strict (g + ιₐ δ) z (- g) l))
 where
  I : (g + ιₐ δ) + (- g) ＝ ιₐ δ
  I = ap (_+ (- g)) (+-comm g (ιₐ δ)) ∙ plus-minus-cancel (ιₐ δ) g

negative-from-margin : (z g : ℝ) (δ : ℚ) → 0ℚ < δ → z + ιₐ δ < g
                     → z + (- g) < 0ℝ
negative-from-margin z g δ k l =
 ℝ<-trans (z + (- g)) ((z + ιₐ δ) + (- g)) 0ℝ I II
 where
  III : (z + (- g)) + ιₐ δ ＝ (z + ιₐ δ) + (- g)
  III = +-assoc z (- g) (ιₐ δ) ∙ ap (z +_) (+-comm (- g) (ιₐ δ))
        ∙ +-assoc z (ιₐ δ) (- g) ⁻¹

  I : z + (- g) < (z + ιₐ δ) + (- g)
  I = transport (z + (- g) <_) III (translate-up (z + (- g)) δ k)

  II : (z + ιₐ δ) + (- g) < 0ℝ
  II = transport ((z + ιₐ δ) + (- g) <_) (+-right-inverse g ∙ ιₐ-zero-is-0ℝ)
        (add-right-strict (z + ιₐ δ) g (- g) l)

\end{code}

The estimates for a fixed rational ε with 0 < ε < 1.

\begin{code}

module square-estimates (ε : ℚ) (ε-positive : 0ℚ < ε) (ε-below-one : ε < 1ℚ)
                      where

 η δ c : ℚ
 η = half ε
 δ = half η
 c = 1ℚ ℚ- η

 η-positive : 0ℚ < η
 η-positive = half-is-positive ε ε-positive

 δ-positive : 0ℚ < δ
 δ-positive = half-is-positive η η-positive

 δ-below-η : δ < η
 δ-below-η = half-is-less η η-positive

 η-below-one : η < 1ℚ
 η-below-one = ℚ<-trans η ε 1ℚ (half-is-less ε ε-positive) ε-below-one

 δ-below-one : δ < 1ℚ
 δ-below-one = ℚ<-trans δ η 1ℚ δ-below-η η-below-one

 c-below-one : c < 1ℚ
 c-below-one = ℚ<-subtraction-preserves-order 1ℚ η η-positive

 c-is-positive : 0ℚ < c
 c-is-positive = ℚ<-difference-positive η 1ℚ η-below-one

 c-plus-η : c ℚ+ η ＝ 1ℚ
 c-plus-η = minus-plus 1ℚ η

 minus-c : ℚ- c ＝ (ℚ- 1ℚ) ℚ+ η
 minus-c = ℚ-minus-dist' 1ℚ η ∙ ℚ+-comm η (ℚ- 1ℚ)

 c-plus-δ-below-two : c ℚ+ δ < 1ℚ ℚ+ 1ℚ
 c-plus-δ-below-two = ℚ<-adding c 1ℚ δ 1ℚ c-below-one δ-below-one

 lo hi : ℝ
 lo = ιₐ (ℚ- c)
 hi = ιₐ c

 lo-≤-hi : lo ≤ hi
 lo-≤-hi = ιₐ-≤-ιₐ (ℚ- c) c
            (ℚ<-coarser-than-≤ (ℚ- c) c
              (ℚ<-trans (ℚ- c) 0ℚ c (neg-is-negative c c-is-positive)
                c-is-positive))

 clamp-c : ℝ → ℝ
 clamp-c = clamp lo hi

 clamp-bounds : (t : ℝ) → (lo ≤ clamp-c t) × (clamp-c t ≤ hi)
 clamp-bounds t = clamp-is-above-lo lo hi t , clamp-is-below-hi lo hi t lo-≤-hi

 clamp-close-above : (t : ℝ) → ιₐ (ℚ- 1ℚ) ≤ t → clamp-c t ≤ t + ιₐ η
 clamp-close-above t k = max-≤ lo (min hi t) (t + ιₐ η) I II
  where
   I : lo ≤ t + ιₐ η
   I = transport (_≤ t + ιₐ η) (ιₐ-sum (ℚ- 1ℚ) η ∙ ap ιₐ (minus-c ⁻¹))
        (sum-≤ (ιₐ (ℚ- 1ℚ)) t (ιₐ η) (ιₐ η) k (ℝ≤-refl (ιₐ η)))

   II : min hi t ≤ t + ιₐ η
   II = ℝ≤-trans (min hi t) t (t + ιₐ η) (min-≤-right hi t)
         (ℝ<-gives-≤ t (t + ιₐ η) (translate-up t η η-positive))

 clamp-close-below : (t : ℝ) → t ≤ ιₐ 1ℚ → t ≤ clamp-c t + ιₐ η
 clamp-close-below t k =
  transport (_≤ clamp-c t + ιₐ η) (shift-back' t η)
   (sum-≤ (t + ιₐ (ℚ- η)) (clamp-c t) (ιₐ η) (ιₐ η) I (ℝ≤-refl (ιₐ η)))
  where
   III : t + ιₐ (ℚ- η) ≤ hi
   III = transport (t + ιₐ (ℚ- η) ≤_) (ιₐ-sum 1ℚ (ℚ- η))
          (sum-≤ t (ιₐ 1ℚ) (ιₐ (ℚ- η)) (ιₐ (ℚ- η)) k (ℝ≤-refl (ιₐ (ℚ- η))))

   IV : t + ιₐ (ℚ- η) ≤ t
   IV = ℝ<-gives-≤ (t + ιₐ (ℚ- η)) t (translate-down t η η-positive)

   I : t + ιₐ (ℚ- η) ≤ clamp-c t
   I = ℝ≤-trans (t + ιₐ (ℚ- η)) (min hi t) (clamp-c t)
        (≤-min hi t (t + ιₐ (ℚ- η)) III IV) (≤-max-right lo (min hi t))

 east-margin : (g : ℝ) → g ≤ hi → g + ιₐ δ < ιₐ (1ℚ ℚ+ 1ℚ)
 east-margin g k =
  ℝ≤-<-trans (g + ιₐ δ) (ιₐ (c ℚ+ δ)) (ιₐ (1ℚ ℚ+ 1ℚ))
   (transport (g + ιₐ δ ≤_) (ιₐ-sum c δ)
     (sum-≤ g hi (ιₐ δ) (ιₐ δ) k (ℝ≤-refl (ιₐ δ))))
   (ιₐ-strict (c ℚ+ δ) (1ℚ ℚ+ 1ℚ) c-plus-δ-below-two)

 west-margin : (g : ℝ) → lo ≤ g → ιₐ (ℚ- (1ℚ ℚ+ 1ℚ)) + ιₐ δ < g
 west-margin g k =
  ℝ<-≤-trans (ιₐ (ℚ- (1ℚ ℚ+ 1ℚ)) + ιₐ δ) lo g
   (transport (_< lo) (ιₐ-sum (ℚ- (1ℚ ℚ+ 1ℚ)) δ ⁻¹)
     (ιₐ-strict ((ℚ- (1ℚ ℚ+ 1ℚ)) ℚ+ δ) (ℚ- c) r))
   k
  where
   s : ℚ- (1ℚ ℚ+ 1ℚ) < (ℚ- c) ℚ- δ
   s = transport (ℚ- (1ℚ ℚ+ 1ℚ) <_) (ℚ-minus-dist c δ ⁻¹)
        (ℚ<-swap (c ℚ+ δ) (1ℚ ℚ+ 1ℚ) c-plus-δ-below-two)

   r : (ℚ- (1ℚ ℚ+ 1ℚ)) ℚ+ δ < ℚ- c
   r = transport ((ℚ- (1ℚ ℚ+ 1ℚ)) ℚ+ δ <_) (minus-plus (ℚ- c) δ)
        (ℚ<-addition-preserves-order (ℚ- (1ℚ ℚ+ 1ℚ)) ((ℚ- c) ℚ- δ) δ s)

 inside-gives-cube : (z g : ℝ) → lo ≤ g → g ≤ hi → z < g + ιₐ η → g < z + ιₐ η
                   → (ιₐ (ℚ- 1ℚ) ≤ z) × (z ≤ ιₐ 1ℚ)
 inside-gives-cube z g k k' l l' = I , II
  where
   II : z ≤ ιₐ 1ℚ
   II = ℝ<-gives-≤ z (ιₐ 1ℚ)
         (ℝ<-≤-trans z (g + ιₐ η) (ιₐ 1ℚ) l
           (transport (g + ιₐ η ≤_) (ιₐ-sum c η ∙ ap ιₐ c-plus-η)
             (sum-≤ g hi (ιₐ η) (ιₐ η) k' (ℝ≤-refl (ιₐ η)))))

   III : lo < z + ιₐ η
   III = ℝ≤-<-trans lo g (z + ιₐ η) k l'

   IV : lo + ιₐ (ℚ- η) ＝ ιₐ (ℚ- 1ℚ)
   IV = ιₐ-sum (ℚ- c) (ℚ- η) ∙ ap ιₐ (ℚ-minus-dist c η ∙ ap ℚ-_ c-plus-η)

   I : ιₐ (ℚ- 1ℚ) ≤ z
   I = ℝ<-gives-≤ (ιₐ (ℚ- 1ℚ)) z
        (transport₂ _<_ IV (shift-back z η)
          (add-right-strict lo (z + ιₐ η) (ιₐ (ℚ- η)) III))

 within-from-inside : (z t : ℝ) → ιₐ (ℚ- 1ℚ) ≤ t → t ≤ ιₐ 1ℚ
                    → z < clamp-c t + ιₐ η → clamp-c t < z + ιₐ η
                    → (t < z + ιₐ ε) × (z < t + ιₐ ε)
 within-from-inside z t k k' l l' = I , II
  where
   g : ℝ
   g = clamp-c t

   I : t < z + ιₐ ε
   I = ℝ≤-<-trans t (g + ιₐ η) (z + ιₐ ε) (clamp-close-below t k')
        (transport (g + ιₐ η <_)
          (twice-shift z η η ∙ ap (λ y → z + ιₐ y) (halves-add-up ε))
          (add-right-strict g (z + ιₐ η) (ιₐ η) l'))

   II : z < t + ιₐ ε
   II = ℝ<-≤-trans z (g + ιₐ η) (t + ιₐ ε) l
         (transport (g + ιₐ η ≤_)
           (twice-shift t η η ∙ ap (λ y → t + ιₐ y) (halves-add-up ε))
           (sum-≤ g (t + ιₐ η) (ιₐ η) (ιₐ η) (clamp-close-above t k)
             (ℝ≤-refl (ιₐ η))))

\end{code}
