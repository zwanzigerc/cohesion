Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. See the AI disclosure in
gist.RealCohesion.index.

Algebra of real numbers: the laws of the addition and negation of
gist.RealCohesion.RealLattice that are not recorded there, and the
identities in which they meet the multiplication of
gist.RealCohesion.RealMultiplication, as the sphere of
gist.RealCohesion.EuclideanSphere uses them (gate G14, step E4).

The group laws are TypeTopology's, transported along +-is-+ᵗ, and the
ring identities follow from the laws of the multiplication. The two
identities of the sphere are the expansion of (x + t y)², and the
completion of the square b (t + t) + t² = (t + b)² - b². A real whose
double is at least 0 is at least 0, since a sum of negative reals is
negative.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.RealAlgebra
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
open import DedekindReals.Addition fe pe pt using (ℝ+-comm ; ℝ+-assoc)
 renaming (_+_ to _+ᵗ_)
open import gist.RealCohesion.RationalArithmetic using (add-difference)
open import gist.RealCohesion.RationalPoints fe pe pt using (ιₐ ; ιₐ-lower⁻¹)
open import gist.RealCohesion.RealOrder fe pe pt using (ℝ≤-refl)
open import gist.RealCohesion.RealLattice fe pe pt
 using
  (_+_ ; -_ ; +-is-+ᵗ ; plus-zero ; zero-plus ; minus-plus-cancel ; sum-below ;
   ιₐ-zero-is-0ℝ ; sum-≤ ; <-gives-≤-ιₐ ; translate-up ; ιₐ-sum)
open import gist.RealCohesion.RealMultiplication fe pe pt
 using (_*_ ; *-comm ; *-assoc ; *-right-unit ; *-left-distributive ;
         *-right-distributive)

open PropositionalTruncation pt

\end{code}

The group laws of the addition.

\begin{code}

+-comm : (x y : ℝ) → x + y ＝ y + x
+-comm x y = +-is-+ᵗ x y ∙ ℝ+-comm x y ∙ +-is-+ᵗ y x ⁻¹

+-assoc : (x y z : ℝ) → (x + y) + z ＝ x + (y + z)
+-assoc x y z = +-is-+ᵗ (x + y) z
              ∙ ap (_+ᵗ z) (+-is-+ᵗ x y)
              ∙ ℝ+-assoc x y z
              ∙ ap (x +ᵗ_) (+-is-+ᵗ y z ⁻¹)
              ∙ +-is-+ᵗ x (y + z) ⁻¹

+-left-inverse : (x : ℝ) → (- x) + x ＝ ιₐ 0ℚ
+-left-inverse x = ap (_+ x) (zero-plus (- x) ⁻¹) ∙ minus-plus-cancel (ιₐ 0ℚ) x

+-right-inverse : (x : ℝ) → x + (- x) ＝ ιₐ 0ℚ
+-right-inverse x = +-comm x (- x) ∙ +-left-inverse x

plus-minus-cancel : (x y : ℝ) → (x + y) + (- y) ＝ x
plus-minus-cancel x y =
 +-assoc x y (- y) ∙ ap (x +_) (+-right-inverse y) ∙ plus-zero x

plus-difference : (x y : ℝ) → x + (y + (- x)) ＝ y
plus-difference x y = +-comm x (y + (- x)) ∙ minus-plus-cancel y x

interchange : (a b c d : ℝ) → (a + b) + (c + d) ＝ (a + c) + (b + d)
interchange a b c d =
 (a + b) + (c + d) ＝⟨ +-assoc a b (c + d) ⟩
 a + (b + (c + d)) ＝⟨ ap (a +_) (+-assoc b c d ⁻¹) ⟩
 a + ((b + c) + d) ＝⟨ ap (λ - → a + (- + d)) (+-comm b c) ⟩
 a + ((c + b) + d) ＝⟨ ap (a +_) (+-assoc c b d) ⟩
 a + (c + (b + d)) ＝⟨ +-assoc a c (b + d) ⁻¹ ⟩
 (a + c) + (b + d) ∎

\end{code}

A sum of negative reals is negative, so a real whose double is at
least 0 is at least 0. Adding a real preserves the strict order:
TypeTopology's ℝ<-addition-preserves-order is commented out at the
commit we use, so we prove it, through rationals k < k' between x and
y: x + z ≤ k + z < k' + z ≤ y + z.

\begin{code}

sum-of-negatives : (x y : ℝ) → x < 0ℝ → y < 0ℝ → x + y < 0ℝ
sum-of-negatives x y l m = ∥∥-functor γ (binary-choice l m)
 where
  γ : (Σ q ꞉ ℚ , (x < q) × (q < 0ℝ)) × (Σ q' ꞉ ℚ , (y < q') × (q' < 0ℝ))
    → Σ r ꞉ ℚ , (x + y < r) × (r < 0ℝ)
  γ ((q , k , k') , (q' , o , o')) =
   q ℚ+ q' , sum-below x y q q' k o ,
   transport (q ℚ+ q' <_) (ℚ-zero-left-neutral 0ℚ) (ℚ<-adding q 0ℚ q' 0ℚ k' o')

add-right-strict : (x y z : ℝ) → x < y → x + z < y + z
add-right-strict x y z = ∥∥-rec (<-is-prop (x + z) (y + z)) γ
 where
  γ : (Σ k ꞉ ℚ , (x < k) × (k < y)) → x + z < y + z
  γ (k , m , n) = ∥∥-rec (<-is-prop (x + z) (y + z)) δ (rounded-left-d y k n)
   where
    δ : (Σ k' ꞉ ℚ , (k < k') × (k' < y)) → x + z < y + z
    δ (k' , o , o') = ℝ≤-<-trans (x + z) (ιₐ k + z) (y + z) I
                       (ℝ<-≤-trans (ιₐ k + z) (ιₐ k' + z) (y + z) II III)
     where
      I : x + z ≤ ιₐ k + z
      I = sum-≤ x (ιₐ k) z z (<-gives-≤-ιₐ x k m) (ℝ≤-refl z)

      III : ιₐ k' + z ≤ y + z
      III = sum-≤ (ιₐ k') y z z
             (λ p l → use-rounded-real-L y p k' (ιₐ-lower⁻¹ p k' l) o')
             (ℝ≤-refl z)

      IV : (z + ιₐ k) + ιₐ (k' ℚ- k) ＝ ιₐ k' + z
      IV = +-assoc z (ιₐ k) (ιₐ (k' ℚ- k))
         ∙ ap (z +_) (ιₐ-sum k (k' ℚ- k) ∙ ap ιₐ (add-difference k k'))
         ∙ +-comm z (ιₐ k')

      II : ιₐ k + z < ιₐ k' + z
      II = transport₂ _<_ (+-comm z (ιₐ k)) IV
            (translate-up (z + ιₐ k) (k' ℚ- k) (ℚ<-difference-positive k k' o))

add-left-strict : (x y z : ℝ) → x < y → z + x < z + y
add-left-strict x y z l =
 transport₂ _<_ (+-comm x z) (+-comm y z) (add-right-strict x y z l)

nonneg-from-double : (x : ℝ) → 0ℝ ≤ x + x → 0ℝ ≤ x
nonneg-from-double x k =
 ℝ-not-less-is-greater-or-equal x 0ℝ
  (λ l →
    ℝ-less-than-or-equal-not-greater 0ℝ (x + x) k (sum-of-negatives x x l l))

\end{code}

Ring identities: a square of a product, the expansion of (x + t y)² and
the completion of the square.

\begin{code}

square-of-scaled : (a m : ℝ) → (a * m) * (a * m) ＝ (a * a) * (m * m)
square-of-scaled a m =
 (a * m) * (a * m) ＝⟨ *-assoc a m (a * m) ⟩
 a * (m * (a * m)) ＝⟨ ap (a *_) (*-assoc m a m ⁻¹) ⟩
 a * ((m * a) * m) ＝⟨ ap (λ - → a * (- * m)) (*-comm m a) ⟩
 a * ((a * m) * m) ＝⟨ ap (a *_) (*-assoc a m m) ⟩
 a * (a * (m * m)) ＝⟨ *-assoc a a (m * m) ⁻¹ ⟩
 (a * a) * (m * m) ∎

square-of-shifted
 : (x y t : ℝ)
 → (x + t * y) * (x + t * y) ＝ x * x + ((y * x) * (t + t) + (y * y) * (t * t))
square-of-shifted x y t =
 (x + t * y) * (x + t * y)
  ＝⟨ *-left-distributive (x + t * y) x (t * y) ⟩
 (x + t * y) * x + (x + t * y) * (t * y)
  ＝⟨ ap₂ _+_ (*-right-distributive x (t * y) x)
       (*-right-distributive x (t * y) (t * y)) ⟩
 (x * x + (t * y) * x) + (x * (t * y) + (t * y) * (t * y))
  ＝⟨ ap₂ (λ u w → (x * x + u) + w) I II ⟩
 (x * x + (y * x) * t) + ((y * x) * t + (y * y) * (t * t))
  ＝⟨ +-assoc (x * x) ((y * x) * t) _ ⟩
 x * x + ((y * x) * t + ((y * x) * t + (y * y) * (t * t)))
  ＝⟨ ap (x * x +_) (+-assoc ((y * x) * t) ((y * x) * t) _ ⁻¹) ⟩
 x * x + (((y * x) * t + (y * x) * t) + (y * y) * (t * t))
  ＝⟨ ap (λ - → x * x + (- + (y * y) * (t * t)))
       (*-left-distributive (y * x) t t ⁻¹) ⟩
 x * x + ((y * x) * (t + t) + (y * y) * (t * t))   ∎
 where
  III : (t * y) * x ＝ (y * x) * t
  III = *-assoc t y x ∙ *-comm t (y * x)

  I : (t * y) * x ＝ (y * x) * t
  I = III

  II : x * (t * y) + (t * y) * (t * y) ＝ (y * x) * t + (y * y) * (t * t)
  II = ap₂ _+_ (*-comm x (t * y) ∙ III)
        (square-of-scaled t y ∙ *-comm (t * t) (y * y))

completing-the-square : (t b : ℝ)
                      → b * (t + t) + t * t ＝ (t + b) * (t + b) + (- (b * b))
completing-the-square t b = I ⁻¹
 where
  I : (t + b) * (t + b) + (- (b * b)) ＝ b * (t + t) + t * t
  I = (t + b) * (t + b) + (- (b * b))
      ＝⟨ ap (_+ (- (b * b)))
           (*-right-distributive t b (t + b)) ⟩
      (t * (t + b) + b * (t + b)) + (- (b * b))
       ＝⟨ ap (λ w → w + (- (b * b)))
            (ap₂ _+_ (*-left-distributive t t b)
                     (*-left-distributive b t b)) ⟩
      ((t * t + t * b) + (b * t + b * b)) + (- (b * b))
       ＝⟨ +-assoc (t * t + t * b) (b * t + b * b) (- (b * b)) ⟩
      (t * t + t * b) + ((b * t + b * b) + (- (b * b)))
       ＝⟨ ap ((t * t + t * b) +_) (plus-minus-cancel (b * t) (b * b)) ⟩
      (t * t + t * b) + b * t
       ＝⟨ +-assoc (t * t) (t * b) (b * t) ⟩
      t * t + (t * b + b * t)
       ＝⟨ ap (λ - → t * t + (- + b * t)) (*-comm t b) ⟩
      t * t + (b * t + b * t)
       ＝⟨ ap (t * t +_) (*-left-distributive b t t ⁻¹) ⟩
      t * t + b * (t + t)
       ＝⟨ +-comm (t * t) (b * (t + t)) ⟩
      b * (t + t) + t * t                         ∎

\end{code}
