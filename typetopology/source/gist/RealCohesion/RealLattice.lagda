Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 10 November 2026. See the AI disclosure in
gist.RealCohesion.index.

Maximum, minimum and clamping of Dedekind real numbers, and the order
facts about them, about negation and about addition that the proof of
the approximate intermediate value theorem uses.

TypeTopology's DedekindReals provides the cuts, the order, addition,
negation and their group laws, but no maximum or minimum. We define
them directly on cuts:

 * max x y has lower cut Lₓ ∪ L_y and upper cut Uₓ ∩ U_y;
 * min x y has lower cut Lₓ ∩ L_y and upper cut Uₓ ∪ U_y.

The comparisons of max x y and min x y with rationals are then true by
definition, and their equalities with x or y in the obvious cases
follow by comparing lower cuts. Clamping t to [lo , hi] is
max lo (min hi t).

For addition and negation, which TypeTopology defines on cuts too, we
record the comparisons with rationals that hold by definition, the
compatibility of addition with ≤, and the facts relating them to the
abstract copy ιₐ of the embedding of the rationals
(gist.RealCohesion.RationalPoints), which keeps type checking fast.
Doubling is x + x. We use only
comparisons of reals with rationals and the order ≤ of reals, where
x ≤ y means that the lower cut of x is contained in that of y.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Fin.Type using (Fin ; 𝟎 ; suc)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.RealLattice
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import Notation.CanonicalMap
open import Notation.Order
open import UF.Base
open import UF.Powerset
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier using (holds-is-prop)
open import Rationals.Type
open import Rationals.Order
open import Rationals.Addition renaming (_+_ to _ℚ+_)
open import Rationals.Negation renaming (_-_ to _ℚ-_ ; -_ to ℚ-_)
open import Rationals.MinMax renaming (max to ℚ-max ; min to ℚ-min)
open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import DedekindReals.Properties fe pe pt using (ℝ-arithmetically-located)
open import DedekindReals.Addition fe pe pt
 using (ℝ+-assoc ; ℝ+-comm ; ℝ+-inverse-exists ; ℝ-zero-left-neutral ;
         ℝ-zero-right-neutral)
 renaming (_+_ to _+ᵗ_ ; -_ to -ᵗ_)
open import gist.RealCohesion.RationalArithmetic
 using (add-difference ; <-move-left ; <-add-right ; plus-minus ; minus-plus)
open import gist.RealCohesion.RealOrder fe pe pt
 using (cuts-are-ordered ; not-below-and-above)
open import gist.RealCohesion.RealOrder fe pe pt using (ℝ≤-refl) public
open import gist.RealCohesion.RationalPoints fe pe pt

open PropositionalTruncation pt

\end{code}

Basic facts about comparisons of reals with rationals, and equality of
reals from their lower cuts. We apply TypeTopology's criterion for the
latter only through the wrapper equal-if-lower-cuts-agree, at variable
arguments.

\begin{code}

ℚ<ℝ-is-prop : (p : ℚ) (x : ℝ) → is-prop (p < x)
ℚ<ℝ-is-prop p x = ∈-is-prop (lower-cut-of x) p

ℝ<ℚ-is-prop : (x : ℝ) (q : ℚ) → is-prop (x < q)
ℝ<ℚ-is-prop x q = ∈-is-prop (upper-cut-of x) q

≤-<-trans-ℚ : (x y : ℝ) (q : ℚ) → x ≤ y → y < q → x < q
≤-<-trans-ℚ x y q k l = ∥∥-rec (ℝ<ℚ-is-prop x q) γ
                          (rounded-right-b (upper-cut-of y)
                            (rounded-from-real-R y) q l)
 where
  γ : (Σ q' ꞉ ℚ , (q' < q) × (y < q')) → x < q
  γ (q' , m , n) = ∥∥-rec (ℝ<ℚ-is-prop x q) δ (ℝ-locatedness x q' q m)
   where
    δ : (q' < x) ∔ (x < q) → x < q
    δ (inl o) = 𝟘-elim (not-below-and-above y q' (k q' o) n)
    δ (inr o) = o

<-≤-trans-ℚ : (x y : ℝ) (p : ℚ) → p < x → x ≤ y → p < y
<-≤-trans-ℚ x y p l k = k p l

<-gives-≤-ιₐ : (x : ℝ) (q : ℚ) → x < q → x ≤ ιₐ q
<-gives-≤-ιₐ x q l p m = ιₐ-lower p q (cuts-are-ordered x p q m l)

>-gives-ιₐ-≤ : (x : ℝ) (q : ℚ) → q < x → ιₐ q ≤ x
>-gives-ιₐ-≤ x q l p m = use-rounded-real-L x p q (ιₐ-lower⁻¹ p q m) l

ιₐ-≤-gives-not-below : (x : ℝ) (q : ℚ) → ιₐ q ≤ x → x < q → 𝟘 {𝓤₀}
ιₐ-≤-gives-not-below x q k l = ∥∥-rec 𝟘-is-prop γ
                                (rounded-right-b (upper-cut-of x)
                                  (rounded-from-real-R x) q l)
 where
  γ : (Σ q' ꞉ ℚ , (q' < q) × (x < q')) → 𝟘
  γ (q' , m , n) = not-below-and-above x q' (k q' (ιₐ-lower q' q m)) n

ιₐ-≤-ιₐ : (a b : ℚ) → a ≤ b → ιₐ a ≤ ιₐ b
ιₐ-≤-ιₐ a b l p m = ιₐ-lower p b (ℚ<-≤-trans p a b (ιₐ-lower⁻¹ p a m) l)

ιₐ-<-gives-≤ : (a b : ℚ) → a < b → ιₐ a ≤ ιₐ b
ιₐ-<-gives-≤ a b l = ιₐ-≤-ιₐ a b (ℚ<-coarser-than-≤ a b l)

equal-if-lower-cuts-agree : (x y : ℝ)
                          → lower-cut-of x ⊆ lower-cut-of y
                          → lower-cut-of y ⊆ lower-cut-of x
                          → x ＝ y
equal-if-lower-cuts-agree x y = ℝ-equality-from-left-cut' x y

\end{code}

The maximum and the minimum. Their lower cuts are Lₓ ∪ L_y and
Lₓ ∩ L_y, and their upper cuts Uₓ ∩ U_y and Uₓ ∪ U_y. The definitions
are abstract, together with the facts about them that are proved by
unfolding them: their comparisons with rationals, which hold by
definition, their order properties, and their equalities with x or y
when x and y are comparable. Outside this block Agda cannot unfold
max and min, so that it compares max x y with max x' y' by comparing
the arguments, which keeps type checking fast.

\begin{code}

abstract
 max : ℝ → ℝ → ℝ
 max x y = (L , R) , inhabited-L , inhabited-R , rounded-L , rounded-R ,
           disjoint-LR , located-LR
  where
   L R : 𝓟 ℚ
   L p = ((p < x) ∨ (p < y)) , ∨-is-prop
   R q = ((x < q) × (y < q)) , ×-is-prop (ℝ<ℚ-is-prop x q) (ℝ<ℚ-is-prop y q)

   inhabited-L : inhabited-left L
   inhabited-L =
    ∥∥-functor (λ (p , l) → p , ∣ inl l ∣) (inhabited-from-real-L x)

   inhabited-R : inhabited-right R
   inhabited-R = ∥∥-functor γ (binary-choice (inhabited-from-real-R x)
                                             (inhabited-from-real-R y))
    where
     γ : (Σ q ꞉ ℚ , x < q) × (Σ q' ꞉ ℚ , y < q') → Σ r ꞉ ℚ , r ∈ R
     γ ((q , l) , (q' , l')) =
      ℚ-max q q' ,
      use-rounded-real-R' x q (ℚ-max q q') (max≤ q q') l ,
      use-rounded-real-R' y q' (ℚ-max q q') (max≤' q q') l'

   rounded-L : rounded-left L
   rounded-L p = α , β
    where
     α : p ∈ L → ∃ p' ꞉ ℚ , (p < p') × p' ∈ L
     α = ∥∥-rec ∃-is-prop γ
      where
       γ : (p < x) ∔ (p < y) → ∃ p' ꞉ ℚ , (p < p') × p' ∈ L
       γ (inl l) = ∥∥-functor (λ (p' , m , m') → p' , m , ∣ inl m' ∣)
                    (rounded-left-d x p l)
       γ (inr l) = ∥∥-functor (λ (p' , m , m') → p' , m , ∣ inr m' ∣)
                    (rounded-left-d y p l)

     β : (∃ p' ꞉ ℚ , (p < p') × p' ∈ L) → p ∈ L
     β = ∥∥-rec ∨-is-prop γ
      where
       γ : (Σ p' ꞉ ℚ , (p < p') × p' ∈ L) → p ∈ L
       γ (p' , m , d) = ∥∥-functor δ d
        where
         δ : (p' < x) ∔ (p' < y) → (p < x) ∔ (p < y)
         δ (inl l) = inl (use-rounded-real-L x p p' m l)
         δ (inr l) = inr (use-rounded-real-L y p p' m l)

   rounded-R : rounded-right R
   rounded-R q = α , β
    where
     α : q ∈ R → ∃ q' ꞉ ℚ , (q' < q) × q' ∈ R
     α (l , l') = ∥∥-functor γ
                   (binary-choice
                     (rounded-right-b (upper-cut-of x) (rounded-from-real-R x) q
                       l)
                     (rounded-right-b (upper-cut-of y) (rounded-from-real-R y) q
                       l'))
      where
       γ : (Σ r ꞉ ℚ , (r < q) × (x < r)) × (Σ r' ꞉ ℚ , (r' < q) × (y < r'))
         → Σ q' ꞉ ℚ , (q' < q) × q' ∈ R
       γ ((r , m , n) , (r' , m' , n')) =
        ℚ-max r r' ,
        δ (decide-max r r') ,
        use-rounded-real-R' x r (ℚ-max r r') (max≤ r r') n ,
        use-rounded-real-R' y r' (ℚ-max r r') (max≤' r r') n'
        where
         δ : (ℚ-max r r' ＝ r') ∔ (ℚ-max r r' ＝ r) → ℚ-max r r' < q
         δ (inl e) = transport (_< q) (e ⁻¹) m'
         δ (inr e) = transport (_< q) (e ⁻¹) m

     β : (∃ q' ꞉ ℚ , (q' < q) × q' ∈ R) → q ∈ R
     β = ∥∥-rec (holds-is-prop (R q)) γ
      where
       γ : (Σ q' ꞉ ℚ , (q' < q) × q' ∈ R) → q ∈ R
       γ (q' , m , n , n') = use-rounded-real-R x q' q m n ,
                             use-rounded-real-R y q' q m n'

   disjoint-LR : disjoint L R
   disjoint-LR p q (l , (r , r')) = ∥∥-rec (ℚ<-is-prop p q) γ l
    where
     γ : (p < x) ∔ (p < y) → p < q
     γ (inl m) = cuts-are-ordered x p q m r
     γ (inr m) = cuts-are-ordered y p q m r'

   located-LR : located L R
   located-LR p q l = ∥∥-rec ∨-is-prop γ
                       (binary-choice (ℝ-locatedness x p q l)
                         (ℝ-locatedness y p q l))
    where
     γ : ((p < x) ∔ (x < q)) × ((p < y) ∔ (y < q)) → p ∈ L ∨ q ∈ R
     γ (inl m , _)      = ∣ inl ∣ inl m ∣ ∣
     γ (inr _ , inl m') = ∣ inl ∣ inr m' ∣ ∣
     γ (inr m , inr m') = ∣ inr (m , m') ∣

 min : ℝ → ℝ → ℝ
 min x y = (L , R) , inhabited-L , inhabited-R , rounded-L , rounded-R ,
           disjoint-LR , located-LR
  where
   L R : 𝓟 ℚ
   L p = ((p < x) × (p < y)) , ×-is-prop (ℚ<ℝ-is-prop p x) (ℚ<ℝ-is-prop p y)
   R q = ((x < q) ∨ (y < q)) , ∨-is-prop

   inhabited-L : inhabited-left L
   inhabited-L = ∥∥-functor γ (binary-choice (inhabited-from-real-L x)
                                             (inhabited-from-real-L y))
    where
     γ : (Σ p ꞉ ℚ , p < x) × (Σ p' ꞉ ℚ , p' < y) → Σ r ꞉ ℚ , r ∈ L
     γ ((p , l) , (p' , l')) =
      ℚ-min p p' ,
      use-rounded-real-L' x (ℚ-min p p') p (min≤ p p') l ,
      use-rounded-real-L' y (ℚ-min p p') p' (min≤' p p') l'

   inhabited-R : inhabited-right R
   inhabited-R =
    ∥∥-functor (λ (q , l) → q , ∣ inl l ∣) (inhabited-from-real-R x)

   rounded-L : rounded-left L
   rounded-L p = α , β
    where
     α : p ∈ L → ∃ p' ꞉ ℚ , (p < p') × p' ∈ L
     α (l , l') = ∥∥-functor γ
      (binary-choice (rounded-left-d x p l) (rounded-left-d y p l'))
      where
       γ : (Σ r ꞉ ℚ , (p < r) × (r < x)) × (Σ r' ꞉ ℚ , (p < r') × (r' < y))
         → Σ p' ꞉ ℚ , (p < p') × p' ∈ L
       γ ((r , m , n) , (r' , m' , n')) =
        ℚ-min r r' ,
        δ (decide-min r r') ,
        use-rounded-real-L' x (ℚ-min r r') r (min≤ r r') n ,
        use-rounded-real-L' y (ℚ-min r r') r' (min≤' r r') n'
        where
         δ : (ℚ-min r r' ＝ r) ∔ (ℚ-min r r' ＝ r') → p < ℚ-min r r'
         δ (inl e) = transport (p <_) (e ⁻¹) m
         δ (inr e) = transport (p <_) (e ⁻¹) m'

     β : (∃ p' ꞉ ℚ , (p < p') × p' ∈ L) → p ∈ L
     β = ∥∥-rec (holds-is-prop (L p)) γ
      where
       γ : (Σ p' ꞉ ℚ , (p < p') × p' ∈ L) → p ∈ L
       γ (p' , m , n , n') = use-rounded-real-L x p p' m n ,
                             use-rounded-real-L y p p' m n'

   rounded-R : rounded-right R
   rounded-R q = α , β
    where
     α : q ∈ R → ∃ q' ꞉ ℚ , (q' < q) × q' ∈ R
     α = ∥∥-rec ∃-is-prop γ
      where
       γ : (x < q) ∔ (y < q) → ∃ q' ꞉ ℚ , (q' < q) × q' ∈ R
       γ (inl l) = ∥∥-functor (λ (q' , m , m') → q' , m , ∣ inl m' ∣)
                    (rounded-right-b (upper-cut-of x) (rounded-from-real-R x) q
                      l)
       γ (inr l) = ∥∥-functor (λ (q' , m , m') → q' , m , ∣ inr m' ∣)
                    (rounded-right-b (upper-cut-of y) (rounded-from-real-R y) q
                      l)

     β : (∃ q' ꞉ ℚ , (q' < q) × q' ∈ R) → q ∈ R
     β = ∥∥-rec ∨-is-prop γ
      where
       γ : (Σ q' ꞉ ℚ , (q' < q) × q' ∈ R) → q ∈ R
       γ (q' , m , d) = ∥∥-functor δ d
        where
         δ : (x < q') ∔ (y < q') → (x < q) ∔ (y < q)
         δ (inl l) = inl (use-rounded-real-R x q' q m l)
         δ (inr l) = inr (use-rounded-real-R y q' q m l)

   disjoint-LR : disjoint L R
   disjoint-LR p q ((l , l') , r) = ∥∥-rec (ℚ<-is-prop p q) γ r
    where
     γ : (x < q) ∔ (y < q) → p < q
     γ (inl m) = cuts-are-ordered x p q l m
     γ (inr m) = cuts-are-ordered y p q l' m

   located-LR : located L R
   located-LR p q l = ∥∥-rec ∨-is-prop γ
                       (binary-choice (ℝ-locatedness x p q l)
                         (ℝ-locatedness y p q l))
    where
     γ : ((p < x) ∔ (x < q)) × ((p < y) ∔ (y < q)) → p ∈ L ∨ q ∈ R
     γ (inr m , _)      = ∣ inr ∣ inl m ∣ ∣
     γ (inl _ , inr m') = ∣ inr ∣ inr m' ∣ ∣
     γ (inl m , inl m') = ∣ inl (m , m') ∣

 below-max-left : (x y : ℝ) (p : ℚ) → p < x → p < max x y
 below-max-left x y p l = ∣ inl l ∣

 below-max-right : (x y : ℝ) (p : ℚ) → p < y → p < max x y
 below-max-right x y p l = ∣ inr l ∣

 below-max : (x y : ℝ) (p : ℚ) → p < max x y → (p < x) ∨ (p < y)
 below-max x y p l = l

 max-below : (x y : ℝ) (q : ℚ) → x < q → y < q → max x y < q
 max-below x y q l l' = l , l'

 max-below-left : (x y : ℝ) (q : ℚ) → max x y < q → x < q
 max-below-left x y q = pr₁

 max-below-right : (x y : ℝ) (q : ℚ) → max x y < q → y < q
 max-below-right x y q = pr₂

 below-min : (x y : ℝ) (p : ℚ) → p < x → p < y → p < min x y
 below-min x y p l l' = l , l'

 below-min-left : (x y : ℝ) (p : ℚ) → p < min x y → p < x
 below-min-left x y p = pr₁

 below-min-right : (x y : ℝ) (p : ℚ) → p < min x y → p < y
 below-min-right x y p = pr₂

 min-below-left : (x y : ℝ) (q : ℚ) → x < q → min x y < q
 min-below-left x y q l = ∣ inl l ∣

 min-below-right : (x y : ℝ) (q : ℚ) → y < q → min x y < q
 min-below-right x y q l = ∣ inr l ∣

 min-below : (x y : ℝ) (q : ℚ) → min x y < q → (x < q) ∨ (y < q)
 min-below x y q l = l

 ≤-max-left : (x y : ℝ) → x ≤ max x y
 ≤-max-left x y p l = ∣ inl l ∣

 ≤-max-right : (x y : ℝ) → y ≤ max x y
 ≤-max-right x y p l = ∣ inr l ∣

 max-≤ : (x y z : ℝ) → x ≤ z → y ≤ z → max x y ≤ z
 max-≤ x y z k k' p = ∥∥-rec (ℚ<ℝ-is-prop p z) γ
  where
   γ : (p < x) ∔ (p < y) → p < z
   γ (inl l) = k p l
   γ (inr l) = k' p l

 min-≤-left : (x y : ℝ) → min x y ≤ x
 min-≤-left x y p = pr₁

 min-≤-right : (x y : ℝ) → min x y ≤ y
 min-≤-right x y p = pr₂

 ≤-min : (x y z : ℝ) → z ≤ x → z ≤ y → z ≤ min x y
 ≤-min x y z k k' p l = k p l , k' p l

 max-is-right : (x y : ℝ) → x ≤ y → max x y ＝ y
 max-is-right x y k = ℝ-equality-from-left-cut' (max x y) y
                       (max-≤ x y y k (ℝ≤-refl y)) (≤-max-right x y)

 max-is-left : (x y : ℝ) → y ≤ x → max x y ＝ x
 max-is-left x y k = ℝ-equality-from-left-cut' (max x y) x
                      (max-≤ x y x (ℝ≤-refl x) k) (≤-max-left x y)

 min-is-left : (x y : ℝ) → x ≤ y → min x y ＝ x
 min-is-left x y k = ℝ-equality-from-left-cut' (min x y) x
                      (min-≤-left x y) (≤-min x y x (ℝ≤-refl x) k)

 min-is-right : (x y : ℝ) → y ≤ x → min x y ＝ y
 min-is-right x y k = ℝ-equality-from-left-cut' (min x y) y
                       (min-≤-right x y) (≤-min x y y k (ℝ≤-refl y))

\end{code}

Clamping t to the interval [lo , hi].

\begin{code}

clamp : ℝ → ℝ → ℝ → ℝ
clamp lo hi t = max lo (min hi t)

clamp-below : (lo hi t : ℝ) → t ≤ lo → clamp lo hi t ＝ lo
clamp-below lo hi t k = max-is-left lo (min hi t)
                         (ℝ≤-trans (min hi t) t lo (min-≤-right hi t) k)

clamp-above : (lo hi t : ℝ) → lo ≤ hi → hi ≤ t → clamp lo hi t ＝ hi
clamp-above lo hi t k k' =
 ap (max lo) (min-is-left hi t k') ∙ max-is-right lo hi k

clamp-inside : (lo hi t : ℝ) → lo ≤ t → t ≤ hi → clamp lo hi t ＝ t
clamp-inside lo hi t k k' =
 ap (max lo) (min-is-right hi t k') ∙ max-is-right lo t k

clamp-is-above-lo : (lo hi t : ℝ) → lo ≤ clamp lo hi t
clamp-is-above-lo lo hi t = ≤-max-left lo (min hi t)

clamp-is-below-hi : (lo hi t : ℝ) → lo ≤ hi → clamp lo hi t ≤ hi
clamp-is-below-hi lo hi t k = max-≤ lo (min hi t) hi k (min-≤-left hi t)

clamp-degenerate : (c t : ℝ) → clamp c c t ＝ c
clamp-degenerate c t = max-is-left c (min c t) (min-≤-left c t)

\end{code}

Addition and negation. TypeTopology's sum of x and y has lower cut
{r + s | r < x , s < y}, and its negation of x has lower cut
{- r | x < r}. Both are defined by pattern matching on the cut
structure of their arguments, and Agda unfolds them when it compares
two sums or two negations whose arguments differ syntactically, which
can be very slow. So we use abstract copies _+_ and -_ of them, and
prove inside the abstract block the facts that need unfolding: the
comparisons with rationals, monotonicity of addition, the two
equalities (x + ιₐ a) + ιₐ b ＝ x + ιₐ (a + b) and x + ιₐ 0 ＝ x, and,
since 12 November 2026, the cancellation (x + (- y)) + y ＝ x. The
second uses the abstract copy ιₐ of the embedding of the rationals of
gist.RealCohesion.RationalPoints, as we do throughout. We also record
that _+_ is TypeTopology's sum, for statements made in its terms.

\begin{code}

infixl 35 _+_

abstract
 _+_ : ℝ → ℝ → ℝ
 x + y = x +ᵗ y

 -_ : ℝ → ℝ
 - x = -ᵗ x

 below-neg : (x : ℝ) (r : ℚ) → x < r → (ℚ- r) < (- x)
 below-neg x r l = ∣ r , l , refl ∣

 neg-below : (x : ℝ) (r : ℚ) → r < x → (- x) < (ℚ- r)
 neg-below x r l = ∣ r , l , refl ∣

 below-neg⁻¹ : (x : ℝ) (p : ℚ) → p < (- x) → x < (ℚ- p)
 below-neg⁻¹ x p = ∥∥-rec (ℝ<ℚ-is-prop x (ℚ- p)) γ
  where
   γ : (Σ r ꞉ ℚ , (x < r) × (p ＝ ℚ- r)) → x < (ℚ- p)
   γ (r , l , e) = transport (x <_) (ℚ-minus-minus r ∙ ap ℚ-_ (e ⁻¹)) l

 neg-below⁻¹ : (x : ℝ) (q : ℚ) → (- x) < q → (ℚ- q) < x
 neg-below⁻¹ x q = ∥∥-rec (ℚ<ℝ-is-prop (ℚ- q) x) γ
  where
   γ : (Σ r ꞉ ℚ , (r < x) × (q ＝ ℚ- r)) → (ℚ- q) < x
   γ (r , l , e) = transport (_< x) (ℚ-minus-minus r ∙ ap ℚ-_ (e ⁻¹)) l

 neg-≤ : (x y : ℝ) → x ≤ y → (- y) ≤ (- x)
 neg-≤ x y k p = ∥∥-functor γ
  where
   γ : (Σ r ꞉ ℚ , (y < r) × (p ＝ ℚ- r)) → Σ r ꞉ ℚ , (x < r) × (p ＝ ℚ- r)
   γ (r , m , e) = r , ≤-<-trans-ℚ x y r k m , e

 below-sum : (x y : ℝ) (r s : ℚ) → r < x → s < y → (r ℚ+ s) < x + y
 below-sum x y r s l m = ∣ (r , s) , l , m , refl ∣

 sum-below : (x y : ℝ) (r s : ℚ) → x < r → y < s → x + y < (r ℚ+ s)
 sum-below x y r s l m = ∣ (r , s) , l , m , refl ∣

 below-sum' : (x y : ℝ) (p r s : ℚ) → r < x → s < y → p ＝ r ℚ+ s → p < x + y
 below-sum' x y p r s l m e = ∣ (r , s) , l , m , e ∣

 sum-below' : (x y : ℝ) (q r s : ℚ) → x < r → y < s → q ＝ r ℚ+ s → x + y < q
 sum-below' x y q r s l m e = ∣ (r , s) , l , m , e ∣

 below-sum⁻¹ : (x y : ℝ) (p : ℚ)
             → p < x + y
             → ∃ (r , s) ꞉ ℚ × ℚ , (r < x) × (s < y) × (p ＝ r ℚ+ s)
 below-sum⁻¹ x y p l = l

 sum-below⁻¹ : (x y : ℝ) (q : ℚ)
             → x + y < q
             → ∃ (r , s) ꞉ ℚ × ℚ , (x < r) × (y < s) × (q ＝ r ℚ+ s)
 sum-below⁻¹ x y q l = l

 sum-≤ : (x x' y y' : ℝ) → x ≤ x' → y ≤ y' → (x + y) ≤ (x' + y')
 sum-≤ x x' y y' k k' p = ∥∥-functor γ
  where
   γ : (Σ (r , s) ꞉ ℚ × ℚ , (r < x) × (s < y) × (p ＝ r ℚ+ s))
     → (Σ (r , s) ꞉ ℚ × ℚ , (r < x') × (s < y') × (p ＝ r ℚ+ s))
   γ ((r , s) , l , m , e) = (r , s) , k r l , k' s m , e

 ιₐ-zero-is-0ℝ : ιₐ 0ℚ ＝ 0ℝ
 ιₐ-zero-is-0ℝ = ιₐ-is-ι 0ℚ

 plus-zero : (x : ℝ) → x + ιₐ 0ℚ ＝ x
 plus-zero x =
  transport (λ - → x + - ＝ x) (ιₐ-zero-is-0ℝ ⁻¹) (ℝ-zero-right-neutral x)

 +-is-+ᵗ : (x y : ℝ) → x + y ＝ x +ᵗ y
 +-is-+ᵗ x y = refl

 minus-plus-cancel : (x y : ℝ) → (x + (- y)) + y ＝ x
 minus-plus-cancel x y = ℝ+-assoc x (-ᵗ y) y
                       ∙ ap (x +ᵗ_)
                          (ℝ+-comm (-ᵗ y) y ∙ pr₂ (ℝ+-inverse-exists y))
                       ∙ ℝ-zero-right-neutral x

\end{code}

A real number is at most another if and only if their difference is
at most 0.

\begin{code}

difference-of-≤ : (a b : ℝ) → a ≤ b → (a + (- b)) ≤ 0ℝ
difference-of-≤ a b k = transport ((a + (- b)) ≤_) ιₐ-zero-is-0ℝ γ
 where
  γ : (a + (- b)) ≤ ιₐ 0ℚ
  γ p l = ∥∥-rec (ℚ<ℝ-is-prop p (ιₐ 0ℚ)) δ (below-sum⁻¹ a (- b) p l)
   where
    δ : (Σ (r , s) ꞉ ℚ × ℚ , (r < a) × (s < (- b)) × (p ＝ r ℚ+ s)) → p < ιₐ 0ℚ
    δ ((r , s) , m , o , e) =
     ιₐ-lower p 0ℚ
      (transport (_< 0ℚ) (e ⁻¹)
        (transport (r ℚ+ s <_) (ℚ-inverse-sum-to-zero' s)
          (ℚ<-addition-preserves-order r (ℚ- s) s
            (cuts-are-ordered b r (ℚ- s) (k r m) (below-neg⁻¹ b s o)))))

≤-from-difference : (a b : ℝ) → (a + (- b)) ≤ 0ℝ → a ≤ b
≤-from-difference a b k = ℝ-not-less-is-greater-or-equal b a γ
 where
  k' : (a + (- b)) ≤ ιₐ 0ℚ
  k' = transport ((a + (- b)) ≤_) (ιₐ-zero-is-0ℝ ⁻¹) k

  γ : ¬ (b < a)
  γ l = ∥∥-rec 𝟘-is-prop δ l
   where
    δ : (Σ q ꞉ ℚ , (b < q) × (q < a)) → 𝟘
    δ (q , m , o) = ∥∥-rec 𝟘-is-prop ε (rounded-left-d a q o)
     where
      ε : (Σ q' ꞉ ℚ , (q < q') × (q' < a)) → 𝟘
      ε (q' , o' , o'') =
       ℚ<-irrefl 0ℚ
        (ℚ<-trans 0ℚ (q' ℚ- q) 0ℚ (ℚ<-difference-positive q q' o')
          (ιₐ-lower⁻¹ (q' ℚ- q) 0ℚ
            (k' (q' ℚ- q) (below-sum a (- b) q' (ℚ- q) o'' (below-neg b q m)))))

\end{code}

The embedding of the rationals preserves addition, and translations by
rationals compose.

\begin{code}

ιₐ-sum : (a b : ℚ) → ιₐ a + ιₐ b ＝ ιₐ (a ℚ+ b)
ιₐ-sum a b = equal-if-lower-cuts-agree (ιₐ a + ιₐ b) (ιₐ (a ℚ+ b)) I II
 where
  I : lower-cut-of (ιₐ a + ιₐ b) ⊆ lower-cut-of (ιₐ (a ℚ+ b))
  I p l = ∥∥-rec (ℚ<ℝ-is-prop p (ιₐ (a ℚ+ b))) γ (below-sum⁻¹ (ιₐ a) (ιₐ b) p l)
   where
    γ : (Σ (r , s) ꞉ ℚ × ℚ , (r < ιₐ a) × (s < ιₐ b) × (p ＝ r ℚ+ s))
      → p < ιₐ (a ℚ+ b)
    γ ((r , s) , l , m , e) =
     ιₐ-lower p (a ℚ+ b)
      (transport (_< a ℚ+ b) (e ⁻¹)
        (ℚ<-adding r a s b (ιₐ-lower⁻¹ r a l) (ιₐ-lower⁻¹ s b m)))

  II : lower-cut-of (ιₐ (a ℚ+ b)) ⊆ lower-cut-of (ιₐ a + ιₐ b)
  II p l = below-sum' (ιₐ a) (ιₐ b) p r (p ℚ- r)
            (ιₐ-lower r a (pr₂ (pr₂ d)))
            (ιₐ-lower (p ℚ- r) b (ℚ<-swap' p b r (pr₁ (pr₂ d))))
            (add-difference r p ⁻¹)
   where
    d : Σ r ꞉ ℚ , (p ℚ- b < r) × (r < a)
    d = ℚ-dense (p ℚ- b) a (<-move-left p a b (ιₐ-lower⁻¹ p (a ℚ+ b) l))

    r : ℚ
    r = pr₁ d

abstract
 translate-twice : (x : ℝ) (a b : ℚ) → (x + ιₐ a) + ιₐ b ＝ x + ιₐ (a ℚ+ b)
 translate-twice x a b = ℝ+-assoc x (ιₐ a) (ιₐ b) ∙ ap (x +_) (ιₐ-sum a b)

\end{code}

Strict cancellation for rationals, and doubling.

\begin{code}

ℚ<-cancel-left : (a b c : ℚ) → a ℚ+ b < a ℚ+ c → b < c
ℚ<-cancel-left a b c = ℚ<-addition-cancellable' b a c

double : ℝ → ℝ
double x = x + x

below-double : (x : ℝ) (p : ℚ) → p < x → (p ℚ+ p) < double x
below-double x p l = below-sum x x p p l l

double-below : (x : ℝ) (q : ℚ) → x < q → double x < (q ℚ+ q)
double-below x q l = sum-below x x q q l l

below-double⁻¹ : (x : ℝ) (p : ℚ) → (p ℚ+ p) < double x → p < x
below-double⁻¹ x p l = ∥∥-rec (ℚ<ℝ-is-prop p x) γ (below-sum⁻¹ x x (p ℚ+ p) l)
 where
  γ : (Σ (r , s) ꞉ ℚ × ℚ , (r < x) × (s < x) × (p ℚ+ p ＝ r ℚ+ s)) → p < x
  γ ((r , s) , l , m , e) = δ (ℚ-trichotomous p r)
   where
    δ : (p < r) ∔ (p ＝ r) ∔ (r < p) → p < x
    δ (inl k)       = use-rounded-real-L x p r k l
    δ (inr (inl k)) = transport (_< x) (k ⁻¹) l
    δ (inr (inr k)) = use-rounded-real-L x p s
                       (ℚ<-cancel-left p p s
                         (transport (_< p ℚ+ s) (e ⁻¹)
                           (ℚ<-addition-preserves-order r p s k)))
                       m

double-below⁻¹ : (x : ℝ) (q : ℚ) → double x < (q ℚ+ q) → x < q
double-below⁻¹ x q l = ∥∥-rec (ℝ<ℚ-is-prop x q) γ (sum-below⁻¹ x x (q ℚ+ q) l)
 where
  γ : (Σ (r , s) ꞉ ℚ × ℚ , (x < r) × (x < s) × (q ℚ+ q ＝ r ℚ+ s)) → x < q
  γ ((r , s) , l , m , e) = δ (ℚ-trichotomous r q)
   where
    δ : (r < q) ∔ (r ＝ q) ∔ (q < r) → x < q
    δ (inl k)       = use-rounded-real-R x r q k l
    δ (inr (inl k)) = transport (x <_) k l
    δ (inr (inr k)) = use-rounded-real-R x s q
                       (ℚ<-cancel-left q s q
                         (transport (q ℚ+ s <_) (e ⁻¹)
                           (ℚ<-addition-preserves-order q r s k)))
                       m

nonneg-below-double : (x : ℝ) → ιₐ 0ℚ ≤ x → x ≤ double x
nonneg-below-double x k p l =
 ∥∥-rec (ℚ<ℝ-is-prop p (double x)) γ (rounded-left-d x p l)
 where
  γ : (Σ r ꞉ ℚ , (p < r) × (r < x)) → p < double x
  γ (r , m , n) = below-sum' x x p r (p ℚ- r) n
                    (k (p ℚ- r)
                      (ιₐ-lower (p ℚ- r) 0ℚ (ℚ<-difference-positive' p r m)))
                    (add-difference r p ⁻¹)

≤-double : (x y : ℝ) → x ≤ y → double x ≤ double y
≤-double x y k = sum-≤ x y x y k k

double-is-positive⁻¹ : (x : ℝ) → 0ℚ < double x → 0ℚ < x
double-is-positive⁻¹ x l =
 below-double⁻¹ x 0ℚ (transport (_< double x) (ℚ-zero-left-neutral 0ℚ ⁻¹) l)

\end{code}

Translations and reflections compared with rationals. These give the
values of the piecewise linear functions used later without any case
analysis on real numbers: each hypothesis is a strict comparison of a
real with a rational, and each conclusion is an inequality ≤ of reals,
or a strict comparison with a rational.

\begin{code}

private
 neg-plus-sum : (c d : ℚ) → (ℚ- d) ℚ+ (c ℚ+ d) ＝ c
 neg-plus-sum c d = ℚ+-comm (ℚ- d) (c ℚ+ d) ∙ ℚ-inverse-intro'' c d ⁻¹

translate-above : (t : ℝ) (c d : ℚ) → (c ℚ+ d) < t → ιₐ c ≤ (t + ιₐ (ℚ- d))
translate-above t c d l p m =
 below-sum' t (ιₐ (ℚ- d)) p (c ℚ+ d) (p ℚ- (c ℚ+ d)) l
  (ιₐ-lower (p ℚ- (c ℚ+ d)) (ℚ- d)
    (<-move-left p (ℚ- d) (c ℚ+ d)
      (transport (p <_) (neg-plus-sum c d ⁻¹) (ιₐ-lower⁻¹ p c m))))
  (add-difference (c ℚ+ d) p ⁻¹)

translate-below : (t : ℝ) (c d : ℚ) → t < (c ℚ+ d) → (t + ιₐ (ℚ- d)) ≤ ιₐ c
translate-below t c d l p m = ∥∥-rec (ℚ<ℝ-is-prop p (ιₐ c)) γ
                               (below-sum⁻¹ t (ιₐ (ℚ- d)) p m)
 where
  γ : (Σ (r , s) ꞉ ℚ × ℚ , (r < t) × (s < ιₐ (ℚ- d)) × (p ＝ r ℚ+ s))
    → p < ιₐ c
  γ ((r , s) , n , o , e) =
   ιₐ-lower p c
    (transport₂ _<_ (e ⁻¹) (plus-minus c d)
      (ℚ<-adding r (c ℚ+ d) s (ℚ- d) (cuts-are-ordered t r (c ℚ+ d) n l)
        (ιₐ-lower⁻¹ s (ℚ- d) o)))

reflect-above : (t : ℝ) (c d : ℚ) → t < (d ℚ- c) → ιₐ c ≤ (ιₐ d + (- t))
reflect-above t c d l p m =
 below-sum' (ιₐ d) (- t) p (p ℚ- s) s
  (ιₐ-lower (p ℚ- s) d
    (transport (_< d) I
      (transport (p ℚ+ (d ℚ- c) <_) (add-difference c d)
        (ℚ<-addition-preserves-order p c (d ℚ- c) (ιₐ-lower⁻¹ p c m)))))
  (below-neg t (d ℚ- c) l)
  (minus-plus p s ⁻¹)
 where
  s : ℚ
  s = ℚ- (d ℚ- c)

  I : p ℚ+ (d ℚ- c) ＝ p ℚ- s
  I = ap (p ℚ+_) (ℚ-minus-minus (d ℚ- c))

reflect-below : (t : ℝ) (c d : ℚ) → (d ℚ- c) < t → (ιₐ d + (- t)) ≤ ιₐ c
reflect-below t c d l p m = ∥∥-rec (ℚ<ℝ-is-prop p (ιₐ c)) γ
                             (below-sum⁻¹ (ιₐ d) (- t) p m)
 where
  γ : (Σ (r , s) ꞉ ℚ × ℚ , (r < ιₐ d) × (s < (- t)) × (p ＝ r ℚ+ s))
    → p < ιₐ c
  γ ((r , s) , n , o , e) =
   ιₐ-lower p c
    (transport₂ _<_ (e ⁻¹) (add-difference d c)
      (ℚ<-adding r d s (c ℚ- d) (ιₐ-lower⁻¹ r d n) II))
   where
    I : (d ℚ- c) < (ℚ- s)
    I = cuts-are-ordered t (d ℚ- c) (ℚ- s) l (below-neg⁻¹ t s o)

    II : s < c ℚ- d
    II = transport₂ _<_ (ℚ-minus-minus s ⁻¹) (ℚ-minus-dist' d c)
          (ℚ<-swap (d ℚ- c) (ℚ- s) I)

translate-strict : (t : ℝ) (c d : ℚ) → (c ℚ+ d) < t → c < (t + ιₐ (ℚ- d))
translate-strict t c d l =
 ∥∥-rec (ℚ<ℝ-is-prop c (t + ιₐ (ℚ- d))) γ (rounded-left-d t (c ℚ+ d) l)
 where
  γ : (Σ r ꞉ ℚ , (c ℚ+ d < r) × (r < t)) → c < (t + ιₐ (ℚ- d))
  γ (r , m , n) = below-sum' t (ιₐ (ℚ- d)) c r (c ℚ- r) n
                   (ιₐ-lower (c ℚ- r) (ℚ- d)
                     (<-move-left c (ℚ- d) r
                       (transport (c <_) (ℚ+-comm r (ℚ- d))
                         (ℚ<-subtraction-preserves-order''' c d r m))))
                   (add-difference r c ⁻¹)

reflect-strict : (t : ℝ) (c d : ℚ) → t < (d ℚ- c) → c < (ιₐ d + (- t))
reflect-strict t c d l = ∥∥-rec (ℚ<ℝ-is-prop c (ιₐ d + (- t))) γ
                          (rounded-right-b (upper-cut-of t)
                            (rounded-from-real-R t) (d ℚ- c) l)
 where
  γ : (Σ r ꞉ ℚ , (r < d ℚ- c) × (t < r)) → c < (ιₐ d + (- t))
  γ (r , m , n) = below-sum' (ιₐ d) (- t) c (c ℚ+ r) (ℚ- r)
                   (ιₐ-lower (c ℚ+ r) d
                     (transport (_< d) (ℚ+-comm r c) (<-add-right r d c m)))
                   (below-neg t r n)
                   (ℚ-inverse-intro'' c r)

below-reflect⁻¹ : (t : ℝ) (c d : ℚ) → c < (ιₐ d + (- t)) → t < (d ℚ- c)
below-reflect⁻¹ t c d l =
 ∥∥-rec (ℝ<ℚ-is-prop t (d ℚ- c)) γ (below-sum⁻¹ (ιₐ d) (- t) c l)
 where
  γ : (Σ (r , s) ꞉ ℚ × ℚ , (r < ιₐ d) × (s < (- t)) × (c ＝ r ℚ+ s))
    → t < (d ℚ- c)
  γ ((r , s) , m , n , e) = use-rounded-real-R t (ℚ- s) (d ℚ- c)
                             (transport (_< d ℚ- c) I
                               (ℚ<-addition-preserves-order r d (ℚ- c)
                                 (ιₐ-lower⁻¹ r d m)))
                             (below-neg⁻¹ t s n)
   where
    I : r ℚ- c ＝ ℚ- s
    I = r ℚ- c                    ＝⟨ ap (λ x → r ℚ- x) e ⟩
        r ℚ- (r ℚ+ s)             ＝⟨ ap (r ℚ+_) (ℚ-minus-dist r s ⁻¹) ⟩
        r ℚ+ ((ℚ- r) ℚ+ (ℚ- s))   ＝⟨ ℚ+-assoc r (ℚ- r) (ℚ- s) ⁻¹ ⟩
        (r ℚ- r) ℚ+ (ℚ- s)        ＝⟨ ap (_ℚ+ (ℚ- s)) (ℚ-inverse-sum-to-zero r) ⟩
        0ℚ ℚ+ (ℚ- s)              ＝⟨ ℚ-zero-left-neutral (ℚ- s) ⟩
        ℚ- s                      ∎

\end{code}

Converses of the strict translation lemmas, and two facts about the
negation of embedded rationals, used in the reduction of the
approximate intermediate value theorem to its normal form.

\begin{code}

below-translate⁻¹ : (t : ℝ) (c d : ℚ) → c < (t + ιₐ (ℚ- d)) → (c ℚ+ d) < t
below-translate⁻¹ t c d l =
 ∥∥-rec (ℚ<ℝ-is-prop (c ℚ+ d) t) γ (below-sum⁻¹ t (ιₐ (ℚ- d)) c l)
 where
  γ : (Σ (u , v) ꞉ ℚ × ℚ , (u < t) × (v < ιₐ (ℚ- d)) × (c ＝ u ℚ+ v))
    → (c ℚ+ d) < t
  γ ((u , v) , m , n , e) = use-rounded-real-L t (c ℚ+ d) u o m
   where
    o : c ℚ+ d < u
    o = transport₂ _<_ (ap (_ℚ+ d) (e ⁻¹)) (ℚ-inverse-intro'' u d ⁻¹ ∙ refl)
         (transport (λ w → (u ℚ+ v) ℚ+ d < w)
           (ℚ+-assoc u (ℚ- d) d ∙ ap (u ℚ+_) (ℚ-inverse-sum-to-zero' d)
            ∙ ℚ-zero-right-neutral u ∙ ℚ-inverse-intro'' u d)
           (ℚ<-addition-preserves-order (u ℚ+ v) (u ℚ+ (ℚ- d)) d
             (transport₂ _<_ (ℚ+-comm v u) (ℚ+-comm (ℚ- d) u)
               (ℚ<-addition-preserves-order v (ℚ- d) u
                 (ιₐ-lower⁻¹ v (ℚ- d) n)))))

translate-below⁻¹ : (t : ℝ) (c d : ℚ) → (t + ιₐ (ℚ- d)) < c → t < (c ℚ+ d)
translate-below⁻¹ t c d l =
 ∥∥-rec (ℝ<ℚ-is-prop t (c ℚ+ d)) γ (sum-below⁻¹ t (ιₐ (ℚ- d)) c l)
 where
  γ : (Σ (u , v) ꞉ ℚ × ℚ , (t < u) × (ιₐ (ℚ- d) < v) × (c ＝ u ℚ+ v))
    → t < (c ℚ+ d)
  γ ((u , v) , m , n , e) = use-rounded-real-R t u (c ℚ+ d) o m
   where
    o : u < c ℚ+ d
    o =
     transport₂ _<_ (ℚ-inverse-intro'' u (ℚ- d) ⁻¹ ∙ refl) (ap (_ℚ+ d) (e ⁻¹))
         (transport (λ w → w < (u ℚ+ v) ℚ+ d)
           (ℚ+-assoc u (ℚ- d) d ∙ ap (u ℚ+_) (ℚ-inverse-sum-to-zero' d)
            ∙ ℚ-zero-right-neutral u ∙ ℚ-inverse-intro'' u (ℚ- d))
           (ℚ<-addition-preserves-order (u ℚ+ (ℚ- d)) (u ℚ+ v) d
             (transport₂ _<_ (ℚ+-comm (ℚ- d) u) (ℚ+-comm v u)
               (ℚ<-addition-preserves-order (ℚ- d) v u
                 (ιₐ-upper⁻¹ (ℚ- d) v n)))))

zero-below-neg-zero : ιₐ 0ℚ ≤ (- ιₐ 0ℚ)
zero-below-neg-zero p l = transport (_< (- ιₐ 0ℚ)) (ℚ-minus-minus p ⁻¹)
                           (below-neg (ιₐ 0ℚ) (ℚ- p)
                             (ιₐ-upper 0ℚ (ℚ- p)
                               (ℚ<-swap'' p (ιₐ-lower⁻¹ p 0ℚ l))))

neg-ιₐ-≤ : (c : ℚ) → (- ιₐ c) ≤ ιₐ (ℚ- c)
neg-ιₐ-≤ c p l = ιₐ-lower p (ℚ- c)
                  (transport (_< ℚ- c) (ℚ-minus-minus p ⁻¹)
                    (ℚ<-swap c (ℚ- p)
                      (ιₐ-upper⁻¹ c (ℚ- p) (below-neg⁻¹ (ιₐ c) p l))))

\end{code}

Positivity. A real number is positive if a positive rational is below
it, and 0 is a left unit of the sum. A difference a - b is positive if and only
if b < a. A positive sum has a positive summand, and a positive maximum a
positive argument; a minimum is positive if and only if both arguments are. A
positive rational translation moves every real number up.

\begin{code}

0ℝ-below-positive : (q : ℚ) → 0ℚ < q → 0ℝ < q
0ℝ-below-positive q l = transport (_< q) ιₐ-zero-is-0ℝ (ιₐ-upper 0ℚ q l)

0ℝ-below-positive⁻¹ : (q : ℚ) → 0ℝ < q → 0ℚ < q
0ℝ-below-positive⁻¹ q l =
 ιₐ-upper⁻¹ 0ℚ q (transport (_< q) (ιₐ-zero-is-0ℝ ⁻¹) l)

positive-from-below : (x : ℝ) (q : ℚ) → 0ℚ < q → q < x → 0ℝ < x
positive-from-below x q l m = ∣ q , 0ℝ-below-positive q l , m ∣

ιₐ-positive : (q : ℚ) → 0ℚ < q → 0ℝ < ιₐ q
ιₐ-positive q l =
 positive-from-below (ιₐ q) c (pr₁ (pr₂ d)) (ιₐ-lower c q (pr₂ (pr₂ d)))
 where
  d : Σ c ꞉ ℚ , (0ℚ < c) × (c < q)
  d = ℚ-dense 0ℚ q l

  c : ℚ
  c = pr₁ d

ιₐ-zero-is-not-positive : ¬ (0ℝ < ιₐ 0ℚ)
ιₐ-zero-is-not-positive = ∥∥-rec 𝟘-is-prop γ
 where
  γ : (Σ q ꞉ ℚ , (0ℝ < q) × (q < ιₐ 0ℚ)) → 𝟘
  γ (q , m , n) =
   ℚ<-irrefl 0ℚ (ℚ<-trans 0ℚ q 0ℚ (0ℝ-below-positive⁻¹ q m) (ιₐ-lower⁻¹ q 0ℚ n))

zero-plus : (x : ℝ) → ιₐ 0ℚ + x ＝ x
zero-plus x =
 +-is-+ᵗ (ιₐ 0ℚ) x ∙ ap (_+ᵗ x) ιₐ-zero-is-0ℝ ∙ ℝ-zero-left-neutral x

<-from-difference : (a b : ℝ) → 0ℝ < (a + (- b)) → b < a
<-from-difference a b = ∥∥-rec (<-is-prop b a) γ
 where
  γ : (Σ q ꞉ ℚ , (0ℝ < q) × (q < (a + (- b)))) → b < a
  γ (q , l , m) = ∥∥-functor δ (below-sum⁻¹ a (- b) q m)
   where
    δ : (Σ (r , s) ꞉ ℚ × ℚ , (r < a) × (s < (- b)) × (q ＝ r ℚ+ s))
      → Σ t ꞉ ℚ , (b < t) × (t < a)
    δ ((r , s) , n , o , e) =
     r , use-rounded-real-R b (ℚ- s) r I (below-neg⁻¹ b s o) , n
     where
      I : (ℚ- s) < r
      I = transport₂ _<_ (ℚ-zero-left-neutral (ℚ- s)) (plus-minus r s)
           (ℚ<-addition-preserves-order 0ℚ (r ℚ+ s) (ℚ- s)
             (transport (0ℚ <_) e (0ℝ-below-positive⁻¹ q l)))

<-gives-positive-difference : (a b : ℝ) → b < a → 0ℝ < (a + (- b))
<-gives-positive-difference a b = ∥∥-rec (<-is-prop 0ℝ (a + (- b))) γ
 where
  γ : (Σ t ꞉ ℚ , (b < t) × (t < a)) → 0ℝ < (a + (- b))
  γ (t , m , n) = ∥∥-functor δ (rounded-left-d a t n)
   where
    δ : (Σ t' ꞉ ℚ , (t < t') × (t' < a))
      → Σ q ꞉ ℚ , (0ℝ < q) × (q < (a + (- b)))
    δ (t' , o , o') = t' ℚ- t ,
                      0ℝ-below-positive (t' ℚ- t)
                       (ℚ<-difference-positive t t' o) ,
                      below-sum a (- b) t' (ℚ- t) o' (below-neg b t m)

positive-sum : (u v : ℝ) → 0ℝ < (u + v) → (0ℝ < u) ∨ (0ℝ < v)
positive-sum u v = ∥∥-rec ∨-is-prop γ
 where
  γ : (Σ q ꞉ ℚ , (0ℝ < q) × (q < (u + v))) → (0ℝ < u) ∨ (0ℝ < v)
  γ (q , l , m) = ∥∥-functor δ (below-sum⁻¹ u v q m)
   where
    δ : (Σ (r , s) ꞉ ℚ × ℚ , (r < u) × (s < v) × (q ＝ r ℚ+ s))
      → (0ℝ < u) ∔ (0ℝ < v)
    δ ((r , s) , n , o , e) = ε (ℚ-dichotomous' 0ℚ r)
     where
      ε : (0ℚ < r) ∔ (r ≤ 0ℚ) → (0ℝ < u) ∔ (0ℝ < v)
      ε (inl k) = inl (positive-from-below u r k n)
      ε (inr k) = inr (positive-from-below v s I o)
       where
        I : 0ℚ < s
        I = ℚ<-≤-trans 0ℚ (r ℚ+ s) s
             (transport (0ℚ <_) e (0ℝ-below-positive⁻¹ q l))
             (transport (r ℚ+ s ≤_) (ℚ-zero-left-neutral s)
               (ℚ≤-addition-preserves-order r 0ℚ s k))

positive-max : (u v : ℝ) → 0ℝ < max u v → (0ℝ < u) ∨ (0ℝ < v)
positive-max u v = ∥∥-rec ∨-is-prop γ
 where
  γ : (Σ q ꞉ ℚ , (0ℝ < q) × (q < max u v)) → (0ℝ < u) ∨ (0ℝ < v)
  γ (q , l , m) = ∥∥-functor δ (below-max u v q m)
   where
    δ : (q < u) ∔ (q < v) → (0ℝ < u) ∔ (0ℝ < v)
    δ (inl n) = inl ∣ q , l , n ∣
    δ (inr n) = inr ∣ q , l , n ∣

positive-max-right : (u v : ℝ) → 0ℝ < v → 0ℝ < max u v
positive-max-right u v = ∥∥-functor γ
 where
  γ : (Σ q ꞉ ℚ , (0ℝ < q) × (q < v)) → Σ q ꞉ ℚ , (0ℝ < q) × (q < max u v)
  γ (q , l , m) = q , l , below-max-right u v q m

positive-min : (u v : ℝ) → 0ℝ < u → 0ℝ < v → 0ℝ < min u v
positive-min u v l l' = ∥∥-rec (<-is-prop 0ℝ (min u v)) γ l
 where
  γ : (Σ q ꞉ ℚ , (0ℝ < q) × (q < u)) → 0ℝ < min u v
  γ (q , m , n) = ∥∥-functor δ l'
   where
    δ : (Σ q' ꞉ ℚ , (0ℝ < q') × (q' < v)) → Σ p ꞉ ℚ , (0ℝ < p) × (p < min u v)
    δ (q' , m' , n') = ε (ℚ-dichotomous' q q')
     where
      ε : (q < q') ∔ (q' ≤ q) → Σ p ꞉ ℚ , (0ℝ < p) × (p < min u v)
      ε (inl o) = q , m , below-min u v q n (use-rounded-real-L v q q' o n')
      ε (inr o) = q' , m' , below-min u v q' (use-rounded-real-L' u q' q o n) n'

positive-min⁻¹ : (u v : ℝ) → 0ℝ < min u v → (0ℝ < u) × (0ℝ < v)
positive-min⁻¹ u v l = ∥∥-functor γ l , ∥∥-functor δ l
 where
  γ : (Σ q ꞉ ℚ , (0ℝ < q) × (q < min u v)) → Σ q ꞉ ℚ , (0ℝ < q) × (q < u)
  γ (q , m , n) = q , m , below-min-left u v q n

  δ : (Σ q ꞉ ℚ , (0ℝ < q) × (q < min u v)) → Σ q ꞉ ℚ , (0ℝ < q) × (q < v)
  δ (q , m , n) = q , m , below-min-right u v q n

translate-up : (u : ℝ) (c : ℚ) → 0ℚ < c → u < (u + ιₐ c)
translate-up u c l = ∥∥-functor γ (ℝ-arithmetically-located u (c , l))
 where
  γ : (Σ (a , b) ꞉ ℚ × ℚ , ((a < u) × (u < b)) × (b ℚ- a < c))
    → Σ t ꞉ ℚ , (u < t) × (t < (u + ιₐ c))
  γ ((a , b) , (m , n) , d) =
   b , n , below-sum' u (ιₐ c) b a (b ℚ- a) m (ιₐ-lower (b ℚ- a) c d)
    (add-difference a b ⁻¹)

translate-down : (u : ℝ) (c : ℚ) → 0ℚ < c → (u + ιₐ (ℚ- c)) < u
translate-down u c l =
 transport ((u + ιₐ (ℚ- c)) <_) I (translate-up (u + ιₐ (ℚ- c)) c l)
 where
  I : (u + ιₐ (ℚ- c)) + ιₐ c ＝ u
  I = translate-twice u (ℚ- c) c
    ∙ ap (λ - → u + ιₐ -) (ℚ-inverse-sum-to-zero' c)
    ∙ plus-zero u

\end{code}

Finite minima over Fin n. The minimum over Fin 0 is 1/2, so that a
positive minimum and positive terms correspond in every dimension.
Moved here on 12 November 2026 from
gist.RealCohesion.ApproximateCubeFixedPoint, which re-exports them, so
that modules without --cohesion can use them.

\begin{code}

Fin-min : {n : ℕ} → (Fin n → ℝ) → ℝ
Fin-min {0}      t = ιₐ 1/2
Fin-min {succ n} t = min (t 𝟎) (Fin-min (t ∘ suc))

Fin-min-is-positive : {n : ℕ} (t : Fin n → ℝ) → ((i : Fin n) → 0ℝ < t i)
                    → 0ℝ < Fin-min t
Fin-min-is-positive {0}      t h = ιₐ-positive 1/2 0<1/2
Fin-min-is-positive {succ n} t h = positive-min (t 𝟎) (Fin-min (t ∘ suc)) (h 𝟎)
                                    (Fin-min-is-positive (t ∘ suc) (h ∘ suc))

positive-Fin-min : {n : ℕ} (t : Fin n → ℝ) → 0ℝ < Fin-min t → (i : Fin n)
                 → 0ℝ < t i
positive-Fin-min {0}      t l i       = 𝟘-elim i
positive-Fin-min {succ n} t l 𝟎       =
 pr₁ (positive-min⁻¹ (t 𝟎) (Fin-min (t ∘ suc)) l)
positive-Fin-min {succ n} t l (suc i) =
 positive-Fin-min (t ∘ suc) (pr₂ (positive-min⁻¹ (t 𝟎) (Fin-min (t ∘ suc)) l)) i

\end{code}
