Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 26 October 2026. See the AI disclosure in
gist.RealCohesion.index.

Signs of real numbers, and order facts relating rationals and reals.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.RealOrder
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import Notation.CanonicalMap
open import Notation.Order
open import Rationals.Order
open import Rationals.Type
open import UF.Powerset
open import DedekindReals.Order fe pe pt
open import DedekindReals.Type fe pe pt
open import gist.RealCohesion.RationalArithmetic using (opposite) public

open PropositionalTruncation pt

\end{code}

Signs.

\begin{code}

Has-Sign : 𝟚 → ℝ → 𝓤₀ ̇
Has-Sign ₀ x = x < 0ℚ
Has-Sign ₁ x = 0ℚ < x

Has-Sign-is-prop : (σ : 𝟚) (x : ℝ) → is-prop (Has-Sign σ x)
Has-Sign-is-prop ₀ x = ∈-is-prop (upper-cut-of x) 0ℚ
Has-Sign-is-prop ₁ x = ∈-is-prop (lower-cut-of x) 0ℚ

signs-are-exclusive : (σ : 𝟚) (x : ℝ) → Has-Sign σ x → ¬ Has-Sign (opposite σ) x
signs-are-exclusive ₀ x l m = ℚ<-irrefl 0ℚ (disjoint-from-real x 0ℚ 0ℚ (m , l))
signs-are-exclusive ₁ x l m = ℚ<-irrefl 0ℚ (disjoint-from-real x 0ℚ 0ℚ (l , m))

zero-has-no-sign : (σ : 𝟚) → ¬ Has-Sign σ 0ℝ
zero-has-no-sign ₀ = ℚ<-irrefl 0ℚ
zero-has-no-sign ₁ = ℚ<-irrefl 0ℚ

no-sign-gives-zero : (x : ℝ) → ¬ (0ℚ < x) → ¬ (x < 0ℚ) → x ＝ 0ℝ
no-sign-gives-zero x a b = ℝ-equality-from-left-cut' x 0ℝ I II
 where
  I : lower-cut-of x ⊆ lower-cut-of 0ℝ
  I q l = γ (ℚ-dichotomous' q 0ℚ)
   where
    γ : (q < 0ℚ) ∔ (0ℚ ≤ q) → q < 0ℚ
    γ (inl m) = m
    γ (inr m) = 𝟘-elim (a (use-rounded-real-L' x 0ℚ q m l))

  II : lower-cut-of 0ℝ ⊆ lower-cut-of x
  II q l = ∥∥-rec (∈-is-prop (lower-cut-of x) q) γ (ℝ-locatedness x q 0ℚ l)
   where
    γ : q ∈ lower-cut-of x ∔ 0ℚ ∈ upper-cut-of x → q ∈ lower-cut-of x
    γ (inl m) = m
    γ (inr m) = 𝟘-elim (b m)

\end{code}

Order facts relating rationals and reals.

\begin{code}

below-a-real : (x : ℝ) (p q : ℚ) → p < q → q < x → p < x
below-a-real = use-rounded-real-L

above-a-real : (x : ℝ) (p q : ℚ) → p < q → x < p → x < q
above-a-real = use-rounded-real-R

cuts-are-ordered : (x : ℝ) (p q : ℚ) → p < x → x < q → p < q
cuts-are-ordered x p q a b = disjoint-from-real x p q (a , b)

not-below-and-above : (x : ℝ) (p : ℚ) → p < x → x < p → 𝟘 {𝓤₀}
not-below-and-above x p a b = ℚ<-irrefl p (cuts-are-ordered x p p a b)

located-above : (x : ℝ) (p q : ℚ) → p < q → ¬ (x < q) → p < x
located-above x p q l ν =
 ∥∥-rec (∈-is-prop (lower-cut-of x) p) γ (ℝ-locatedness x p q l)
 where
  γ : p ∈ lower-cut-of x ∔ q ∈ upper-cut-of x → p < x
  γ (inl m) = m
  γ (inr m) = 𝟘-elim (ν m)

located-below : (x : ℝ) (p q : ℚ) → p < q → ¬ (p < x) → x < q
located-below x p q l ν =
 ∥∥-rec (∈-is-prop (upper-cut-of x) q) γ (ℝ-locatedness x p q l)
 where
  γ : p ∈ lower-cut-of x ∔ q ∈ upper-cut-of x → x < q
  γ (inl m) = 𝟘-elim (ν m)
  γ (inr m) = m

above-lower-bound : (t : ℝ) (r α : ℚ) → r < α → ι α ≤ t → r < t
above-lower-bound t r α l k = k r l

below-upper-bound : (t : ℝ) (β r' : ℚ) → β < r' → t ≤ ι β → t < r'
below-upper-bound t β r' l k =
 located-below t β r' l (λ m → ℚ<-irrefl β (k β m))

ℝ≤-refl : (x : ℝ) → x ≤ x
ℝ≤-refl x q l = l

ℝ<-gives-≤ : (x y : ℝ) → x < y → x ≤ y
ℝ<-gives-≤ x y l = ℝ-not-less-is-greater-or-equal y x
                    (λ m → <ℝ-irreflexive x (ℝ<-trans x y x l m))

embedding-preserves-≤ : (p q : ℚ) → p ≤ q → ι p ≤ ι q
embedding-preserves-≤ p q l r m = ℚ<-≤-trans r p q m l

embedding-reflects-≤ : (p q : ℚ) → ι p ≤ ι q → p ≤ q
embedding-reflects-≤ p q k = γ (ℚ-dichotomous' q p)
 where
  γ : (q < p) ∔ (p ≤ q) → p ≤ q
  γ (inl l) = 𝟘-elim (ℚ<-irrefl q (k q l))
  γ (inr l) = l

\end{code}

Tightness of the order: two real numbers neither of which is below the
other are equal. This was in gist.RealCohesion.CrispExactIVT, which
re-exports it.

\begin{code}

ℝ<-tight : (x y : ℝ) → ¬ (x < y) → ¬ (y < x) → x ＝ y
ℝ<-tight x y n n' = ≤-ℝ-ℝ-antisym x y
                     (ℝ-not-less-is-greater-or-equal y x n')
                     (ℝ-not-less-is-greater-or-equal x y n)

\end{code}
