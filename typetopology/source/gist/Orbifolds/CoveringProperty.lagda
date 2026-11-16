Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 13 November 2026 (local time). Orbifold gate H10 of Fable's
roadmap [1], for the target T5b.

The Covering Property, and Myers's Theorems 6.2.8 and 6.2.13
------------------------------------------------------------

Myers's Postulate E [2, p. 30], the Covering Property of Bunge and
Dubuc: if two subsets A and B of R cover R, then every x has a ball
B(x, ε), ε > 0, inside A or inside B. Here it is stated for subsets
valued in a universe 𝓤, the level of the refinement predicates of T5b
[3, Section A], with the balls of Definition 5.1.4 for n = 1:
B(x, ε) = {y | (x − y)² < ε²}.

  Postulate-E 𝓤 : the Covering Property for 𝓤-valued subsets;

  theorem-6-2-8 : for a Dubuc–Penon compact K and a relation r on
  K × R that is Penon open, if r(k , x) for every k, then for some
  ε > 0, r(k , y) for every y in B(x, ε) and every k [2, Theorem 6.2.8];

  theorem-6-2-13 : for a Dubuc–Penon compact K and a cover of K by
  Penon-open subsets U n, n : ℕ, there is merely a bound N such that
  every point of K lies in some U n with n < N [2, Theorem 6.2.13]. As
  in [1, Section 3.10] and [4, Section 5], the relation of the proof is
  r(k , x) = ∃ n , U n k ∧ x < 1/(n + 1), repairing the printed 1/n,
  which divides by zero at n = 0. The statement is for families
  indexed by ℕ. For an index set I ⊆ ℕ one takes for U n the product
  of the proposition that n is in I with the given member;
  FiniteSubcovers does this inline (its family U), and no general
  statement of it is declared.

The hypotheses are Postulates O, Exp (for the translation law) and K,
and Postulate E at 𝓤.

[1] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026.
    references/F01-orbifolds-roadmap-rev2.md
[2] D. J. Myers. Orbifolds as microlinear types in synthetic
    differential cohesive homotopy type theory. arXiv:2205.15887v1.
[3] GPT-6 Astra. H10 T5b implementation preflight, 13 November 2026
    (UTC).
    references/A24-t5b-preflight.txt
[4] GPT-6 Astra. DP properness implies the replacement over the
    five-item core, 11 November 2026.
    references/A02-dp-properness-implies-replacement.txt

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc

module gist.Orbifolds.CoveringProperty where

open import Naturals.Order
 using (_≤ℕ_ ; ≤-decidable ; not-less-bigger-or-equal ; <-trans ; <-succ)
open import UF.Base
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UniverseEmbedding using (Lift ; lift ; lower ; Lift-≃)
open import UF.Equiv using (equiv-to-prop)
open import gist.Orbifolds.SmoothLine
open import gist.Orbifolds.SmoothOrder
open import gist.Orbifolds.SmoothOrderAlgebra
open import gist.Orbifolds.MetricTopology
open import gist.Orbifolds.RationalPoints

module covering-property
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
        (𝓡 : Commutative-Ring)
       where

 open PropositionalTruncation pt
 open smooth-line fe pt 𝓡
 open smooth-order fe pt 𝓡
 open smooth-order-algebra fe pt 𝓡
 open metric-topology fe pt 𝓡 using (≤-is-transitive ; ≤-translation)
 open rational-points fe pt 𝓡
 open import gist.Orbifolds.DubucPenon fe pt
 open import gist.Orbifolds.CoverFiniteness fe pt using (is-Penon-open)

 _<ℕ_ : ℕ → ℕ → 𝓤₀ ̇
 m <ℕ n = succ m ≤ℕ n

 module _ (O : Postulate-O) (Exp : Postulate-Exp O) (K : Postulate-K) where

  open Postulate-O O

  private
   translation : Translation-Law O
   translation = translation-law-from-Exp O Exp

  open order-lemmas O translation
  open order-algebra O translation

\end{code}

Balls in R, and the Covering Property.

\begin{code}

  ball : R → R → R → 𝓤₀ ̇
  ball x ε y = (x +ᴿ (-ᴿ y)) ·ᴿ (x +ᴿ (-ᴿ y)) < ε ·ᴿ ε

  centres-are-in-balls : (x ε : R) → 0ᴿ < ε → ball x ε x
  centres-are-in-balls x ε l =
   transport (_< ε ·ᴿ ε)
    ((·-zero 0ᴿ)⁻¹ ∙ ap₂ _·ᴿ_ ((+-inverse x)⁻¹) ((+-inverse x)⁻¹))
    (products-of-positives-are-positive ε ε l l)

  Postulate-E : (𝓤 : Universe) → 𝓤 ⁺ ̇
  Postulate-E 𝓤 =
     (A B : R → 𝓤 ̇ ) → ((x : R) → is-prop (A x)) → ((x : R) → is-prop (B x))
   → ((x : R) → A x ∨ B x)
   → (x : R) → (∃ ε ꞉ R , (0ᴿ < ε) × ((y : R) → ball x ε y → A y))
             ∨ (∃ ε ꞉ R , (0ᴿ < ε) × ((y : R) → ball x ε y → B y))

\end{code}

Theorem 6.2.8.

\begin{code}

  module _ {𝓤 : Universe} (E : Postulate-E 𝓤) where

   theorem-6-2-8
    : (L : 𝓤 ̇ ) → is-DP-compact L
    → (r : L → R → 𝓤 ̇ ) → ((k : L) (x : R) → is-prop (r k x))
    → is-Penon-open (λ (z : L × R) → r (pr₁ z) (pr₂ z))
    → (x : R) → ((k : L) → r k x)
    → ∃ ε ꞉ R , (0ᴿ < ε) × ((y : R) → ball x ε y → (k : L) → r k y)
   theorem-6-2-8 L c r r-is-prop r-is-Penon-open x h =
    ∥∥-rec ∃-is-prop
     (cases (λ first → 𝟘-elim (∥∥-rec 𝟘-is-prop
                                 (λ (ε , lε , f) → lower
                                   (f x (centres-are-in-balls x ε lε)) refl)
                                 first))
            id)
     (E (λ y → Lift 𝓤 (x ≠ y)) (λ y → (k : L) → r k y)
        (λ y → equiv-to-prop (Lift-≃ 𝓤 _) (negations-are-props fe))
        (λ y → Π-is-prop fe (λ k → r-is-prop k y))
        cover x)
    where
     cover : (y : R) → Lift 𝓤 (x ≠ y) ∨ ((k : L) → r k y)
     cover y =
      c (Lift 𝓤 (x ≠ y)) (equiv-to-prop (Lift-≃ 𝓤 _) (negations-are-props fe))
        (λ k → r k y) (λ k → r-is-prop k y)
        (λ k → ∥∥-functor
                (cases (λ ne → inl (lift 𝓤 (λ p → ne (ap (k ,_) p)))) inr)
                (r-is-Penon-open (k , x) (h k) (k , y)))

\end{code}

The natural numbers in R are non-negative and reflect the order.

\begin{code}

   private
    ι-is-nonnegative : (n : ℕ) → 0ᴿ ≤ ι n
    ι-is-nonnegative 0 = <-is-irreflexive 0ᴿ
    ι-is-nonnegative (succ n) =
     ≤-is-transitive O translation K 0ᴿ (ι n) (ι n +ᴿ 1ᴿ) (ι-is-nonnegative n)
      (<-gives-≤ _ _
        (below-sum-with-positive O translation K (ι n) 1ᴿ one-is-positive))

    ι-is-monotone : (a b : ℕ) → a ≤ℕ b → ι a ≤ ι b
    ι-is-monotone 0 b l = ι-is-nonnegative b
    ι-is-monotone (succ a) 0 ()
    ι-is-monotone (succ a) (succ b) l =
     ≤-translation O translation K (ι a) (ι b) 1ᴿ (ι-is-monotone a b l)

    ι-reflects-order : (a b : ℕ) → ι a < ι b → a <ℕ b
    ι-reflects-order a b l =
     cases id
      (λ ν → 𝟘-elim (ι-is-monotone b a (not-less-bigger-or-equal b a ν) l))
      (≤-decidable (succ a) b)

\end{code}

Theorem 6.2.13, with 1/(n + 1).

\begin{code}

   theorem-6-2-13
    : (L : 𝓤 ̇ ) → is-DP-compact L
    → (U : ℕ → L → 𝓤 ̇ ) → ((n : ℕ) (k : L) → is-prop (U n k))
    → ((n : ℕ) → is-Penon-open (U n))
    → ((k : L) → ∃ n ꞉ ℕ , U n k)
    → ∃ N ꞉ ℕ , ((k : L) → ∃ n ꞉ ℕ , (n <ℕ N) × U n k)
   theorem-6-2-13 L c U U-is-prop U-is-Penon-open U-covers =
    ∥∥-rec ∃-is-prop with-radius
     (theorem-6-2-8 L c r (λ k x → ∃-is-prop) r-is-Penon-open 0ᴿ
       (λ k → ∥∥-functor (λ (n , u) → n , u , w-is-positive O translation K n)
               (U-covers k)))
    where
     r : L → R → 𝓤 ̇
     r k x = ∃ n ꞉ ℕ , U n k × (x < w O translation K n)

     r-is-Penon-open : is-Penon-open (λ (z : L × R) → r (pr₁ z) (pr₂ z))
     r-is-Penon-open (k , x) h (q , y) =
      ∥∥-rec ∥∥-is-prop
       (λ (n , u , l) →
         ∥∥-rec ∥∥-is-prop
          (cases (λ (kq : k ≠ q) → ∣ inl (λ p → kq (ap pr₁ p)) ∣)
                 (λ (uq : U n q) →
                   ∥∥-functor
                    (cases
                      (λ (yl : y < w O translation K n) → inr ∣ n , uq , yl ∣)
                           (λ (xy : x < y) → inl (λ p → <-is-irreflexive y
                                                         (transport (_< y)
                                                           (ap pr₂ p) xy))))
                    (<-is-cotransitive (w O translation K n) x y l)))
          (U-is-Penon-open n k u q))
       h

     with-radius
      : (Σ ε ꞉ R , (0ᴿ < ε) × ((y : R) → ball 0ᴿ ε y → (k : L) → r k y))
                 → ∃ N ꞉ ℕ , ((k : L) → ∃ n ꞉ ℕ , (n <ℕ N) × U n k)
     with-radius (ε , lε , f) =
      ∥∥-functor (λ (N , yN) →
        N , (λ k → ∥∥-functor (λ (n , u , l) → n , bound N yN n l , u)
                              (f y y-in-ball k)))
       (archimedean y')
      where
       y = ε ·ᴿ w O translation K 1
       ly : 0ᴿ < y
       ly = products-of-positives-are-positive ε _ lε
             (w-is-positive O translation K 1)
       y<ε : y < ε
       y<ε = transport (y <_) (halves O translation K ε)
              (below-sum-with-positive O translation K y y ly)
       y-in-ball : ball 0ᴿ ε y
       y-in-ball =
        square-from-interval ε (0ᴿ +ᴿ (-ᴿ y))
         (transport (-ᴿ ε <_) ((+-unit-left (-ᴿ y))⁻¹)
           (negation-reverses-order y ε y<ε))
         (transport (_< ε) ((+-unit-left (-ᴿ y))⁻¹)
           (<-is-transitive _ _ _ (negation-of-positive-is-negative y ly) lε))
       y-inverse = positive-elements-are-invertible K y ly
       y' = pr₁ y-inverse
       y'y : y' ·ᴿ y ＝ 1ᴿ
       y'y = pr₂ y-inverse
       ly' : 0ᴿ < y'
       ly' = inverses-of-positive-elements-are-positive K y ly
       bound : (N : ℕ) → y' < ι N → (n : ℕ) → y < w O translation K n → n <ℕ N
       bound N yN n l =
        <-trans n (succ n) N (<-succ n)
         (ι-reflects-order (succ n) N (<-is-transitive _ _ _ sn<y' yN))
        where
         sn = ι n +ᴿ 1ᴿ
         wn = w O translation K n
         sn<y' : sn < y'
         sn<y' =
          transport₂ _<_
           (·-comm (y ·ᴿ sn) y' ∙ (·-assoc y' y sn)⁻¹ ∙ ap (_·ᴿ sn) y'y
            ∙ ·-unit-left sn)
           (·-unit-left y')
           (products-with-positive-factor-preserve-order (y ·ᴿ sn) 1ᴿ y' ly'
             (transport (y ·ᴿ sn <_) (w-is-inverse O translation K n)
               (products-with-positive-factor-preserve-order y wn sn
                 (s-is-positive O translation K n) l)))

\end{code}
