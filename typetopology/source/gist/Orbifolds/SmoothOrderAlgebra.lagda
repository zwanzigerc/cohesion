Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026 (local time). Orbifold gate H9 of Fable's
roadmap [1], following Fable's corrected guidance [2] and GPT-6
Astra's audits [3].

Algebra of the ordered smooth line
----------------------------------

The facts about the order of R that the metric topology of Rⁿ needs
(Myers's Theorem 5.1.5 [4, p. 42]), from Postulate O as printed, the
translation law (from Postulate Exp, SmoothOrder) and Postulate K, with
no square roots and no decision of the order:

  ring identities for negation (through the uniqueness of additive
  inverses);

  monotonicity of sums and of products with a positive factor; the sign
  of a product; squares are not negative, and squares of nonzero
  elements are positive;

  positive elements are invertible, with positive inverse (K);

  a positive element below two given positive elements
  (positive-below-two), and one whose square is below a given positive
  element (positive-with-small-square);

  interval-from-square : if 0 < ε and a² < ε², then −ε < a < ε;
  square-from-interval : if −δ < a < δ, then a² < δ².

[1] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026.
    references/F01-orbifolds-roadmap-rev2.md
[2] Claude Fable 5.2. Orbifolds H9 and H10: follow-up to Astra's
    readiness audits, 13 November 2026 (UTC).
    references/F04-orbifolds-h9-h10-followup.md
[3] GPT-6 Astra. Fable H9 follow-up: route and interface audit,
    13 November 2026 (UTC).
    references/A15-h9-followup-audit.txt
[4] D. J. Myers. Orbifolds as microlinear types in synthetic
    differential cohesive homotopy type theory. arXiv:2205.15887v1.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc

module gist.Orbifolds.SmoothOrderAlgebra where

open import UF.Base
open import UF.Subsingletons
open import gist.Orbifolds.SmoothLine
open import gist.Orbifolds.SmoothOrder

module smooth-order-algebra
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
        (𝓡 : Commutative-Ring)
       where

 open PropositionalTruncation pt
 open smooth-line fe pt 𝓡
 open smooth-order fe pt 𝓡

\end{code}

Ring identities.

\begin{code}

 negation-is-unique : (x y : R) → x +ᴿ y ＝ 0ᴿ → y ＝ -ᴿ x
 negation-is-unique x y p =
  y                         ＝⟨ (+-unit-left y)⁻¹ ⟩
  0ᴿ +ᴿ y                   ＝⟨ ap (_+ᴿ y) ((+-inverse-left x)⁻¹) ⟩
  (-ᴿ x) +ᴿ x +ᴿ y          ＝⟨ +-assoc (-ᴿ x) x y ⟩
  (-ᴿ x) +ᴿ (x +ᴿ y)        ＝⟨ ap ((-ᴿ x) +ᴿ_) p ⟩
  (-ᴿ x) +ᴿ 0ᴿ              ＝⟨ +-unit (-ᴿ x) ⟩
  -ᴿ x                      ∎

 negation-is-involutive : (x : R) → -ᴿ (-ᴿ x) ＝ x
 negation-is-involutive x = (negation-is-unique (-ᴿ x) x (+-inverse-left x))⁻¹

 negation-of-zero : -ᴿ 0ᴿ ＝ 0ᴿ
 negation-of-zero = (negation-is-unique 0ᴿ 0ᴿ (+-unit 0ᴿ))⁻¹

 ·-negation-right : (x y : R) → x ·ᴿ (-ᴿ y) ＝ -ᴿ (x ·ᴿ y)
 ·-negation-right x y =
  negation-is-unique (x ·ᴿ y) (x ·ᴿ (-ᴿ y))
   ((distributivity x y (-ᴿ y))⁻¹ ∙ ap (x ·ᴿ_) (+-inverse y) ∙ ·-zero x)

 ·-negation-left : (x y : R) → (-ᴿ x) ·ᴿ y ＝ -ᴿ (x ·ᴿ y)
 ·-negation-left x y =
  ·-comm (-ᴿ x) y ∙ ·-negation-right y x ∙ ap -ᴿ_ (·-comm y x)

 ·-negation-both : (x y : R) → (-ᴿ x) ·ᴿ (-ᴿ y) ＝ x ·ᴿ y
 ·-negation-both x y = ·-negation-left x (-ᴿ y) ∙ ap -ᴿ_ (·-negation-right x y)
                     ∙ negation-is-involutive (x ·ᴿ y)

 distributivity-right : (x y z : R) → (x +ᴿ y) ·ᴿ z ＝ (x ·ᴿ z) +ᴿ (y ·ᴿ z)
 distributivity-right x y z = ·-comm (x +ᴿ y) z ∙ distributivity z x y
                            ∙ ap₂ _+ᴿ_ (·-comm z x) (·-comm z y)

 +-interchange : (a b c d : R) → (a +ᴿ b) +ᴿ (c +ᴿ d) ＝ (a +ᴿ c) +ᴿ (b +ᴿ d)
 +-interchange a b c d =
  +-assoc a b (c +ᴿ d)
  ∙ ap (a +ᴿ_) ((+-assoc b c d)⁻¹ ∙ ap (_+ᴿ d) (+-comm b c) ∙ +-assoc c b d)
  ∙ (+-assoc a c (b +ᴿ d))⁻¹

 negation-of-sum : (x y : R) → -ᴿ (x +ᴿ y) ＝ (-ᴿ x) +ᴿ (-ᴿ y)
 negation-of-sum x y =
  (negation-is-unique (x +ᴿ y) ((-ᴿ x) +ᴿ (-ᴿ y))
    (+-interchange x y (-ᴿ x) (-ᴿ y) ∙ ap₂ _+ᴿ_ (+-inverse x) (+-inverse y)
     ∙ +-unit 0ᴿ))⁻¹

 difference-of-squares : (e a : R)
                       → (e +ᴿ (-ᴿ a)) ·ᴿ (e +ᴿ a) ＝ (e ·ᴿ e) +ᴿ (-ᴿ (a ·ᴿ a))
 difference-of-squares e a =
  (e +ᴿ (-ᴿ a)) ·ᴿ (e +ᴿ a)
   ＝⟨ distributivity-right e (-ᴿ a) (e +ᴿ a) ⟩
  (e ·ᴿ (e +ᴿ a)) +ᴿ ((-ᴿ a) ·ᴿ (e +ᴿ a))
   ＝⟨ ap₂ _+ᴿ_ (distributivity e e a) (distributivity (-ᴿ a) e a) ⟩
  (e ·ᴿ e +ᴿ e ·ᴿ a) +ᴿ ((-ᴿ a) ·ᴿ e +ᴿ (-ᴿ a) ·ᴿ a)
   ＝⟨ ap (λ - → (e ·ᴿ e +ᴿ e ·ᴿ a) +ᴿ (- +ᴿ (-ᴿ a) ·ᴿ a))
          (·-negation-left a e ∙ ap -ᴿ_ (·-comm a e)) ⟩
  (e ·ᴿ e +ᴿ e ·ᴿ a) +ᴿ (-ᴿ (e ·ᴿ a) +ᴿ (-ᴿ a) ·ᴿ a)
   ＝⟨ +-interchange (e ·ᴿ e) (e ·ᴿ a) (-ᴿ (e ·ᴿ a)) ((-ᴿ a) ·ᴿ a) ⟩
  (e ·ᴿ e +ᴿ -ᴿ (e ·ᴿ a)) +ᴿ (e ·ᴿ a +ᴿ (-ᴿ a) ·ᴿ a)
   ＝⟨ ap₂ _+ᴿ_ refl
          (ap (e ·ᴿ a +ᴿ_) (·-negation-left a a)) ⟩
  (e ·ᴿ e +ᴿ -ᴿ (e ·ᴿ a)) +ᴿ (e ·ᴿ a +ᴿ -ᴿ (a ·ᴿ a))
   ＝⟨ +-interchange (e ·ᴿ e) (-ᴿ (e ·ᴿ a)) (e ·ᴿ a) (-ᴿ (a ·ᴿ a)) ⟩
  (e ·ᴿ e +ᴿ e ·ᴿ a) +ᴿ (-ᴿ (e ·ᴿ a) +ᴿ -ᴿ (a ·ᴿ a))
   ＝⟨ +-assoc (e ·ᴿ e) (e ·ᴿ a) (-ᴿ (e ·ᴿ a) +ᴿ -ᴿ (a ·ᴿ a)) ⟩
  e ·ᴿ e +ᴿ (e ·ᴿ a +ᴿ (-ᴿ (e ·ᴿ a) +ᴿ -ᴿ (a ·ᴿ a)))
   ＝⟨ ap (e ·ᴿ e +ᴿ_) ((+-assoc (e ·ᴿ a) (-ᴿ (e ·ᴿ a)) (-ᴿ (a ·ᴿ a)))⁻¹
          ∙ ap (_+ᴿ -ᴿ (a ·ᴿ a)) (+-inverse (e ·ᴿ a))
          ∙ +-unit-left (-ᴿ (a ·ᴿ a))) ⟩
  e ·ᴿ e +ᴿ -ᴿ (a ·ᴿ a)                                   ∎

\end{code}

Order algebra under O and the translation law.

\begin{code}

 module order-algebra (O : Postulate-O) (translation : Translation-Law O) where

  open Postulate-O O
  open order-lemmas O translation

  <-adds : (a b c d : R) → a < b → c < d → a +ᴿ c < b +ᴿ d
  <-adds a b c d l m =
   <-is-transitive _ _ _ (translation a b c l)
    (transport₂ _<_ (+-comm c b) (+-comm d b) (translation c d b m))

  products-with-positive-factor-preserve-order
   : (x y z : R) → 0ᴿ < z → x < y → x ·ᴿ z < y ·ᴿ z
  products-with-positive-factor-preserve-order x y z p l =
   positive-difference (x ·ᴿ z) (y ·ᴿ z)
    (transport (0ᴿ <_)
      (distributivity-right y (-ᴿ x) z
       ∙ ap ((y ·ᴿ z) +ᴿ_) (·-negation-left x z))
      (products-of-positives-are-positive (y +ᴿ (-ᴿ x)) z
        (difference-is-positive x y l) p))

  negation-of-negative-is-positive : (x : R) → x < 0ᴿ → 0ᴿ < -ᴿ x
  negation-of-negative-is-positive x l =
   transport (_< -ᴿ x) negation-of-zero (negation-reverses-order x 0ᴿ l)

  negation-of-positive-is-negative : (x : R) → 0ᴿ < x → -ᴿ x < 0ᴿ
  negation-of-positive-is-negative x l =
   transport (-ᴿ x <_) negation-of-zero (negation-reverses-order 0ᴿ x l)

  positive-from-negation : (x : R) → 0ᴿ < -ᴿ x → x < 0ᴿ
  positive-from-negation x l =
   transport (_< 0ᴿ) (negation-is-involutive x)
    (negation-of-positive-is-negative (-ᴿ x) l)

  positive-times-negative-is-negative : (x y : R) → 0ᴿ < x → y < 0ᴿ
                                      → x ·ᴿ y < 0ᴿ
  positive-times-negative-is-negative x y p n =
   positive-from-negation (x ·ᴿ y)
    (transport (0ᴿ <_) (·-negation-right x y)
      (products-of-positives-are-positive x (-ᴿ y) p
        (negation-of-negative-is-positive y n)))

  negative-times-negative-is-positive : (x y : R) → x < 0ᴿ → y < 0ᴿ
                                      → 0ᴿ < x ·ᴿ y
  negative-times-negative-is-positive x y n m =
   transport (0ᴿ <_) (·-negation-both x y)
    (products-of-positives-are-positive (-ᴿ x) (-ᴿ y)
      (negation-of-negative-is-positive x n)
       (negation-of-negative-is-positive y m))

  nonzero-squares-are-positive : (x : R) → x ≠ 0ᴿ → 0ᴿ < x ·ᴿ x
  nonzero-squares-are-positive x ν =
   ∥∥-rec (<-is-prop-valued 0ᴿ (x ·ᴿ x))
    (cases (λ n → negative-times-negative-is-positive x x n n)
           (λ p → products-of-positives-are-positive x x p p))
    (nonzero-elements-are-comparable x ν)

  squares-are-not-negative : (x : R) → ¬ (x ·ᴿ x < 0ᴿ)
  squares-are-not-negative x l =
   <-is-asymmetric _ _ l (nonzero-squares-are-positive x ν)
   where
    ν : x ≠ 0ᴿ
    ν p =
     <-is-irreflexive 0ᴿ (transport (_< 0ᴿ) (ap (λ - → - ·ᴿ -) p ∙ ·-zero 0ᴿ) l)

  nonzero-from-positive-product : (x y : R) → 0ᴿ < x ·ᴿ y → x ≠ 0ᴿ
  nonzero-from-positive-product x y l p =
   <-is-irreflexive 0ᴿ
    (transport (0ᴿ <_) (ap (_·ᴿ y) p ∙ ·-comm 0ᴿ y ∙ ·-zero y) l)

  two-is-positive : 0ᴿ < 1ᴿ +ᴿ 1ᴿ
  two-is-positive =
   sums-of-positives-are-positive 1ᴿ 1ᴿ one-is-positive one-is-positive

\end{code}

Inverses of positive elements, under Postulate K.

\begin{code}

  module _ (K : Postulate-K) where

   being-invertible-is-prop : (x : R) → is-prop (is-invertible x)
   being-invertible-is-prop x (u , p) (v , q) = to-subtype-＝ (λ _ → R-is-set) γ
    where
     γ : u ＝ v
     γ = u                    ＝⟨ (·-unit u)⁻¹ ⟩
         u ·ᴿ 1ᴿ              ＝⟨ ap (u ·ᴿ_) (q ⁻¹ ∙ ·-comm v x) ⟩
         u ·ᴿ (x ·ᴿ v)        ＝⟨ (·-assoc u x v)⁻¹ ⟩
         (u ·ᴿ x) ·ᴿ v        ＝⟨ ap (_·ᴿ v) p ⟩
         1ᴿ ·ᴿ v              ＝⟨ ·-unit-left v ⟩
         v                    ∎

   positive-elements-are-invertible : (x : R) → 0ᴿ < x → is-invertible x
   positive-elements-are-invertible x l =
    ∥∥-rec (being-invertible-is-prop x) id
     (nonzero-elements-are-invertible K x (positive-elements-are-nonzero x l))

   inverses-of-positive-elements-are-positive
    : (x : R) (l : 0ᴿ < x) → 0ᴿ < pr₁ (positive-elements-are-invertible x l)
   inverses-of-positive-elements-are-positive x l =
    ∥∥-rec (<-is-prop-valued 0ᴿ u)
     (cases (λ (n : u < 0ᴿ) →
              𝟘-elim (<-is-asymmetric _ _
                       (transport (_< 0ᴿ) p
                         (transport (_< 0ᴿ) (·-comm x u)
                           (positive-times-negative-is-negative x u l n)))
                       one-is-positive))
            id)
     (nonzero-elements-are-comparable u ν)
    where
     u = pr₁ (positive-elements-are-invertible x l)
     p : u ·ᴿ x ＝ 1ᴿ
     p = pr₂ (positive-elements-are-invertible x l)
     ν : u ≠ 0ᴿ
     ν q = zero-is-not-one ((·-comm 0ᴿ x ∙ ·-zero x)⁻¹ ∙ ap (_·ᴿ x) (q ⁻¹) ∙ p)

\end{code}

A positive element below two given ones, and one with a small square.

\begin{code}

   positive-below-two : (a b : R) → 0ᴿ < a → 0ᴿ < b
                      → Σ c ꞉ R , (0ᴿ < c) × (c < a) × (c < b)
   positive-below-two a b la lb = c , c-is-positive , c<a , c<b
    where
     s = a +ᴿ b
     ls : 0ᴿ < s
     ls = sums-of-positives-are-positive a b la lb
     w = pr₁ (positive-elements-are-invertible s ls)
     ws : w ·ᴿ s ＝ 1ᴿ
     ws = pr₂ (positive-elements-are-invertible s ls)
     lw : 0ᴿ < w
     lw = inverses-of-positive-elements-are-positive s ls
     c = (a ·ᴿ b) ·ᴿ w
     c-is-positive : 0ᴿ < c
     c-is-positive = products-of-positives-are-positive _ _
                      (products-of-positives-are-positive a b la lb) lw
     cancel : (z : R) → (z ·ᴿ s) ·ᴿ w ＝ z
     cancel z = ·-assoc z s w ∙ ap (z ·ᴿ_) (·-comm s w ∙ ws) ∙ ·-unit z
     c<a : c < a
     c<a = transport (c <_) (cancel a)
            (products-with-positive-factor-preserve-order _ _ w lw
              (transport₂ _<_ (+-unit-left (a ·ᴿ b))
                              ((ap (_+ᴿ (a ·ᴿ b)) refl)
                               ∙ (distributivity a a b)⁻¹)
                (translation 0ᴿ (a ·ᴿ a) (a ·ᴿ b)
                  (products-of-positives-are-positive a a la la))))
     c<b : c < b
     c<b = transport (c <_) (cancel b)
            (products-with-positive-factor-preserve-order _ _ w lw
              (transport₂ _<_ (+-unit-left (a ·ᴿ b))
                              (+-comm (b ·ᴿ b) (a ·ᴿ b)
                               ∙ ap (_+ᴿ (b ·ᴿ b)) (·-comm a b)
                               ∙ (distributivity b a b)⁻¹)
                (translation 0ᴿ (b ·ᴿ b) (a ·ᴿ b)
                  (products-of-positives-are-positive b b lb lb))))

   positive-with-small-square : (c : R) → 0ᴿ < c
                              → Σ δ ꞉ R , (0ᴿ < δ) × (δ ·ᴿ δ < c)
   positive-with-small-square c lc = r , r-is-positive , square-below
    where
     β = positive-below-two 1ᴿ c one-is-positive lc
     r = pr₁ β
     r-is-positive = pr₁ (pr₂ β)
     square-below : r ·ᴿ r < c
     square-below = <-is-transitive _ _ _
                     (transport (r ·ᴿ r <_) (·-unit-left r)
                       (products-with-positive-factor-preserve-order r 1ᴿ r
                         r-is-positive (pr₁ (pr₂ (pr₂ β)))))
                     (pr₂ (pr₂ (pr₂ β)))

\end{code}

Intervals and squares.

\begin{code}

  interval-from-square : (ε a : R) → 0ᴿ < ε → a ·ᴿ a < ε ·ᴿ ε
                       → (-ᴿ ε < a) × (a < ε)
  interval-from-square ε a lε l = left , right
   where
    product-is-positive : 0ᴿ < (ε +ᴿ (-ᴿ a)) ·ᴿ (ε +ᴿ a)
    product-is-positive = transport (0ᴿ <_) ((difference-of-squares ε a)⁻¹)
                           (difference-is-positive (a ·ᴿ a) (ε ·ᴿ ε) l)

    sum-is-positive : 0ᴿ < (ε +ᴿ (-ᴿ a)) +ᴿ (ε +ᴿ a)
    sum-is-positive = transport (0ᴿ <_)
                       ((+-interchange ε (-ᴿ a) ε a
                         ∙ ap ((ε +ᴿ ε) +ᴿ_) (+-inverse-left a)
                         ∙ +-unit (ε +ᴿ ε))⁻¹
                        ∙ refl)
                       (sums-of-positives-are-positive ε ε lε lε)

    both-positive : (0ᴿ < ε +ᴿ (-ᴿ a)) × (0ᴿ < ε +ᴿ a)
    both-positive =
     ∥∥-rec (×-is-prop (<-is-prop-valued _ _) (<-is-prop-valued _ _))
      (cases first-negative first-positive)
      (nonzero-elements-are-comparable (ε +ᴿ (-ᴿ a))
        (nonzero-from-positive-product _ _ product-is-positive))
     where
      second-positive : 0ᴿ < ε +ᴿ (-ᴿ a) → 0ᴿ < ε +ᴿ a
      second-positive p =
       ∥∥-rec (<-is-prop-valued _ _)
        (cases (λ n → 𝟘-elim (<-is-asymmetric _ _ product-is-positive
                                (positive-times-negative-is-negative _ _ p n)))
               id)
        (nonzero-elements-are-comparable (ε +ᴿ a)
          (nonzero-from-positive-product _ _
            (transport (0ᴿ <_) (·-comm (ε +ᴿ (-ᴿ a)) (ε +ᴿ a))
              product-is-positive)))

      first-positive : 0ᴿ < ε +ᴿ (-ᴿ a)
                     → (0ᴿ < ε +ᴿ (-ᴿ a)) × (0ᴿ < ε +ᴿ a)
      first-positive p = p , second-positive p

      first-negative : ε +ᴿ (-ᴿ a) < 0ᴿ
                     → (0ᴿ < ε +ᴿ (-ᴿ a)) × (0ᴿ < ε +ᴿ a)
      first-negative n =
       ∥∥-rec (×-is-prop (<-is-prop-valued _ _) (<-is-prop-valued _ _))
        (cases (λ m → 𝟘-elim (<-is-asymmetric _ _ sum-is-positive
                                (transport ((ε +ᴿ (-ᴿ a)) +ᴿ (ε +ᴿ a) <_)
                                  (+-unit 0ᴿ)
                                  (<-adds _ 0ᴿ _ 0ᴿ n m))))
               (λ q → 𝟘-elim (<-is-asymmetric _ _ product-is-positive
                                (transport (_< 0ᴿ)
                                  (·-comm (ε +ᴿ a) (ε +ᴿ (-ᴿ a)))
                                  (positive-times-negative-is-negative _ _ q
                                    n)))))
        (nonzero-elements-are-comparable (ε +ᴿ a)
          (nonzero-from-positive-product _ _
            (transport (0ᴿ <_) (·-comm (ε +ᴿ (-ᴿ a)) (ε +ᴿ a))
              product-is-positive)))

    right : a < ε
    right = positive-difference a ε (pr₁ both-positive)

    left : -ᴿ ε < a
    left = positive-difference (-ᴿ ε) a
            (transport (0ᴿ <_)
              (+-comm ε a ∙ ap (a +ᴿ_) ((negation-is-involutive ε)⁻¹))
              (pr₂ both-positive))

  square-from-interval : (δ a : R) → -ᴿ δ < a → a < δ → a ·ᴿ a < δ ·ᴿ δ
  square-from-interval δ a l m =
   positive-difference (a ·ᴿ a) (δ ·ᴿ δ)
    (transport (0ᴿ <_) (difference-of-squares δ a)
      (products-of-positives-are-positive _ _
        (difference-is-positive a δ m)
        (transport (0ᴿ <_) (ap (a +ᴿ_) (negation-is-involutive δ) ∙ +-comm a δ)
          (difference-is-positive (-ᴿ δ) a l))))

\end{code}
