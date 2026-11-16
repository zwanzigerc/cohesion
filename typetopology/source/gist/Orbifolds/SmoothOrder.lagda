Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026 (local time). Orbifold gate H9 of Fable's
roadmap [1], following Fable's corrected guidance [2] and GPT-6
Astra's audit of it [3].

The order of the smooth line
----------------------------

Myers's Postulate O [4, Axiom 3, p. 30] says that the smooth line R is
strictly ordered: there is a binary relation < on R with

  O.1  1 > 0, and if x > 0 and y > 0, then x + y > 0 and xy > 0;
  O.2  it is never the case that x > x;
  O.3  if x > y, then either x > z or z > y, for any z;
  O.4  if x ≠ 0, then x < 0 or x > 0;
  O.5  (Archimedean law) for any x : R there is an n : ℕ with x < n.

Postulate-O states these exactly as printed, with "either … or" and
"there is" read as truncated disjunction and existence, and the
relation proposition-valued. It does not say that the order is
compatible with addition. That law, x < y → x + z < y + z, comes from
Myers's Postulate Exp [4, p. 30], which calls exp an isomorphism of
ordered groups from the additive group of R, with this same order, to
the multiplicative group of positive reals [2, Section 1, item 1; 3,
Section 1]. Postulate-Exp states Exp with both ordered-group
structures and the isomorphism; translation-law-from-Exp exports the
fragment that is used, the ordered-group law of the additive group. The
functions exp and log themselves are not used here or in T1; they are
used once, for T5a, to take square roots of positive elements
(SmoothLineGroupoid, the order defined by the ring). Lemmas below
take the translation law as an explicit premise, and final theorems
supply it from Exp.

Under O and the translation law: < is transitive and asymmetric
(<-is-transitive, <-is-asymmetric), x < y exactly when 0 < y − x, the
order reverses under negation, ≤ (defined as the negation of >) mixes
with < as expected, positive elements are nonzero, and 0 ≠ 1.

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

module gist.Orbifolds.SmoothOrder where

open import UF.Base
open import UF.Subsingletons
open import gist.Orbifolds.SmoothLine

module smooth-order
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
        (𝓡 : Commutative-Ring)
       where

 open PropositionalTruncation pt
 open smooth-line fe pt 𝓡

\end{code}

The natural numbers in R, and Postulate O.

\begin{code}

 ι : ℕ → R
 ι 0        = 0ᴿ
 ι (succ n) = ι n +ᴿ 1ᴿ

 record Postulate-O : 𝓤₁ ̇ where
  field
   _<_ : R → R → 𝓤₀ ̇
   <-is-prop-valued : (x y : R) → is-prop (x < y)
   one-is-positive : 0ᴿ < 1ᴿ
   sums-of-positives-are-positive : (x y : R) → 0ᴿ < x → 0ᴿ < y → 0ᴿ < x +ᴿ y
   products-of-positives-are-positive : (x y : R) → 0ᴿ < x → 0ᴿ < y
                                      → 0ᴿ < x ·ᴿ y
   <-is-irreflexive : (x : R) → ¬ (x < x)
   <-is-cotransitive : (x y z : R) → y < x → (z < x) ∨ (y < z)
   nonzero-elements-are-comparable : (x : R) → x ≠ 0ᴿ → (x < 0ᴿ) ∨ (0ᴿ < x)
   archimedean : (x : R) → ∃ n ꞉ ℕ , x < ι n

  infix 4 _<_

\end{code}

Postulate Exp, with its ordered-group structures, and the translation
law that it gives.

\begin{code}

 module _ (O : Postulate-O) where

  open Postulate-O O

  Translation-Law : 𝓤₀ ̇
  Translation-Law = (x y z : R) → x < y → x +ᴿ z < y +ᴿ z

  record Postulate-Exp : 𝓤₀ ̇ where
   field
    additive-group-is-ordered : Translation-Law
    positive-group-is-ordered : (x y z : R) → 0ᴿ < x → 0ᴿ < y → 0ᴿ < z
                              → x < y → x ·ᴿ z < y ·ᴿ z
    exp : R → R
    exp-is-positive : (x : R) → 0ᴿ < exp x
    log : (y : R) → 0ᴿ < y → R
    log-exp : (x : R) → log (exp x) (exp-is-positive x) ＝ x
    exp-log : (y : R) (p : 0ᴿ < y) → exp (log y p) ＝ y
    exp-is-homomorphism : (x y : R) → exp (x +ᴿ y) ＝ exp x ·ᴿ exp y
    exp-preserves-order : (x y : R) → x < y → exp x < exp y
    exp-reflects-order : (x y : R) → exp x < exp y → x < y

  translation-law-from-Exp : Postulate-Exp → Translation-Law
  translation-law-from-Exp = Postulate-Exp.additive-group-is-ordered

\end{code}

Ring identities used below.

\begin{code}

 +-inverse-left : (x : R) → (-ᴿ x) +ᴿ x ＝ 0ᴿ
 +-inverse-left x = +-comm (-ᴿ x) x ∙ +-inverse x

 +-cancel : (x y : R) → (y +ᴿ (-ᴿ x)) +ᴿ x ＝ y
 +-cancel x y = +-assoc y (-ᴿ x) x ∙ ap (y +ᴿ_) (+-inverse-left x) ∙ +-unit y

 +-cancel' : (x y : R) → (y +ᴿ x) +ᴿ (-ᴿ x) ＝ y
 +-cancel' x y = +-assoc y x (-ᴿ x) ∙ ap (y +ᴿ_) (+-inverse x) ∙ +-unit y

 differences-compose : (x y z : R)
                     → (z +ᴿ (-ᴿ y)) +ᴿ (y +ᴿ (-ᴿ x)) ＝ z +ᴿ (-ᴿ x)
 differences-compose x y z =
  +-assoc z (-ᴿ y) (y +ᴿ (-ᴿ x))
  ∙ ap (z +ᴿ_) ((+-assoc (-ᴿ y) y (-ᴿ x))⁻¹
                ∙ ap (_+ᴿ (-ᴿ x)) (+-inverse-left y)
                ∙ +-unit-left (-ᴿ x))

\end{code}

Consequences of O and the translation law.

\begin{code}

 module order-lemmas (O : Postulate-O) (translation : Translation-Law O) where

  open Postulate-O O

  _>_ : R → R → 𝓤₀ ̇
  x > y = y < x

  _≤_ : R → R → 𝓤₀ ̇
  x ≤ y = ¬ (y < x)

  infix 4 _>_
  infix 4 _≤_

  difference-is-positive : (x y : R) → x < y → 0ᴿ < y +ᴿ (-ᴿ x)
  difference-is-positive x y l =
   transport (_< y +ᴿ (-ᴿ x)) (+-inverse x) (translation x y (-ᴿ x) l)

  positive-difference : (x y : R) → 0ᴿ < y +ᴿ (-ᴿ x) → x < y
  positive-difference x y l =
   transport₂ _<_ (+-unit-left x) (+-cancel x y)
    (translation 0ᴿ (y +ᴿ (-ᴿ x)) x l)

  <-is-transitive : (x y z : R) → x < y → y < z → x < z
  <-is-transitive x y z l m =
   positive-difference x z
    (transport (0ᴿ <_) (differences-compose x y z)
      (sums-of-positives-are-positive _ _ (difference-is-positive y z m)
                                          (difference-is-positive x y l)))

  <-is-asymmetric : (x y : R) → x < y → ¬ (y < x)
  <-is-asymmetric x y l m = <-is-irreflexive x (<-is-transitive x y x l m)

  ≤-<-is-transitive : (x y z : R) → x ≤ y → y < z → x < z
  ≤-<-is-transitive x y z a l =
   ∥∥-rec (<-is-prop-valued x z)
    (cases id (λ (y<x : y < x) → 𝟘-elim (a y<x)))
    (<-is-cotransitive z y x l)

  <-≤-is-transitive : (x y z : R) → x < y → y ≤ z → x < z
  <-≤-is-transitive x y z l a =
   ∥∥-rec (<-is-prop-valued x z)
    (cases (λ (z<y : z < y) → 𝟘-elim (a z<y)) id)
    (<-is-cotransitive y x z l)

  <-gives-≤ : (x y : R) → x < y → x ≤ y
  <-gives-≤ x y l m = <-is-asymmetric x y l m

  positive-elements-are-nonzero : (x : R) → 0ᴿ < x → x ≠ 0ᴿ
  positive-elements-are-nonzero x l p =
   <-is-irreflexive 0ᴿ (transport (0ᴿ <_) p l)

  zero-is-not-one : 0ᴿ ≠ 1ᴿ
  zero-is-not-one p =
   <-is-irreflexive 0ᴿ (transport (0ᴿ <_) (p ⁻¹) one-is-positive)

  negation-reverses-order : (x y : R) → x < y → (-ᴿ y) < (-ᴿ x)
  negation-reverses-order x y l =
   transport₂ _<_
    ((+-assoc x (-ᴿ x) (-ᴿ y))⁻¹ ∙ ap (_+ᴿ (-ᴿ y)) (+-inverse x)
     ∙ +-unit-left (-ᴿ y))
    (ap (y +ᴿ_) (+-comm (-ᴿ x) (-ᴿ y)) ∙ (+-assoc y (-ᴿ y) (-ᴿ x))⁻¹
     ∙ ap (_+ᴿ (-ᴿ x)) (+-inverse y) ∙ +-unit-left (-ᴿ x))
    (translation x y ((-ᴿ x) +ᴿ (-ᴿ y)) l)

\end{code}
