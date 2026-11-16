Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 13 November 2026 (local time), for gate WG4 of Claude Fable
5.2's plan for the comparison of Weil algebras with presentations [1],
as reviewed by GPT-6 Astra [2], amended by Fable's addendum 01 [3] and
released by Astra [4]. The exported names, and the universes and
hypotheses of their statements, are those of the plan's statement
companion; the proofs are Claude Opus 5.5's. See the AI disclosure in
gist.RealCohesion.index.

Finite sums and products in an algebra, and products in nilpotent ideals
------------------------------------------------------------------------

Everything here concerns one algebra 𝓐 over the ring 𝓡 of
gist.Orbifolds.SmoothLine, with carrier in an arbitrary universe 𝓦; no
presented algebra occurs.

  ∑ᴬ, ∏ᴬ : finite sums and products, by the recursion of SmoothLine.∑:
  the empty sum is 0 and the empty product 1, and a family on Fin (m + 1)
  is its tail, then its head. product-of-a-constant-family : a product
  of N copies of x is the N-th power of x.

  is-in-the-ideal-of x w : w is merely a combination ∑ x i · c i of the
  elements x i, which generate the ideal.

  constant-term-decomposition : the value of an expression p at a point
  y of 𝓐 is ι of the value of p at the origin of R plus an explicit
  combination of the y i. By induction on p, with explicit coefficients
  and no truncation: a variable has the coefficients of a Kronecker row,
  a constant has none, the coefficients of a sum add, and those of a
  product p ⊗ q are a · d i + c i · (b + T), when p takes the value
  a + S and q the value b + T. The additive form needs no subtraction.

  products-in-ideals-of-nilpotents-vanish : if the (k + 1)-st powers of
  the n elements x i vanish, then every product of k * n + 1 elements of
  their ideal vanishes, for an arbitrary family of such elements, not
  merely for the powers of one of them. The bound succ (k * n) is
  n · k + 1, with the multiplication of Naturals.Multiplication, which
  recurses on n. The proof is the monomial bound of the plan [1, Section
  5.1]; it uses neither a pigeonhole principle nor a binomial expansion,
  and it never chooses coefficients from a truncation.
    monomial x e and degree e are the product of the x i ^ e i and the sum
    of the exponents e i; bump i e raises the i-th exponent by one, by
    four exact clauses and no decidable equality. L1:
    monomial-of-bump and degree-of-bump. L2, some-exponent-is-large : an
    exponent vector of degree at least k * n + 1 has an actual index whose
    exponent is at least k + 1, found by deciding the order of ℕ. L3,
    monomials-with-a-large-exponent-vanish. in-power x j w : w lies merely
    in the j-th power of the ideal, as a combination ∑ x i · c i of
    elements c i of the (j - 1)-st; L4 : these powers are closed under
    multiplication by anything (in-power-is-closed-under-multiplication),
    and a product of N elements of the ideal lies in the N-th power
    (products-are-in-powers). L5,
    monomials-of-high-degree-annihilate-powers : if w lies in the j-th
    power and the degree of e plus j is at least k * n + 1, then
    monomial x e · w is 0, by induction on j, eliminating each truncated
    combination into this proposition. The theorem is L5 at the zero
    exponent vector and j = k * n + 1.
  The cases n = 0 and k = 0 need no clause of their own; both give the
  bound 1.

Helpers, exported in addition: ≤-right-cancellable, about ℕ; and, for an
algebra, interchangeᴬ, ·ᴬ-swap, ∑ᴬ-of-zeros, ∑ᴬ-pointwise, ∑ᴬ-additive,
∑ᴬ-scalar-left, ∑ᴬ-scalar-right, Kronecker-sumᴬ, monomial-of-zeros and
degree-of-zeros.

Assumptions: function extensionality and propositional truncations, as
in SmoothLine, and nothing else. No choice, quotient, univalence,
resizing, excluded middle or crisp datum is assumed, and the module adds
no option and no postulate. The decidability used is that of the order of
ℕ, which is proved.

[1] Claude Fable 5.2. Plan: formalizing the comparison of Weil algebras
    with presentations, 13 November 2026, Section 5.1, with its statement
    companion, Section WG4 (plan SHA-256 b1662ecc…; companion SHA-256
    47974af8…).
[2] GPT-6 Astra. Review of Fable's Weil plan, 13 November 2026
    (FABLE-WEIL-PLAN-REVIEW-01).
[3] Claude Fable 5.2. Addendum 01 to the plan, 13 November 2026
    (SHA-256 abf31923…).
[4] GPT-6 Astra. Release of gate WG4, 13 November 2026
    (SHA-256 0499a901…).

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import gist.Orbifolds.SmoothLine
 using (Commutative-Ring ; module smooth-line)

module gist.Orbifolds.NilpotentIdeals
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
        (𝓡 : Commutative-Ring)
       where

open import Fin.Type
open import Naturals.Addition
 using (succ-left ; zero-left-neutral ; addition-commutativity)
 renaming (_+_ to _+ᴺ_)
open import Naturals.Multiplication using (_*_)
open import Naturals.Order
 using (Order-ℕ-ℕ ; Strict-Order-ℕ-ℕ ; ≤-refl ; ≤-trans ; ≤-decidable ;
        ≤-n-monotone-left ; not-less-or-equal-is-bigger)
open import Notation.Order using (_≤_)
open import UF.Base
open import UF.Subsingletons

open PropositionalTruncation pt
open smooth-line fe pt 𝓡
open import gist.Orbifolds.Algebras fe pt 𝓡

≤-right-cancellable : (x y z : ℕ) → (x +ᴺ z) ≤ (y +ᴺ z) → x ≤ y
≤-right-cancellable x y 0        l = l
≤-right-cancellable x y (succ z) l = ≤-right-cancellable x y z l

module _ {𝓦 : Universe} (𝓐 : Algebra 𝓦) where

 open Algebra 𝓐

\end{code}

Finite sums and products.

\begin{code}

 ∑ᴬ : {m : ℕ} → (Fin m → A) → A
 ∑ᴬ {0}      g = 0ᴬ
 ∑ᴬ {succ m} g = ∑ᴬ (g ∘ suc) +ᴬ g 𝟎

 ∏ᴬ : {m : ℕ} → (Fin m → A) → A
 ∏ᴬ {0}      g = 1ᴬ
 ∏ᴬ {succ m} g = ∏ᴬ (g ∘ suc) ·ᴬ g 𝟎

 product-of-a-constant-family
  : (x : A) (N : ℕ) → ∏ᴬ {N} (λ _ → x) ＝ _^ᴬ_ 𝓐 x N
 product-of-a-constant-family x 0        = refl
 product-of-a-constant-family x (succ N) =
  ap (_·ᴬ x) (product-of-a-constant-family x N)

 interchangeᴬ : (a b c d : A) → (a +ᴬ b) +ᴬ (c +ᴬ d) ＝ (a +ᴬ c) +ᴬ (b +ᴬ d)
 interchangeᴬ a b c d =
  +ᴬ-assoc a b (c +ᴬ d)
  ∙ ap (a +ᴬ_) ((+ᴬ-assoc b c d)⁻¹
                ∙ ap (_+ᴬ d) (+ᴬ-comm b c)
                ∙ +ᴬ-assoc c b d)
  ∙ (+ᴬ-assoc a c (b +ᴬ d))⁻¹

 ·ᴬ-swap : (a b c : A) → a ·ᴬ (b ·ᴬ c) ＝ b ·ᴬ (a ·ᴬ c)
 ·ᴬ-swap a b c =
  (·ᴬ-assoc a b c)⁻¹ ∙ ap (_·ᴬ c) (·ᴬ-comm a b) ∙ ·ᴬ-assoc b a c

 ∑ᴬ-of-zeros : {m : ℕ} (g : Fin m → A) → ((i : Fin m) → g i ＝ 0ᴬ) → ∑ᴬ g ＝ 0ᴬ
 ∑ᴬ-of-zeros {0}      g z = refl
 ∑ᴬ-of-zeros {succ m} g z =
  ap₂ _+ᴬ_ (∑ᴬ-of-zeros (g ∘ suc) (z ∘ suc)) (z 𝟎) ∙ +ᴬ-unit 0ᴬ

 ∑ᴬ-pointwise : {m : ℕ} (g g' : Fin m → A) → g ∼ g' → ∑ᴬ g ＝ ∑ᴬ g'
 ∑ᴬ-pointwise g g' H = ap ∑ᴬ (dfunext fe H)

 ∑ᴬ-additive
  : {m : ℕ} (f g : Fin m → A) → ∑ᴬ (λ i → f i +ᴬ g i) ＝ ∑ᴬ f +ᴬ ∑ᴬ g
 ∑ᴬ-additive {0}      f g = (+ᴬ-unit 0ᴬ)⁻¹
 ∑ᴬ-additive {succ m} f g =
  ap (_+ᴬ (f 𝟎 +ᴬ g 𝟎)) (∑ᴬ-additive (f ∘ suc) (g ∘ suc))
  ∙ interchangeᴬ (∑ᴬ (f ∘ suc)) (∑ᴬ (g ∘ suc)) (f 𝟎) (g 𝟎)

 ∑ᴬ-scalar-left
  : {m : ℕ} (a : A) (f : Fin m → A) → ∑ᴬ (λ i → a ·ᴬ f i) ＝ a ·ᴬ ∑ᴬ f
 ∑ᴬ-scalar-left {0}      a f = (·ᴬ-zero 𝓐 a)⁻¹
 ∑ᴬ-scalar-left {succ m} a f =
  ap (_+ᴬ (a ·ᴬ f 𝟎)) (∑ᴬ-scalar-left a (f ∘ suc))
  ∙ (distributivityᴬ a (∑ᴬ (f ∘ suc)) (f 𝟎))⁻¹

 ∑ᴬ-scalar-right
  : {m : ℕ} (f : Fin m → A) (a : A) → ∑ᴬ (λ i → f i ·ᴬ a) ＝ ∑ᴬ f ·ᴬ a
 ∑ᴬ-scalar-right {0}      f a = (·ᴬ-zero-left 𝓐 a)⁻¹
 ∑ᴬ-scalar-right {succ m} f a =
  ap (_+ᴬ (f 𝟎 ·ᴬ a)) (∑ᴬ-scalar-right (f ∘ suc) a)
  ∙ (distributivityᴬ-right 𝓐 (∑ᴬ (f ∘ suc)) (f 𝟎) a)⁻¹

 Kronecker-sumᴬ
  : {n : ℕ} (i : Fin n) (g : Fin n → A) → ∑ᴬ (λ j → g j ·ᴬ ι (δ i j)) ＝ g i
 Kronecker-sumᴬ {0}      ()      g
 Kronecker-sumᴬ {succ n} (suc i) g =
  ap₂ _+ᴬ_ (Kronecker-sumᴬ i (g ∘ suc))
           (ap (g 𝟎 ·ᴬ_) (ι-preserves-0 𝓐) ∙ ·ᴬ-zero 𝓐 (g 𝟎))
  ∙ +ᴬ-unit (g (suc i))
 Kronecker-sumᴬ {succ n} 𝟎       g =
  ap₂ _+ᴬ_ (∑ᴬ-of-zeros (λ j → g (suc j) ·ᴬ ι (δ 𝟎 (suc j)))
              (λ j → ap (g (suc j) ·ᴬ_) (ι-preserves-0 𝓐)
                   ∙ ·ᴬ-zero 𝓐 (g (suc j))))
           (ap (g 𝟎 ·ᴬ_) ι-preserves-1 ∙ ·ᴬ-unit (g 𝟎))
  ∙ +ᴬ-unit-left 𝓐 (g 𝟎)

\end{code}

Ideals, and the decomposition of a value into its constant term and a
combination of the coordinates.

\begin{code}

 is-in-the-ideal-of : {n : ℕ} → (Fin n → A) → A → 𝓦 ̇
 is-in-the-ideal-of {n} x w = ∃ c ꞉ (Fin n → A) , w ＝ ∑ᴬ (λ i → x i ·ᴬ c i)

 constant-term-decomposition
  : {n : ℕ} (y : Fin n → A) (p : Poly n)
  → Σ c ꞉ (Fin n → A) ,
    ⟦ p ⟧[ 𝓐 ] y ＝ ι (⟦ p ⟧ (λ _ → 0ᴿ)) +ᴬ ∑ᴬ (λ i → y i ·ᴬ c i)
 constant-term-decomposition y (var i) =
  (λ j → ι (δ i j)) ,
  ((Kronecker-sumᴬ i y)⁻¹
   ∙ (+ᴬ-unit-left 𝓐 (∑ᴬ (λ j → y j ·ᴬ ι (δ i j))))⁻¹
   ∙ ap (_+ᴬ ∑ᴬ (λ j → y j ·ᴬ ι (δ i j))) ((ι-preserves-0 𝓐)⁻¹))
 constant-term-decomposition y (con r) =
  (λ _ → 0ᴬ) ,
  ((+ᴬ-unit (ι r))⁻¹
   ∙ ap (ι r +ᴬ_) ((∑ᴬ-of-zeros (λ i → y i ·ᴬ 0ᴬ) (λ i → ·ᴬ-zero 𝓐 (y i)))⁻¹))
 constant-term-decomposition {n} y (p ⊕ q) =
  (λ i → c i +ᴬ d i) ,
  (ap₂ _+ᴬ_ e e'
   ∙ interchangeᴬ (ι a) S (ι b) T
   ∙ ap₂ _+ᴬ_ ((ι-preserves-+ a b)⁻¹)
              ((∑ᴬ-additive (λ i → y i ·ᴬ c i) (λ i → y i ·ᴬ d i))⁻¹
               ∙ ∑ᴬ-pointwise (λ i → (y i ·ᴬ c i) +ᴬ (y i ·ᴬ d i))
                              (λ i → y i ·ᴬ (c i +ᴬ d i))
                              (λ i → (distributivityᴬ (y i) (c i) (d i))⁻¹)))
  where
   a b : R
   a = ⟦ p ⟧ (λ _ → 0ᴿ)
   b = ⟦ q ⟧ (λ _ → 0ᴿ)

   c d : Fin n → A
   c = pr₁ (constant-term-decomposition y p)
   d = pr₁ (constant-term-decomposition y q)

   S T : A
   S = ∑ᴬ (λ i → y i ·ᴬ c i)
   T = ∑ᴬ (λ i → y i ·ᴬ d i)

   e : ⟦ p ⟧[ 𝓐 ] y ＝ ι a +ᴬ S
   e = pr₂ (constant-term-decomposition y p)

   e' : ⟦ q ⟧[ 𝓐 ] y ＝ ι b +ᴬ T
   e' = pr₂ (constant-term-decomposition y q)
 constant-term-decomposition {n} y (p ⊗ q) =
  h ,
  (ap₂ _·ᴬ_ e e'
   ∙ distributivityᴬ-right 𝓐 (ι a) S U
   ∙ ap (_+ᴬ (S ·ᴬ U)) (distributivityᴬ (ι a) (ι b) T)
   ∙ +ᴬ-assoc (ι a ·ᴬ ι b) (ι a ·ᴬ T) (S ·ᴬ U)
   ∙ ap₂ _+ᴬ_ ((ι-preserves-· a b)⁻¹) (sum-part ⁻¹))
  where
   a b : R
   a = ⟦ p ⟧ (λ _ → 0ᴿ)
   b = ⟦ q ⟧ (λ _ → 0ᴿ)

   c d : Fin n → A
   c = pr₁ (constant-term-decomposition y p)
   d = pr₁ (constant-term-decomposition y q)

   S T U : A
   S = ∑ᴬ (λ i → y i ·ᴬ c i)
   T = ∑ᴬ (λ i → y i ·ᴬ d i)
   U = ι b +ᴬ T

   e : ⟦ p ⟧[ 𝓐 ] y ＝ ι a +ᴬ S
   e = pr₂ (constant-term-decomposition y p)

   e' : ⟦ q ⟧[ 𝓐 ] y ＝ U
   e' = pr₂ (constant-term-decomposition y q)

   h : Fin n → A
   h i = (ι a ·ᴬ d i) +ᴬ (c i ·ᴬ U)

   γ : (i : Fin n) → y i ·ᴬ h i ＝ (ι a ·ᴬ (y i ·ᴬ d i)) +ᴬ ((y i ·ᴬ c i) ·ᴬ U)
   γ i = distributivityᴬ (y i) (ι a ·ᴬ d i) (c i ·ᴬ U)
       ∙ ap₂ _+ᴬ_ (·ᴬ-swap (y i) (ι a) (d i)) ((·ᴬ-assoc (y i) (c i) U)⁻¹)

   sum-part : ∑ᴬ (λ i → y i ·ᴬ h i) ＝ (ι a ·ᴬ T) +ᴬ (S ·ᴬ U)
   sum-part =
    ∑ᴬ-pointwise (λ i → y i ·ᴬ h i)
                 (λ i → (ι a ·ᴬ (y i ·ᴬ d i)) +ᴬ ((y i ·ᴬ c i) ·ᴬ U)) γ
    ∙ ∑ᴬ-additive (λ i → ι a ·ᴬ (y i ·ᴬ d i)) (λ i → (y i ·ᴬ c i) ·ᴬ U)
    ∙ ap₂ _+ᴬ_ (∑ᴬ-scalar-left (ι a) (λ i → y i ·ᴬ d i))
               (∑ᴬ-scalar-right (λ i → y i ·ᴬ c i) U)

\end{code}

The monomial bound.

\begin{code}

 monomial : {n : ℕ} → (Fin n → A) → (Fin n → ℕ) → A
 monomial {0}      x e = 1ᴬ
 monomial {succ n} x e = monomial (x ∘ suc) (e ∘ suc) ·ᴬ (_^ᴬ_ 𝓐 (x 𝟎) (e 𝟎))

 degree : {n : ℕ} → (Fin n → ℕ) → ℕ
 degree {0}      e = 0
 degree {succ n} e = degree (e ∘ suc) +ᴺ e 𝟎

 bump : {n : ℕ} → Fin n → (Fin n → ℕ) → (Fin n → ℕ)
 bump {0}      ()
 bump {succ n} 𝟎       e 𝟎       = succ (e 𝟎)
 bump {succ n} 𝟎       e (suc j) = e (suc j)
 bump {succ n} (suc i) e 𝟎       = e 𝟎
 bump {succ n} (suc i) e (suc j) = bump i (e ∘ suc) j

 monomial-of-zeros : {n : ℕ} (x : Fin n → A) → monomial x (λ _ → 0) ＝ 1ᴬ
 monomial-of-zeros {0}      x = refl
 monomial-of-zeros {succ n} x =
  ap (_·ᴬ 1ᴬ) (monomial-of-zeros (x ∘ suc)) ∙ ·ᴬ-unit 1ᴬ

 degree-of-zeros : (n : ℕ) → degree {n} (λ _ → 0) ＝ 0
 degree-of-zeros 0        = refl
 degree-of-zeros (succ n) = degree-of-zeros n

 monomial-of-bump
  : {n : ℕ} (x : Fin n → A) (i : Fin n) (e : Fin n → ℕ)
  → monomial x (bump i e) ＝ monomial x e ·ᴬ x i
 monomial-of-bump {0}      x ()      e
 monomial-of-bump {succ n} x 𝟎       e =
  (·ᴬ-assoc (monomial (x ∘ suc) (e ∘ suc)) (_^ᴬ_ 𝓐 (x 𝟎) (e 𝟎)) (x 𝟎))⁻¹
 monomial-of-bump {succ n} x (suc i) e =
  ap (_·ᴬ P) (monomial-of-bump (x ∘ suc) i (e ∘ suc))
  ∙ ·ᴬ-assoc M (x (suc i)) P
  ∙ ap (M ·ᴬ_) (·ᴬ-comm (x (suc i)) P)
  ∙ (·ᴬ-assoc M P (x (suc i)))⁻¹
  where
   M P : A
   M = monomial (x ∘ suc) (e ∘ suc)
   P = _^ᴬ_ 𝓐 (x 𝟎) (e 𝟎)

 degree-of-bump
  : {n : ℕ} (i : Fin n) (e : Fin n → ℕ) → degree (bump i e) ＝ succ (degree e)
 degree-of-bump {0}      ()      e
 degree-of-bump {succ n} 𝟎       e = refl
 degree-of-bump {succ n} (suc i) e =
  ap (_+ᴺ e 𝟎) (degree-of-bump i (e ∘ suc)) ∙ succ-left (degree (e ∘ suc)) (e 𝟎)

 some-exponent-is-large
  : {n : ℕ} (k : ℕ) (e : Fin n → ℕ)
  → succ (k * n) ≤ degree e → Σ i ꞉ Fin n , succ k ≤ e i
 some-exponent-is-large {0}      k e l = 𝟘-elim l
 some-exponent-is-large {succ n} k e l =
  Cases (≤-decidable (succ k) (e 𝟎))
   (λ (m : succ k ≤ e 𝟎) → 𝟎 , m)
   (λ (ν : ¬ (succ k ≤ e 𝟎))
         → γ (some-exponent-is-large {n} k (e ∘ suc) (bound ν)))
  where
   γ : (Σ i ꞉ Fin n , succ k ≤ e (suc i)) → Σ i ꞉ Fin (succ n) , succ k ≤ e i
   γ (i , m) = suc i , m

   bound : ¬ (succ k ≤ e 𝟎) → succ (k * n) ≤ degree (e ∘ suc)
   bound ν = ≤-right-cancellable (succ (k * n)) (degree (e ∘ suc)) k
              (transport (λ - → - ≤ (degree (e ∘ suc) +ᴺ k)) p
                (≤-trans (succ (k +ᴺ k * n))
                         (degree (e ∘ suc) +ᴺ e 𝟎)
                         (degree (e ∘ suc) +ᴺ k)
                         l
                         (≤-n-monotone-left (e 𝟎) k (degree (e ∘ suc))
                           (not-less-or-equal-is-bigger (succ k) (e 𝟎) ν))))
    where
     p : succ (k +ᴺ k * n) ＝ succ (k * n) +ᴺ k
     p = ap succ (addition-commutativity k (k * n)) ∙ (succ-left (k * n) k)⁻¹

 monomials-with-a-large-exponent-vanish
  : {n : ℕ} (x : Fin n → A) (k : ℕ)
  → ((i : Fin n) → _^ᴬ_ 𝓐 (x i) (succ k) ＝ 0ᴬ)
  → (e : Fin n → ℕ) (i : Fin n) → succ k ≤ e i → monomial x e ＝ 0ᴬ
 monomials-with-a-large-exponent-vanish {0}      x k ν e ()      l
 monomials-with-a-large-exponent-vanish {succ n} x k ν e 𝟎       l =
  ap (monomial (x ∘ suc) (e ∘ suc) ·ᴬ_)
     (powers-vanish-from-an-exponent-on 𝓐 (x 𝟎) (succ k) (e 𝟎) (ν 𝟎) l)
  ∙ ·ᴬ-zero 𝓐 (monomial (x ∘ suc) (e ∘ suc))
 monomials-with-a-large-exponent-vanish {succ n} x k ν e (suc i) l =
  ap (λ - → - ·ᴬ _^ᴬ_ 𝓐 (x 𝟎) (e 𝟎))
     (monomials-with-a-large-exponent-vanish (x ∘ suc) k (ν ∘ suc) (e ∘ suc)
       i l)
  ∙ ·ᴬ-zero-left 𝓐 (_^ᴬ_ 𝓐 (x 𝟎) (e 𝟎))

 module _ {n : ℕ} (x : Fin n → A) where

  in-power : ℕ → A → 𝓦 ̇
  in-power 0        w = 𝟙
  in-power (succ j) w = ∃ c ꞉ (Fin n → A) ,
                          ((i : Fin n) → in-power j (c i))
                        × (w ＝ ∑ᴬ (λ i → x i ·ᴬ c i))

  in-power-is-closed-under-multiplication
   : (j : ℕ) (w d : A) → in-power j w → in-power j (w ·ᴬ d)
  in-power-is-closed-under-multiplication 0        w d _ = ⋆
  in-power-is-closed-under-multiplication (succ j) w d = ∥∥-functor γ
   where
    γ : (Σ c ꞉ (Fin n → A) , ((i : Fin n) → in-power j (c i))
                          × (w ＝ ∑ᴬ (λ i → x i ·ᴬ c i)))
      → Σ c ꞉ (Fin n → A) , ((i : Fin n) → in-power j (c i))
                          × (w ·ᴬ d ＝ ∑ᴬ (λ i → x i ·ᴬ c i))
    γ (c , h , q) =
     (λ i → c i ·ᴬ d) ,
     (λ i → in-power-is-closed-under-multiplication j (c i) d (h i)) ,
     (ap (_·ᴬ d) q
      ∙ (∑ᴬ-scalar-right (λ i → x i ·ᴬ c i) d)⁻¹
      ∙ ∑ᴬ-pointwise (λ i → (x i ·ᴬ c i) ·ᴬ d) (λ i → x i ·ᴬ (c i ·ᴬ d))
                     (λ i → ·ᴬ-assoc (x i) (c i) d))

  products-are-in-powers
   : (N : ℕ) (w : Fin N → A)
   → ((l : Fin N) → is-in-the-ideal-of x (w l)) → in-power N (∏ᴬ w)
  products-are-in-powers 0        w h = ⋆
  products-are-in-powers (succ N) w h = ∥∥-functor γ (h 𝟎)
   where
    P : A
    P = ∏ᴬ (w ∘ suc)

    P-in-power : in-power N P
    P-in-power = products-are-in-powers N (w ∘ suc) (h ∘ suc)

    γ : (Σ c ꞉ (Fin n → A) , w 𝟎 ＝ ∑ᴬ (λ i → x i ·ᴬ c i))
      → Σ c ꞉ (Fin n → A) , ((i : Fin n) → in-power N (c i))
                          × (P ·ᴬ w 𝟎 ＝ ∑ᴬ (λ i → x i ·ᴬ c i))
    γ (c , q) =
     (λ i → P ·ᴬ c i) ,
     (λ i → in-power-is-closed-under-multiplication N P (c i) P-in-power) ,
     (ap (P ·ᴬ_) q
      ∙ (∑ᴬ-scalar-left P (λ i → x i ·ᴬ c i))⁻¹
      ∙ ∑ᴬ-pointwise (λ i → P ·ᴬ (x i ·ᴬ c i)) (λ i → x i ·ᴬ (P ·ᴬ c i))
                     (λ i → ·ᴬ-swap P (x i) (c i)))

 module _ {n : ℕ} (x : Fin n → A) (k : ℕ)
          (ν : (i : Fin n) → _^ᴬ_ 𝓐 (x i) (succ k) ＝ 0ᴬ)
        where

  monomials-of-high-degree-annihilate-powers
   : (j : ℕ) (e : Fin n → ℕ) (w : A)
   → in-power x j w
   → succ (k * n) ≤ (degree e +ᴺ j)
   → monomial x e ·ᴬ w ＝ 0ᴬ
  monomials-of-high-degree-annihilate-powers 0 e w _ l =
   ap (_·ᴬ w) (monomials-with-a-large-exponent-vanish x k ν e (pr₁ σ) (pr₂ σ))
   ∙ ·ᴬ-zero-left 𝓐 w
   where
    σ : Σ i ꞉ Fin n , succ k ≤ e i
    σ = some-exponent-is-large k e l
  monomials-of-high-degree-annihilate-powers (succ j) e w p l =
   ∥∥-rec A-is-set γ p
   where
    γ : (Σ c ꞉ (Fin n → A) , ((i : Fin n) → in-power x j (c i))
                          × (w ＝ ∑ᴬ (λ i → x i ·ᴬ c i)))
      → monomial x e ·ᴬ w ＝ 0ᴬ
    γ (c , h , q) =
     ap (monomial x e ·ᴬ_) q
     ∙ (∑ᴬ-scalar-left (monomial x e) (λ i → x i ·ᴬ c i))⁻¹
     ∙ ∑ᴬ-of-zeros (λ i → monomial x e ·ᴬ (x i ·ᴬ c i)) vanishes
     where
      bound : (i : Fin n) → succ (k * n) ≤ (degree (bump i e) +ᴺ j)
      bound i = transport (λ - → succ (k * n) ≤ -)
                 ((ap (_+ᴺ j) (degree-of-bump i e)
                   ∙ succ-left (degree e) j)⁻¹)
                 l

      vanishes : (i : Fin n) → monomial x e ·ᴬ (x i ·ᴬ c i) ＝ 0ᴬ
      vanishes i =
       (·ᴬ-assoc (monomial x e) (x i) (c i))⁻¹
       ∙ ap (_·ᴬ c i) ((monomial-of-bump x i e)⁻¹)
       ∙ monomials-of-high-degree-annihilate-powers j (bump i e) (c i) (h i)
          (bound i)

 products-in-ideals-of-nilpotents-vanish
  : {n : ℕ} (x : Fin n → A) (k : ℕ)
  → ((i : Fin n) → _^ᴬ_ 𝓐 (x i) (succ k) ＝ 0ᴬ)
  → (w : Fin (succ (k * n)) → A)
  → ((l : Fin (succ (k * n))) → is-in-the-ideal-of x (w l))
  → ∏ᴬ w ＝ 0ᴬ
 products-in-ideals-of-nilpotents-vanish {n} x k ν w h =
  (·ᴬ-unit-left 𝓐 (∏ᴬ w))⁻¹
  ∙ ap (_·ᴬ ∏ᴬ w) ((monomial-of-zeros x)⁻¹)
  ∙ monomials-of-high-degree-annihilate-powers x k ν (succ (k * n)) (λ _ → 0)
     (∏ᴬ w) (products-are-in-powers x (succ (k * n)) w h)
     (transport (λ - → succ (k * n) ≤ -) (q ⁻¹) (≤-refl (succ (k * n))))
  where
   q : degree {n} (λ _ → 0) +ᴺ succ (k * n) ＝ succ (k * n)
   q = ap (_+ᴺ succ (k * n)) (degree-of-zeros n)
     ∙ zero-left-neutral (succ (k * n))

\end{code}
