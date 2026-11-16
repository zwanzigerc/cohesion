Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 11 November 2026. See the AI disclosure in
gist.RealCohesion.index.

Sequential hitting for functionals, and closed half-lines (Part B of
the blueprint addendum [3]).

Exact statement served. Theorem 7.4 of the write-up [2] (GPT-6 Astra):
assume Axiom R♭; let h : ℝᵐ → ℝ, a : ℝᵐ and z : ℕ → ℝᵐ with
|z j - a| ≤ 2⁻ʲ for all j, in the supremum norm; if h a > 0, then
h (z j) > 0 for some j. The formal statements, and their relation to
it:

 * Sequential-Hitting-In-ℝ^ is the theorem itself, with the supremum
   norm written coordinatewise and |u - v| ≤ ε as two inequalities, as
   in Sequential-Hitting of gist.RealCohesion.ApproximateIVTStatement.

 * Positive-Sequential-Hitting-For-Functionals is the remark after the
   theorem in the write-up, for functionals on X → ℝ with X any type;
   the write-up records that this remark has not been audited [2].
   Theorem 7.4 for ℝᵐ is its instance X = Fin m.

 * Sequential-Hitting-For-Functionals has the hypothesis 1 ≤ h a in
   place of 0 < h a. Stated from Axiom R♭, it is the target
   Target-hitting of gist.RealCohesion.BrouwerStatements. Multiplying h
   by a power of 2 turns the one hypothesis into the other [3, B5].

 * Closed-Half-Lines-Are-Sequentially-Closed [3, B4]: if H (z j) ≤ 0
   for all j, then H a ≤ 0. It is a form of Corollary 7.5 of the
   write-up (closed-zero preservation), and it is the form that the
   proof of Corollary 3.7 on the cube uses [3, Part C].

gist.RealCohesion.Theorems states all four from Axiom R♭, with the
types of gist.RealCohesion.BrouwerStatements for the second and the
fourth. This module proves them from the constancy of maps ℝ → Q,
which follows from Axiom R♭
(gist.RealCohesion.FiniteChainDiscreteness).

The proof adds no construction to those already in the library. For
each x : X, let Φ t x be the plateau path
(gist.RealCohesion.PlateauPath) from a x through the sequence
n ↦ z (n + 3) x. Then Φ 0 ＝ a, and Φ (m j) ＝ z (j + 3) at the
midpoint m j of the plateau of each index j ≥ 1, by function
extensionality. The midpoints converge to 0, so sequential hitting for
functions of one variable (gist.RealCohesion.SequentialHitting),
applied to t ↦ h (Φ t) at 0 along the midpoints, gives the claim. No
continuity of Φ is needed. gist.RealCohesion.PairHitting first proved
the case of pairs by this reduction, and that case is now the instance
X = 𝟚; an earlier revision of the write-up proved the case of ℝⁿ in the
same way [1, Proposition 3.2]. The addendum suggests rerunning the
one-variable construction pointwise in x instead [3, B1–B3]; the
reduction gives the same theorem from the existing modules.

The rescaling by powers of 2 uses the repeated doubling of
gist.RealCohesion.ApproximateIVTReduction.

[1] Answers to some open problems in real-cohesive homotopy type
    theory. Research notes, revised 10 November 2026.
    references/C02-write-up-2026-11-10.tex

[2] Answers to some open problems in real-cohesive homotopy type
    theory. Research notes, seventh revision of 11 November 2026,
    Theorem 7.4, the remark after it, and Corollary 7.5.
    references/C03-write-up-2026-11-11-seventh.tex
    references/C03a-write-up-seventh-README.txt

[3] Formalization blueprint, addendum: Theorem 7.10, Corollary 3.7,
    Theorem 4.3 and Theorem 8.32, revision 4, Part B. Claude Fable
    5.2, 11 November 2026.
    references/F14-brouwer-addendum-rev4.md

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.FunctionalHitting
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import Fin.Type
open import Naturals.Addition renaming (_+_ to _+ℕ_)
open import Naturals.Order using (≤-refl)
open import Notation.CanonicalMap
open import Notation.Order
open import UF.Base
open import Rationals.Type
open import Rationals.Order
open import Rationals.Addition renaming (_+_ to _ℚ+_)
open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import DedekindReals.Addition fe pe pt using () renaming (_+_ to _+ℝ_)
open import gist.RealCohesion.RationalPoints fe pe pt
open import gist.RealCohesion.RealLattice fe pe pt
 using (ℚ<ℝ-is-prop ; ιₐ-zero-is-0ℝ)
open import gist.RealCohesion.RealLimits fe pe pt
 using (ρ ; ρ-decreases ; ρ-becomes-small ; ℚ<-add-left ; within ; within-zero)
open import gist.RealCohesion.FiniteChainQuotient fe pe pt using (Q)
open import gist.RealCohesion.Plateaus fe pe pt
 using (α ; m ; β ; α-below-m ; m-below-β ; m-is-positive ; ρ-double-below)
open import gist.RealCohesion.PlateauPath fe pe pt using (module plateau-path)
open import gist.RealCohesion.SequentialHitting fe pe pt
 using (module sequential-hitting ; within-from-starter-bounds ;
         positive-from-rational)
open import gist.RealCohesion.ApproximateIVTStatement fe pe pt using (2⁻)
open import gist.RealCohesion.ApproximateIVTReduction fe pe pt
 using (dbl^ ; dbl^-is-monotone ; dbl^-of-zero ; dbl^-of-ρ ;
        dbl-ℝ ; below-dbl-ℝ ; below-dbl-ℝ⁻¹)

open PropositionalTruncation pt

\end{code}

The statements. The first three are those of
gist.RealCohesion.BrouwerStatements, which needs --cohesion and crisp
parameters; gist.RealCohesion.Theorems confirms that they agree by
stating the results of this module with the types of that one. The
function 2⁻ is that of gist.RealCohesion.ApproximateIVTStatement.

\begin{code}

_is-within-2⁻_of_ : {𝓥 : Universe} {X : 𝓥 ̇ } → (X → ℝ) → ℕ → (X → ℝ) → 𝓥 ̇
_is-within-2⁻_of_ {𝓥} {X} z j a =
 (x : X) → (z x ≤ a x +ℝ 2⁻ j) × (a x ≤ z x +ℝ 2⁻ j)

Sequential-Hitting-For-Functionals : (𝓥 : Universe) → 𝓤₁ ⊔ (𝓥 ⁺) ̇
Sequential-Hitting-For-Functionals 𝓥 =
   (X : 𝓥 ̇ ) (h : (X → ℝ) → ℝ) (a : X → ℝ) (z : ℕ → X → ℝ)
 → ((j : ℕ) → z j is-within-2⁻ j of a)
 → 1ℝ ≤ h a
 → ∃ j ꞉ ℕ , 0ℝ < h (z j)

Closed-Half-Lines-Are-Sequentially-Closed : (𝓥 : Universe) → 𝓤₁ ⊔ (𝓥 ⁺) ̇
Closed-Half-Lines-Are-Sequentially-Closed 𝓥 =
   (X : 𝓥 ̇ ) (H : (X → ℝ) → ℝ) (a : X → ℝ) (z : ℕ → X → ℝ)
 → ((j : ℕ) → z j is-within-2⁻ j of a)
 → ((j : ℕ) → H (z j) ≤ 0ℝ)
 → H a ≤ 0ℝ

Positive-Sequential-Hitting-For-Functionals : (𝓥 : Universe) → 𝓤₁ ⊔ (𝓥 ⁺) ̇
Positive-Sequential-Hitting-For-Functionals 𝓥 =
   (X : 𝓥 ̇ ) (h : (X → ℝ) → ℝ) (a : X → ℝ) (z : ℕ → X → ℝ)
 → ((j : ℕ) → z j is-within-2⁻ j of a)
 → 0ℝ < h a
 → ∃ j ꞉ ℕ , 0ℝ < h (z j)

Sequential-Hitting-In-ℝ^ : 𝓤₁ ̇
Sequential-Hitting-In-ℝ^ =
   (n : ℕ) (h : (Fin n → ℝ) → ℝ) (a : Fin n → ℝ) (z : ℕ → Fin n → ℝ)
 → ((j : ℕ) → z j is-within-2⁻ j of a)
 → 0ℝ < h a
 → ∃ j ꞉ ℕ , 0ℝ < h (z j)

\end{code}

The path through a family of sequences. For each x : X it is the
plateau path from a x through n ↦ z (n + 3) x, whose terms are within
hgt n = ρ (n + 3) of a x.

\begin{code}

module path-through
        {𝓥 : Universe}
        {X : 𝓥 ̇ }
        (a : X → ℝ)
        (z : ℕ → X → ℝ)
        (z-converges : (j : ℕ) (x : X) → within (ρ j) (z j x) (a x))
       where

 module at (x : X) =
  plateau-path (a x) (λ n → z (n +ℕ 3) x) (λ n → z-converges (n +ℕ 3) x)

 Φ : ℝ → X → ℝ
 Φ t x = at.ψ x t

 Φ-at-zero : Φ (ιₐ 0ℚ) ＝ a
 Φ-at-zero = dfunext fe at.ψ-at-zero

 Φ-at-midpoint : (j : ℕ) → Φ (ιₐ (m (succ j))) ＝ z (succ j +ℕ 3)
 Φ-at-midpoint j =
  dfunext fe (λ x → at.ψ-on-plateau x j (ιₐ (m (succ j)))
                     (ιₐ-lower (α (succ j)) (m (succ j)) (α-below-m (succ j)))
                     (ιₐ-upper (m (succ j)) (β (succ j)) (m-below-β (succ j))))

\end{code}

The midpoints of the plateaus of index j ≥ 1 converge to 0.

\begin{code}

midpoints-converge : (j : ℕ) → within (ρ j) (ιₐ (m (succ j))) (ιₐ 0ℚ)
midpoints-converge j =
 within-zero (ρ j) (m (succ j)) (m-is-positive (succ j))
  (ℚ≤-trans (m (succ j)) (ρ (succ j) ℚ+ ρ (succ j)) (ρ j)
    (ℚ<-coarser-than-≤ (m (succ j)) (ρ (succ j) ℚ+ ρ (succ j))
      (ℚ<-add-left (ρ (succ j)) (ρ (succ (succ j))) (ρ (succ j))
        (ρ-decreases (succ j))))
    (ρ-double-below j (succ j) (≤-refl (succ j))))

\end{code}

A positive real number has 0 in its lower cut.

\begin{code}

rational-from-positive : (y : ℝ) → 0ℝ < y → 0ℚ < y
rational-from-positive y = ∥∥-rec (ℚ<ℝ-is-prop 0ℚ y) γ
 where
  γ : (Σ q ꞉ ℚ , (0ℝ < q) × (q < y)) → 0ℚ < y
  γ (q , o , o') = use-rounded-real-L y 0ℚ q
                    (ιₐ-upper⁻¹ 0ℚ q (transport (_< q) (ιₐ-zero-is-0ℝ ⁻¹) o)) o'

\end{code}

Sequential hitting for functionals, in the form of
gist.RealCohesion.SequentialHitting: the terms z j are within ρ j of
a, the hypothesis is 1 ≤ h a with the abstract embedding ιₐ, and the
conclusion has a rational 0.

\begin{code}

module _ (ν : (k : ℝ → Q) (u v : ℝ) → k u ＝ k v) where

 functional-hitting : {𝓥 : Universe} {X : 𝓥 ̇ }
                      (h : (X → ℝ) → ℝ) (a : X → ℝ) (z : ℕ → X → ℝ)
                    → ((j : ℕ) (x : X) → within (ρ j) (z j x) (a x))
                    → ιₐ 1ℚ ≤ h a
                    → ∃ k ꞉ ℕ , 0ℚ < h (z k)
 functional-hitting h a z c h-at-a =
  ∥∥-functor γ
   (sequential-hitting.sequential-hitting ν g (ιₐ 0ℚ) s midpoints-converge
     g-at-zero)
  where
   open path-through a z c

   g : ℝ → ℝ
   g t = h (Φ t)

   s : ℕ → ℝ
   s j = ιₐ (m (succ j))

   g-at-zero : ιₐ 1ℚ ≤ g (ιₐ 0ℚ)
   g-at-zero = transport (λ f → ιₐ 1ℚ ≤ h f) (Φ-at-zero ⁻¹) h-at-a

   γ : (Σ j ꞉ ℕ , 0ℚ < g (s j)) → Σ k ꞉ ℕ , 0ℚ < h (z k)
   γ (j , p) = succ j +ℕ 3 , transport (λ f → 0ℚ < h f) (Φ-at-midpoint j) p

\end{code}

The statement Sequential-Hitting-For-Functionals. As in
sequential-hitting-as-stated of gist.RealCohesion.SequentialHitting, we
apply functional-hitting to z ∘ succ, whose terms are within
2⁻⁽ʲ⁺¹⁾ ＝ ρ j of a.

\begin{code}

 sequential-hitting-for-functionals : {𝓥 : Universe}
                                    → Sequential-Hitting-For-Functionals 𝓥
 sequential-hitting-for-functionals X h a z c l =
  ∥∥-functor γ (functional-hitting h a (z ∘ succ) c' l')
  where
   c' : (j : ℕ) (x : X) → within (ρ j) (z (succ j) x) (a x)
   c' j x = within-from-starter-bounds (succ j) (z (succ j) x) (a x)
             (pr₁ (c (succ j) x)) (pr₂ (c (succ j) x))

   l' : ιₐ 1ℚ ≤ h a
   l' = transport (_≤ h a) (ιₐ-is-ι 1ℚ ⁻¹) l

   γ : (Σ k ꞉ ℕ , 0ℚ < h (z (succ k))) → Σ j ꞉ ℕ , 0ℝ < h (z j)
   γ (k , p) = succ k , positive-from-rational (h (z (succ k))) p

\end{code}

The hypothesis 0 < h a. Take a rational r with 0 < r < h a, and n with
ρ n < r. Doubling n + 1 times gives 1 = 2ⁿ⁺¹ ρ n < 2ⁿ⁺¹ r < 2ⁿ⁺¹ h a,
and 2ⁿ⁺¹ h (z j) > 0 gives h (z j) > 0.

\begin{code}

 positive-sequential-hitting-for-functionals
  : {𝓥 : Universe} → Positive-Sequential-Hitting-For-Functionals 𝓥
 positive-sequential-hitting-for-functionals X h a z c = ∥∥-rec ∃-is-prop γ
  where
   γ : (Σ r ꞉ ℚ , (0ℝ < r) × (r < h a)) → ∃ j ꞉ ℕ , 0ℝ < h (z j)
   γ (r , o , o') = ∥∥-functor δ
                     (sequential-hitting-for-functionals X (λ f → dbl-ℝ k (h f))
                       a z c
                       one-below)
    where
     r-is-positive : 0ℚ < r
     r-is-positive = ιₐ-upper⁻¹ 0ℚ r (transport (_< r) (ιₐ-zero-is-0ℝ ⁻¹) o)

     small : Σ n ꞉ ℕ , ρ n < r
     small = ρ-becomes-small r r-is-positive

     k : ℕ
     k = succ (pr₁ small)

     one-below' : 1ℚ < dbl-ℝ k (h a)
     one-below' = transport (_< dbl-ℝ k (h a)) (dbl^-of-ρ (pr₁ small))
                   (use-rounded-real-L (dbl-ℝ k (h a)) (dbl^ k (ρ (pr₁ small)))
                     (dbl^ k r)
                     (dbl^-is-monotone k (ρ (pr₁ small)) r (pr₂ small))
                     (below-dbl-ℝ k (h a) r o'))

     one-below : 1ℝ ≤ dbl-ℝ k (h a)
     one-below = transport (_≤ dbl-ℝ k (h a)) (ιₐ-is-ι 1ℚ)
                  (λ p l → use-rounded-real-L (dbl-ℝ k (h a)) p 1ℚ
                            (ιₐ-lower⁻¹ p 1ℚ l) one-below')

     δ : (Σ j ꞉ ℕ , 0ℝ < dbl-ℝ k (h (z j))) → Σ j ꞉ ℕ , 0ℝ < h (z j)
     δ (j , p) = j , positive-from-rational (h (z j))
                      (below-dbl-ℝ⁻¹ k (h (z j)) 0ℚ
                        (transport (_< dbl-ℝ k (h (z j))) (dbl^-of-zero k ⁻¹)
                          (rational-from-positive (dbl-ℝ k (h (z j))) p)))

\end{code}

Closed half-lines are sequentially closed [3, B4]: if 0 < H a, the
previous form gives j with 0 < H (z j).

\begin{code}

 closed-half-lines-are-sequentially-closed
  : {𝓥 : Universe} → Closed-Half-Lines-Are-Sequentially-Closed 𝓥
 closed-half-lines-are-sequentially-closed X H a z c k =
  ℝ-not-less-is-greater-or-equal 0ℝ (H a) γ
  where
   γ : ¬ (0ℝ < H a)
   γ l =
    ∥∥-rec 𝟘-is-prop δ (positive-sequential-hitting-for-functionals X H a z c l)
    where
     δ : (Σ j ꞉ ℕ , 0ℝ < H (z j)) → 𝟘
     δ (j , p) = ℝ-less-than-not-greater-or-equal 0ℝ (H (z j)) p (k j)

\end{code}

Theorem 7.4 of the write-up, for ℝⁿ with the supremum norm: the
instance X = Fin n.

\begin{code}

 sequential-hitting-in-ℝ^ : Sequential-Hitting-In-ℝ^
 sequential-hitting-in-ℝ^ n =
  positive-sequential-hitting-for-functionals (Fin n)

\end{code}
