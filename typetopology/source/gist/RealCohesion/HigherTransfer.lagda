Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 13 November 2026 (local time), in the consolidation that
followed the final audits: gates 1 and 2 of W4 of Claude Fable 5.2's
plan [1], as incorporated by its addendum 01 [2] after GPT-6 Astra's
independent review [3], and released by Astra [4]. See the AI
disclosure in gist.RealCohesion.index.

Nullness transfers along a strictly rising map, for arbitrary types
-------------------------------------------------------------------

Let S and A be arbitrary types such that the constant-map function
A → (S → A) is an equivalence: A is null for S in the strong sense,
which is is-null S A of gist.CohesiveApartness.Flat by definition. This
module is plain and does not import that module, so it states nullness
as that equivalence.

 * Gate 1 (nullness-transfers-along-a-normalized-path): if l : S → ℝ
   has l x ＝ 0 and l y ＝ 1, then the constant-map function A → (ℝ → A)
   is an equivalence. For e : ℝ → A and t : ℝ, the map s ↦ e (t · l s)
   from S to A is constant, by the nullness of A for S, and its values
   at x and y are e 0 and e t, by t · 0 ＝ 0 and t · 1 ＝ t; so
   evaluation at 0 inverts the constant-map function. This pointwise
   form is GPT-6 Astra's [3, Section 1]. The code is that of Fable's
   scratch check HigherTransferCheck.lagda (SHA-256 fa0c2477…, in the
   companion of [2]), unchanged but for the module name and the import
   list, which gains the imports that gate 2 and the generator path
   below use.

 * Gate 2 (nullness-transfers-along-a-strict-rise): the same holds if
   g : S → ℝ has g x < g y. Choose rationals p < q strictly between
   g x and g y, put c = q - p, μ s = clamp 0 c (g s - p) and
   l s = μ s · (1/c), so that l x ＝ 0 and l y ＝ 1 exactly, and apply
   gate 1 [2, Section 3; 3, Section 2]. The rationals are chosen inside
   the elimination of truncations into the statement that the
   constant-map function A → (ℝ → A) is an equivalence, a proposition by
   function extensionality, and no path in A is formed before. Hence,
   for a family R : J → 𝓦 of types for each of which A is null, a
   strictly rising generator path in ℝ (gist.RealCohesion.Constancy),
   merely, makes A null for ℝ
   (nullness-transfers-along-a-rising-generator-path).

No sethood or crispness of A is assumed, and no modality, excluded
middle, choice or resizing is used. The inverse taken is that of the
positive rational c. Of the multiplication of reals of
gist.RealCohesion.RealMultiplication only the laws t · 0 ＝ 0,
t · 1 ＝ t and 0 · t ＝ 0 and its agreement with the product of
rationals are used, and no law of order. The module has the option
--lossy-unification, as RealMultiplication has: without it, Agda did
not finish gate 1 in 400 seconds, by Fable's report [2, Section 3]. It
imports RealMultiplication, which is outside the Agda 2.8 comparison
closure, so no module of the common layer imports this one.

[1] Claude Fable 5.2. Plan: consolidation of r3, and "C1 + NC in place
    of R♭" (G27(d)), 13 November 2026, Section 4.5.
    references/F02-consolidation-plan.md

[2] Claude Fable 5.2. Addendum 01 to the consolidation plan,
    13 November 2026, Sections 3 and 5.
    references/F03-consolidation-plan-addendum-01.md

[3] GPT-6 Astra. W4 independent mathematical review, 13 November 2026.
    references/A13-w4-review.txt

[4] GPT-6 Astra. Consolidation implementation, second release,
    13 November 2026.
    references/A27-consolidation-release-02.txt

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.HigherTransfer
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import Notation.Order
open import UF.Base
open import UF.Equiv
open import UF.Equiv-FunExt using (being-equiv-is-prop)
open import Rationals.Type
open import Rationals.Order
open import Rationals.Addition renaming (_+_ to _ℚ+_)
open import Rationals.Negation renaming (_-_ to _ℚ-_ ; -_ to ℚ-_)
open import Rationals.Multiplication renaming (_*_ to _ℚ*_)
open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import gist.RealCohesion.RationalArithmetic using (minus-plus)
open import gist.RealCohesion.RationalPoints fe pe pt using (ιₐ ; ιₐ-is-ι)
open import gist.RealCohesion.RealLattice fe pe pt
 using (_+_ ; clamp ; clamp-below ; clamp-above ; translate-above ;
        translate-below ; ιₐ-≤-ιₐ)
open import gist.RealCohesion.RealMultiplication fe pe pt
 using (_*_ ; *-right-unit ; *-right-zero ; *-left-zero ; ιₐ-*)
open import gist.RealCohesion.Constancy fe pe pt using (Rising-Generator-Path)

open PropositionalTruncation pt

\end{code}

Gate 1, Fable's code.

\begin{code}

module _ {𝓦 𝓣 : Universe} {S : 𝓦 ̇ } {A : 𝓣 ̇ }
         (n : is-equiv (λ (a : A) (_ : S) → a))
         (l : S → ℝ) (x y : S) (p : l x ＝ 0ℝ) (q : l y ＝ 1ℝ)
       where

 private
  κ : A → (S → A)
  κ a _ = a

  agree : (h : S → A) → h x ＝ h y
  agree h = happly (inverses-are-sections κ n h) x ⁻¹
          ∙ happly (inverses-are-sections κ n h) y

  constant-at-0 : (e : ℝ → A) (t : ℝ) → e 0ℝ ＝ e t
  constant-at-0 e t = ap e (*-right-zero t ⁻¹ ∙ ap (t *_) (p ⁻¹))
                    ∙ agree (λ s → e (t * l s))
                    ∙ ap e (ap (t *_) q ∙ *-right-unit t)

 nullness-transfers-along-a-normalized-path
  : is-equiv (λ (a : A) (_ : ℝ) → a)
 nullness-transfers-along-a-normalized-path =
  qinvs-are-equivs (λ a _ → a)
   ((λ e → e 0ℝ) , (λ a → refl) , (λ e → dfunext fe (constant-at-0 e)))

\end{code}

Gate 2: the normalization of a strict rise, for rationals p < q
strictly between g x and g y, and the elimination of the truncations.

\begin{code}

module _ {𝓦 𝓣 : Universe} {S : 𝓦 ̇ } {A : 𝓣 ̇ }
         (n : is-equiv (λ (a : A) (_ : S) → a))
         (g : S → ℝ) (x y : S)
       where

 private
  module normalization (p q : ℚ) (l₁ : g x < p) (m : p < q) (l₂ : q < g y)
   where

   c : ℚ
   c = q ℚ- p

   c-is-positive : 0ℚ < c
   c-is-positive = ℚ<-difference-positive p q m

   c-is-not-zero : ¬ (c ＝ 0ℚ)
   c-is-not-zero e = ℚ<-irrefl 0ℚ (transport (0ℚ <_) e c-is-positive)

   μ : S → ℝ
   μ s = clamp (ιₐ 0ℚ) (ιₐ c) (g s + ιₐ (ℚ- p))

   μ-at-x : μ x ＝ ιₐ 0ℚ
   μ-at-x = clamp-below (ιₐ 0ℚ) (ιₐ c) (g x + ιₐ (ℚ- p))
             (translate-below (g x) 0ℚ p
               (transport (g x <_) (ℚ-zero-left-neutral p ⁻¹) l₁))

   μ-at-y : μ y ＝ ιₐ c
   μ-at-y = clamp-above (ιₐ 0ℚ) (ιₐ c) (g y + ιₐ (ℚ- p))
             (ιₐ-≤-ιₐ 0ℚ c (ℚ<-coarser-than-≤ 0ℚ c c-is-positive))
             (translate-above (g y) c p
               (transport (_< g y) (minus-plus q p ⁻¹) l₂))

   normalized : S → ℝ
   normalized s = μ s * ιₐ (ℚ*-inv c c-is-not-zero)

   normalized-at-x : normalized x ＝ 0ℝ
   normalized-at-x = ap (_* ιₐ (ℚ*-inv c c-is-not-zero)) (μ-at-x ∙ ιₐ-is-ι 0ℚ)
                   ∙ *-left-zero (ιₐ (ℚ*-inv c c-is-not-zero))

   normalized-at-y : normalized y ＝ 1ℝ
   normalized-at-y = ap (_* ιₐ (ℚ*-inv c c-is-not-zero)) μ-at-y
                   ∙ ιₐ-* c (ℚ*-inv c c-is-not-zero)
                   ∙ ap ιₐ (ℚ*-inverse-product c c-is-not-zero)
                   ∙ ιₐ-is-ι 1ℚ

 nullness-transfers-along-a-strict-rise
  : g x < g y → is-equiv (λ (a : A) (_ : ℝ) → a)
 nullness-transfers-along-a-strict-rise l = ∥∥-rec i γ₁ l
  where
   i : is-prop (is-equiv (λ (a : A) (_ : ℝ) → a))
   i = being-equiv-is-prop (λ 𝓤 𝓥 → fe) (λ (a : A) (_ : ℝ) → a)

   γ₁ : (Σ p ꞉ ℚ , (g x < p) × (p < g y)) → is-equiv (λ (a : A) (_ : ℝ) → a)
   γ₁ (p , l₁ , l₂) =
    ∥∥-rec i γ₂
     (rounded-left-b (lower-cut-of (g y)) (rounded-from-real-L (g y)) p l₂)
    where
     γ₂ : (Σ q ꞉ ℚ , (p < q) × (q < g y)) → is-equiv (λ (a : A) (_ : ℝ) → a)
     γ₂ (q , m , l₃) =
      nullness-transfers-along-a-normalized-path n N.normalized x y
       N.normalized-at-x N.normalized-at-y
      where
       module N = normalization p q l₁ m l₃

\end{code}

A type null for every member of a family is null for ℝ, if some map
from a member to ℝ rises strictly, merely.

\begin{code}

module _ {𝓥 𝓦 𝓣 : Universe} {J : 𝓥 ̇ } (R : J → 𝓦 ̇ ) {A : 𝓣 ̇ }
         (n : (j : J) → is-equiv (λ (a : A) (_ : R j) → a))
       where

 nullness-transfers-along-a-rising-generator-path
  : ∥ Rising-Generator-Path R ∥ → is-equiv (λ (a : A) (_ : ℝ) → a)
 nullness-transfers-along-a-rising-generator-path =
  ∥∥-rec (being-equiv-is-prop (λ 𝓤 𝓥 → fe) (λ (a : A) (_ : ℝ) → a))
   (λ (j , g , x , y , l) →
     nullness-transfers-along-a-strict-rise (n j) g x y l)

\end{code}
