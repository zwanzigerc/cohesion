Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. See the AI disclosure in
gist.RealCohesion.index.

Strong extensionality of every function ℝ → ℝ from Axiom R♭: gate
G16(a) of Claude Fable 5.2's second addendum [2, §3].

The exact statement. Lemma 7.12 of the write-up [1]: assume Axiom R♭;
then for every f : ℝ → ℝ and all real numbers u and v, if f u and f v
are apart, so are u and v. Neither f nor u and v are crisp.

The formal statement, strong-extensionality, is that lemma, from the
constancy of maps ℝ → Q, which follows from Axiom R♭. In
gist.RealCohesion.Theorems it is stated from Axiom R♭ as the target
Target-strong-extensionality of
gist.RealCohesion.ShulmanWeakeningsStatements.

The proof is the addendum's, which Astra audited (Section 1 of the
audit of the note on 11.5). Let f v < f u. Apply sequential hitting
(gist.RealCohesion.FunctionalHitting) to t ↦ f t - f v at u, along the
points z j that move from u towards v by at most 2⁻⁽ʲ⁺¹⁾ (a clamped
step of gist.RealCohesion.RealLimits). It gives a j with f v < f (z j).
By locatedness, applied to v - u and to u - v, either one of them is
above 2⁻⁽ʲ⁺²⁾, and then u < v or v < u, or both are below 2⁻⁽ʲ⁺¹⁾, and
then v is within 2⁻⁽ʲ⁺¹⁾ of u, so z j ＝ v, which contradicts
f v < f (z j). The addendum steps by 2⁻ʲ and compares with 2⁻⁽ʲ⁺¹⁾;
here the steps are ρ j = 2⁻⁽ʲ⁺¹⁾ of gist.RealCohesion.RealLimits, whose
lemmas the library has, and the points z j are still within 2⁻ʲ of u,
as sequential hitting asks.

[1] Answers to some open problems in real-cohesive homotopy type
    theory. Research notes, revision of 12 November 2026, Lemma 7.12.
    references/C04-write-up-2026-11-12.tex

[2] Claude Fable 5.2. Second addendum to the formalization plan,
    revision 4 of 12 November 2026.
    references/F13b-second-addendum-rev4-as-amended.md

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import MLTT.Plus-Properties using (+-commutative)
open import UF.Base using (transport₂)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.StrongExtensionality
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import Notation.Order
open import Rationals.Addition renaming (_+_ to _ℚ+_)
open import Rationals.Negation renaming (_-_ to _ℚ-_ ; -_ to ℚ-_)
open import Rationals.Order
open import Rationals.Type
open import Rationals.Limits fe pe pt using (⟨1/2⟩^_)
open import DedekindReals.Order fe pe pt
open import DedekindReals.Type fe pe pt
open import gist.RealCohesion.FiniteChainQuotient fe pe pt using (Q)
open import gist.RealCohesion.FunctionalHitting fe pe pt
 using (_is-within-2⁻_of_ ; positive-sequential-hitting-for-functionals)
open import gist.RealCohesion.RationalArithmetic
 using (half ; half-is-positive ; half-is-less ; 1/2≤1 ; neg-is-negative)
open import gist.RealCohesion.RationalPoints fe pe pt using (ιₐ)
open import gist.RealCohesion.RealLattice fe pe pt
 using (ℚ<ℝ-is-prop ; ιₐ-<-gives-≤ ; ℝ≤-refl ; neg-below⁻¹ ; sum-below⁻¹ ;
         positive-from-below ;
        <-from-difference ; <-gives-positive-difference)
 renaming (_+_ to _ℝ+_ ; -_ to ℝ-_)
open import gist.RealCohesion.RealLimits fe pe pt
 using (ρ ; ρ-is-positive ; ρ-decreases ; within ; within-sym ; within-weaken ;
        clamped-step ; clamped-step-within ; clamped-step-full)
open import gist.RealCohesion.RealOrder fe pe pt using (cuts-are-ordered)
open import gist.RealCohesion.SequentialHitting fe pe pt
 using (starter-bounds-from-within)

open PropositionalTruncation pt

\end{code}

Three facts. Apartness is symmetric; if u - v and v - u are both below
δ, then u and v are within δ of each other; and ρ j = 2⁻⁽ʲ⁺¹⁾ is at
most 2⁻ʲ.

\begin{code}

apart-sym : (u v : ℝ) → u ♯ v → v ♯ u
apart-sym u v = ∥∥-functor +-commutative

differences-give-within : (δ : ℚ) (u v : ℝ)
                        → (u ℝ+ (ℝ- v)) < δ → (v ℝ+ (ℝ- u)) < δ → within δ u v
differences-give-within δ u v k k' = I u v k , I v u k'
 where
  I : (a b : ℝ) → (a ℝ+ (ℝ- b)) < δ → (p : ℚ) → p < a → (p ℚ- δ) < b
  I a b k p l = ∥∥-rec (ℚ<ℝ-is-prop (p ℚ- δ) b) γ (sum-below⁻¹ a (ℝ- b) δ k)
   where
    γ : (Σ (r , s) ꞉ ℚ × ℚ , (a < r) × ((ℝ- b) < s) × (δ ＝ r ℚ+ s))
      → (p ℚ- δ) < b
    γ ((r , s) , m , n , e) =
     use-rounded-real-L b (p ℚ- δ) (ℚ- s) II (neg-below⁻¹ b s n)
     where
      III : p ℚ- r < 0ℚ
      III = transport (p ℚ- r <_) (ℚ-inverse-sum-to-zero r)
             (ℚ<-addition-preserves-order p r (ℚ- r)
               (cuts-are-ordered a p r l m))

      II : (p ℚ- δ) < (ℚ- s)
      II = transport₂ _<_
            (ℚ+-assoc p (ℚ- r) (ℚ- s) ∙ ap (p ℚ+_) (ℚ-minus-dist r s)
             ∙ ap (λ x → p ℚ- x) (e ⁻¹))
            (ℚ-zero-left-neutral (ℚ- s))
            (ℚ<-addition-preserves-order (p ℚ- r) 0ℚ (ℚ- s) III)

ρ-is-below-power : (j : ℕ) → ρ j ≤ (⟨1/2⟩^ j)
ρ-is-below-power 0        = 1/2≤1
ρ-is-below-power (succ j) = ℚ<-coarser-than-≤ (ρ (succ j)) (ρ j) (ρ-decreases j)

\end{code}

Strong extensionality, if maps ℝ → Q are constant.

\begin{code}

module _ (ν : (k : ℝ → Q) (u v : ℝ) → k u ＝ k v) where

 smaller-value-gives-apartness : (f : ℝ → ℝ) (u v : ℝ) → f v < f u → u ♯ v
 smaller-value-gives-apartness f u v l =
  ∥∥-rec ∨-is-prop γ
   (positive-sequential-hitting-for-functionals ν 𝟙 H (λ _ → u) (λ j _ → z j) c
     (<-gives-positive-difference (f u) (f v) l))
  where
   H : (𝟙 {𝓤₀} → ℝ) → ℝ
   H w = f (w ⋆) ℝ+ (ℝ- f v)

   z : ℕ → ℝ
   z j = clamped-step u (ιₐ (ℚ- ρ j)) (ιₐ (ρ j)) v

   z-is-near : (j : ℕ) → within (ρ j) u (z j)
   z-is-near j = clamped-step-within (ρ j) u (ιₐ (ℚ- ρ j)) (ιₐ (ρ j)) v
                  (ℝ≤-refl (ιₐ (ℚ- ρ j)))
                  (ιₐ-<-gives-≤ (ℚ- ρ j) (ρ j)
                    (ℚ<-trans (ℚ- ρ j) 0ℚ (ρ j)
                      (neg-is-negative (ρ j) (ρ-is-positive j))
                      (ρ-is-positive j)))
                  (ℝ≤-refl (ιₐ (ρ j)))

   c : (j : ℕ) → (λ (_ : 𝟙 {𝓤₀}) → z j) is-within-2⁻ j of (λ _ → u)
   c j _ = starter-bounds-from-within j (z j) u
            (within-weaken (ρ j) (⟨1/2⟩^ j) (z j) u (ρ-is-below-power j)
              (within-sym (ρ j) u (z j) (z-is-near j)))

   γ : (Σ j ꞉ ℕ , 0ℝ < H (λ _ → z j)) → u ♯ v
   γ (j , m) =
    ∥∥-rec ∨-is-prop δ
     (binary-choice (ℝ-locatedness (v ℝ+ (ℝ- u)) (half (ρ j)) (ρ j)
                      (half-is-less (ρ j) (ρ-is-positive j)))
                    (ℝ-locatedness (u ℝ+ (ℝ- v)) (half (ρ j)) (ρ j)
                      (half-is-less (ρ j) (ρ-is-positive j))))
    where
     δ : ((half (ρ j) < (v ℝ+ (ℝ- u))) ∔ ((v ℝ+ (ℝ- u)) < ρ j))
       × ((half (ρ j) < (u ℝ+ (ℝ- v))) ∔ ((u ℝ+ (ℝ- v)) < ρ j))
       → u ♯ v
     δ (inl o , _)      = ∣ inl (<-from-difference v u
                                 (positive-from-below (v ℝ+ (ℝ- u)) (half (ρ j))
                                   (half-is-positive (ρ j) (ρ-is-positive j))
                                    o)) ∣
     δ (inr _ , inl o)  = ∣ inr (<-from-difference u v
                                 (positive-from-below (u ℝ+ (ℝ- v)) (half (ρ j))
                                   (half-is-positive (ρ j) (ρ-is-positive j))
                                    o)) ∣
     δ (inr o , inr o') =
      𝟘-elim (<ℝ-irreflexive (f v) (<-from-difference (f v) (f v) II))
      where
       I : z j ＝ v
       I = clamped-step-full (ρ j) u (ιₐ (ℚ- ρ j)) (ιₐ (ρ j)) v refl refl
            (differences-give-within (ρ j) u v o' o)

       II : 0ℝ < (f v ℝ+ (ℝ- f v))
       II = transport (λ - → 0ℝ < (f - ℝ+ (ℝ- f v))) I m

 strong-extensionality : (f : ℝ → ℝ) (u v : ℝ) → f u ♯ f v → u ♯ v
 strong-extensionality f u v = ∥∥-rec ∨-is-prop γ
  where
   γ : (f u < f v) ∔ (f v < f u) → u ♯ v
   γ (inl l) = apart-sym v u (smaller-value-gives-apartness f v u l)
   γ (inr l) = smaller-value-gives-apartness f u v l

\end{code}
