Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 25 October 2026. See the AI disclosure in
gist.RealCohesion.index.

A conditional refutation of countable continuity, from the
finite-height principle and a tower of unbounded depth.

The countermodel to Shulman's continuity conjecture constructed with
GPT-6 Astra [1, 2] validates two principles, stated here for a
reflective subuniverse with reflection ○, its zero-shape Π₀ and the
iterated path quotients Q^ n of gist.RealCohesion.RealPathQuotient,
for an interval I with endpoints i₀ and i₁. In the real-cohesive
instance, ○ is the shape, I is the real line and the endpoints are 0
and 1 (see gist.RealCohesion.RealShapeContinuity).

 * The finite-height principle [2, §4]. If two crisp points x and y of
   a crisp set X have the same zero-shape, then they become equal at
   some finite stage of the iterated path quotient:

     η₀ X x ＝ η₀ X y → ∃ m ꞉ ℕ , q[ m ] x ＝ q[ m ] y.

   The identification of zero-shapes is an ordinary hypothesis, not a
   crisp one. With m = 1 throughout, this is a form of the π₀-Oka
   principle of [3], which holds in Shulman's intended model.

 * Unbounded depth. There is a crisp sequence of crisp sets B n with
   crisp points b n and t n of the same zero-shape such that, for
   every stage k, some b n and t n are still distinct at stage k:

     (k : ℕ) → ∃ n ꞉ ℕ , q[ k ] (b n) ≠ q[ k ] (t n).

   In the countermodel B n is the stage B_n of [1, §8], and already
   q[ n ] (b n) ≠ q[ n ] (t n), which is the special case treated at
   the end of this module.

From these and countable choice for crisp families we derive that the
comparison κ A : ○ (ℕ → A) → (ℕ → ○ A) is not an equivalence for the
crisp set A = Σ n ꞉ ℕ , B n. Using the tagged sum rather than a
wedge avoids a quotient. The proof has two parts.

 1. Zero-shape separation. Let u n = (n , b n) and v n = (n , t n). If
    u and v had the same zero-shape, the finite-height principle,
    applied to the crisp set ℕ → A, would give merely a stage m at
    which they become equal. Projecting to the summand B n, with n as
    given by unbounded depth at stage m, and using the naturality of
    the iterated quotient maps, gives q[ m ] (b n) ＝ q[ m ] (t n),
    which is impossible. Both truncated witnesses are eliminated into
    the empty type, so no bound and no choice is needed here.

 2. The coordinates agree, because b n and t n have the same
    zero-shape. Then gist.RealCohesion.ContinuityObstruction applies.

The two principles are additional hypotheses: we don't claim that they
follow from Shulman's axioms. Their content is in the models, where
[1, 2] show that they hold in the countermodel. Shulman's conjecture
asserts that κ A is an equivalence under his Axioms R♭ and AC, which
give the countable choice used here. So if the conjecture holds, then
these axioms, together with the finite-height principle, refute
unbounded depth.

[1] An ordinary real-cohesive countermodel to countable-power
    continuity. Research notes, 25 October 2026.
    references/C05-ordinary-countermodel.txt

[2] Internal real-path quotients and the finite-height principle.
    Research notes, 25 October 2026.
    references/C06-internal-real-path-quotients.txt

[3] Shulman's continuity conjecture: statement, context and partial
    progress. Research notes, version 2, 25 October 2026.
    references/C08-continuity-brief-v2.md

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.SetTrunc
open import UF.Subsingletons
open import Modal.Subuniverse
open import Quotient.Type

module gist.RealCohesion.FiniteHeightContinuity
        (@♭ fe : Fun-Ext)
        (@♭ pe : Prop-Ext)
        (@♭ pt : propositional-truncations-exist)
        (@♭ st : set-truncations-exist)
        (@♭ sq : set-quotients-exist)
        {@♭ 𝓤 𝓥 : Universe}
        (@♭ P : subuniverse 𝓤 𝓥)
        (@♭ P-is-reflective : subuniverse-is-reflective P)
        (@♭ I : 𝓤 ̇ )
        (@♭ i₀ i₁ : I)
       where

open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Equiv
open import UF.Sets
open import UF.Sets-Properties
open import gist.RealCohesion.ShapeContinuity fe pe pt st P P-is-reflective
open import gist.RealCohesion.RealPathQuotient pt sq I i₀ i₁
open import gist.RealCohesion.ContinuityObstruction
             fe pe pt st P P-is-reflective

open PropositionalTruncation pt

\end{code}

The finite-height principle.

\begin{code}

Finite-Height : 𝓤 ⁺ ̇
Finite-Height = (@♭ X : 𝓤 ̇ )
              → @♭ is-set X
              → (@♭ x y : X)
              → η₀ X x ＝ η₀ X y
              → ∃ m ꞉ ℕ , q[ m ] x ＝ q[ m ] y

\end{code}

Unbounded depth of a sequence of pairs of points.

\begin{code}

Unbounded-Depth : (B : ℕ → 𝓤 ̇ ) (b t : (n : ℕ) → B n) → 𝓤 ̇
Unbounded-Depth B b t = (k : ℕ) → ∃ n ꞉ ℕ , q[ k ] (b n) ≠ q[ k ] (t n)

\end{code}

We now fix a crisp sequence of sets with two crisp sequences of
points, and consider the tagged sum A and the sequences u and v.

\begin{code}

module _ (@♭ B : ℕ → 𝓤 ̇ )
         (@♭ B-is-set : (n : ℕ) → is-set (B n))
         (@♭ b t : (n : ℕ) → B n)
       where

 A : 𝓤 ̇
 A = Σ n ꞉ ℕ , B n

 A-is-set : is-set A
 A-is-set = Σ-is-set ℕ-is-set B-is-set

 u v : ℕ → A
 u n = n , b n
 v n = n , t n

\end{code}

The inclusion of the n-th summand, and the retraction of A onto the
m-th summand, which is the identity on that summand and the constant
map with value b m on every other summand.

\begin{code}

 ι : (n : ℕ) → B n → A
 ι n x = n , x

 retraction-cases : (m n : ℕ) → B n → is-decidable (n ＝ m) → B m
 retraction-cases m n x (inl e) = transport B e x
 retraction-cases m n x (inr _) = b m

 ρ : (m : ℕ) → A → B m
 ρ m (n , x) = retraction-cases m n x (ℕ-is-discrete n m)

 ρ-on-own-summand : (m : ℕ) (x : B m) → ρ m (ι m x) ＝ x
 ρ-on-own-summand m x = γ (ℕ-is-discrete m m)
  where
   γ : (d : is-decidable (m ＝ m)) → retraction-cases m m x d ＝ x
   γ (inl e) = ap (λ - → transport B - x) (ℕ-is-set e refl)
   γ (inr ν) = 𝟘-elim (ν refl)

\end{code}

The m-th coordinate followed by the retraction onto B m sends u to b m
and v to t m.

\begin{code}

 g : (m : ℕ) → (ℕ → A) → B m
 g m w = ρ m (w m)

 g-on-u : (m : ℕ) → g m u ＝ b m
 g-on-u m = ρ-on-own-summand m (b m)

 g-on-v : (m : ℕ) → g m v ＝ t m
 g-on-v m = ρ-on-own-summand m (t m)

\end{code}

Part 1: zero-shape separation.

\begin{code}

 zero-shapes-of-u-and-v-are-distinct
  : Finite-Height
  → Unbounded-Depth B b t
  → η₀ (ℕ → A) u ≠ η₀ (ℕ → A) v
 zero-shapes-of-u-and-v-are-distinct fh ud e =
  ∥∥-rec 𝟘-is-prop γ (fh (ℕ → A) (Π-is-set fe (λ _ → A-is-set)) u v e)
  where
   γ : (Σ m ꞉ ℕ , q[ m ] u ＝ q[ m ] v) → 𝟘
   γ (m , p) = ∥∥-rec 𝟘-is-prop δ (ud m)
    where
     δ : (Σ n ꞉ ℕ , q[ m ] (b n) ≠ q[ m ] (t n)) → 𝟘
     δ (n , ν) = ν (q[ m ] (b n)              ＝⟨ ap q[ m ] (g-on-u n)⁻¹ ⟩
                    q[ m ] (g n u)            ＝⟨ naturality-at-u ⁻¹ ⟩
                    Q^-map m (g n) (q[ m ] u) ＝⟨ ap (Q^-map m (g n)) p ⟩
                    Q^-map m (g n) (q[ m ] v) ＝⟨ naturality-at-v ⟩
                    q[ m ] (g n v)            ＝⟨ ap q[ m ] (g-on-v n) ⟩
                    q[ m ] (t n)              ∎)
      where
       naturality-at-u = Q^-map-on-units m (g n) u
       naturality-at-v = Q^-map-on-units m (g n) v

\end{code}

Part 2: the coordinates of u and v have the same zero-shape, by
naturality of η₀ along the summand inclusions.

\begin{code}

 coordinates-of-u-and-v-have-equal-zero-shapes
  : ((n : ℕ) → η₀ (B n) (b n) ＝ η₀ (B n) (t n))
  → (n : ℕ) → η₀ A (u n) ＝ η₀ A (v n)
 coordinates-of-u-and-v-have-equal-zero-shapes h n =
  η₀ A (u n)                    ＝⟨ (Π₀-map-on-units (ι n) (b n))⁻¹ ⟩
  Π₀-map (ι n) (η₀ (B n) (b n)) ＝⟨ ap (Π₀-map (ι n)) (h n) ⟩
  Π₀-map (ι n) (η₀ (B n) (t n)) ＝⟨ Π₀-map-on-units (ι n) (t n) ⟩
  η₀ A (v n)                    ∎

\end{code}

The main theorem.

\begin{code}

 κ-is-not-equiv
  : Crisp-Countable-Choice 𝓤
  → Finite-Height
  → @♭ ((n : ℕ) → η₀ (B n) (b n) ＝ η₀ (B n) (t n))
  → Unbounded-Depth B b t
  → ¬ is-equiv (κ A)
 κ-is-not-equiv ccc fh h ud =
  κ-is-not-equiv-if-zero-shapes-separate ccc A u v
   (coordinates-of-u-and-v-have-equal-zero-shapes h)
   (zero-shapes-of-u-and-v-are-distinct fh ud)

\end{code}

In the countermodel the n-th pair is already separated at stage n.
This gives unbounded depth.

\begin{code}

 separation-at-stage-n-gives-unbounded-depth
  : ((n : ℕ) → q[ n ] (b n) ≠ q[ n ] (t n))
  → Unbounded-Depth B b t
 separation-at-stage-n-gives-unbounded-depth d k = ∣ k , d k ∣

\end{code}
