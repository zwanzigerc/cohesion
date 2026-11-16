Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 25 October 2026. See the AI disclosure in
gist.RealCohesion.index. Following a gameplan by GPT-6 Astra
(25 October 2026) [2].

The Boolean cocycle on the kernel of a crisp function g : ℝ → ℝ.

Let N be the kernel relation of g, the set of pairs (p , q) with
g p ＝ g q. On its crisp points we have the function

  h (p , q) = δ p ⊕ δ q,

where δ t is ₁ if t ＝ 0 and ₀ otherwise. This is defined by crisp
excluded middle, and only for crisp t: we never decide whether an
arbitrary real number is 0. The function h is the mod 2 reduction of
the integer invariant [q = 0] - [p = 0] of the research notes [1,
Lemma 5.2].

If h is invariant along crisp real paths in N, unique real-path
descent (gist.RealCohesion.RealPathDescent) extends it to a function
c : N → 𝟚, defined at all points. We show that c is a cocycle:

  c (p , q) ⊕ c (q , r) ＝ c (p , r)

for all triples of points at equal height, not only crisp ones. Both
sides are extensions of the same function on the crisp triples,
because δ q ⊕ δ q = ₀, so they are equal by the uniqueness half of
descent. Finally, if g 1 ＝ g 0, then c takes the value ₁ at (1 , 0),
because δ 1 = ₀ and δ 0 = ₁. We transfer c to the kernel of the
corestriction of g to its image, in the form used by
gist.RealCohesion.BooleanCocycleObstruction.

The invariance of h is a hypothesis here, proved for a concrete g by
an analytic argument elsewhere.

[1] Answers to some open problems in real-cohesive homotopy type
    theory. Research notes, draft of 25 October 2026.
    references/C01-write-up-2026-10-25.tex

[2] GPT-6 Astra. Gameplan for Opus: a subset of the Dedekind reals
    whose shape is not a set, 25 October 2026.
    references/A32-subset-shape-gameplan.md

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.RealKernelCocycle
        (@♭ fe : Fun-Ext)
        (@♭ pe : Prop-Ext)
        (@♭ pt : propositional-truncations-exist)
       where

open import MLTT.Two-Properties
open import UF.Base
open import UF.ImageAndSurjection pt
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties
open import DedekindReals.Order fe pe pt
open import DedekindReals.Type fe pe pt
open import gist.CohesiveApartness.Flat
open import gist.RealCohesion.CrispDecisions
open import gist.RealCohesion.RealPathDescent fe pe pt

\end{code}

Boolean arithmetic.

\begin{code}

⊕-cancel-middle : (a b c : 𝟚) → (a ⊕ b) ⊕ (b ⊕ c) ＝ a ⊕ c
⊕-cancel-middle a b c = ⊕-assoc {a} {b} ∙ ap (a ⊕_) (⊕-involutive {b})

1ℝ-is-not-0ℝ : 1ℝ ≠ 0ℝ
1ℝ-is-not-0ℝ e =
 apartness-gives-inequality 0ℝ 1ℝ ℝ-zero-apart-from-one (e ⁻¹)

\end{code}

The zero indicator on crisp real numbers, from crisp excluded middle
(gist.RealCohesion.CrispDecisions). We make the proofs that equalities
of real numbers are propositions abstract: nothing computes with them,
and unfolding them makes type checking very slow.

\begin{code}

abstract
 equalities-of-reals-are-equal : {x y : ℝ} (e e' : x ＝ y) → e ＝ e'
 equalities-of-reals-are-equal = ℝ-is-set

module _ (@♭ cem : Crisp-EM 𝓤₁) where

 δ : ♭ ℝ → 𝟚
 δ (t ^♭) = crisp-test cem (λ x → x ＝ 0ℝ) (λ _ → ℝ-is-set) t

 δ-at-0 : δ (0ℝ ^♭) ＝ ₁
 δ-at-0 = crisp-test-yes cem (λ x → x ＝ 0ℝ) (λ _ → ℝ-is-set) 0ℝ refl

 δ-at-1 : δ (1ℝ ^♭) ＝ ₀
 δ-at-1 = crisp-test-no cem (λ x → x ＝ 0ℝ) (λ _ → ℝ-is-set) 1ℝ 1ℝ-is-not-0ℝ

\end{code}

The kernel of g, the triples at equal height, and the functions on
their crisp points.

\begin{code}

 module _ (@♭ g : ℝ → ℝ) where

  N : 𝓤₁ ̇
  N = Σ (p , q) ꞉ ℝ × ℝ , g p ＝ g q

  abstract
   N-is-set : is-set N
   N-is-set =
    Σ-is-set (×-is-set ℝ-is-set ℝ-is-set) (λ _ → props-are-sets ℝ-is-set)

  h : ♭ N → 𝟚
  h (w ^♭) = δ ((pr₁ (pr₁ w)) ^♭) ⊕ δ ((pr₂ (pr₁ w)) ^♭)

  N₂ : 𝓤₁ ̇
  N₂ = Σ (p , q , r) ꞉ ℝ × ℝ × ℝ , (g p ＝ g q) × (g q ＝ g r)

  abstract
   N₂-is-set : is-set N₂
   N₂-is-set = Σ-is-set (×-is-set ℝ-is-set (×-is-set ℝ-is-set ℝ-is-set))
                        (λ _ → props-are-sets (×-is-prop ℝ-is-set ℝ-is-set))

  first-pair second-pair outer-pair : N₂ → N
  first-pair  ((p , q , r) , e , e') = (p , q) , e
  second-pair ((p , q , r) , e , e') = (q , r) , e'
  outer-pair  ((p , q , r) , e , e') = (p , r) , (e ∙ e')

  h₂ : ♭ N₂ → 𝟚
  h₂ (w ^♭) = h ((outer-pair w) ^♭)

\end{code}

The image T of g, a subtype of ℝ, and the corestriction q of g, which
is a surjection.

\begin{code}

  T : 𝓤₁ ̇
  T = image g

  T-is-set : is-set T
  T-is-set = image-is-set g ℝ-is-set

  q : ℝ → T
  q = corestriction g

  q-is-surjection : is-surjection q
  q-is-surjection = corestrictions-are-surjections g

\end{code}

From now on, h is invariant along crisp real paths, and descent holds.
Then so is the function on triples, by projection to the outer pair.

\begin{code}

  module _ (@♭ descent : Unique-Boolean-Real-Path-Descent 𝓤₁)
           (@♭ h-is-invariant : Real-Path-Invariant N h)
         where

   h₂-is-invariant : Real-Path-Invariant N₂ h₂
   h₂-is-invariant γ = h-is-invariant (λ t → outer-pair (γ t))

\end{code}

Given a crisp extension c of h, the two functions on triples below
extend h₂, hence agree everywhere. This is the cocycle law.

\begin{code}

   module _ (@♭ 𝓒 : Boolean-Extension N h) where

    c : N → 𝟚
    c = pr₁ 𝓒

    c-extends-h : (@♭ w : N) → c w ＝ h (w ^♭)
    c-extends-h w = pr₂ 𝓒 (w ^♭)

    c-on-triples c-on-outer-pairs : N₂ → 𝟚
    c-on-triples w = c (first-pair w) ⊕ c (second-pair w)
    c-on-outer-pairs w = c (outer-pair w)

    c-on-triples-extends-h₂ : (u : ♭ N₂) → c-on-triples (♭-counit u) ＝ h₂ u
    c-on-triples-extends-h₂ (w ^♭) =
     c (first-pair w) ⊕ c (second-pair w)               ＝⟨ I ⟩
     h ((first-pair w) ^♭) ⊕ h ((second-pair w) ^♭)     ＝⟨ II ⟩
     h₂ (w ^♭)                                           ∎
     where
      I  = ap₂ _⊕_ (c-extends-h (first-pair w)) (c-extends-h (second-pair w))
      II = ⊕-cancel-middle (δ ((pr₁ (pr₁ w)) ^♭))
                           (δ ((pr₁ (pr₂ (pr₁ w))) ^♭))
                           (δ ((pr₂ (pr₂ (pr₁ w))) ^♭))

    c-on-outer-pairs-extends-h₂ : (u : ♭ N₂)
                                → c-on-outer-pairs (♭-counit u) ＝ h₂ u
    c-on-outer-pairs-extends-h₂ (w ^♭) = c-extends-h (outer-pair w)

    c-is-cocycle-on-triples : (w : N₂) → c-on-triples w ＝ c-on-outer-pairs w
    c-is-cocycle-on-triples =
     crisp-extensions-agree descent N₂-is-set h₂-is-invariant
      (c-on-triples , c-on-triples-extends-h₂)
      (c-on-outer-pairs , c-on-outer-pairs-extends-h₂)

\end{code}

The cocycle on the kernel of the corestriction q, its cocycle law, and
its value ₁ at (1 , 0) when g 1 ＝ g 0.

\begin{code}

    kernel-cocycle : (x y : ℝ) → q x ＝ q y → 𝟚
    kernel-cocycle x y e = c ((x , y) , ap pr₁ e)

    kernel-cocycle-is-cocycle
     : (x y z : ℝ) (e : q x ＝ q y) (e' : q y ＝ q z)
     → kernel-cocycle x y e ⊕ kernel-cocycle y z e'
     ＝ kernel-cocycle x z (e ∙ e')
    kernel-cocycle-is-cocycle x y z e e' =
     c-is-cocycle-on-triples ((x , y , z) , ap pr₁ e , ap pr₁ e')
     ∙ ap (λ - → c ((x , z) , -)) (equalities-of-reals-are-equal _ _)

    module _ (@♭ g-at-1-is-g-at-0 : g 1ℝ ＝ g 0ℝ) where

     kernel-pair-at-1-and-0 : q 1ℝ ＝ q 0ℝ
     kernel-pair-at-1-and-0 =
      to-subtype-＝ (λ _ → being-in-the-image-is-prop _ g)
                                            g-at-1-is-g-at-0

     kernel-cocycle-at-1-and-0 : kernel-cocycle 1ℝ 0ℝ kernel-pair-at-1-and-0 ＝ ₁
     kernel-cocycle-at-1-and-0 =
      c ((1ℝ , 0ℝ) , ap pr₁ kernel-pair-at-1-and-0) ＝⟨ I ⟩
      c ((1ℝ , 0ℝ) , g-at-1-is-g-at-0)            ＝⟨ c-extends-h _ ⟩
      δ (1ℝ ^♭) ⊕ δ (0ℝ ^♭)                       ＝⟨ ap₂ _⊕_ δ-at-1 δ-at-0 ⟩
      ₀ ⊕ ₁                                       ＝⟨ refl ⟩
      ₁                                           ∎
      where
       I = ap (λ - → c ((1ℝ , 0ℝ) , -)) (equalities-of-reals-are-equal _ _)

\end{code}
