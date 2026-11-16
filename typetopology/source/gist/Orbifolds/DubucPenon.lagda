Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 13 November 2026 (local time). Orbifold gate H10 of Fable's
roadmap [1], for the targets T5a and T5b.

Dubuc–Penon compactness and properness
--------------------------------------

Myers [2, Definition 6.2.1], after Dubuc and Penon: a type K is
Dubuc–Penon compact if for every proposition A and family of
propositions B over K, (∀ k. A ∨ B k) → A ∨ ∀ k. B k; a map f : X → Y is
Dubuc–Penon proper if the inverse image of every Dubuc–Penon compact
subtype of Y is Dubuc–Penon compact. Here the disjunctions are the
truncated ones, and one level is fixed for both targets [3, 4]: the
carriers, the subtypes and the propositions A and B are all in one
universe 𝓤.

  is-DP-compact, is-DP-proper : the definitions, at the level 𝓤 of
  the carrier. T5a and T5b use these two definitions, at the same 𝓤;

  DP-compactness-is-preserved-by-surjections : Myers's Lemma 6.2.2,
  part 2 (in particular, by equivalences);

  singletons-are-DP-compact;

  DP-proper-maps-have-DP-compact-fibres : the direction of Myers's
  Proposition 6.2.4 that the targets use, from the singleton subtypes
  of a set;

  DP-compact-propositions-are-decidable : from Myers's Warning 6.2.3,
  with A = P and B constantly empty.

The converse of Proposition 6.2.4 is not needed and not formalized.

[1] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026.
    references/F01-orbifolds-roadmap-rev2.md
[2] D. J. Myers. Orbifolds as microlinear types in synthetic
    differential cohesive homotopy type theory. arXiv:2205.15887v1.
[3] GPT-6 Astra. Final H9 universe guidance; original T1/T5 release,
    13 November 2026 (UTC).
    references/A29-h9-t1-t5-release.txt
[4] GPT-6 Astra. H10 T5a and T5b implementation preflights,
    13 November 2026 (UTC).
    references/A23-t5a-preflight.txt
    references/A24-t5b-preflight.txt

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc

module gist.Orbifolds.DubucPenon
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
       where

open import UF.Base
open import UF.Equiv
open import UF.ImageAndSurjection pt using (is-surjection)
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open PropositionalTruncation pt

\end{code}

The definitions.

\begin{code}

is-DP-compact : {𝓤 : Universe} → 𝓤 ̇ → 𝓤 ⁺ ̇
is-DP-compact {𝓤} K =
   (A : 𝓤 ̇ ) → is-prop A
 → (B : K → 𝓤 ̇ ) → ((k : K) → is-prop (B k))
 → ((k : K) → A ∨ B k)
 → A ∨ ((k : K) → B k)

is-DP-proper : {𝓤 : Universe} {X Y : 𝓤 ̇ } → (X → Y) → 𝓤 ⁺ ̇
is-DP-proper {𝓤} {X} {Y} f =
   (S : Y → 𝓤 ̇ ) → ((y : Y) → is-prop (S y))
 → is-DP-compact (Σ y ꞉ Y , S y)
 → is-DP-compact (Σ x ꞉ X , S (f x))

\end{code}

Images, singletons, fibres and propositions.

\begin{code}

DP-compactness-is-preserved-by-surjections
 : {𝓤 : Universe} {K L : 𝓤 ̇ } (g : K → L) → is-surjection g
 → is-DP-compact K → is-DP-compact L
DP-compactness-is-preserved-by-surjections g s c A i B j h =
 ∥∥-functor
  (cases inl
         (λ (f : (k : _) → B (g k)) →
           inr (λ l → ∥∥-rec (j l) (λ (k , p) → transport B p (f k)) (s l))))
  (c A i (B ∘ g) (j ∘ g) (h ∘ g))

singletons-are-DP-compact : {𝓤 : Universe} {K : 𝓤 ̇ } → is-singleton K
                          → is-DP-compact K
singletons-are-DP-compact (k₀ , φ) A i B j h =
 ∥∥-functor (cases inl (λ b → inr (λ k → transport B (φ k) b))) (h k₀)

DP-proper-maps-have-DP-compact-fibres
 : {𝓤 : Universe} {X Y : 𝓤 ̇ } (f : X → Y)
 → is-set Y → is-DP-proper f
 → (y : Y) → is-DP-compact (fiber f y)
DP-proper-maps-have-DP-compact-fibres f Y-is-set p y =
 p (λ y' → y' ＝ y) (λ y' → Y-is-set)
  (singletons-are-DP-compact (singleton-types'-are-singletons y))

DP-compact-propositions-are-decidable
 : {𝓤 : Universe} {P : 𝓤 ̇ } → is-prop P → is-DP-compact P → is-decidable P
DP-compact-propositions-are-decidable {𝓤} {P} i c =
 ∥∥-rec (decidability-of-prop-is-prop fe i)
  (cases inl (λ f → inr (λ p → 𝟘-elim (f p))))
  (c P i (λ _ → 𝟘 {𝓤}) (λ _ → 𝟘-is-prop) (λ p → ∣ inl p ∣))

\end{code}
