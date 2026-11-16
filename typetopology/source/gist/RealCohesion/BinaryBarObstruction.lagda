Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 25 October 2026. See the AI disclosure in
gist.RealCohesion.index. The statements follow a gameplan by Codex
(25 October 2026) [2]. The conditions on the bars are abstracted from the
pointless-end countermodel of the research notes [1, Theorem 2.5].

Binary bars and the full fan theorem.

Let b be a predicate on finite binary words, with values in Ω 𝓥.

 * b splits if a word is in b exactly when both of its one-bit
   extensions are.
 * b has the sibling cover property if, for every word, one of its two
   one-bit extensions is in b.
 * b is a bar if every binary sequence has an initial segment in b.
 * b is uniform if there is a bound N such that every binary sequence
   has an initial segment of length at most N in b.

The full fan theorem says that every bar is uniform, for arbitrary
proposition-valued predicates b. We prove, constructively:

 1. A splitting bar with the sibling cover property doesn't omit the
    empty word: ¬¬ b [].

 2. A uniform splitting predicate contains the empty word.

 3. Hence a family of splitting bars, not all of which contain the
    empty word, refutes the full fan theorem.

The first is the delicate step. Assuming ¬ b [], we build a binary
sequence that avoids b, contradicting the bar condition. At a word s
that isn't in b, splitting and the sibling cover give exactly one bit
c with s ⌢ c not in b. So the type of such bits is a proposition, and
the truncated sibling cover can be eliminated into it. Recursion then
builds the sequence. No form of choice, excluded middle or
double-negation shift is used.

The second needs only splitting, which makes b closed under
extensions. A uniform bound N then puts every word of length N in b,
and splitting gives the empty word by backwards induction. The sibling
cover isn't used, so the refutation of the full fan theorem doesn't
need it.

The notions of word, one-bit extension s ⌢ c and initial segment
α ↾ n are those of gist.RealCohesion.Cylinders.

[1] Answers to some open problems in real-cohesive homotopy type
    theory. Research notes, draft of 25 October 2026.
    references/C01-write-up-2026-10-25.tex

[2] Codex. Gameplan for Opus: syntactic refutations of analytic Markov
    and full FAN, 25 October 2026.
    references/C09b-agda-conditional-refutations.md

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc

module gist.RealCohesion.BinaryBarObstruction
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open import MLTT.List hiding ([_])
open import Naturals.Order
open import Notation.Order
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import gist.RealCohesion.Cylinders pt fe
 using (_⌢_ ; _↾_ ; ⌢-++ ; at-most-one-child ; module following-a-branch)

open PropositionalTruncation pt

\end{code}

The four properties of a predicate on words, and the full fan
theorem. Disjunction and existence are propositionally truncated.

\begin{code}

module _ {𝓥 : Universe} (b : List 𝟚 → Ω 𝓥) where

 Splitting : 𝓥 ̇
 Splitting = (s : List 𝟚)
           → b s holds ↔ (b (s ⌢ ₀) holds × b (s ⌢ ₁) holds)

 Sibling-Cover : 𝓥 ̇
 Sibling-Cover = (s : List 𝟚) → b (s ⌢ ₀) holds ∨ b (s ⌢ ₁) holds

 Bar : 𝓥 ̇
 Bar = (α : ℕ → 𝟚) → ∃ n ꞉ ℕ , b (α ↾ n) holds

 Uniform : 𝓥 ̇
 Uniform = ∃ N ꞉ ℕ , ((α : ℕ → 𝟚) → ∃ n ꞉ ℕ , (n ≤ N) × b (α ↾ n) holds)

Full-FAN : (𝓥 : Universe) → 𝓥 ⁺ ̇
Full-FAN 𝓥 = (b : List 𝟚 → Ω 𝓥) → Bar b → Uniform b

\end{code}

From now on, b splits.

\begin{code}

module _ {𝓥 : Universe}
         (b : List 𝟚 → Ω 𝓥)
         (b-splits : Splitting b)
       where

 children-of-members : (s : List 𝟚)
                     → b s holds → b (s ⌢ ₀) holds × b (s ⌢ ₁) holds
 children-of-members s = lr-implication (b-splits s)

 members-from-children : (s : List 𝟚)
                       → b (s ⌢ ₀) holds × b (s ⌢ ₁) holds → b s holds
 members-from-children s = rl-implication (b-splits s)

\end{code}

1. Root density. A false child of a word s is a bit c such that s ⌢ c
is not in b. With the sibling cover, there is at most one.

\begin{code}

 module _ (b-has-sibling-cover : Sibling-Cover b) where

  False-Child : List 𝟚 → 𝓥 ̇
  False-Child s = Σ c ꞉ 𝟚 , ¬ (b (s ⌢ c) holds)

  false-children-are-unique : (s : List 𝟚) → is-prop (False-Child s)
  false-children-are-unique s =
   at-most-one-child (λ s → ¬ (b s holds)) (λ s → negations-are-props fe) s
    (λ ν₀ ν₁ → ∨-elim 𝟘-is-prop ν₀ ν₁ (b-has-sibling-cover s))

\end{code}

A word that is not in b has a false child, because the two children
are not both in b, and one of them is. Since there is at most one
false child, we get it by eliminating the truncated sibling cover.

\begin{code}

  false-child : (s : List 𝟚) → ¬ (b s holds) → False-Child s
  false-child s ν = ∨-elim (false-children-are-unique s) γ₀ γ₁
                     (b-has-sibling-cover s)
   where
    γ₀ : b (s ⌢ ₀) holds → False-Child s
    γ₀ p₀ = ₁ , (λ p₁ → ν (members-from-children s (p₀ , p₁)))

    γ₁ : b (s ⌢ ₁) holds → False-Child s
    γ₁ p₁ = ₀ , (λ p₀ → ν (members-from-children s (p₀ , p₁)))

\end{code}

If the empty word is not in b, following false children gives a
sequence whose initial segments all avoid b (following-a-branch of
gist.RealCohesion.Cylinders). This is a definition by recursion, not a
use of choice.

\begin{code}

  module _ (empty-word-is-not-in-b : ¬ (b [] holds)) where

   open following-a-branch (λ s → ¬ (b s holds)) empty-word-is-not-in-b
    false-child
    using (Node ; next ; path ; path-is-restriction)
    renaming (branch-sequence to avoiding-sequence ;
              on-the-branch to avoiding-sequence-avoids-b)
    public

 empty-word-is-not-not-in-splitting-bar : Sibling-Cover b
                                        → Bar b
                                        → ¬¬ (b [] holds)
 empty-word-is-not-not-in-splitting-bar cover bar ν =
  ∥∥-rec 𝟘-is-prop
   (λ (n , p) → avoiding-sequence-avoids-b cover ν n p)
   (bar (avoiding-sequence cover ν))

\end{code}

2. Uniformity forces the empty word. Splitting makes b closed under
extensions.

\begin{code}

 members-persist : (s r : List 𝟚) → b s holds → b (s ++ r) holds
 members-persist s []      p =
  transport (λ - → b - holds) ([]-right-neutral s) p
 members-persist s (c ∷ r) p = transport (λ - → b - holds) (⌢-++ s c r)
                                (members-persist (s ⌢ c) r (child c))
  where
   child : (d : 𝟚) → b (s ⌢ d) holds
   child ₀ = pr₁ (children-of-members s p)
   child ₁ = pr₂ (children-of-members s p)

\end{code}

Initial segments of a sequence extend each other.

\begin{code}

restriction-extends : (α : ℕ → 𝟚) (n m : ℕ)
                    → n ≤ m
                    → Σ r ꞉ List 𝟚 , α ↾ m ＝ (α ↾ n) ++ r
restriction-extends α n 0        l =
 [] , (ap (α ↾_) (unique-least n l) ⁻¹ ∙ []-right-neutral (α ↾ n))
restriction-extends α n (succ m) l = γ (≤-split n m l)
 where
  γ : (n ≤ m) + (n ＝ succ m) → Σ r ꞉ List 𝟚 , α ↾ succ m ＝ (α ↾ n) ++ r
  γ (inl k) = (r ⌢ α m) , (ap (_⌢ α m) e ∙ ++-assoc (α ↾ n) r (α m ∷ []))
   where
    r : List 𝟚
    r = pr₁ (restriction-extends α n m k)

    e : α ↾ m ＝ (α ↾ n) ++ r
    e = pr₂ (restriction-extends α n m k)
  γ (inr e) = [] , (ap (α ↾_) (e ⁻¹) ∙ []-right-neutral (α ↾ n))

\end{code}

Extending a word by zeros gives a sequence whose initial segment of
the length of the word is the word.

\begin{code}

zero-extension : List 𝟚 → (ℕ → 𝟚)
zero-extension []      n        = ₀
zero-extension (c ∷ s) 0        = c
zero-extension (c ∷ s) (succ n) = zero-extension s n

restriction-of-succ : (α : ℕ → 𝟚) (n : ℕ)
                    → α ↾ succ n ＝ α 0 ∷ ((α ∘ succ) ↾ n)
restriction-of-succ α 0        = refl
restriction-of-succ α (succ n) = ap (_⌢ α (succ n)) (restriction-of-succ α n)

zero-extension-restricts : (s : List 𝟚) → zero-extension s ↾ length s ＝ s
zero-extension-restricts []      = refl
zero-extension-restricts (c ∷ s) =
 restriction-of-succ (zero-extension (c ∷ s)) (length s)
 ∙ ap (c ∷_) (zero-extension-restricts s)

\end{code}

The uniformity of a splitting predicate gives its empty word. We first
show that a word is in b if all its extensions of a fixed length are,
by induction on the length.

\begin{code}

module _ {𝓥 : Universe}
         (b : List 𝟚 → Ω 𝓥)
         (b-splits : Splitting b)
       where

 members-persist-along-restrictions : (α : ℕ → 𝟚) (n m : ℕ)
                                    → n ≤ m
                                    → b (α ↾ n) holds
                                    → b (α ↾ m) holds
 members-persist-along-restrictions α n m l p =
  transport (λ - → b - holds) (pr₂ (restriction-extends α n m l) ⁻¹)
   (members-persist b b-splits (α ↾ n) (pr₁ (restriction-extends α n m l)) p)

 extensions-of-a-length-give-the-word
  : (N : ℕ) (s : List 𝟚)
  → ((r : List 𝟚) → length r ＝ N → b (s ++ r) holds)
  → b s holds
 extensions-of-a-length-give-the-word 0 s h =
  transport (λ - → b - holds) ([]-right-neutral s ⁻¹) (h [] refl)
 extensions-of-a-length-give-the-word (succ N) s h =
  members-from-children b b-splits s (child ₀ , child ₁)
  where
   child : (c : 𝟚) → b (s ⌢ c) holds
   child c = extensions-of-a-length-give-the-word N (s ⌢ c)
              (λ r e → transport (λ - → b - holds) (⌢-++ s c r ⁻¹)
                        (h (c ∷ r) (ap succ e)))

 uniform-gives-empty-word : Uniform b → b [] holds
 uniform-gives-empty-word = ∥∥-rec (holds-is-prop (b [])) γ
  where
   γ : (Σ N ꞉ ℕ , ((α : ℕ → 𝟚) → ∃ n ꞉ ℕ , (n ≤ N) × b (α ↾ n) holds))
     → b [] holds
   γ (N , h) = extensions-of-a-length-give-the-word N [] δ
    where
     δ : (r : List 𝟚) → length r ＝ N → b r holds
     δ r e = ∥∥-rec (holds-is-prop (b r)) ε (h (zero-extension r))
      where
       ε : (Σ n ꞉ ℕ , (n ≤ N) × b (zero-extension r ↾ n) holds) → b r holds
       ε (n , l , p) = transport (λ - → b - holds) I
                        (members-persist-along-restrictions
                          (zero-extension r) n N l p)
        where
         I : zero-extension r ↾ N ＝ r
         I = ap (zero-extension r ↾_) (e ⁻¹) ∙ zero-extension-restricts r

\end{code}

3. The refutation of the full fan theorem. It uses neither the sibling
cover nor any condition on X; in particular X needn't be a set.

\begin{code}

family-of-splitting-bars-refutes-full-FAN
 : {𝓤 𝓥 : Universe}
   (X : 𝓤 ̇ )
   (B : X → List 𝟚 → Ω 𝓥)
 → ((x : X) → Splitting (B x))
 → ((x : X) → Bar (B x))
 → ¬ ((x : X) → B x [] holds)
 → ¬ Full-FAN 𝓥
family-of-splitting-bars-refutes-full-FAN X B splits bar proper fan =
 proper (λ x → uniform-gives-empty-word (B x) (splits x) (fan (B x) (bar x)))

\end{code}
