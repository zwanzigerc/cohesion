Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 25 October 2026. See the AI disclosure in
gist.RealCohesion.index.

Frames with a system of cylinders have no points.

The countermodel of [1, §2] uses the complete Boolean algebra
P = RO(2^ℕ) of regular open subsets of Cantor space as a pointless
locale, and uses the cylinders of finite binary words in P to refute
the full fan theorem [1, Theorem 2.5(ii)]. Here we isolate what these
arguments need. A cylinder system on a frame B assigns to every finite
binary word s an element cyl s of B, with a complement cyl′ s, such
that

 * cyl [] = 𝟏,
 * cyl s = cyl (s ⌢ ₀) ∨ cyl (s ⌢ ₁), where s ⌢ b is s followed by b,
 * cyl (s ⌢ ₀) ∧ cyl (s ⌢ ₁) = 𝟎, and
 * for every sequence α : ℕ → 𝟚, the complements cyl′ (α ↾ n) of the
   cylinders around α have join 𝟏, where α ↾ n is the word
   α 0 , … , α (n-1).

For P = RO(2^ℕ), cyl s is the set of sequences extending s, which is
clopen, and the last condition holds because the meet of the
cylinders around α is the interior of {α}, which is empty. A
constructive example is in gist.RealCohesion.CohenFrame.

We prove, constructively, that a frame with a cylinder system has no
completely prime filters. A completely prime filter picks a unique
branch through the tree of cylinders, and the last condition says that
no branch survives. The paper argues instead that the meet of a
completely prime filter on a complete Boolean algebra is an atom, and
that P has no atoms. That meet is indexed by a large family, which
isn't available predicatively. We also prove that an element below
cyl′ s for every word s of length N is 𝟎. Both facts are used in
gist.RealCohesion.PointlessEnd.

[1] Answers to some open problems in real-cohesive homotopy type
    theory. Research notes, draft of 25 October 2026.
    references/C01-write-up-2026-10-25.tex

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import MLTT.List hiding ([_])
open import UF.FunExt
open import UF.PropTrunc

module gist.RealCohesion.Cylinders
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open import Locales.Complements pt fe
open import Locales.Frame pt fe hiding (𝟚 ; ₀ ; ₁)
open import Locales.Point.Definition pt fe
open import Slice.Family
open import UF.Base
open import UF.Logic
open import UF.Subsingletons
open import UF.SubtypeClassifier
open import UF.UniverseEmbedding

open AllCombinators pt fe hiding (_∨_)
open DefnOfCPF
open PropositionalTruncation pt

\end{code}

Words, and the initial segments of a binary sequence.

\begin{code}

_⌢_ : List 𝟚 → 𝟚 → List 𝟚
s ⌢ b = s ++ (b ∷ [])

infixl 6 _⌢_

_↾_ : (ℕ → 𝟚) → ℕ → List 𝟚
α ↾ 0      = []
α ↾ succ n = (α ↾ n) ⌢ α n

infixl 7 _↾_

length-⌢ : (s : List 𝟚) (b : 𝟚) → length (s ⌢ b) ＝ succ (length s)
length-⌢ []      b = refl
length-⌢ (a ∷ s) b = ap succ (length-⌢ s b)

length-↾ : (α : ℕ → 𝟚) (n : ℕ) → length (α ↾ n) ＝ n
length-↾ α 0        = refl
length-↾ α (succ n) = length-⌢ (α ↾ n) (α n) ∙ ap succ (length-↾ α n)

⌢-++ : (s : List 𝟚) (b : 𝟚) (r : List 𝟚) → (s ⌢ b) ++ r ＝ s ++ (b ∷ r)
⌢-++ s b r = ++-assoc s (b ∷ []) r

\end{code}

Following a branch. If a predicate Q on words holds at the empty word,
and every word in Q has a child in Q, following the children gives a
sequence whose initial segments are all in Q. This is a definition by
recursion, not a use of choice; it is used here and in
gist.RealCohesion.BinaryBarObstruction. The child is unique if no two
siblings are both in Q.

\begin{code}

at-most-one-child : {𝓣 : Universe} (Q : List 𝟚 → 𝓣 ̇ )
                  → ((s : List 𝟚) → is-prop (Q s))
                  → (s : List 𝟚)
                  → (Q (s ⌢ ₀) → Q (s ⌢ ₁) → 𝟘 {𝓤₀})
                  → is-prop (Σ c ꞉ 𝟚 , Q (s ⌢ c))
at-most-one-child Q Q-is-prop s clash (b , h) (c , k) =
 to-subtype-＝ (λ b → Q-is-prop (s ⌢ b)) (γ b c h k)
 where
  γ : (b c : 𝟚) → Q (s ⌢ b) → Q (s ⌢ c) → b ＝ c
  γ ₀ ₀ _  _  = refl
  γ ₀ ₁ h₀ h₁ = 𝟘-elim (clash h₀ h₁)
  γ ₁ ₀ h₁ h₀ = 𝟘-elim (clash h₀ h₁)
  γ ₁ ₁ _  _  = refl

module following-a-branch
        {𝓣 : Universe}
        (Q : List 𝟚 → 𝓣 ̇ )
        (Q-at-the-root : Q [])
        (child : (s : List 𝟚) → Q s → Σ c ꞉ 𝟚 , Q (s ⌢ c))
       where

 Node : 𝓣 ̇
 Node = Σ s ꞉ List 𝟚 , Q s

 next : Node → Node
 next (s , q) = (s ⌢ pr₁ (child s q)) , pr₂ (child s q)

 path : ℕ → Node
 path 0        = [] , Q-at-the-root
 path (succ n) = next (path n)

 branch-sequence : ℕ → 𝟚
 branch-sequence n = pr₁ (child (pr₁ (path n)) (pr₂ (path n)))

 path-is-restriction : (n : ℕ) → pr₁ (path n) ＝ branch-sequence ↾ n
 path-is-restriction 0        = refl
 path-is-restriction (succ n) =
  ap (_⌢ branch-sequence n) (path-is-restriction n)

 on-the-branch : (n : ℕ) → Q (branch-sequence ↾ n)
 on-the-branch n = transport Q (path-is-restriction n) (pr₂ (path n))

\end{code}

Joins in a frame in TypeTopology are indexed by types in the frame's
index universe 𝓦, so we lift ℕ to 𝓦.

\begin{code}

record Cylinder-System (B : Frame 𝓤 𝓥 𝓦) : 𝓤 ̇ where
 field
  cyl                : List 𝟚 → ⟨ B ⟩
  cyl′               : List 𝟚 → ⟨ B ⟩
  cyl-root           : cyl [] ＝ 𝟏[ B ]
  cyl-split          : (s : List 𝟚) → cyl s ＝ cyl (s ⌢ ₀) ∨[ B ] cyl (s ⌢ ₁)
  cyl-disjoint       : (s : List 𝟚) → cyl (s ⌢ ₀) ∧[ B ] cyl (s ⌢ ₁) ＝ 𝟎[ B ]
  cyl′-is-complement : (s : List 𝟚)
                     → is-boolean-complement-of B (cyl′ s) (cyl s) holds
  cyl′-cover         : (α : ℕ → 𝟚)
                     → ⋁[ B ] (Lift 𝓦 ℕ , (λ n → cyl′ (α ↾ lower n)))
                     ＝ 𝟏[ B ]

\end{code}

A completely prime filter on B gives a branch through the cylinders.
We don't need upward closure, and we allow the filter to take values
in any universe 𝓣.

\begin{code}

module _ {B : Frame 𝓤 𝓥 𝓦} (𝒞 : Cylinder-System B) where

 open Cylinder-System 𝒞

 module _ {𝓣 : Universe}
          (ϕ : ⟨ B ⟩ → Ω 𝓣)
          (ϕ-top   : ϕ 𝟏[ B ] holds)
          (ϕ-meet  : (x y : ⟨ B ⟩)
                   → ϕ x holds → ϕ y holds → ϕ (x ∧[ B ] y) holds)
          (ϕ-prime : (S : Fam 𝓦 ⟨ B ⟩)
                   → ϕ (⋁[ B ] S) holds → ∃ i ꞉ index S , ϕ (S [ i ]) holds)
        where

  private
   ϕ-transport : {x y : ⟨ B ⟩} → x ＝ y → ϕ x holds → ϕ y holds
   ϕ-transport = transport (λ - → ϕ - holds)

  ϕ-misses-𝟎 : ¬ (ϕ 𝟎[ B ] holds)
  ϕ-misses-𝟎 h = ∥∥-rec 𝟘-is-prop (λ (i , _) → 𝟘-elim i) (ϕ-prime (∅ 𝓦) h)

  branch-is-unique : (s : List 𝟚) → is-prop (Σ b ꞉ 𝟚 , ϕ (cyl (s ⌢ b)) holds)
  branch-is-unique s =
   at-most-one-child (λ s → ϕ (cyl s) holds) (λ s → holds-is-prop (ϕ (cyl s))) s
    (λ h₀ h₁ → ϕ-misses-𝟎 (ϕ-transport (cyl-disjoint s) (ϕ-meet _ _ h₀ h₁)))

  branch : (s : List 𝟚) → ϕ (cyl s) holds → Σ b ꞉ 𝟚 , ϕ (cyl (s ⌢ b)) holds
  branch s h =
   ∥∥-rec (branch-is-unique s) γ (ϕ-prime S (ϕ-transport (cyl-split s) h))
   where
    S : Fam 𝓦 ⟨ B ⟩
    S = binary-family 𝓦 (cyl (s ⌢ ₀)) (cyl (s ⌢ ₁))

    γ : (Σ i ꞉ index S , ϕ (S [ i ]) holds) → Σ b ꞉ 𝟚 , ϕ (cyl (s ⌢ b)) holds
    γ (inl ⋆ , k) = ₀ , k
    γ (inr ⋆ , k) = ₁ , k

  open following-a-branch (λ s → ϕ (cyl s) holds)
   (ϕ-transport (cyl-root ⁻¹) ϕ-top) branch
   using (Node ; next ; path ; path-is-restriction)
   renaming
    (branch-sequence to path-sequence ; on-the-branch to ϕ-contains-the-path)
   public

  no-completely-prime-filter : 𝟘
  no-completely-prime-filter = ∥∥-rec 𝟘-is-prop γ (ϕ-prime S h)
   where
    α = path-sequence

    S : Fam 𝓦 ⟨ B ⟩
    S = Lift 𝓦 ℕ , (λ n → cyl′ (α ↾ lower n))

    h : ϕ (⋁[ B ] S) holds
    h = ϕ-transport (cyl′-cover α ⁻¹) ϕ-top

    γ : (Σ n ꞉ index S , ϕ (S [ n ]) holds) → 𝟘
    γ (n , k) = ϕ-misses-𝟎
                 (ϕ-transport (pr₁ (cyl′-is-complement (α ↾ lower n)))
                   (ϕ-meet _ _ (ϕ-contains-the-path (lower n)) k))

\end{code}

In particular, the locale of a frame with a cylinder system has no
points in the sense of Locales.Point.Definition.

\begin{code}

frame-to-locale : Frame (𝓤 ⁺) 𝓤 𝓤 → Locale (𝓤 ⁺) 𝓤 𝓤
frame-to-locale L = record { ⟨_⟩ₗ = ⟨ L ⟩ ; frame-str-of = pr₂ L }

cylinder-locales-have-no-points : {B : Frame (𝓤 ⁺) 𝓤 𝓤}
                                → Cylinder-System B
                                → ¬ Point (frame-to-locale B)
cylinder-locales-have-no-points 𝒞 (ϕ , (_ , ϕ-top , ϕ-meet) , ϕ-prime) =
 no-completely-prime-filter 𝒞 ϕ ϕ-top ϕ-meet ϕ-prime

\end{code}

An element below the complements of all cylinders of a fixed length N
is 𝟎. We first prove the version for elements disjoint from these
cylinders, by induction on N. The induction step: an element disjoint
from both children of a cylinder is disjoint from the cylinder.

\begin{code}

module _ {B : Frame 𝓤 𝓥 𝓦} (𝒞 : Cylinder-System B) where

 open Cylinder-System 𝒞
 open PosetNotation (poset-of B)
 open PosetReasoning (poset-of B)

 disjoint-from-both-children : (s : List 𝟚) (x : ⟨ B ⟩)
                             → x ∧[ B ] cyl (s ⌢ ₀) ＝ 𝟎[ B ]
                             → x ∧[ B ] cyl (s ⌢ ₁) ＝ 𝟎[ B ]
                             → x ∧[ B ] cyl s ＝ 𝟎[ B ]
 disjoint-from-both-children s x p₀ p₁ =
  x ∧[ B ] cyl s                                       ＝⟨ I ⟩
  x ∧[ B ] (cyl (s ⌢ ₀) ∨[ B ] cyl (s ⌢ ₁))            ＝⟨ II ⟩
  (x ∧[ B ] cyl (s ⌢ ₀)) ∨[ B ] (x ∧[ B ] cyl (s ⌢ ₁)) ＝⟨ III ⟩
  𝟎[ B ] ∨[ B ] 𝟎[ B ]                                 ＝⟨ IV ⟩
  𝟎[ B ]                                               ∎
   where
    I   = ap (λ - → x ∧[ B ] -) (cyl-split s)
    II  = binary-distributivity B x (cyl (s ⌢ ₀)) (cyl (s ⌢ ₁))
    III = ap₂ (λ a b → a ∨[ B ] b) p₀ p₁
    IV  = 𝟎-left-unit-of-∨ B 𝟎[ B ]

 disjoint-from-all-cylinders-of-length
  : (N : ℕ) (x : ⟨ B ⟩)
  → ((s : List 𝟚) → length s ＝ N → x ∧[ B ] cyl s ＝ 𝟎[ B ])
  → x ＝ 𝟎[ B ]
 disjoint-from-all-cylinders-of-length 0 x h =
  x               ＝⟨ 𝟏-right-unit-of-∧ B x ⁻¹ ⟩
  x ∧[ B ] 𝟏[ B ] ＝⟨ ap (λ - → x ∧[ B ] -) (cyl-root ⁻¹) ⟩
  x ∧[ B ] cyl [] ＝⟨ h [] refl ⟩
  𝟎[ B ]          ∎
 disjoint-from-all-cylinders-of-length (succ N) x h =
  disjoint-from-all-cylinders-of-length N x γ
  where
   γ : (s : List 𝟚) → length s ＝ N → x ∧[ B ] cyl s ＝ 𝟎[ B ]
   γ s p = disjoint-from-both-children s x
            (h (s ⌢ ₀) (length-⌢ s ₀ ∙ ap succ p))
            (h (s ⌢ ₁) (length-⌢ s ₁ ∙ ap succ p))

 below-complement-gives-disjoint : (s : List 𝟚) (x : ⟨ B ⟩)
                                 → (x ≤ cyl′ s) holds
                                 → x ∧[ B ] cyl s ＝ 𝟎[ B ]
 below-complement-gives-disjoint s x l = only-𝟎-is-below-𝟎 B (x ∧[ B ] cyl s) γ
  where
   δ : ((x ∧[ B ] cyl s) ≤ cyl′ s) holds
   δ = x ∧[ B ] cyl s ≤⟨ ∧[ B ]-lower₁ x (cyl s) ⟩
       x              ≤⟨ l ⟩
       cyl′ s         ■

   γ : ((x ∧[ B ] cyl s) ≤ 𝟎[ B ]) holds
   γ = x ∧[ B ] cyl s      ≤⟨ ∧[ B ]-greatest (cyl s) (cyl′ s) (x ∧[ B ] cyl s)
                                 (∧[ B ]-lower₂ x (cyl s)) δ ⟩
       cyl s ∧[ B ] cyl′ s ＝⟨ pr₁ (cyl′-is-complement s) ⟩ₚ
       𝟎[ B ]              ■

 below-all-complements-of-length
  : (N : ℕ) (x : ⟨ B ⟩)
  → ((s : List 𝟚) → length s ＝ N → (x ≤ cyl′ s) holds)
  → x ＝ 𝟎[ B ]
 below-all-complements-of-length N x h =
  disjoint-from-all-cylinders-of-length N x
   (λ s p → below-complement-gives-disjoint s x (h s p))

\end{code}

Cylinders shrink, and their complements grow, along extensions of
words.

\begin{code}

 cylinders-shrink : (b : 𝟚) (s : List 𝟚) → (cyl (s ⌢ b) ≤ cyl s) holds
 cylinders-shrink ₀ s =
  cyl (s ⌢ ₀)
   ≤⟨ ∨[ B ]-upper₁ (cyl (s ⌢ ₀)) (cyl (s ⌢ ₁)) ⟩
  cyl (s ⌢ ₀) ∨[ B ] cyl (s ⌢ ₁)    ＝⟨ cyl-split s ⁻¹ ⟩ₚ
  cyl s                             ■
 cylinders-shrink ₁ s =
  cyl (s ⌢ ₁)
   ≤⟨ ∨[ B ]-upper₂ (cyl (s ⌢ ₀)) (cyl (s ⌢ ₁)) ⟩
  cyl (s ⌢ ₀) ∨[ B ] cyl (s ⌢ ₁)    ＝⟨ cyl-split s ⁻¹ ⟩ₚ
  cyl s                             ■

 complements-are-antitone : (a a′ c c′ : ⟨ B ⟩)
                          → (a ≤ a′) holds
                          → a ∨[ B ] c ＝ 𝟏[ B ]
                          → a′ ∧[ B ] c′ ＝ 𝟎[ B ]
                          → (c′ ≤ c) holds
 complements-are-antitone a a′ c c′ l p q =
  c′                                 ＝⟨ 𝟏-right-unit-of-∧ B c′ ⁻¹ ⟩ₚ
  c′ ∧[ B ] 𝟏[ B ]                   ＝⟨ ap (λ - → c′ ∧[ B ] -) (p ⁻¹) ⟩ₚ
  c′ ∧[ B ] (a ∨[ B ] c)             ＝⟨ binary-distributivity B c′ a c ⟩ₚ
  (c′ ∧[ B ] a) ∨[ B ] (c′ ∧[ B ] c) ≤⟨ ∨[ B ]-least γ (∧[ B ]-lower₂ c′ c) ⟩
  c                                  ■
  where
   δ : ((c′ ∧[ B ] a) ≤ a′) holds
   δ = c′ ∧[ B ] a ≤⟨ ∧[ B ]-lower₂ c′ a ⟩
       a           ≤⟨ l ⟩
       a′          ■

   γ : ((c′ ∧[ B ] a) ≤ c) holds
   γ =
    c′ ∧[ B ] a  ≤⟨ ∧[ B ]-greatest a′ c′ (c′ ∧[ B ] a) δ (∧[ B ]-lower₁ c′ a) ⟩
       a′ ∧[ B ] c′ ＝⟨ q ⟩ₚ
       𝟎[ B ]       ≤⟨ 𝟎-is-bottom B c ⟩
       c            ■

 complements-grow : (b : 𝟚) (s : List 𝟚) → (cyl′ s ≤ cyl′ (s ⌢ b)) holds
 complements-grow b s =
  complements-are-antitone
   (cyl (s ⌢ b)) (cyl s) (cyl′ (s ⌢ b)) (cyl′ s)
   (cylinders-shrink b s)
   (pr₂ (cyl′-is-complement (s ⌢ b)))
   (pr₁ (cyl′-is-complement s))

 complements-grow-along-extensions : (s r : List 𝟚)
                                   → (cyl′ s ≤ cyl′ (s ++ r)) holds
 complements-grow-along-extensions s []      =
  cyl′ s        ＝⟨ ap cyl′ ([]-right-neutral s) ⟩ₚ
  cyl′ (s ++ []) ■
 complements-grow-along-extensions s (b ∷ r) =
  cyl′ s              ≤⟨ complements-grow b s ⟩
  cyl′ (s ⌢ b)        ≤⟨ complements-grow-along-extensions (s ⌢ b) r ⟩
  cyl′ ((s ⌢ b) ++ r) ＝⟨ ap cyl′ (⌢-++ s b r) ⟩ₚ
  cyl′ (s ++ b ∷ r)   ■

\end{code}
