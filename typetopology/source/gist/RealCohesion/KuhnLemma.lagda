Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 11 and 12 November 2026; the statement moved to
gist.RealCohesion.KuhnStatement on 13 November 2026, in the
consolidation after the final audits. See the AI disclosure in
gist.RealCohesion.index.

Kuhn's cubical lemma in dimensions 0, 1 and 2.

The proof of Corollary 3.7 of the write-up [1] uses a cubical form of
Sperner's lemma, due to Kuhn [2], in the form in which it serves the
formal proofs of Brouwer's theorem [3]: let N ≥ 1, and let every point
k of {0, …, N}ⁿ carry bits l₁(k), …, lₙ(k) such that lᵢ(k) = 0
whenever kᵢ = 0 and lᵢ(k) = 1 whenever kᵢ = N; then there is a point q
of {0, …, N - 1}ⁿ such that, for every i, the bit lᵢ takes both values
on the 2ⁿ points of q + {0, 1}ⁿ.

Kuhn-Lemma n is that statement with N written as p + 1, so that no
hypothesis N ≥ 1 is needed, with the corners of the unit cube at q
written as corner q r for r : Fin n → 𝟚, and with the existence given
as a Σ. It is the statement of the same name in Claude Fable 5.2's
starter module gist.RealCohesion.BrouwerStatements, which follows
Isabelle's kuhn_lemma [3]. The statement depends on the function bit
from 𝟚 to ℕ only through corner, so it is stated for any such function
(Kuhn-Lemma-with), and Kuhn-Lemma is the instance for bit. Kuhn's
lemma involves neither real numbers nor modalities, and this module
does not use --cohesion. The five definitions of the statement were
first made here. On 13 November 2026 they moved unchanged to
gist.RealCohesion.KuhnStatement, so that
gist.RealCohesion.BrouwerStatements, which uses --cohesion, states the
lemma with the same constants without importing the proofs below; both
modules name them by typed aliases.

We prove the cases n = 0 and n = 1, as gate G10 of Fable's blueprint
addendum [4, §5.3] asks, and n = 2, gate G13. For n = 0 there is
nothing to prove. For n = 1, a sequence of bits on {0, …, p + 1} that
starts with ₀ and ends with ₁ changes from ₀ to ₁ somewhere, by
induction on p. For n = 2 we follow the addendum's parity argument,
described below; it uses function extensionality, which kuhn-lemma-2
takes as a hypothesis. General n, the last item of gate G14 of the
second addendum, is gist.RealCohesion.KuhnLemmaGeneral.

[1] Answers to some open problems in real-cohesive homotopy type
    theory. Research notes, seventh revision of 11 November 2026,
    proof of Corollary 3.7.
    references/C03-write-up-2026-11-11-seventh.tex
    references/C03a-write-up-seventh-README.txt

[2] Harold W. Kuhn. Some combinatorial lemmas in topology. IBM Journal
    of Research and Development 4(5), 518–524, 1960.

[3] John Harrison's proof, translated from HOL Light to Isabelle/HOL by
    Robert Himmelmann: lemma kuhn_lemma of Brouwer_Fixpoint.thy
    (src/HOL/Analysis), at revision
    87958a2e5f99606413f8c4f3af90935a5ac33110 of the Isabelle mirror.

[4] Claude Fable 5.2. Formalization blueprint, addendum, revision 4 of
    11 November 2026.
    references/F14-brouwer-addendum-rev4.md

\begin{code}

{-# OPTIONS --safe --without-K #-}

module gist.RealCohesion.KuhnLemma where

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Fin.Type
open import Naturals.Addition renaming (_+_ to _+ℕ_)
open import Naturals.Order
open import Notation.Order
open import MLTT.Two-Properties using (_⊕_ ; Lemma[b⊕b＝₀] ; zero-is-not-one)
open import UF.Base using (ap₂ ; transport₂)
open import UF.FunExt
import gist.RealCohesion.KuhnStatement as KS

\end{code}

The statement, for any function b from 𝟚 to ℕ in the corners, and its
instance for bit: typed aliases of the definitions corner-with,
Kuhn-Lemma-with, bit, corner and Kuhn-Lemma of
gist.RealCohesion.KuhnStatement, so that the names of this module keep
their types, and the types that mention them keep their printed form.

\begin{code}

corner-with : (𝟚 → ℕ) → {n : ℕ} → (Fin n → ℕ) → (Fin n → 𝟚) → Fin n → ℕ
corner-with = KS.corner-with

Kuhn-Lemma-with : (𝟚 → ℕ) → ℕ → 𝓤₀ ̇
Kuhn-Lemma-with = KS.Kuhn-Lemma-with

bit : 𝟚 → ℕ
bit = KS.bit

corner : {n : ℕ} → (Fin n → ℕ) → (Fin n → 𝟚) → Fin n → ℕ
corner = KS.corner

Kuhn-Lemma : ℕ → 𝓤₀ ̇
Kuhn-Lemma = KS.Kuhn-Lemma

\end{code}

Dimension 0: Fin 0 is empty.

\begin{code}

kuhn-lemma-0 : Kuhn-Lemma 0
kuhn-lemma-0 p ℓ lower upper =
 (λ i → 𝟘-elim i) , (λ i → 𝟘-elim i) , (λ i → 𝟘-elim i)

\end{code}

Dimension 1. A sequence of bits that is ₀ at 0 and ₁ at p + 1 changes
from ₀ to ₁ between some k ≤ p and k + 1.

\begin{code}

bits-change : (b : ℕ → 𝟚) (p : ℕ)
            → b 0 ＝ ₀ → b (succ p) ＝ ₁
            → Σ k ꞉ ℕ , (k ≤ p) × (b k ＝ ₀) × (b (succ k) ＝ ₁)
bits-change b 0        e₀ e₁ = 0 , ⋆ , e₀ , e₁
bits-change b (succ p) e₀ e₁ = γ (b (succ p)) refl
 where
  γ : (c : 𝟚) → b (succ p) ＝ c
    → Σ k ꞉ ℕ , (k ≤ succ p) × (b k ＝ ₀) × (b (succ k) ＝ ₁)
  γ ₀ e = succ p , ≤-refl p , e , e₁
  γ ₁ e = k , ≤-trans k p (succ p) l (≤-succ p) , d
   where
    k : ℕ
    k = pr₁ (bits-change b p e₀ e)

    l : k ≤ p
    l = pr₁ (pr₂ (bits-change b p e₀ e))

    d : (b k ＝ ₀) × (b (succ k) ＝ ₁)
    d = pr₂ (pr₂ (bits-change b p e₀ e))

\end{code}

In dimension 1 a grid point is a function on Fin 1, which has the one
element 𝟎, and the unit cube at q has the two corners q and q + 1.

\begin{code}

kuhn-lemma-1 : Kuhn-Lemma 1
kuhn-lemma-1 p ℓ lower upper = (λ _ → k) , (λ _ → l) , γ
 where
  b : ℕ → 𝟚
  b k = ℓ (λ _ → k) 𝟎

  change : Σ k ꞉ ℕ , (k ≤ p) × (b k ＝ ₀) × (b (succ k) ＝ ₁)
  change = bits-change b p
            (lower (λ _ → 0) (λ _ → ⋆) 𝟎 refl)
            (upper (λ _ → succ p) (λ _ → ≤-refl p) 𝟎 refl)

  k : ℕ
  k = pr₁ change

  l : k ≤ p
  l = pr₁ (pr₂ change)

  γ : (i : Fin 1)
    → Σ r ꞉ (Fin 1 → 𝟚) , Σ s ꞉ (Fin 1 → 𝟚)
      , (ℓ (corner (λ _ → k) r) i ＝ ₀) × (ℓ (corner (λ _ → k) s) i ＝ ₁)
  γ 𝟎       =
   (λ _ → ₀) , (λ _ → ₁) , pr₁ (pr₂ (pr₂ change)) , pr₂ (pr₂ (pr₂ change))
  γ (suc i) = 𝟘-elim i

\end{code}

Dimension 2, gate G13 of the addendum [4, §5.3], by Fable's parity
argument. Give every point of the grid a tag: τ₀ if its first label is
₁, τ₁ if its first label is ₀ and its second ₁, and τ₂ if both are ₀.
A unit square on whose corners all three tags occur is a Kuhn square:
τ₀ and τ₁ give both values of the first label, and τ₁ and τ₂ both
values of the second. Cut every unit square along the diagonal from q
to q + (1 , 1), and call an edge a door if its ends have the tags τ₀
and τ₁.

 1. A triangle has an odd number of doors if and only if all three
    tags occur on it (odd-triangle, 27 cases).
 2. For each square, the door counts of its two triangles add up,
    modulo 2, to the doors among its four sides, because the diagonal
    is counted twice (square-is-its-sides).
 3. Summing over a row, the vertical sides shared by neighbours cancel;
    summing the rows, the horizontal ones cancel. So the sum over all
    triangles is the number of doors on the boundary, modulo 2.
 4. The bottom side carries only τ₀ and τ₂, the left side only τ₁ and
    τ₂, and the right side only τ₀, so they have no doors. The top side
    carries only τ₀ and τ₁, with τ₁ at its left end and τ₀ at its right
    end, so its doors are odd in number.
 5. So the sum over all triangles is 1, and some triangle carries all
    three tags.

The sums are iterated exclusive-or over ℕ-indexed rows and columns.
The same grid point is a corner of several unit squares, written with
different functions Fin 2 → ℕ; function extensionality identifies its
labels, so the lemma takes it as a hypothesis.

\begin{code}

xor-sum : (ℕ → 𝟚) → ℕ → 𝟚
xor-sum f 0        = ₀
xor-sum f (succ n) = xor-sum f n ⊕ f n

xor-right-unit : (b : 𝟚) → b ⊕ ₀ ＝ b
xor-right-unit ₀ = refl
xor-right-unit ₁ = refl

xor-swap : (a b c d : 𝟚) → (a ⊕ b) ⊕ (c ⊕ d) ＝ (a ⊕ c) ⊕ (b ⊕ d)
xor-swap ₀ ₀ ₀ ₀ = refl
xor-swap ₀ ₀ ₀ ₁ = refl
xor-swap ₀ ₀ ₁ ₀ = refl
xor-swap ₀ ₀ ₁ ₁ = refl
xor-swap ₀ ₁ ₀ ₀ = refl
xor-swap ₀ ₁ ₀ ₁ = refl
xor-swap ₀ ₁ ₁ ₀ = refl
xor-swap ₀ ₁ ₁ ₁ = refl
xor-swap ₁ ₀ ₀ ₀ = refl
xor-swap ₁ ₀ ₀ ₁ = refl
xor-swap ₁ ₀ ₁ ₀ = refl
xor-swap ₁ ₀ ₁ ₁ = refl
xor-swap ₁ ₁ ₀ ₀ = refl
xor-swap ₁ ₁ ₀ ₁ = refl
xor-swap ₁ ₁ ₁ ₀ = refl
xor-swap ₁ ₁ ₁ ₁ = refl

xor-cancel-middle : (a b c : 𝟚) → (a ⊕ b) ⊕ (b ⊕ c) ＝ a ⊕ c
xor-cancel-middle ₀ ₀ ₀ = refl
xor-cancel-middle ₀ ₀ ₁ = refl
xor-cancel-middle ₀ ₁ ₀ = refl
xor-cancel-middle ₀ ₁ ₁ = refl
xor-cancel-middle ₁ ₀ ₀ = refl
xor-cancel-middle ₁ ₀ ₁ = refl
xor-cancel-middle ₁ ₁ ₀ = refl
xor-cancel-middle ₁ ₁ ₁ = refl

xor-square : (a b c d e : 𝟚) → ((a ⊕ b) ⊕ e) ⊕ ((c ⊕ d) ⊕ e) ＝ (a ⊕ d) ⊕ (c ⊕ b)
xor-square ₀ ₀ ₀ ₀ ₀ = refl
xor-square ₀ ₀ ₀ ₀ ₁ = refl
xor-square ₀ ₀ ₀ ₁ ₀ = refl
xor-square ₀ ₀ ₀ ₁ ₁ = refl
xor-square ₀ ₀ ₁ ₀ ₀ = refl
xor-square ₀ ₀ ₁ ₀ ₁ = refl
xor-square ₀ ₀ ₁ ₁ ₀ = refl
xor-square ₀ ₀ ₁ ₁ ₁ = refl
xor-square ₀ ₁ ₀ ₀ ₀ = refl
xor-square ₀ ₁ ₀ ₀ ₁ = refl
xor-square ₀ ₁ ₀ ₁ ₀ = refl
xor-square ₀ ₁ ₀ ₁ ₁ = refl
xor-square ₀ ₁ ₁ ₀ ₀ = refl
xor-square ₀ ₁ ₁ ₀ ₁ = refl
xor-square ₀ ₁ ₁ ₁ ₀ = refl
xor-square ₀ ₁ ₁ ₁ ₁ = refl
xor-square ₁ ₀ ₀ ₀ ₀ = refl
xor-square ₁ ₀ ₀ ₀ ₁ = refl
xor-square ₁ ₀ ₀ ₁ ₀ = refl
xor-square ₁ ₀ ₀ ₁ ₁ = refl
xor-square ₁ ₀ ₁ ₀ ₀ = refl
xor-square ₁ ₀ ₁ ₀ ₁ = refl
xor-square ₁ ₀ ₁ ₁ ₀ = refl
xor-square ₁ ₀ ₁ ₁ ₁ = refl
xor-square ₁ ₁ ₀ ₀ ₀ = refl
xor-square ₁ ₁ ₀ ₀ ₁ = refl
xor-square ₁ ₁ ₀ ₁ ₀ = refl
xor-square ₁ ₁ ₀ ₁ ₁ = refl
xor-square ₁ ₁ ₁ ₀ ₀ = refl
xor-square ₁ ₁ ₁ ₀ ₁ = refl
xor-square ₁ ₁ ₁ ₁ ₀ = refl
xor-square ₁ ₁ ₁ ₁ ₁ = refl

xor-is-one : (a b : 𝟚) → a ⊕ b ＝ ₁ → (a ＝ ₁) ∔ (b ＝ ₁)
xor-is-one ₀ ₀ ()
xor-is-one ₀ ₁ e = inr refl
xor-is-one ₁ ₀ e = inl refl
xor-is-one ₁ ₁ ()

xor-sum-ext : (f g : ℕ → 𝟚) → f ∼ g → (n : ℕ) → xor-sum f n ＝ xor-sum g n
xor-sum-ext f g e 0        = refl
xor-sum-ext f g e (succ n) = ap₂ _⊕_ (xor-sum-ext f g e n) (e n)

below-succ : (k n : ℕ) → k < n → k < succ n
below-succ k n l = ≤-trans (succ k) n (succ n) l (≤-succ n)

xor-sum-below : (f g : ℕ → 𝟚) (n : ℕ)
              → ((k : ℕ) → k < n → f k ＝ g k) → xor-sum f n ＝ xor-sum g n
xor-sum-below f g 0        e = refl
xor-sum-below f g (succ n) e =
 ap₂ _⊕_ (xor-sum-below f g n (λ k l → e k (below-succ k n l))) (e n (<-succ n))

xor-sum-of-zeros : (f : ℕ → 𝟚) (n : ℕ) → ((k : ℕ) → k < n → f k ＝ ₀)
                 → xor-sum f n ＝ ₀
xor-sum-of-zeros f 0        e = refl
xor-sum-of-zeros f (succ n) e =
 ap₂ _⊕_ (xor-sum-of-zeros f n (λ k l → e k (below-succ k n l)))
  (e n (<-succ n))

xor-sum-of-xor : (f g : ℕ → 𝟚) (n : ℕ)
               → xor-sum (λ k → f k ⊕ g k) n ＝ xor-sum f n ⊕ xor-sum g n
xor-sum-of-xor f g 0        = refl
xor-sum-of-xor f g (succ n) = ap (_⊕ (f n ⊕ g n)) (xor-sum-of-xor f g n)
                            ∙ xor-swap (xor-sum f n) (xor-sum g n) (f n) (g n)

xor-sum-telescopes : (g : ℕ → 𝟚) (n : ℕ)
                   → xor-sum (λ k → g k ⊕ g (succ k)) n ＝ g 0 ⊕ g n
xor-sum-telescopes g 0        = Lemma[b⊕b＝₀] {g 0} ⁻¹
xor-sum-telescopes g (succ n) =
 ap (_⊕ (g n ⊕ g (succ n))) (xor-sum-telescopes g n)
                              ∙ xor-cancel-middle (g 0) (g n) (g (succ n))

odd-xor-sum : (f : ℕ → 𝟚) (n : ℕ) → xor-sum f n ＝ ₁
            → Σ k ꞉ ℕ , (k < n) × (f k ＝ ₁)
odd-xor-sum f 0        e = 𝟘-elim (zero-is-not-one e)
odd-xor-sum f (succ n) e = γ (xor-is-one (xor-sum f n) (f n) e)
 where
  γ : (xor-sum f n ＝ ₁) ∔ (f n ＝ ₁) → Σ k ꞉ ℕ , (k < succ n) × (f k ＝ ₁)
  γ (inl d) = k , below-succ k n (pr₁ (pr₂ IH)) , pr₂ (pr₂ IH)
   where
    IH : Σ k ꞉ ℕ , (k < n) × (f k ＝ ₁)
    IH = odd-xor-sum f n d

    k : ℕ
    k = pr₁ IH
  γ (inr d) = n , <-succ n , d

\end{code}

The tags and the doors.

\begin{code}

data Tag : 𝓤₀ ̇ where
 τ₀ τ₁ τ₂ : Tag

tag : 𝟚 → 𝟚 → Tag
tag ₁ b = τ₀
tag ₀ ₁ = τ₁
tag ₀ ₀ = τ₂

door : Tag → Tag → 𝟚
door τ₀ τ₀ = ₀
door τ₀ τ₁ = ₁
door τ₀ τ₂ = ₀
door τ₁ τ₀ = ₁
door τ₁ τ₁ = ₀
door τ₁ τ₂ = ₀
door τ₂ τ₀ = ₀
door τ₂ τ₁ = ₀
door τ₂ τ₂ = ₀

Among : Tag → Tag → Tag → Tag → 𝓤₀ ̇
Among t u v w = (u ＝ t) ∔ (v ＝ t) ∔ (w ＝ t)

odd-triangle : (u v w : Tag) → (door u v ⊕ door v w) ⊕ door u w ＝ ₁
             → Among τ₀ u v w × Among τ₁ u v w × Among τ₂ u v w
odd-triangle τ₀ τ₀ τ₀ ()
odd-triangle τ₀ τ₀ τ₁ ()
odd-triangle τ₀ τ₀ τ₂ ()
odd-triangle τ₀ τ₁ τ₀ ()
odd-triangle τ₀ τ₁ τ₁ ()
odd-triangle τ₀ τ₁ τ₂ _ = inl refl , inr (inl refl) , inr (inr refl)
odd-triangle τ₀ τ₂ τ₀ ()
odd-triangle τ₀ τ₂ τ₁ _ = inl refl , inr (inr refl) , inr (inl refl)
odd-triangle τ₀ τ₂ τ₂ ()
odd-triangle τ₁ τ₀ τ₀ ()
odd-triangle τ₁ τ₀ τ₁ ()
odd-triangle τ₁ τ₀ τ₂ _ = inr (inl refl) , inl refl , inr (inr refl)
odd-triangle τ₁ τ₁ τ₀ ()
odd-triangle τ₁ τ₁ τ₁ ()
odd-triangle τ₁ τ₁ τ₂ ()
odd-triangle τ₁ τ₂ τ₀ _ = inr (inr refl) , inl refl , inr (inl refl)
odd-triangle τ₁ τ₂ τ₁ ()
odd-triangle τ₁ τ₂ τ₂ ()
odd-triangle τ₂ τ₀ τ₀ ()
odd-triangle τ₂ τ₀ τ₁ _ = inr (inl refl) , inr (inr refl) , inl refl
odd-triangle τ₂ τ₀ τ₂ ()
odd-triangle τ₂ τ₁ τ₀ _ = inr (inr refl) , inr (inl refl) , inl refl
odd-triangle τ₂ τ₁ τ₁ ()
odd-triangle τ₂ τ₁ τ₂ ()
odd-triangle τ₂ τ₂ τ₀ ()
odd-triangle τ₂ τ₂ τ₁ ()
odd-triangle τ₂ τ₂ τ₂ ()

tag-is-τ₀ : (b₁ b₂ : 𝟚) → tag b₁ b₂ ＝ τ₀ → b₁ ＝ ₁
tag-is-τ₀ ₁ b₂ e = refl
tag-is-τ₀ ₀ ₁ ()
tag-is-τ₀ ₀ ₀ ()

tag-is-τ₁ : (b₁ b₂ : 𝟚) → tag b₁ b₂ ＝ τ₁ → (b₁ ＝ ₀) × (b₂ ＝ ₁)
tag-is-τ₁ ₁ b₂ ()
tag-is-τ₁ ₀ ₁ e = refl , refl
tag-is-τ₁ ₀ ₀ ()

tag-is-τ₂ : (b₁ b₂ : 𝟚) → tag b₁ b₂ ＝ τ₂ → (b₁ ＝ ₀) × (b₂ ＝ ₀)
tag-is-τ₂ ₁ b₂ ()
tag-is-τ₂ ₀ ₁ ()
tag-is-τ₂ ₀ ₀ e = refl , refl

door-on-bottom : (b b' : 𝟚) → door (tag b ₀) (tag b' ₀) ＝ ₀
door-on-bottom ₀ ₀ = refl
door-on-bottom ₀ ₁ = refl
door-on-bottom ₁ ₀ = refl
door-on-bottom ₁ ₁ = refl

door-on-left : (b b' : 𝟚) → door (tag ₀ b) (tag ₀ b') ＝ ₀
door-on-left ₀ ₀ = refl
door-on-left ₀ ₁ = refl
door-on-left ₁ ₀ = refl
door-on-left ₁ ₁ = refl

door-on-right : (b b' : 𝟚) → door (tag ₁ b) (tag ₁ b') ＝ ₀
door-on-right b b' = refl

door-on-top : (b b' : 𝟚) → door (tag b ₁) (tag b' ₁) ＝ b ⊕ b'
door-on-top ₀ ₀ = refl
door-on-top ₀ ₁ = refl
door-on-top ₁ ₀ = refl
door-on-top ₁ ₁ = refl

\end{code}

Points of the plane grid, and the corners of the unit square at a
point.

\begin{code}

pt : ℕ → ℕ → Fin 2 → ℕ
pt x y 𝟎             = x
pt x y 𝟏             = y
pt x y (suc (suc i)) = 𝟘-elim i

bits : 𝟚 → 𝟚 → Fin 2 → 𝟚
bits b c 𝟎             = b
bits b c 𝟏             = c
bits b c (suc (suc i)) = 𝟘-elim i

corner-is-pt : funext 𝓤₀ 𝓤₀ → (x y : ℕ) (r : Fin 2 → 𝟚)
             → corner (pt x y) r ＝ pt (x +ℕ bit (r 𝟎)) (y +ℕ bit (r 𝟏))
corner-is-pt fe x y r = dfunext fe γ
 where
  γ : corner (pt x y) r ∼ pt (x +ℕ bit (r 𝟎)) (y +ℕ bit (r 𝟏))
  γ 𝟎             = refl
  γ 𝟏             = refl
  γ (suc (suc i)) = 𝟘-elim i

\end{code}

The parity argument, for a labelling ℓ of the grid of side p + 1 with
the boundary conditions of Kuhn-Lemma 2.

\begin{code}

module dimension-2
        (fe : funext 𝓤₀ 𝓤₀)
        (p : ℕ)
        (ℓ : (Fin 2 → ℕ) → Fin 2 → 𝟚)
        (lower : (a : Fin 2 → ℕ) → ((j : Fin 2) → a j ≤ succ p)
               → (i : Fin 2) → a i ＝ 0 → ℓ a i ＝ ₀)
        (upper : (a : Fin 2 → ℕ) → ((j : Fin 2) → a j ≤ succ p)
               → (i : Fin 2) → a i ＝ succ p → ℓ a i ＝ ₁)
       where

 N : ℕ
 N = succ p

 lab : ℕ → ℕ → Fin 2 → 𝟚
 lab x y = ℓ (pt x y)

 τ : ℕ → ℕ → Tag
 τ x y = tag (lab x y 𝟎) (lab x y 𝟏)

 τc : ℕ → ℕ → (Fin 2 → 𝟚) → Tag
 τc x y r = τ (x +ℕ bit (r 𝟎)) (y +ℕ bit (r 𝟏))

 triangle : ℕ → ℕ → (r₁ r₂ r₃ : Fin 2 → 𝟚) → 𝟚
 triangle x y r₁ r₂ r₃ =
  (door (τc x y r₁) (τc x y r₂) ⊕ door (τc x y r₂) (τc x y r₃))
                       ⊕ door (τc x y r₁) (τc x y r₃)

 h v e : ℕ → ℕ → 𝟚
 h x y = door (τ x y) (τ (succ x) y)
 v x y = door (τ x y) (τ x (succ y))
 e x y = door (τ x y) (τ (succ x) (succ y))

 square : ℕ → ℕ → 𝟚
 square x y = triangle x y (bits ₀ ₀) (bits ₁ ₀) (bits ₁ ₁)
            ⊕ triangle x y (bits ₀ ₀) (bits ₀ ₁) (bits ₁ ₁)

 square-is-its-sides : (x y : ℕ)
  → square x y ＝ (h x y ⊕ h x (succ y)) ⊕ (v x y ⊕ v (succ x) y)
 square-is-its-sides x y =
  xor-square (h x y) (v (succ x) y) (v x y) (h x (succ y)) (e x y)

 H : ℕ → 𝟚
 H y = xor-sum (λ x → h x y) N

 V : ℕ → 𝟚
 V x = xor-sum (λ y → v x y) N

 row : ℕ → 𝟚
 row y = xor-sum (λ x → square x y) N

 row-is : (y : ℕ) → row y ＝ (H y ⊕ H (succ y)) ⊕ (v 0 y ⊕ v N y)
 row-is y = xor-sum-ext (λ x → square x y)
             (λ x → (h x y ⊕ h x (succ y)) ⊕ (v x y ⊕ v (succ x) y))
             (λ x → square-is-its-sides x y) N
          ∙ xor-sum-of-xor (λ x → h x y ⊕ h x (succ y))
             (λ x → v x y ⊕ v (succ x) y) N
          ∙ ap₂ _⊕_ (xor-sum-of-xor (λ x → h x y) (λ x → h x (succ y)) N)
                    (xor-sum-telescopes (λ x → v x y) N)

 total : 𝟚
 total = xor-sum row N

 total-is : total ＝ (H 0 ⊕ H N) ⊕ (V 0 ⊕ V N)
 total-is =
  xor-sum-ext row (λ y → (H y ⊕ H (succ y)) ⊕ (v 0 y ⊕ v N y)) row-is N
          ∙ xor-sum-of-xor (λ y → H y ⊕ H (succ y)) (λ y → v 0 y ⊕ v N y) N
          ∙ ap₂ _⊕_ (xor-sum-telescopes H N)
             (xor-sum-of-xor (λ y → v 0 y) (λ y → v N y) N)

 in-range : (x y : ℕ) → x ≤ N → y ≤ N → (j : Fin 2) → pt x y j ≤ N
 in-range x y k k' 𝟎             = k
 in-range x y k k' 𝟏             = k'
 in-range x y k k' (suc (suc i)) = 𝟘-elim i

 near : (x : ℕ) → x < N → x ≤ N
 near x k = ≤-trans x p N k (≤-succ p)

 bottom : H 0 ＝ ₀
 bottom = xor-sum-of-zeros (λ x → h x 0) N γ
  where
   γ : (x : ℕ) → x < N → h x 0 ＝ ₀
   γ x k = transport₂
            (λ c c' → door (tag (lab x 0 𝟎) c) (tag (lab (succ x) 0 𝟎) c') ＝ ₀)
            (I ⁻¹) (II ⁻¹) (door-on-bottom (lab x 0 𝟎) (lab (succ x) 0 𝟎))
    where
     I : lab x 0 𝟏 ＝ ₀
     I = lower (pt x 0) (in-range x 0 (near x k) ⋆) 𝟏 refl

     II : lab (succ x) 0 𝟏 ＝ ₀
     II = lower (pt (succ x) 0) (in-range (succ x) 0 k ⋆) 𝟏 refl

 left : V 0 ＝ ₀
 left = xor-sum-of-zeros (λ y → v 0 y) N γ
  where
   γ : (y : ℕ) → y < N → v 0 y ＝ ₀
   γ y k = transport₂
            (λ c c' → door (tag c (lab 0 y 𝟏)) (tag c' (lab 0 (succ y) 𝟏)) ＝ ₀)
            (I ⁻¹) (II ⁻¹) (door-on-left (lab 0 y 𝟏) (lab 0 (succ y) 𝟏))
    where
     I : lab 0 y 𝟎 ＝ ₀
     I = lower (pt 0 y) (in-range 0 y ⋆ (near y k)) 𝟎 refl

     II : lab 0 (succ y) 𝟎 ＝ ₀
     II = lower (pt 0 (succ y)) (in-range 0 (succ y) ⋆ k) 𝟎 refl

 right : V N ＝ ₀
 right = xor-sum-of-zeros (λ y → v N y) N γ
  where
   γ : (y : ℕ) → y < N → v N y ＝ ₀
   γ y k = transport₂
            (λ c c' → door (tag c (lab N y 𝟏)) (tag c' (lab N (succ y) 𝟏)) ＝ ₀)
            (I ⁻¹) (II ⁻¹) (door-on-right (lab N y 𝟏) (lab N (succ y) 𝟏))
    where
     I : lab N y 𝟎 ＝ ₁
     I = upper (pt N y) (in-range N y (≤-refl N) (near y k)) 𝟎 refl

     II : lab N (succ y) 𝟎 ＝ ₁
     II = upper (pt N (succ y)) (in-range N (succ y) (≤-refl N) k) 𝟎 refl

 top : H N ＝ ₁
 top = xor-sum-below (λ x → h x N) (λ x → lab x N 𝟎 ⊕ lab (succ x) N 𝟎) N γ
     ∙ xor-sum-telescopes (λ x → lab x N 𝟎) N
     ∙ ap₂ _⊕_ (lower (pt 0 N) (in-range 0 N ⋆ (≤-refl N)) 𝟎 refl)
               (upper (pt N N) (in-range N N (≤-refl N) (≤-refl N)) 𝟎 refl)
  where
   γ : (x : ℕ) → x < N → h x N ＝ lab x N 𝟎 ⊕ lab (succ x) N 𝟎
   γ x k =
    transport₂ (λ c c' → door (tag (lab x N 𝟎) c) (tag (lab (succ x) N 𝟎) c')
                        ＝ lab x N 𝟎 ⊕ lab (succ x) N 𝟎)
            (I ⁻¹) (II ⁻¹) (door-on-top (lab x N 𝟎) (lab (succ x) N 𝟎))
    where
     I : lab x N 𝟏 ＝ ₁
     I = upper (pt x N) (in-range x N (near x k) (≤-refl N)) 𝟏 refl

     II : lab (succ x) N 𝟏 ＝ ₁
     II = upper (pt (succ x) N) (in-range (succ x) N k (≤-refl N)) 𝟏 refl

 total-is-odd : total ＝ ₁
 total-is-odd = total-is ∙ ap₂ _⊕_ (ap₂ _⊕_ bottom top) (ap₂ _⊕_ left right)

\end{code}

A triangle with an odd number of doors gives a Kuhn square: its
corners carry all three tags.

\begin{code}

 kuhn-square-from-odd-triangle
  : (x y : ℕ) (r₁ r₂ r₃ : Fin 2 → 𝟚) → triangle x y r₁ r₂ r₃ ＝ ₁
  → (i : Fin 2) → Σ r ꞉ (Fin 2 → 𝟚) , Σ s ꞉ (Fin 2 → 𝟚)
                   , (ℓ (corner (pt x y) r) i ＝ ₀)
                   × (ℓ (corner (pt x y) s) i ＝ ₁)
 kuhn-square-from-odd-triangle x y r₁ r₂ r₃ o = γ
  where
   t : Among τ₀ (τc x y r₁) (τc x y r₂) (τc x y r₃)
     × Among τ₁ (τc x y r₁) (τc x y r₂) (τc x y r₃)
     × Among τ₂ (τc x y r₁) (τc x y r₂) (τc x y r₃)
   t = odd-triangle (τc x y r₁) (τc x y r₂) (τc x y r₃) o

   pick : (t' : Tag) → Among t' (τc x y r₁) (τc x y r₂) (τc x y r₃)
        → Σ r ꞉ (Fin 2 → 𝟚) , τc x y r ＝ t'
   pick t' (inl d)       = r₁ , d
   pick t' (inr (inl d)) = r₂ , d
   pick t' (inr (inr d)) = r₃ , d

   at-corner : (r : Fin 2 → 𝟚) (i : Fin 2)
             → ℓ (corner (pt x y) r) i ＝ lab (x +ℕ bit (r 𝟎)) (y +ℕ bit (r 𝟏)) i
   at-corner r i = ap (λ a → ℓ a i) (corner-is-pt fe x y r)

   c₀ c₁ c₂ : Σ r ꞉ (Fin 2 → 𝟚) , τc x y r ＝ _
   c₀ = pick τ₀ (pr₁ t)
   c₁ = pick τ₁ (pr₁ (pr₂ t))
   c₂ = pick τ₂ (pr₂ (pr₂ t))

   first : (r : Fin 2 → 𝟚) → Fin 2 → 𝟚
   first r = lab (x +ℕ bit (r 𝟎)) (y +ℕ bit (r 𝟏))

   γ : (i : Fin 2) → Σ r ꞉ (Fin 2 → 𝟚) , Σ s ꞉ (Fin 2 → 𝟚)
                      , (ℓ (corner (pt x y) r) i ＝ ₀)
                      × (ℓ (corner (pt x y) s) i ＝ ₁)
   γ 𝟎 = pr₁ c₁ , pr₁ c₀ ,
         (at-corner (pr₁ c₁) 𝟎
          ∙ pr₁ (tag-is-τ₁ (first (pr₁ c₁) 𝟎) (first (pr₁ c₁) 𝟏) (pr₂ c₁))) ,
         (at-corner (pr₁ c₀) 𝟎
          ∙ tag-is-τ₀ (first (pr₁ c₀) 𝟎) (first (pr₁ c₀) 𝟏) (pr₂ c₀))
   γ 𝟏 = pr₁ c₂ , pr₁ c₁ ,
         (at-corner (pr₁ c₂) 𝟏
          ∙ pr₂ (tag-is-τ₂ (first (pr₁ c₂) 𝟎) (first (pr₁ c₂) 𝟏) (pr₂ c₂))) ,
         (at-corner (pr₁ c₁) 𝟏
          ∙ pr₂ (tag-is-τ₁ (first (pr₁ c₁) 𝟎) (first (pr₁ c₁) 𝟏) (pr₂ c₁)))
   γ (suc (suc i)) = 𝟘-elim i

\end{code}

Kuhn's lemma in dimension 2.

\begin{code}

kuhn-lemma-2 : funext 𝓤₀ 𝓤₀ → Kuhn-Lemma 2
kuhn-lemma-2 fe p ℓ lower upper =
 pt x y , range , γ (xor-is-one _ _ (pr₂ (pr₂ X)))
 where
  open dimension-2 fe p ℓ lower upper

  Y : Σ y ꞉ ℕ , (y < N) × (row y ＝ ₁)
  Y = odd-xor-sum row N total-is-odd

  y : ℕ
  y = pr₁ Y

  X : Σ x ꞉ ℕ , (x < N) × (square x y ＝ ₁)
  X = odd-xor-sum (λ x → square x y) N (pr₂ (pr₂ Y))

  x : ℕ
  x = pr₁ X

  range : (i : Fin 2) → pt x y i ≤ p
  range 𝟎             = pr₁ (pr₂ X)
  range 𝟏             = pr₁ (pr₂ Y)
  range (suc (suc i)) = 𝟘-elim i

  γ : (triangle x y (bits ₀ ₀) (bits ₁ ₀) (bits ₁ ₁) ＝ ₁)
    ∔ (triangle x y (bits ₀ ₀) (bits ₀ ₁) (bits ₁ ₁) ＝ ₁)
    → (i : Fin 2) → Σ r ꞉ (Fin 2 → 𝟚) , Σ s ꞉ (Fin 2 → 𝟚)
                     , (ℓ (corner (pt x y) r) i ＝ ₀)
                     × (ℓ (corner (pt x y) s) i ＝ ₁)
  γ (inl o) =
   kuhn-square-from-odd-triangle x y (bits ₀ ₀) (bits ₁ ₀) (bits ₁ ₁) o
  γ (inr o) =
   kuhn-square-from-odd-triangle x y (bits ₀ ₀) (bits ₀ ₁) (bits ₁ ₁) o

\end{code}
