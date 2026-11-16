Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. See the AI disclosure in
gist.RealCohesion.index.

Shulman's Theorem 11.5 from Axiom R♭ alone: Theorem 7.14 of the
write-up [1], gate G23 of Claude Fable 5.2's second addendum [2].

The exact statement. Theorem 7.14 of [1]: assume Axiom R♭; let
f :: ℝ → ℝ and a :: ℝ be crisp. For every ε > 0 there is δ > 0 such
that |f x - f a| < ε for every x : ℝ with |x - a| < δ. Shulman states
it as his Theorem 11.5 [3], from Axioms R♭ and T.

The formal statement, crisp-functions-are-continuous, is the same with
rational intervals in place of ε and δ: for rationals u < f a < v
there is a rational interval around a on which u < f x < v, for every
x, crisp or not. gist.RealCohesion.ContinuityForms converts it to the
ε-δ form, and gist.RealCohesion.Theorems states the result as
Shulman-11-5 of gist.RealCohesion.ShulmanWeakeningsStatements, from
Axiom R♭ alone, and Crisp-Real-Continuity of
gist.RealCohesion.CrispRealAnalysis as a corollary.

The proof follows that of [1], which is Shulman's proof with strong
extensionality (Lemma 7.12, gist.RealCohesion.StrongExtensionality) in
place of his two uses of Axiom T, as Fable's note [4] proposes and
GPT-6 Astra's audit [5] confirms. One step is simpler. The proof in [1]
needs points apart from f a on both sides of a, so that V meets both
half-lines, and gets them by modifying f outside [a - 1, a + 1] in
four ways. Here the second set of each cover is a half-line. For crisp
rationals u₁ < f a < v₁, let U be the set of x with u₁ < f x < v₁.

 1. By locatedness and strong extensionality, every x is in U or apart
    from a. So U ∪ (-∞, a) and (a, ∞) cover ℝ, and so do
    U ∪ (a, ∞) and (-∞, a).

 2. Lemma 7.13 (gist.RealCohesion.IndistinguishablePoints) gives points
    y₂ > a and y₁ < a that no map to 𝟚 on U ∪ (-∞, a), respectively on
    U ∪ (a, ∞), separates from a.

 3. Let x lie between y₁ and y₂, and suppose that every point of U is
    apart from x. Then a is apart from x, and if a < x, the side of x
    on which a point lies is a map to 𝟚 on U ∪ (-∞, a) that separates
    a from y₂; if x < a, it separates a from y₁ on U ∪ (a, ∞).

 4. For rationals u < u₁ and v₁ < v, and x between y₁ and y₂, locatedness
    gives u < f x < v, or f x < u₁, or v₁ < f x. In the last two cases
    every point of U is apart from x, by strong extensionality, which
    step 3 excludes.

No crisp excluded middle, Axiom T, choice or univalence is used. Axiom
R♭ is used in both directions, in Lemma 7.13, and in strong
extensionality through sequential hitting. The sets of the proof are
defined, and opened, before Axiom R♭ is assumed, so that they are
crisp.

Since the consolidation of 13 November 2026, by Claude Opus 5.5 (W3 of
[6]), the proof is carried out under Axiom C1 for an ordinary family of
pointed generators, the ♭-discreteness of 𝟚 and a strictly rising
generator path in ℝ, merely (modules steps-under-C1 and
continuity-under-C1), with Lemma 7.13 and strong extensionality in the
same generality; strong extensionality uses Axiom R♭ only through the
constancy of maps from ℝ to the finite chain quotient, which C1 and the
rising path give (gist.RealCohesion.FiniteChainDiscreteness). Axiom R♭
is the case of the one generator ℝ, whose identity map rises from 0 to
1, and crisp-functions-are-continuous keeps its type under Axiom R♭.

[1] Answers to some open problems in real-cohesive homotopy type
    theory. Research notes, revision of 12 November 2026, Theorem 7.14.
    references/C04-write-up-2026-11-12.tex

[2] Claude Fable 5.2. Second addendum to the formalization plan,
    revision 4 of 12 November 2026.
    references/F13b-second-addendum-rev4-as-amended.md

[3] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer
    Science 28(6), 856–941, 2018. https://arxiv.org/abs/1509.07584v3

[4] Claude Fable 5.2. Shulman's Theorem 11.5 from R♭ alone. Note of
    12 November 2026.
    references/F12-shulman-11-5.md

[5] GPT-6 Astra. Audit: Shulman 11.5 from R-flat alone, 12 November
    2026.
    references/A12-shulman-11-5-audit.txt

[6] Claude Fable 5.2. Plan: consolidation of r3, and "C1 + NC in place
    of R♭" (G27(d)), 13 November 2026, Section 4.3, as corrected by
    its addendum 01 and released by GPT-6 Astra.
    references/F02-consolidation-plan.md

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import gist.CohesiveApartness.Flat

module gist.RealCohesion.CrispFunctionsAreContinuous
        (@♭ fe : Fun-Ext)
        (@♭ pe : Prop-Ext)
        (@♭ pt : propositional-truncations-exist)
        (@♭ crisp-ap-^♭ : {@♭ 𝓤 : Universe} {@♭ A : 𝓤 ̇ } {@♭ x y : A}
                        → @♭ x ＝ y → x ^♭ ＝ y ^♭)
       where

open import MLTT.Two-Properties using (one-is-not-zero)
open import Notation.Order
open import Rationals.Type
open import Rationals.Order
open import Rationals.Negation renaming (_-_ to _ℚ-_ ; -_ to ℚ-_)
open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import gist.RealCohesion.CrispRationals
 using (ℚ-has-crisp-representatives ; crisp-elim₂)
open import gist.RealCohesion.RationalPoints fe pe pt using (ιₐ)
open import gist.RealCohesion.RealLattice fe pe pt
 using (ℚ<ℝ-is-prop ; ℝ<ℚ-is-prop ; translate-up ; translate-down)
 renaming (_+_ to _ℝ+_)
open import gist.RealCohesion.FiniteChainQuotient fe pe pt using (Q)
import gist.RealCohesion.FiniteChainDiscreteness fe pe pt crisp-ap-^♭ as FCD
import gist.RealCohesion.IndistinguishablePoints fe pe pt crisp-ap-^♭ as IP
import gist.RealCohesion.StrongExtensionality fe pe pt as SE
open import gist.RealCohesion.Constancy fe pe pt
 using (Rising-Generator-Path ; identity-of-ℝ-rises)

open PropositionalTruncation pt

\end{code}

The side of x on which a point apart from x lies, as an element of 𝟚,
and step 3 for any set W of points apart from x.

\begin{code}

bit-of : {𝓥 𝓦 : Universe} {A : 𝓥 ̇ } {B : 𝓦 ̇ } → A ∔ B → 𝟚
bit-of (inl _) = ₀
bit-of (inr _) = ₁

module _ (x : ℝ) where

 sides-are-a-prop : (p : ℝ) → is-prop ((p < x) ∔ (x < p))
 sides-are-a-prop p = +-is-prop (<-is-prop p x) (<-is-prop x p)
                       (λ l m → <ℝ-irreflexive p (ℝ<-trans p x p l m))

 side : (p : ℝ) → p ♯ x → (p < x) ∔ (x < p)
 side p = ∥∥-rec (sides-are-a-prop p) id

 side-below : (p : ℝ) (k : p ♯ x) → p < x → bit-of (side p k) ＝ ₀
 side-below p k l = ap bit-of (sides-are-a-prop p (side p k) (inl l))

 side-above : (p : ℝ) (k : p ♯ x) → x < p → bit-of (side p k) ＝ ₁
 side-above p k l = ap bit-of (sides-are-a-prop p (side p k) (inr l))

 separation : (W : ℝ → 𝓤₀ ̇ )
            → (apart : (p : ℝ) → W p → p ♯ x)
            → (a y : ℝ) (wa : W a) (wy : W y)
            → ((q : (Σ p ꞉ ℝ , W p) → 𝟚) → q (y , wy) ＝ q (a , wa))
            → ((a < x) × (x < y)) ∔ ((y < x) × (x < a))
            → 𝟘
 separation W apart a y wa wy indistinguishable = γ
  where
   q : (Σ p ꞉ ℝ , W p) → 𝟚
   q (p , w) = bit-of (side p (apart p w))

   γ : ((a < x) × (x < y)) ∔ ((y < x) × (x < a)) → 𝟘
   γ (inl (l , m)) = one-is-not-zero (side-above y (apart y wy) m ⁻¹
                                      ∙ indistinguishable q
                                      ∙ side-below a (apart a wa) l)
   γ (inr (l , m)) = one-is-not-zero (side-above a (apart a wa) m ⁻¹
                                      ∙ indistinguishable q ⁻¹
                                      ∙ side-below y (apart y wy) l)

\end{code}

The sets of the proof, for crisp f, a, u₁ and v₁.

\begin{code}

module sets (@♭ f : ℝ → ℝ) (@♭ a : ℝ) (@♭ u₁ v₁ : ℚ) where

 U : ℝ → 𝓤₀ ̇
 U x = (u₁ < f x) × (f x < v₁)

 U-or-left U-or-right left right : ℝ → 𝓤₀ ̇
 U-or-left  x = U x ∨ (x < a)
 U-or-right x = U x ∨ (a < x)
 left       x = x < a
 right      x = a < x

module _ (@♭ f : ℝ → ℝ) (@♭ a : ℝ) (@♭ u₁ v₁ : ℚ) where

 open sets f a u₁ v₁

 module steps-under-C1
         {𝓥 𝓦 : Universe} {J : 𝓥 ̇ } (R : J → 𝓦 ̇ ) (c1 : Axiom-C1 R)
         (𝟚-is-♭-discrete : is-♭-discrete 𝟚)
         (nc : ∥ Rising-Generator-Path R ∥)
         (l : u₁ < f a)
         (m : f a < v₁)
        where

  private
   ν : (k : ℝ → Q) (u v : ℝ) → k u ＝ k v
   ν = FCD.under-C1.constancy-from-C1-and-NC R c1 𝟚-is-♭-discrete nc

  a-is-in-U : U a
  a-is-in-U = l , m

\end{code}

Step 1.

\begin{code}

  near-or-apart : (x : ℝ) → U x ∨ (x ♯ a)
  near-or-apart x =
   ∥∥-rec ∨-is-prop γ
    (binary-choice (rounded-left-d (f a) u₁ l)
                   (rounded-right-b (upper-cut-of (f a))
                     (rounded-from-real-R (f a)) v₁ m))
   where
    γ : (Σ u₂ ꞉ ℚ , (u₁ < u₂) × (u₂ < f a))
      × (Σ v₂ ꞉ ℚ , (v₂ < v₁) × (f a < v₂))
      → U x ∨ (x ♯ a)
    γ ((u₂ , o , o') , (v₂ , p , p')) =
     ∥∥-functor δ (binary-choice (ℝ-locatedness (f x) u₁ u₂ o)
                    (ℝ-locatedness (f x) v₂ v₁ p))
     where
      δ : ((u₁ < f x) ∔ (f x < u₂)) × ((v₂ < f x) ∔ (f x < v₁)) → U x ∔ (x ♯ a)
      δ (inl k , inr k') = inl (k , k')
      δ (inr k , _)      =
       inr (SE.strong-extensionality ν f x a ∣ inl ∣ u₂ , k , o' ∣ ∣)
      δ (inl _ , inl k') =
       inr (SE.strong-extensionality ν f x a ∣ inr ∣ v₂ , p' , k' ∣ ∣)

\end{code}

Steps 2 and 3, on each side of a.

\begin{code}

  right-point : ∃ y ꞉ ℝ , (a < y)
                        ×
                        ((x : ℝ) → a < x → x < y → ((p : ℝ) → U p → p ♯ x) → 𝟘)
  right-point =
   ∥∥-functor γ
    (IP.quotient-under-C1.indistinguishable-point U-or-left right R c1
      𝟚-is-♭-discrete nc
      (λ s → ∨-is-prop) (λ s → <-is-prop a s) cover
      a ∣ inl a-is-in-U ∣ (a ℝ+ ιₐ 1ℚ) (translate-up a 1ℚ 0<1))
   where
    cover : (s : ℝ) → U-or-left s ∨ right s
    cover s = ∥∥-rec ∨-is-prop δ (near-or-apart s)
     where
      δ : U s ∔ (s ♯ a) → U-or-left s ∨ right s
      δ (inl w) = ∣ inl ∣ inl w ∣ ∣
      δ (inr k) = ∥∥-functor ε k
       where
        ε : (s < a) ∔ (a < s) → U-or-left s ∔ right s
        ε (inl o) = inl ∣ inr o ∣
        ε (inr o) = inr o

    γ : (Σ y ꞉ ℝ , Σ w ꞉ U-or-left y , right y
                 × ((q : (Σ s ꞉ ℝ , U-or-left s) → 𝟚)
                    → q (y , w) ＝ q (a , ∣ inl a-is-in-U ∣)))
      → Σ y ꞉ ℝ , (a < y)
                × ((x : ℝ) → a < x → x < y → ((p : ℝ) → U p → p ♯ x) → 𝟘)
    γ (y , w , o , indistinguishable) = y , o , δ
     where
      δ : (x : ℝ) → a < x → x < y → ((p : ℝ) → U p → p ♯ x) → 𝟘
      δ x n n' apart =
       separation x U-or-left apart' a y ∣ inl a-is-in-U ∣ w indistinguishable
                        (inl (n , n'))
       where
        apart' : (p : ℝ) → U-or-left p → p ♯ x
        apart' p = ∥∥-rec ∨-is-prop ε
         where
          ε : U p ∔ (p < a) → p ♯ x
          ε (inl w') = apart p w'
          ε (inr o') = ∣ inl (ℝ<-trans p a x o' n) ∣

  left-point : ∃ y ꞉ ℝ , (y < a)
                       × ((x : ℝ) → y < x → x < a → ((p : ℝ) → U p → p ♯ x) → 𝟘)
  left-point =
   ∥∥-functor γ
    (IP.quotient-under-C1.indistinguishable-point U-or-right left R c1
      𝟚-is-♭-discrete nc
      (λ s → ∨-is-prop) (λ s → <-is-prop s a) cover
      a ∣ inl a-is-in-U ∣ (a ℝ+ ιₐ (ℚ- 1ℚ)) (translate-down a 1ℚ 0<1))
   where
    cover : (s : ℝ) → U-or-right s ∨ left s
    cover s = ∥∥-rec ∨-is-prop δ (near-or-apart s)
     where
      δ : U s ∔ (s ♯ a) → U-or-right s ∨ left s
      δ (inl w) = ∣ inl ∣ inl w ∣ ∣
      δ (inr k) = ∥∥-functor ε k
       where
        ε : (s < a) ∔ (a < s) → U-or-right s ∔ left s
        ε (inl o) = inr o
        ε (inr o) = inl ∣ inr o ∣

    γ : (Σ y ꞉ ℝ , Σ w ꞉ U-or-right y , left y
                 × ((q : (Σ s ꞉ ℝ , U-or-right s) → 𝟚)
                    → q (y , w) ＝ q (a , ∣ inl a-is-in-U ∣)))
      → Σ y ꞉ ℝ , (y < a)
                × ((x : ℝ) → y < x → x < a → ((p : ℝ) → U p → p ♯ x) → 𝟘)
    γ (y , w , o , indistinguishable) = y , o , δ
     where
      δ : (x : ℝ) → y < x → x < a → ((p : ℝ) → U p → p ♯ x) → 𝟘
      δ x n n' apart =
       separation x U-or-right apart' a y ∣ inl a-is-in-U ∣ w indistinguishable
                        (inr (n , n'))
       where
        apart' : (p : ℝ) → U-or-right p → p ♯ x
        apart' p = ∥∥-rec ∨-is-prop ε
         where
          ε : U p ∔ (a < p) → p ♯ x
          ε (inl w') = apart p w'
          ε (inr o') = ∣ inr (ℝ<-trans x a p n' o') ∣

\end{code}

Steps 2 and 3 together: a rational interval around a in which no x has
every point of U apart from it.

\begin{code}

  no-separated-point-near-a
   : ∃ (r , r') ꞉ ℚ × ℚ , (r < a) × (a < r')
                        ×
                        ((x : ℝ) → r < x → x < r' → ((p : ℝ) → U p → p ♯ x) → 𝟘)
  no-separated-point-near-a =
   ∥∥-rec ∃-is-prop γ (binary-choice left-point right-point)
   where
    γ : (Σ y₁ ꞉ ℝ , (y₁ < a)
                  × ((x : ℝ) → y₁ < x → x < a → ((p : ℝ) → U p → p ♯ x) → 𝟘))
      × (Σ y₂ ꞉ ℝ , (a < y₂)
                  × ((x : ℝ) → a < x → x < y₂ → ((p : ℝ) → U p → p ♯ x) → 𝟘))
      → ∃ (r , r') ꞉ ℚ × ℚ , (r < a) × (a < r')
                           × ((x : ℝ) → r < x → x < r' → ((p : ℝ) → U p → p ♯ x)
                              → 𝟘)
    γ ((y₁ , o₁ , h₁) , (y₂ , o₂ , h₂)) = ∥∥-functor δ (binary-choice o₁ o₂)
     where
      δ : (Σ r ꞉ ℚ , (y₁ < r) × (r < a)) × (Σ r' ꞉ ℚ , (a < r') × (r' < y₂))
        → Σ (r , r') ꞉ ℚ × ℚ , (r < a) × (a < r')
                             × ((x : ℝ) → r < x → x < r'
                                → ((p : ℝ) → U p → p ♯ x) → 𝟘)
      δ ((r , k , k') , (r' , n , n')) = (r , r') , k' , n , ζ
       where
        ζ : (x : ℝ) → r < x → x < r' → ((p : ℝ) → U p → p ♯ x) → 𝟘
        ζ x c c' apart = ∥∥-rec 𝟘-is-prop θ (apart a a-is-in-U)
         where
          θ : (a < x) ∔ (x < a) → 𝟘
          θ (inl e) = h₂ x e ∣ r' , c' , n' ∣ apart
          θ (inr e) = h₁ x ∣ r , k , c ∣ e apart

\end{code}

Steps 1 to 3 under Axiom R♭, the instance for the one generator ℝ,
whose identity map rises from 0 to 1, with the names and types of the
module before the consolidation of 13 November 2026.

\begin{code}

 module _ (r♭ : Singly-Generated-Punctual-Cohesion ℝ 0ℝ)
          (𝟚-is-♭-discrete : is-♭-discrete 𝟚)
          (l : u₁ < f a)
          (m : f a < v₁)
        where

  private
   module G = steps-under-C1 (λ (_ : 𝟙 {𝓤₀}) → ℝ)
               (singly-generated-punctual-cohesion-gives-Axiom-C1 fe ℝ 0ℝ r♭)
               𝟚-is-♭-discrete identity-of-ℝ-rises l m

  a-is-in-U : U a
  a-is-in-U = G.a-is-in-U

  near-or-apart : (x : ℝ) → U x ∨ (x ♯ a)
  near-or-apart = G.near-or-apart

  right-point : ∃ y ꞉ ℝ , (a < y)
                        ×
                        ((x : ℝ) → a < x → x < y → ((p : ℝ) → U p → p ♯ x) → 𝟘)
  right-point = G.right-point

  left-point : ∃ y ꞉ ℝ , (y < a)
                       × ((x : ℝ) → y < x → x < a → ((p : ℝ) → U p → p ♯ x) → 𝟘)
  left-point = G.left-point

  no-separated-point-near-a
   : ∃ (r , r') ꞉ ℚ × ℚ , (r < a) × (a < r')
                        ×
                        ((x : ℝ) → r < x → x < r' → ((p : ℝ) → U p → p ♯ x) → 𝟘)
  no-separated-point-near-a = G.no-separated-point-near-a

\end{code}

Step 4, and the theorem. The rationals u₁ and v₁ are chosen between u
and f a and between f a and v, and replaced by crisp ones.

\begin{code}

module continuity-under-C1
        {𝓥 𝓦 : Universe} {J : 𝓥 ̇ } (R : J → 𝓦 ̇ ) (c1 : Axiom-C1 R)
        (𝟚-is-♭-discrete : is-♭-discrete 𝟚)
        (nc : ∥ Rising-Generator-Path R ∥)
       where

 private
  ν : (k : ℝ → Q) (u v : ℝ) → k u ＝ k v
  ν = FCD.under-C1.constancy-from-C1-and-NC R c1 𝟚-is-♭-discrete nc

 crisp-functions-are-continuous
  : (@♭ f : ℝ → ℝ) (@♭ a : ℝ) (u v : ℚ)
  → u < f a → f a < v
  → ∃ (r , r') ꞉ ℚ × ℚ , (r < a) × (a < r')
                       × ((x : ℝ) → r < x → x < r' → (u < f x) × (f x < v))
 crisp-functions-are-continuous f a u v l m =
  ∥∥-rec ∃-is-prop γ
   (binary-choice (rounded-left-d (f a) u l)
                  (rounded-right-b (upper-cut-of (f a))
                    (rounded-from-real-R (f a)) v m))
  where
   Goal : ℚ → ℚ → 𝓤₁ ̇
   Goal u₁ v₁ = u < u₁ → u₁ < f a → v₁ < v → f a < v₁
              → ∃ (r , r') ꞉ ℚ × ℚ , (r < a) × (a < r')
                                   × ((x : ℝ) → r < x → x < r'
                                      → (u < f x) × (f x < v))

   δ : (@♭ u₁ v₁ : ℚ) → Goal u₁ v₁
   δ u₁ v₁ o o' p p' =
    ∥∥-functor ε
     (steps-under-C1.no-separated-point-near-a f a u₁ v₁ R c1 𝟚-is-♭-discrete
       nc o' p')
    where
     ε : (Σ (r , r') ꞉ ℚ × ℚ , (r < a) × (a < r')
                             × ((x : ℝ) → r < x → x < r'
                                        → ((q : ℝ) → sets.U f a u₁ v₁ q → q ♯ x)
                                        → 𝟘))
       → Σ (r , r') ꞉ ℚ × ℚ , (r < a) × (a < r')
                            × ((x : ℝ) → r < x → x < r' → (u < f x) × (f x < v))
     ε ((r , r') , k , k' , h) = (r , r') , k , k' , θ
      where
       θ : (x : ℝ) → r < x → x < r' → (u < f x) × (f x < v)
       θ x c c' =
        ∥∥-rec (×-is-prop (ℚ<ℝ-is-prop u (f x)) (ℝ<ℚ-is-prop (f x) v)) ζ
                   (binary-choice (ℝ-locatedness (f x) u u₁ o)
                     (ℝ-locatedness (f x) v₁ v p))
        where
         ζ : ((u < f x) ∔ (f x < u₁)) × ((v₁ < f x) ∔ (f x < v))
           → (u < f x) × (f x < v)
         ζ (inl n , inr n') = n , n'
         ζ (inr n , _)      = 𝟘-elim (h x c c'
                               (λ q w → SE.strong-extensionality ν f q x
                                         ∣ inr ∣ u₁ , n , pr₁ w ∣ ∣))
         ζ (inl _ , inl n') = 𝟘-elim (h x c c'
                               (λ q w → SE.strong-extensionality ν f q x
                                         ∣ inl ∣ v₁ , pr₂ w , n' ∣ ∣))

   γ : (Σ u₁ ꞉ ℚ , (u < u₁) × (u₁ < f a)) × (Σ v₁ ꞉ ℚ , (v₁ < v) × (f a < v₁))
     → ∃ (r , r') ꞉ ℚ × ℚ , (r < a) × (a < r')
                          × ((x : ℝ) → r < x → x < r' → (u < f x) × (f x < v))
   γ ((u₁ , o , o') , (v₁ , p , p')) =
    crisp-elim₂ ℚ-has-crisp-representatives ℚ-has-crisp-representatives Goal δ
     u₁ v₁ o o' p p'

\end{code}

Under Axiom R♭: the instance for the one generator ℝ, with the name and
type of the module before the consolidation of 13 November 2026.

\begin{code}

module _ (r♭ : Singly-Generated-Punctual-Cohesion ℝ 0ℝ)
         (𝟚-is-♭-discrete : is-♭-discrete 𝟚)
       where

 crisp-functions-are-continuous
  : (@♭ f : ℝ → ℝ) (@♭ a : ℝ) (u v : ℚ)
  → u < f a → f a < v
  → ∃ (r , r') ꞉ ℚ × ℚ , (r < a) × (a < r')
                       × ((x : ℝ) → r < x → x < r' → (u < f x) × (f x < v))
 crisp-functions-are-continuous =
  continuity-under-C1.crisp-functions-are-continuous (λ (_ : 𝟙 {𝓤₀}) → ℝ)
   (singly-generated-punctual-cohesion-gives-Axiom-C1 fe ℝ 0ℝ r♭)
   𝟚-is-♭-discrete identity-of-ℝ-rises

\end{code}
