Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 25 October 2026; prose corrected 13 November 2026, after
the final audits. See the AI disclosure in gist.RealCohesion.index.

Every natural number, integer and rational number is equal to a crisp
one.

That is, the counit ♭ A → A has a section for A = ℕ, ℤ, ℚ. This is
half of the ♭-discreteness of these types; the other half needs crisp
identity induction, which Agda provides by pattern matching only with
--flat-split (see gist.RealCohesion.FlatSplit). For ℕ,
gist.CohesiveApartness.CrispInduction derives the ♭-discreteness in
--safe mode from the native ♯ of Agda 2.9.0. This module imports
neither, so that it stays in the route of gist.RealCohesion.FlatSplit,
which is also checked with Agda 2.8. The half proved here is enough for our
purposes: to apply crisp excluded middle to a statement about an
arbitrary rational number, we may replace the number by an equal crisp
one. The proof is by ordinary induction, building elements of ♭ ℕ, and
for ℚ goes through the normalization of fractions.

Added by Claude Opus 5.5 on 11 November 2026, for Lemma 3.6 of the
write-up (gate G9 of Fable's addendum to the formalization plan, §5.1):
crisp elimination, of which decide-at-rationals is now an instance, and
crisp representatives for lists and for functions on Fin n. The
addendum asks for the latter for every A with crisp representatives, by
induction on the crisp n. Pattern matching on a crisp n needs
--flat-split; induction on a crisp n could instead be derived from the
♭-discreteness of ℕ, which gist.CohesiveApartness.CrispInduction proves
from the native ♯. We go through the list of values instead, by
ordinary induction, which needs a crisp default value in A. Every use
has one: 0 in ℕ and ℚ, and ₀ in 𝟚.

The general statement, for every crisp n and every A with crisp
representatives, with no default value, is
finite-powers-have-crisp-representatives in
gist.RealCohesion.CrispFinitePowers (added 13 November 2026), by
induction on the crisp n derived from the ♭-discreteness of ℕ. It is
not here because it needs gist.CohesiveApartness.CrispInduction, and
so the native ♯, while this module is in the import closure of
gist.RealCohesion.FlatSplit, which is also checked with Agda 2.8,
which has no ♯. The form with a default value below is kept unchanged,
with its uses.

Moved here by Claude Opus 5.5 on 11 November 2026, so that it is
proved once: the other half for crisp sets, assuming crisp identity
induction in the form crisp-ap-^♭. If crisp propositions are
♭-discrete, the counit is left cancellable, and so an embedding, on
every crisp set [1, Theorem 8.21]. gist.RealCohesion.CrispDiscreteness
derives the hypothesis from axiom C1 and
gist.RealCohesion.FiniteChainDiscreteness from Axiom R♭; both proved
the two lemmas separately before, and both now open this module.

Fin-cons and Fin-cons-of-parts are in gist.RealCohesion.FinVectors
since 12 November 2026, so that modules without --cohesion can use
them; this module re-exports them.

[1] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer
    Science 28(6), 856–941, 2018. https://arxiv.org/abs/1509.07584v3

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

module gist.RealCohesion.CrispRationals where

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Fin.Type
open import Integers.Type
open import MLTT.List using (List ; [] ; _∷_)
open import Rationals.Fractions
open import Rationals.Type
open import UF.Base
open import UF.Embeddings
open import UF.FunExt
open import UF.LeftCancellable
open import UF.Sets
open import UF.Subsingletons
open import gist.CohesiveApartness.Flat

\end{code}

The property, its closure under products and sums, and ♭-discrete
types.

\begin{code}

has-crisp-representatives : {@♭ 𝓤 : Universe} (@♭ A : 𝓤 ̇ ) → 𝓤 ̇
has-crisp-representatives A = (a : A) → Σ u ꞉ ♭ A , ♭-counit u ＝ a

×-has-crisp-representatives : {@♭ 𝓤 𝓥 : Universe} {@♭ A : 𝓤 ̇ } {@♭ B : 𝓥 ̇ }
                            → has-crisp-representatives A
                            → has-crisp-representatives B
                            → has-crisp-representatives (A × B)
×-has-crisp-representatives {𝓤} {𝓥} {A} {B} ρ σ (a , b) = γ (ρ a) (σ b)
 where
  γ : (Σ u ꞉ ♭ A , ♭-counit u ＝ a)
    → (Σ v ꞉ ♭ B , ♭-counit v ＝ b)
    → Σ w ꞉ ♭ (A × B) , ♭-counit w ＝ (a , b)
  γ ((a' ^♭) , d) ((b' ^♭) , e) = ((a' , b') ^♭) , to-×-＝ d e

+-has-crisp-representatives : {@♭ 𝓤 𝓥 : Universe} {@♭ A : 𝓤 ̇ } {@♭ B : 𝓥 ̇ }
                            → has-crisp-representatives A
                            → has-crisp-representatives B
                            → has-crisp-representatives (A ∔ B)
+-has-crisp-representatives {𝓤} {𝓥} {A} {B} ρ σ (inl a) = γ (ρ a)
 where
  γ : (Σ u ꞉ ♭ A , ♭-counit u ＝ a) → Σ w ꞉ ♭ (A ∔ B) , ♭-counit w ＝ inl a
  γ ((a' ^♭) , d) = ((inl a') ^♭) , ap inl d
+-has-crisp-representatives {𝓤} {𝓥} {A} {B} ρ σ (inr b) = γ (σ b)
 where
  γ : (Σ v ꞉ ♭ B , ♭-counit v ＝ b) → Σ w ꞉ ♭ (A ∔ B) , ♭-counit w ＝ inr b
  γ ((b' ^♭) , d) = ((inr b') ^♭) , ap inr d

♭-discrete-types-have-crisp-representatives : {@♭ 𝓤 : Universe} {@♭ A : 𝓤 ̇ }
                                            → is-♭-discrete A
                                            → has-crisp-representatives A
♭-discrete-types-have-crisp-representatives d a = pr₁ (pr₁ d) a , pr₂ (pr₁ d) a

\end{code}

Natural numbers, integers, fractions and rational numbers.

\begin{code}

ℕ-has-crisp-representatives : has-crisp-representatives ℕ
ℕ-has-crisp-representatives 0        = (0 ^♭) , refl
ℕ-has-crisp-representatives (succ n) = γ (ℕ-has-crisp-representatives n)
 where
  γ : (Σ u ꞉ ♭ ℕ , ♭-counit u ＝ n) → Σ u ꞉ ♭ ℕ , ♭-counit u ＝ succ n
  γ ((m ^♭) , e) = ((succ m) ^♭) , ap succ e

ℤ-has-crisp-representatives : has-crisp-representatives ℤ
ℤ-has-crisp-representatives (pos n)     = γ (ℕ-has-crisp-representatives n)
 where
  γ : (Σ u ꞉ ♭ ℕ , ♭-counit u ＝ n) → Σ u ꞉ ♭ ℤ , ♭-counit u ＝ pos n
  γ ((m ^♭) , e) = ((pos m) ^♭) , ap pos e
ℤ-has-crisp-representatives (negsucc n) = γ (ℕ-has-crisp-representatives n)
 where
  γ : (Σ u ꞉ ♭ ℕ , ♭-counit u ＝ n) → Σ u ꞉ ♭ ℤ , ♭-counit u ＝ negsucc n
  γ ((m ^♭) , e) = ((negsucc m) ^♭) , ap negsucc e

𝔽-has-crisp-representatives : has-crisp-representatives 𝔽
𝔽-has-crisp-representatives =
 ×-has-crisp-representatives ℤ-has-crisp-representatives
                             ℕ-has-crisp-representatives

ℚ-has-crisp-representatives : has-crisp-representatives ℚ
ℚ-has-crisp-representatives q = γ (𝔽-has-crisp-representatives (to𝔽 q))
 where
  γ : (Σ u ꞉ ♭ 𝔽 , ♭-counit u ＝ to𝔽 q) → Σ u ꞉ ♭ ℚ , ♭-counit u ＝ q
  γ ((f ^♭) , e) = ((toℚ f) ^♭) , (ap toℚ e ∙ toℚ-to𝔽 q ⁻¹)

\end{code}

Lists, and functions on Fin n with values in a type with a crisp
point.

\begin{code}

List-has-crisp-representatives : {@♭ 𝓤 : Universe} {@♭ A : 𝓤 ̇ }
                               → has-crisp-representatives A
                               → has-crisp-representatives (List A)
List-has-crisp-representatives ρ []                = ([] ^♭) , refl
List-has-crisp-representatives {𝓤} {A} ρ (a ∷ l) =
 γ (ρ a) (List-has-crisp-representatives ρ l)
 where
  γ : (Σ u ꞉ ♭ A , ♭-counit u ＝ a)
    → (Σ v ꞉ ♭ (List A) , ♭-counit v ＝ l)
    → Σ w ꞉ ♭ (List A) , ♭-counit w ＝ a ∷ l
  γ ((a' ^♭) , d) ((l' ^♭) , e) = ((a' ∷ l') ^♭) , ap₂ _∷_ d e

open import gist.RealCohesion.FinVectors using (Fin-cons ; Fin-cons-of-parts)
 public

values : {𝓤 : Universe} {A : 𝓤 ̇ } (n : ℕ) → (Fin n → A) → List A
values 0        f = []
values (succ n) f = f 𝟎 ∷ values n (f ∘ suc)

from-values : {𝓤 : Universe} {A : 𝓤 ̇ } (n : ℕ) → A → List A → Fin n → A
from-values 0        a₀ l       ()
from-values (succ n) a₀ []      i       = a₀
from-values (succ n) a₀ (a ∷ l) 𝟎       = a
from-values (succ n) a₀ (a ∷ l) (suc i) = from-values n a₀ l i

from-values-of-values
 : {𝓤 : Universe} {A : 𝓤 ̇ } (n : ℕ) (a₀ : A) (f : Fin n → A)
                      → from-values n a₀ (values n f) ∼ f
from-values-of-values 0        a₀ f ()
from-values-of-values (succ n) a₀ f 𝟎       = refl
from-values-of-values (succ n) a₀ f (suc i) =
 from-values-of-values n a₀ (f ∘ suc) i

Fin-functions-have-crisp-representatives
 : Fun-Ext
 → (@♭ n : ℕ) {@♭ 𝓤 : Universe} {@♭ A : 𝓤 ̇ }
 → (@♭ a₀ : A)
 → has-crisp-representatives A
 → has-crisp-representatives (Fin n → A)
Fin-functions-have-crisp-representatives fe n {𝓤} {A} a₀ ρ f =
 γ (List-has-crisp-representatives ρ (values n f))
 where
  γ : (Σ v ꞉ ♭ (List A) , ♭-counit v ＝ values n f)
    → Σ w ꞉ ♭ (Fin n → A) , ♭-counit w ＝ f
  γ ((l ^♭) , e) = (from-values n a₀ l ^♭) ,
                   (ap (from-values n a₀) e
                    ∙ dfunext fe (from-values-of-values n a₀ f))

\end{code}

Crisp elimination: a statement about the elements of a type with crisp
representatives holds for all of them as soon as it holds for the
crisp ones; likewise for two variables. A statement that holds at an
element holds at a crisp one (a crisp witness). And crisp excluded
middle decides a crisp family of propositions on such a type at every
point, crisp or not.

\begin{code}

crisp-elim : {@♭ 𝓤 : Universe} {@♭ A : 𝓤 ̇ } {𝓦 : Universe}
           → has-crisp-representatives A
           → (V : A → 𝓦 ̇ )
           → ((@♭ a : A) → V a)
           → (a : A) → V a
crisp-elim {𝓤} {A} ρ V h a = γ (ρ a)
 where
  γ : (Σ u ꞉ ♭ A , ♭-counit u ＝ a) → V a
  γ ((a' ^♭) , e) = transport V e (h a')

crisp-elim₂ : {@♭ 𝓤 𝓥 : Universe} {@♭ A : 𝓤 ̇ } {@♭ B : 𝓥 ̇ } {𝓦 : Universe}
            → has-crisp-representatives A
            → has-crisp-representatives B
            → (V : A → B → 𝓦 ̇ )
            → ((@♭ a : A) (@♭ b : B) → V a b)
            → (a : A) (b : B) → V a b
crisp-elim₂ {𝓤} {𝓥} {A} {B} ρ σ V h a =
 crisp-elim ρ (λ a → (b : B) → V a b) (λ a' → crisp-elim σ (V a') (h a')) a

crisp-witness : {@♭ 𝓤 : Universe} {@♭ A : 𝓤 ̇ } {𝓦 : Universe}
              → has-crisp-representatives A
              → (P : A → 𝓦 ̇ ) (a : A) → P a → Σ u ꞉ ♭ A , P (♭-counit u)
crisp-witness {𝓤} {A} ρ P =
 crisp-elim ρ (λ a → P a → Σ u ꞉ ♭ A , P (♭-counit u))
                             (λ a p → (a ^♭) , p)

decide-at : {@♭ 𝓤 𝓦 : Universe} {@♭ A : 𝓤 ̇ }
          → has-crisp-representatives A
          → (@♭ cem : Crisp-EM 𝓦)
          → (@♭ P : A → 𝓦 ̇ )
          → (@♭ P-is-prop : (a : A) → is-prop (P a))
          → (a : A) → P a ∔ ¬ P a
decide-at ρ cem P P-is-prop =
 crisp-elim ρ (λ a → P a ∔ ¬ P a) (λ a → cem (P a) (P-is-prop a))

decide-at-rationals : {@♭ 𝓦 : Universe}
                    → (@♭ cem : Crisp-EM 𝓦)
                    → (@♭ P : ℚ → 𝓦 ̇ )
                    → (@♭ P-is-prop : (q : ℚ) → is-prop (P q))
                    → (q : ℚ) → P q ∔ ¬ P q
decide-at-rationals cem P P-is-prop =
 decide-at ℚ-has-crisp-representatives cem P P-is-prop

\end{code}

The other half for crisp sets: given crisp x and y with x ＝ y, the
crisp proposition x ＝ y is ♭-discrete, so the identification may be
taken crisp, and then crisp-ap-^♭ applies.

\begin{code}

module counit-on-crisp-sets
        (@♭ crisp-ap-^♭ : {@♭ 𝓤 : Universe} {@♭ A : 𝓤 ̇ } {@♭ x y : A}
                        → @♭ x ＝ y → x ^♭ ＝ y ^♭)
        (crisp-props-are-♭-discrete : {@♭ 𝓣 : Universe} (@♭ P : 𝓣 ̇ )
                                    → @♭ is-prop P → is-♭-discrete P)
       where

 ♭-counit-is-lc-on-crisp-sets
  : {@♭ 𝓣 : Universe} (@♭ B : 𝓣 ̇ )
  → @♭ is-set B
  → left-cancellable (♭-counit {𝓣} {B})
 ♭-counit-is-lc-on-crisp-sets B B-is-set {x ^♭} {y ^♭} p = γ (s p)
  where
   s : x ＝ y → ♭ (x ＝ y)
   s = pr₁ (pr₁ (crisp-props-are-♭-discrete (x ＝ y) B-is-set))

   γ : ♭ (x ＝ y) → x ^♭ ＝ y ^♭
   γ (e ^♭) = crisp-ap-^♭ e

 ♭-counit-is-embedding-on-crisp-sets
  : {@♭ 𝓣 : Universe} (@♭ B : 𝓣 ̇ )
  → @♭ is-set B
  → is-embedding (♭-counit {𝓣} {B})
 ♭-counit-is-embedding-on-crisp-sets B B-is-set =
  lc-maps-into-sets-are-embeddings ♭-counit
   (♭-counit-is-lc-on-crisp-sets B B-is-set) B-is-set

\end{code}
