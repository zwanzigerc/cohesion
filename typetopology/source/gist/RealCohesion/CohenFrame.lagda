Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 25 October 2026. See the AI disclosure in
gist.RealCohesion.index.

The Cohen frame: regular open sets of the binary tree.

We construct, constructively, a nontrivial frame with a cylinder
system in the sense of gist.RealCohesion.Cylinders. So the hypotheses
of gist.RealCohesion.Cylinders, and those on the pointless end in
gist.RealCohesion.PointlessEnd, can be satisfied, and the frame is a
constructive stand-in for the complete Boolean algebra RO(2^ℕ) used
in [1, §2].

The nodes of the full binary tree are the finite binary words,
ordered by extension. A set of words is open if it is closed under
extension, and regular if it contains every word below which it is
dense: s belongs to U whenever, for every extension v of s, it is not
the case that no extension of v belongs to U. The regular open sets
form a frame, the double negation sublocale of the frame of open
sets. Classically this is the Cohen algebra, which is isomorphic to
RO(2^ℕ), because the cylinders form a basis of Cantor space that is
ordered like the tree.

The cylinder of a word s is the set of its extensions, and the
complement of a cylinder is the set of words with no common extension
with s. The properties of a cylinder system are proved using that the
prefix relation on words is decidable. Hence the locale has no
points, by gist.RealCohesion.Cylinders.

[1] Answers to some open problems in real-cohesive homotopy type
    theory. Research notes, draft of 25 October 2026.
    references/C01-write-up-2026-10-25.tex

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import MLTT.List hiding ([_])
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.CohenFrame
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

open import Locales.Complements pt fe
open import Locales.Frame pt fe hiding (𝟚 ; ₀ ; ₁)
open import Locales.Point.Definition pt fe
open import MLTT.Two-Properties
open import Naturals.Properties
open import Slice.Family
open import UF.DiscreteAndSeparated
open import UF.Logic
open import UF.NotNotStablePropositions
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import UF.UniverseEmbedding
open import gist.RealCohesion.Cylinders pt fe

open AllCombinators pt fe hiding (_∨_)
open DefnOfCPF
open PropositionalTruncation pt

\end{code}

Words and the prefix relation.

\begin{code}

Word : 𝓤₀ ̇
Word = List 𝟚

_≼_ : Word → Word → 𝓤₀ ̇
[]      ≼ v       = 𝟙
(a ∷ s) ≼ []      = 𝟘
(a ∷ s) ≼ (b ∷ v) = (a ＝ b) × (s ≼ v)

infix 4 _≼_

≼-is-prop : (s v : Word) → is-prop (s ≼ v)
≼-is-prop []      v       = 𝟙-is-prop
≼-is-prop (a ∷ s) []      = 𝟘-is-prop
≼-is-prop (a ∷ s) (b ∷ v) = ×-is-prop 𝟚-is-set (≼-is-prop s v)

≼-refl : (s : Word) → s ≼ s
≼-refl []      = ⋆
≼-refl (a ∷ s) = refl , ≼-refl s

≼-trans : (s t v : Word) → s ≼ t → t ≼ v → s ≼ v
≼-trans []      t       v       _       _       = ⋆
≼-trans (a ∷ s) []      v       l       _       = 𝟘-elim l
≼-trans (a ∷ s) (b ∷ t) []      _       m       = 𝟘-elim m
≼-trans (a ∷ s) (b ∷ t) (c ∷ v) (p , l) (q , m) = (p ∙ q) , ≼-trans s t v l m

≼-is-decidable : (s v : Word) → is-decidable (s ≼ v)
≼-is-decidable []      v       = inl ⋆
≼-is-decidable (a ∷ s) []      = inr id
≼-is-decidable (a ∷ s) (b ∷ v) = γ (𝟚-is-discrete a b) (≼-is-decidable s v)
 where
  γ : is-decidable (a ＝ b) → is-decidable (s ≼ v)
    → is-decidable ((a ∷ s) ≼ (b ∷ v))
  γ (inl p) (inl l) = inl (p , l)
  γ (inl p) (inr ν) = inr (λ (_ , l) → ν l)
  γ (inr μ) _       = inr (λ (p , _) → μ p)

≼-++ : (s r : Word) → s ≼ (s ++ r)
≼-++ []      r = ⋆
≼-++ (a ∷ s) r = refl , ≼-++ s r

\end{code}

If s is not a prefix of v, some extension of v has no common extension
with s.

\begin{code}

separation : (s v : Word)
           → ¬ (s ≼ v)
           → Σ v′ ꞉ Word , (v ≼ v′) × ((w : Word) → v′ ≼ w → ¬ (s ≼ w))
separation []      v       ν = 𝟘-elim (ν ⋆)
separation (a ∷ s) []      ν = (complement a ∷ []) , ⋆ , γ
 where
  γ : (w : Word) → (complement a ∷ []) ≼ w → ¬ ((a ∷ s) ≼ w)
  γ []      l       _       = l
  γ (c ∷ w) (p , _) (q , _) = complement-no-fp a (q ∙ p ⁻¹)
separation (a ∷ s) (b ∷ v) ν = γ (𝟚-is-discrete a b)
 where
  γ : is-decidable (a ＝ b)
    → Σ v′ ꞉ Word , ((b ∷ v) ≼ v′) × ((w : Word) → v′ ≼ w → ¬ ((a ∷ s) ≼ w))
  γ (inr μ) = (b ∷ v) , ≼-refl (b ∷ v) , δ
   where
    δ : (w : Word) → (b ∷ v) ≼ w → ¬ ((a ∷ s) ≼ w)
    δ []      l       _       = l
    δ (c ∷ w) (p , _) (q , _) = μ (q ∙ p ⁻¹)
  γ (inl p) = (b ∷ pr₁ IH) , (refl , pr₁ (pr₂ IH)) , δ
   where
    IH : Σ v′ ꞉ Word , (v ≼ v′) × ((w : Word) → v′ ≼ w → ¬ (s ≼ w))
    IH = separation s v (λ l → ν (p , l))

    δ : (w : Word) → (b ∷ pr₁ IH) ≼ w → ¬ ((a ∷ s) ≼ w)
    δ []      l       _       = l
    δ (c ∷ w) (_ , l) (_ , k) = pr₂ (pr₂ IH) w l k

\end{code}

Three more facts about prefixes: extensions of a prefix of v pass
through a child of it, the two children of a word have no common
extension, and a word is not a prefix of a shorter one.

\begin{code}

child-of-prefix : (s v : Word) → s ≼ v → (b : 𝟚) → Σ c ꞉ 𝟚 , s ⌢ c ≼ v ⌢ b
child-of-prefix []      []       _       b = b , refl , ⋆
child-of-prefix []      (d ∷ v)  _       b = d , refl , ⋆
child-of-prefix (a ∷ s) []       l       b = 𝟘-elim l
child-of-prefix (a ∷ s) (a′ ∷ v) (p , l) b = pr₁ IH , p , pr₂ IH
 where
  IH = child-of-prefix s v l b

children-are-incompatible : (s w : Word) (a b : 𝟚)
                          → s ⌢ a ≼ w → s ⌢ b ≼ w → a ＝ b
children-are-incompatible []      []      a b l       _       = 𝟘-elim l
children-are-incompatible []      (c ∷ w) a b (p , _) (q , _) = p ∙ q ⁻¹
children-are-incompatible (d ∷ s) []      a b l       _       = 𝟘-elim l
children-are-incompatible (d ∷ s) (c ∷ w) a b (_ , l) (_ , m) =
 children-are-incompatible s w a b l m

no-long-prefix : (s v : Word) (b : 𝟚) → length s ＝ length v → ¬ (s ⌢ b ≼ v)
no-long-prefix []      []      b _ l       = l
no-long-prefix []      (c ∷ v) b p _       = positive-not-zero (length v) (p ⁻¹)
no-long-prefix (a ∷ s) []      b p l       = l
no-long-prefix (a ∷ s) (c ∷ v) b p (_ , l) = no-long-prefix s v b (succ-lc p) l

\end{code}

Open and regular sets of words.

\begin{code}

𝓟W : 𝓤₁ ̇
𝓟W = Word → Ω 𝓤₀

is-open : 𝓟W → 𝓤₀ ̇
is-open U = (s v : Word) → s ≼ v → U s holds → U v holds

dense-below : 𝓟W → Word → 𝓤₀ ̇
dense-below U s = (v : Word) → s ≼ v → ¬¬ (∃ w ꞉ Word , (v ≼ w) × U w holds)

is-regular : 𝓟W → 𝓤₀ ̇
is-regular U = (s : Word) → dense-below U s → U s holds

being-open-is-prop : (U : 𝓟W) → is-prop (is-open U)
being-open-is-prop U = Π₄-is-prop fe (λ _ v _ _ → holds-is-prop (U v))

dense-below-is-prop : (U : 𝓟W) (s : Word) → is-prop (dense-below U s)
dense-below-is-prop U s = Π₂-is-prop fe (λ _ _ → negations-are-props fe)

being-regular-is-prop : (U : 𝓟W) → is-prop (is-regular U)
being-regular-is-prop U = Π₂-is-prop fe (λ s _ → holds-is-prop (U s))

dense-below-is-monotone : (U V : 𝓟W)
                        → ((w : Word) → U w holds → V w holds)
                        → (s : Word) → dense-below U s → dense-below V s
dense-below-is-monotone U V f s d v l =
 ¬¬-functor (∥∥-functor (λ (w , m , h) → w , m , f w h)) (d v l)

RO : 𝓤₁ ̇
RO = Σ U ꞉ 𝓟W , is-open U × is-regular U

_∈ᴿ_ : Word → RO → 𝓤₀ ̇
s ∈ᴿ U = pr₁ U s holds

RO-is-open : (U : RO) → is-open (pr₁ U)
RO-is-open U = pr₁ (pr₂ U)

RO-is-regular : (U : RO) → is-regular (pr₁ U)
RO-is-regular U = pr₂ (pr₂ U)

_⊆ᴿ_ : RO → RO → Ω 𝓤₀
U ⊆ᴿ V = Ɐ s ꞉ Word , pr₁ U s ⇒ pr₁ V s

to-RO-＝ : {U V : RO} → (U ⊆ᴿ V) holds → (V ⊆ᴿ U) holds → U ＝ V
to-RO-＝ f g =
 to-subtype-＝ (λ W → ×-is-prop (being-open-is-prop W) (being-regular-is-prop W))
  (dfunext fe (λ s → Ω-extensionality pe fe (f s) (g s)))

\end{code}

The frame operations. Meets are intersections, and the join of a
family is the set of words below which its union is dense.

\begin{code}

𝟏ᴿ : RO
𝟏ᴿ = (λ _ → ⊤) , (λ _ _ _ _ → ⋆) , (λ _ _ → ⋆)

meet-of-sets : RO → RO → 𝓟W
meet-of-sets U V s = pr₁ U s ∧ pr₁ V s

_∩ᴿ_ : RO → RO → RO
U ∩ᴿ V = meet-of-sets U V , o , r
 where
  o : is-open (meet-of-sets U V)
  o s v l (h , k) = RO-is-open U s v l h , RO-is-open V s v l k

  r : is-regular (meet-of-sets U V)
  r s d = RO-is-regular U s
   (dense-below-is-monotone (meet-of-sets U V) (pr₁ U) (λ _ → pr₁) s d) ,
          RO-is-regular V s
           (dense-below-is-monotone (meet-of-sets U V) (pr₁ V) (λ _ → pr₂) s d)

⋃ᴿ : Fam 𝓤₀ RO → 𝓟W
⋃ᴿ S w = Ǝ i ꞉ index S , w ∈ᴿ (S [ i ])

join-of-sets : Fam 𝓤₀ RO → 𝓟W
join-of-sets S s = dense-below (⋃ᴿ S) s , dense-below-is-prop (⋃ᴿ S) s

⋁ᴿ_ : Fam 𝓤₀ RO → RO
⋁ᴿ S = join-of-sets S , o , r
 where
  o : is-open (join-of-sets S)
  o s v l d v′ m = d v′ (≼-trans s v v′ l m)

  r : is-regular (join-of-sets S)
  r s d v l ν = d v l γ
   where
    δ : (Σ w ꞉ Word , (v ≼ w) × dense-below (⋃ᴿ S) w) → 𝟘
    δ (w , m , e) = e w (≼-refl w)
                     (λ t → ν (∥∥-functor
                       (λ (w′ , m′ , k) → w′ , ≼-trans v w w′ m m′ , k) t))

    γ : ¬ (∃ w ꞉ Word , (v ≼ w) × dense-below (⋃ᴿ S) w)
    γ = ∥∥-rec 𝟘-is-prop δ

RO-data : frame-data 𝓤₀ 𝓤₀ RO
RO-data = _⊆ᴿ_ , 𝟏ᴿ , _∩ᴿ_ , ⋁ᴿ_

RO-satisfies-frame-laws : satisfies-frame-laws RO-data
RO-satisfies-frame-laws = ((ρ , τ) , α) , top , meets , joins , distributive
 where
  open Meets _⊆ᴿ_
  open Joins _⊆ᴿ_

  ρ : is-reflexive _⊆ᴿ_ holds
  ρ U s h = h

  τ : is-transitive _⊆ᴿ_ holds
  τ U V W f g s h = g s (f s h)

  α : is-antisymmetric _⊆ᴿ_
  α = to-RO-＝

  top : (U : RO) → (U ⊆ᴿ 𝟏ᴿ) holds
  top U s _ = ⋆

  meets : ((U , V) : RO × RO) → ((U ∩ᴿ V) is-glb-of (U , V)) holds
  meets (U , V) = ((λ s → pr₁) , (λ s → pr₂)) , γ
   where
    γ : ((W , _) : lower-bound (U , V)) → (W ⊆ᴿ (U ∩ᴿ V)) holds
    γ (W , f , g) s h = f s h , g s h

  joins : (S : Fam 𝓤₀ RO) → ((⋁ᴿ S) is-lub-of S) holds
  joins S = upper , least
   where
    upper : (i : index S) → ((S [ i ]) ⊆ᴿ (⋁ᴿ S)) holds
    upper i s h v l ν =
     ν ∣ v , ≼-refl v , ∣ i , RO-is-open (S [ i ]) s v l h ∣ ∣

    least : ((V , _) : upper-bound S) → ((⋁ᴿ S) ⊆ᴿ V) holds
    least (V , f) s d =
     RO-is-regular V s (dense-below-is-monotone (⋃ᴿ S) (pr₁ V) γ s d)
     where
      γ : (w : Word) → ⋃ᴿ S w holds → w ∈ᴿ V
      γ w = ∥∥-rec (holds-is-prop (pr₁ V w)) (λ (i , k) → f i w k)

  distributive : ((U , S) : RO × Fam 𝓤₀ RO)
               → U ∩ᴿ (⋁ᴿ (index S , λ i → S [ i ]))
               ＝ ⋁ᴿ (index S , λ i → U ∩ᴿ (S [ i ]))
  distributive (U , S) = to-RO-＝ f g
   where
    T : Fam 𝓤₀ RO
    T = index S , λ i → U ∩ᴿ (S [ i ])

    f : ((U ∩ᴿ (⋁ᴿ S)) ⊆ᴿ (⋁ᴿ T)) holds
    f s (h , d) v l = ¬¬-functor (∥∥-functor γ) (d v l)
     where
      γ : (Σ w ꞉ Word , (v ≼ w) × ⋃ᴿ S w holds)
        → Σ w ꞉ Word , (v ≼ w) × ⋃ᴿ T w holds
      γ (w , m , t) = w , m ,
                      ∥∥-functor
                       (λ (i , k) →
                         i , RO-is-open U s w (≼-trans s v w l m) h , k)
                       t

    g : ((⋁ᴿ T) ⊆ᴿ (U ∩ᴿ (⋁ᴿ S))) holds
    g s d = RO-is-regular U s (dense-below-is-monotone (⋃ᴿ T) (pr₁ U) γ₁ s d) ,
            dense-below-is-monotone (⋃ᴿ T) (⋃ᴿ S) γ₂ s d
     where
      γ₁ : (w : Word) → ⋃ᴿ T w holds → w ∈ᴿ U
      γ₁ w = ∥∥-rec (holds-is-prop (pr₁ U w)) (λ (i , h , _) → h)

      γ₂ : (w : Word) → ⋃ᴿ T w holds → ⋃ᴿ S w holds
      γ₂ w = ∥∥-functor (λ (i , _ , k) → i , k)

Cohen-frame : Frame 𝓤₁ 𝓤₀ 𝓤₀
Cohen-frame = RO , RO-data , RO-satisfies-frame-laws

Cohen-frame-is-nontrivial : 𝟎[ Cohen-frame ] ≠ 𝟏[ Cohen-frame ]
Cohen-frame-is-nontrivial p = γ (transport ([] ∈ᴿ_) (p ⁻¹) ⋆)
 where
  γ : ¬ ([] ∈ᴿ 𝟎[ Cohen-frame ])
  γ d = d [] ⋆ (∥∥-rec 𝟘-is-prop
                 (λ (w , _ , t) → ∥∥-rec 𝟘-is-prop (λ (i , _) → 𝟘-elim i) t))

\end{code}

Cylinders and their complements.

\begin{code}

cylinder : Word → RO
cylinder s = P , o , r
 where
  P : 𝓟W
  P v = (s ≼ v) , ≼-is-prop s v

  o : is-open P
  o v v′ l h = ≼-trans s v v′ h l

  r : is-regular P
  r v d = decidable-types-are-¬¬-stable (≼-is-decidable s v) γ
   where
    γ : ¬¬ (s ≼ v)
    γ ν = d v′ m (∥∥-rec 𝟘-is-prop (λ (w , k , l) → incompatible w k l))
     where
      σ = separation s v ν
      v′ = pr₁ σ
      m = pr₁ (pr₂ σ)
      incompatible = pr₂ (pr₂ σ)

anticylinder : Word → RO
anticylinder s = P , o , r
 where
  P : 𝓟W
  P v = ((w : Word) → v ≼ w → ¬ (s ≼ w)) ,
        Π₂-is-prop fe (λ _ _ → negations-are-props fe)

  o : is-open P
  o v v′ l h w m = h w (≼-trans v v′ w l m)

  r : is-regular P
  r v d w m k = d w m (∥∥-rec 𝟘-is-prop
                        (λ (w′ , m′ , h) →
                          h w′ (≼-refl w′) (≼-trans s w w′ k m′)))

Cohen-cylinders : Cylinder-System Cohen-frame
Cohen-cylinders = record
 { cyl                = cylinder
  ; cyl′               = anticylinder
  ; cyl-root           = to-RO-＝ (λ _ _ → ⋆) (λ _ _ → ⋆)
  ; cyl-split          = split
  ; cyl-disjoint       = disjoint
  ; cyl′-is-complement = complement-law
  ; cyl′-cover         = cover
  }
 where
  split : (s : Word)
        → cylinder s ＝ cylinder (s ⌢ ₀) ∨[ Cohen-frame ] cylinder (s ⌢ ₁)
  split s = to-RO-＝ β γ
   where
    S : Fam 𝓤₀ RO
    S = binary-family 𝓤₀ (cylinder (s ⌢ ₀)) (cylinder (s ⌢ ₁))

    pick : (w : Word) (c : 𝟚) → s ⌢ c ≼ w → ⋃ᴿ S w holds
    pick w ₀ l = ∣ inl ⋆ , l ∣
    pick w ₁ l = ∣ inr ⋆ , l ∣

    β : (cylinder s ⊆ᴿ (⋁ᴿ S)) holds
    β v h v′ l ν =
     ν ∣ v′ ⌢ ₀ , ≼-++ v′ (₀ ∷ []) , pick (v′ ⌢ ₀) (pr₁ c) (pr₂ c) ∣
     where
      c = child-of-prefix s v′ (≼-trans s v v′ h l) ₀

    δ : (i : index S) → ((S [ i ]) ⊆ᴿ cylinder s) holds
    δ (inl ⋆) v h = ≼-trans s (s ⌢ ₀) v (≼-++ s (₀ ∷ [])) h
    δ (inr ⋆) v h = ≼-trans s (s ⌢ ₁) v (≼-++ s (₁ ∷ [])) h

    γ : ((⋁ᴿ S) ⊆ᴿ cylinder s) holds
    γ = ⋁[ Cohen-frame ]-least S (cylinder s , δ)

  disjoint : (s : Word)
           → cylinder (s ⌢ ₀) ∧[ Cohen-frame ] cylinder (s ⌢ ₁)
           ＝ 𝟎[ Cohen-frame ]
  disjoint s = only-𝟎-is-below-𝟎 Cohen-frame _
                (λ v (h , k) → 𝟘-elim
                  (zero-is-not-one (children-are-incompatible s v ₀ ₁ h k)))

  complement-law : (s : Word)
                 → is-boolean-complement-of Cohen-frame (anticylinder s)
                    (cylinder s) holds
  complement-law s = disjointness , covering
   where
    disjointness : cylinder s ∧[ Cohen-frame ] anticylinder s ＝ 𝟎[ Cohen-frame ]
    disjointness = only-𝟎-is-below-𝟎 Cohen-frame _
                    (λ v (h , k) → 𝟘-elim (k v (≼-refl v) h))

    γ : (𝟏ᴿ ⊆ᴿ (cylinder s ∨[ Cohen-frame ] anticylinder s)) holds
    γ v _ v′ l ν = δ (≼-is-decidable s v′)
     where
      δ : is-decidable (s ≼ v′) → 𝟘
      δ (inl h) = ν ∣ v′ , ≼-refl v′ , ∣ inl ⋆ , h ∣ ∣
      δ (inr μ) = ν ∣ pr₁ σ , pr₁ (pr₂ σ) , ∣ inr ⋆ , pr₂ (pr₂ σ) ∣ ∣
       where
        σ = separation s v′ μ

    covering : cylinder s ∨[ Cohen-frame ] anticylinder s ＝ 𝟏[ Cohen-frame ]
    covering = only-𝟏-is-above-𝟏 Cohen-frame _ γ

  cover : (α : ℕ → 𝟚)
        → ⋁[ Cohen-frame ] (Lift 𝓤₀ ℕ , (λ n → anticylinder (α ↾ lower n)))
        ＝ 𝟏[ Cohen-frame ]
  cover α = only-𝟏-is-above-𝟏 Cohen-frame _ γ
   where
    γ : (𝟏ᴿ ⊆ᴿ (⋁ᴿ (Lift 𝓤₀ ℕ , (λ n → anticylinder (α ↾ lower n))))) holds
    γ v _ v′ l ν =
     ν ∣ pr₁ σ , pr₁ (pr₂ σ) , ∣ lift 𝓤₀ (succ m) , pr₂ (pr₂ σ) ∣ ∣
     where
      m = length v′
      σ = separation (α ↾ succ m) v′
           (no-long-prefix (α ↾ m) v′ (α m) (length-↾ α m))

\end{code}

Hence the Cohen locale has no points.

\begin{code}

Cohen-locale : Locale 𝓤₁ 𝓤₀ 𝓤₀
Cohen-locale = frame-to-locale Cohen-frame

Cohen-locale-has-no-points : ¬ Point Cohen-locale
Cohen-locale-has-no-points = cylinder-locales-have-no-points Cohen-cylinders

\end{code}
