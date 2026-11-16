Adapted for the Orbifolds library by Claude Opus 5.5, an AI model made by
Anthropic, prompted by Colin Zwanziger, 12 November 2026 (local time),
at orbifold gate H9, with Astra's release of 13 November 2026 (UTC). The
source is Claude Fable 5.2's scratch check StableClassifierUniverseCheck.lagda
(SHA-256
ee879bbb9d4c4a84ae0bcab05faef72814ad61bb56def4c09c696f165e4f0479), in
provenance/companions/orbifolds-h9-universe-2026-11-13.zip, code of
this project. Changes: the module name (gist.Scratch to gist.Orbifolds)
and the imports of the other adapted modules; only the classifier part
(items 1 and 2 below) is kept, since Lemmas A and B are proved against
the existing modality interface in LemmasAB. The original text follows.
The two audits that it names are
references/A18-h9-universe-interface-audit.txt and
references/A15-h9-followup-audit.txt.

Claude (Fable), 13 November 2026.

A scratch check of the universe levels in the convention for Lemmas A and B
of the orbifolds roadmap (gate H9), as fixed in Astra's two source audits
`h9-universe-interface-audit.txt` and `fable-h9-followup-audit.txt`.

It is NOT part of the formalization and it does not use the Orbifolds
library.  The modality is abstracted to what the same-universe interface
provides at one universe: a reflector ○ with unit η on that universe, and a
recursor into types of that universe that are null for the generators.  The
check then proves, with function extensionality and propositional
extensionality at the universe of the propositions only:

 1. the type Ω¬¬ 𝓦 of ¬¬-stable propositions of 𝓦 is ¬¬-separated;
 2. it is null for every pointed type whose points are all ¬¬-equal to the
    base point (the property that Postulate K gives for the spectra);
 3. Lemma A for a carrier X : 𝓦, with the modality at (𝓦 ⊔ 𝓣) ⁺ for any 𝓣:
    if η (lift x) ＝ η (lift y) then ¬¬ (x ＝ y);
 4. the two maps of Lemma B between the fibre of the inclusion of a stable
    subtype and E (η z), for E w = ∥ Σ s , η (j s) ＝ w ∥, with a predicate
    that takes values in the universe of the modality;
 5. the two instances that the route for H9 needs, against one and the same
    modality at 𝓤 ⁺: carriers in 𝓤 (the manifolds) and carriers in 𝓤₀ (the
    Euclidean spaces, since the smooth line lives in 𝓤₀).

No external code is used or adapted.  No postulate, no cohesion.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module gist.Orbifolds.StableClassifier where

open import MLTT.Spartan
open import UF.Equiv
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UniverseEmbedding using (Lift ; lift ; lower)

Ω¬¬ : (𝓦 : Universe) → 𝓦 ⁺ ̇
Ω¬¬ 𝓦 = Σ Q ꞉ 𝓦 ̇ , is-prop Q × (¬¬ Q → Q)

module classifier
        (fe : Fun-Ext)
        {𝓦 : Universe}
        (pe : propext 𝓦)
       where

 Ω¬¬-to-＝ : (P Q : Ω¬¬ 𝓦) → (pr₁ P → pr₁ Q) → (pr₁ Q → pr₁ P) → P ＝ Q
 Ω¬¬-to-＝ (P , i , s) (Q , j , t) f g =
  to-subtype-＝
   (λ Z → Σ-is-prop (being-prop-is-prop fe) (λ k → Π-is-prop fe (λ _ → k)))
   (pe i j f g)

 Ω¬¬-is-¬¬-separated : (P Q : Ω¬¬ 𝓦) → ¬¬ (P ＝ Q) → P ＝ Q
 Ω¬¬-is-¬¬-separated P Q ν = Ω¬¬-to-＝ P Q f g
  where
   f : pr₁ P → pr₁ Q
   f p = pr₂ (pr₂ Q) (λ u → ν (λ e → u (transport pr₁ e p)))

   g : pr₁ Q → pr₁ P
   g q = pr₂ (pr₂ P) (λ u → ν (λ e → u (transport pr₁ (e ⁻¹) q)))

 module _ {𝓣 : Universe} {B : 𝓣 ̇ } (b : B) (ν : (v : B) → ¬¬ (v ＝ b)) where

  maps-into-Ω¬¬-are-constant : (f : B → Ω¬¬ 𝓦) (v : B) → f v ＝ f b
  maps-into-Ω¬¬-are-constant f v =
   Ω¬¬-is-¬¬-separated (f v) (f b) (¬¬-functor (ap f) (ν v))

  Ω¬¬-is-null : is-equiv (λ (P : Ω¬¬ 𝓦) (_ : B) → P)
  Ω¬¬-is-null =
   qinvs-are-equivs
    (λ P _ → P)
    ((λ f → f b) ,
     (λ P → refl) ,
     (λ f → dfunext fe (λ v → (maps-into-Ω¬¬-are-constant f v) ⁻¹)))

\end{code}
