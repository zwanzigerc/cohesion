import RealContinuity.Stage
import Mathlib.CategoryTheory.Sites.Canonical

/-!
# The controlled topology on stages

`H` consists of the finite composites of open embeddings between stages and of
projections from actual base changes of designated maps (isomorphic copies
included). Every `H`-arrow is open. A sieve is covering iff it contains a
point-surjective family of `H`-arrows.

The weak pullback lemma: pulling an `H`-arrow back along any map from a stage
admits a point-surjective refinement by `H`-arrows. For an open embedding the
pullback is an open subspace, covered by connected open stages; for a
base-change projection the further pullback is again a designated pullback.
Identities, the lemma and composition give the Grothendieck axioms.

Every covering sieve contains, by definition, a jointly surjective family of
open maps. An `H`-arrow also covers its actual open image (`isH_corestriction`).

All presheaves `T(Z)(U) = C(U, Z)` are sheaves, for every space `Z`; in particular
the topology is subcanonical. Matching families agree on ordinary points of
overlaps because point maps are morphisms of stages; the joint open quotient
property makes the glued function continuous.
-/

noncomputable section

open Set Topology Filter CategoryTheory Opposite

namespace RealContinuity

namespace Stage

/-! ### `H`-arrows -/

/-- Isomorphic copies of the projections from designated base changes. -/
def IsPbProj {X Y : Stage} (h : X ⟶ Y) : Prop :=
  ∃ (g : GIdx) (f : C(Y.X, g.Base)) (φ : X.X ≃ₜ TopPullback f g.map),
    ∀ x, h x = pbFst f g.map (φ x)

/-- The arrows `H`: finite composites of open embeddings and designated base-change
projections. -/
inductive IsH : {X Y : Stage} → (X ⟶ Y) → Prop
  | openEmb {X Y : Stage} (h : X ⟶ Y) : IsOpenEmbedding h → IsH h
  | pbProj {X Y : Stage} (h : X ⟶ Y) : IsPbProj h → IsH h
  | comp {X Y Z : Stage} (h : X ⟶ Y) (k : Y ⟶ Z) : IsH h → IsH k → IsH (h ≫ k)

theorem IsH.id (X : Stage) : IsH (𝟙 X) := .openEmb _ IsOpenEmbedding.id

theorem isPbProj_pbProj (U : Stage) (g : GIdx) (f : C(U.X, g.Base)) : IsPbProj (pbProj U g f) :=
  ⟨g, f, pbHomeo U g f, fun _ => rfl⟩

theorem isH_pbProj (U : Stage) (g : GIdx) (f : C(U.X, g.Base)) : IsH (Stage.pbProj U g f) :=
  .pbProj _ (isPbProj_pbProj U g f)

theorem isH_opnIncl (U : Stage) (O : Set U.X) (hO : IsOpen O) (hc : IsConnected O) :
    IsH (Stage.opnIncl U O hO hc) :=
  .openEmb _ (isOpenEmbedding_opnIncl U O hO hc)

/-- Every `H`-arrow is open. -/
theorem IsH.isOpenMap {X Y : Stage} {h : X ⟶ Y} (hh : IsH h) : IsOpenMap h := by
  induction hh with
  | openEmb h hemb => exact hemb.isOpenMap
  | @pbProj X Y h hp =>
    obtain ⟨g, f, φ, hφ⟩ := hp
    have e : (h : X.X → Y.X) = pbFst f g.map ∘ φ := funext hφ
    rw [e]
    exact (pbFst_isOpenMap (f := f) g.goodMap.isOpenMap).comp φ.isOpenMap
  | comp h k _ _ ihh ihk => exact ihk.comp ihh

/-! ### The weak pullback lemma -/

/-- Base change of a topological pullback along a map of bases. -/
def pbMap {U U' D B : Type} [TopologicalSpace U] [TopologicalSpace U'] [TopologicalSpace D]
    [TopologicalSpace B] (f : C(U, B)) (g : C(D, B)) (k : C(U', U)) :
    C(TopPullback (f.comp k) g, TopPullback f g) :=
  ⟨fun p => ⟨(k p.1.1, p.1.2), p.2⟩,
    ((k.continuous.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val)).subtype_mk _⟩

/-- **Weak pullback lemma.** For an `H`-arrow `h : X → Y`, a map `k : Y' → Y` and a
point `(y', x)` of the set-theoretic pullback, there is an `H`-arrow `a : W → Y'`
with a lift `b : W → X` over `Y`, hitting `(y', x)`. -/
theorem IsH.pullback {X Y : Stage} {h : X ⟶ Y} (hh : IsH h) :
    ∀ {Y' : Stage} (k : Y' ⟶ Y) (y' : Y'.X) (x : X.X), k y' = h x →
      ∃ (W : Stage) (a : W ⟶ Y') (b : W ⟶ X), IsH a ∧ a ≫ k = b ≫ h ∧
        ∃ w, a w = y' ∧ b w = x := by
  induction hh with
  | @openEmb X Y h hemb =>
    intro Y' k y' x hx
    have hO : IsOpen (k ⁻¹' range h) := hemb.isOpen_range.preimage (hom_continuous k)
    obtain ⟨O, hOo, hOc, hyO, hOsub⟩ := exists_opn (hO.mem_nhds ⟨x, hx.symm⟩)
    let e := hemb.isEmbedding.toHomeomorph
    let a := Stage.opnIncl Y' O hOo hOc
    have ha : ∀ w, k (a w) ∈ range h := fun w => by
      have := range_opnIncl Y' O hOo hOc ▸ mem_range_self (f := a) w
      exact hOsub this
    let b : opn Y' O hOo hOc ⟶ X :=
      ofHom ((e.symm : C(range h, X.X)).comp
        ⟨fun w => ⟨k (a w), ha w⟩,
          ((hom_continuous k).comp (hom_continuous a)).subtype_mk _⟩)
    have hb : ∀ w, h (b w) = k (a w) := fun w => by
      have := congrArg Subtype.val (e.apply_symm_apply ⟨k (a w), ha w⟩)
      rw [IsEmbedding.toHomeomorph_apply_coe] at this
      exact this
    refine ⟨opn Y' O hOo hOc, a, b, isH_opnIncl _ _ _ _, hom_ext fun w => (hb w).symm,
      ⟨y'.1, y', hyO, rfl⟩, rfl, ?_⟩
    apply hemb.injective
    rw [hb]; exact hx
  | @pbProj X Y h hp =>
    intro Y' k y' x hx
    obtain ⟨g, f, φ, hφ⟩ := hp
    let W := pb Y' g (f.comp (toCont k))
    let a := Stage.pbProj Y' g (f.comp (toCont k))
    let b : W ⟶ X := ofHom ((φ.symm : C(TopPullback f g.map, X.X)).comp
      ((pbMap f g.map (toCont k)).comp (pbHomeo Y' g (f.comp (toCont k)) :
        C(W.X, TopPullback (f.comp (toCont k)) g.map))))
    have hb : ∀ w, h (b w) = k (a w) := fun w => by
      rw [hφ]
      change pbFst f g.map (φ (φ.symm _)) = _
      rw [φ.apply_symm_apply]
      rfl
    refine ⟨W, a, b, isH_pbProj _ _ _, hom_ext fun w => (hb w).symm, ?_⟩
    have hmem : (y', ((φ x).1.2)) ∈ TopPullback (f.comp (toCont k)) g.map := by
      change f (k y') = g.map (φ x).1.2
      rw [hx, hφ]; exact (φ x).2
    refine ⟨(pbHomeo Y' g (f.comp (toCont k))).symm ⟨_, hmem⟩, ?_, ?_⟩
    · change pbFst _ _ ((pbHomeo Y' g _) ((pbHomeo Y' g _).symm _)) = y'
      rw [Homeomorph.apply_symm_apply]; rfl
    · change φ.symm (pbMap f g.map (toCont k) ((pbHomeo Y' g _) ((pbHomeo Y' g _).symm _))) = x
      rw [Homeomorph.apply_symm_apply, φ.symm_apply_eq]
      apply Subtype.ext
      change (k y', (φ x).1.2) = (φ x).1
      rw [hx, hφ]; rfl
  | @comp X Y Z h₁ h₂ _ _ ih₁ ih₂ =>
    intro Y' k y' x hx
    obtain ⟨W₁, a₁, b₁, ha₁, hcomm₁, w₁, hw₁a, hw₁b⟩ := ih₂ k y' (h₁ x) hx
    obtain ⟨W, a, b, ha, hcomm, w, hwa, hwb⟩ := ih₁ b₁ w₁ x hw₁b
    refine ⟨W, a ≫ a₁, b, IsH.comp _ _ ha ha₁, ?_, w, ?_, hwb⟩
    · rw [Category.assoc, hcomm₁, ← Category.assoc, hcomm, Category.assoc]
    · change a₁ (a w) = y'
      rw [hwa, hw₁a]

/-! ### The topology -/

/-- A sieve covers when it contains a point-surjective family of `H`-arrows. -/
def Covers {U : Stage} (S : Sieve U) : Prop :=
  ∀ u : U.X, ∃ (V : Stage) (h : V ⟶ U), S h ∧ IsH h ∧ u ∈ range h

/-- **The controlled Grothendieck topology.** -/
def topology : GrothendieckTopology Stage where
  sieves U := {S | Covers S}
  top_mem' U u := ⟨U, 𝟙 U, trivial, IsH.id U, u, rfl⟩
  pullback_stable' := by
    intro U U' S k hS
    have hS' : Covers S := hS
    intro u'
    obtain ⟨V, h, hSh, hH, v, hv⟩ := hS' (k u')
    obtain ⟨W, a, b, ha, hcomm, w, hwa, -⟩ := hH.pullback k u' v hv.symm
    refine ⟨W, a, ?_, ha, w, hwa⟩
    change S (a ≫ k)
    rw [hcomm]
    exact S.downward_closed hSh b
  transitive' := by
    intro U S hS R hR
    have hS' : Covers S := hS
    intro u
    obtain ⟨V, h, hSh, hH, v, rfl⟩ := hS' u
    have hR' : Covers (R.pullback h) := hR hSh
    obtain ⟨V', h', hRh', hH', v', rfl⟩ := hR' v
    exact ⟨V', h' ≫ h, hRh', IsH.comp _ _ hH' hH, v', rfl⟩

theorem mem_topology {U : Stage} {S : Sieve U} : S ∈ topology U ↔ Covers S := Iff.rfl

/-- The sieve generated by one `H`-arrow onto its image covers that image. -/
theorem isH_corestriction {X Y : Stage} {h : X ⟶ Y} (hh : IsH h) {W : Stage} (i : W ⟶ Y)
    (hi : Function.Injective i) (hrange : range i ⊆ range h) (c : X ⟶ W) (hc : c ≫ i = h) :
    Sieve.generate (Presieve.singleton c) ∈ topology W := by
  intro w
  obtain ⟨x, hx⟩ := hrange ⟨w, rfl⟩
  obtain ⟨W', a, b, ha, hcomm, w', hwa, -⟩ := hh.pullback i w x hx.symm
  refine ⟨W', a, ⟨X, b, c, Presieve.singleton.mk, ?_⟩, ha, w', hwa⟩
  apply hom_ext
  intro z
  apply hi
  change i (c (b z)) = i (a z)
  rw [← comp_apply c i, hc]
  exact (congrArg (fun m : W' ⟶ Y => m z) hcomm).symm

/-! ### Sheaves of continuous maps -/

/-- The presheaf `T(Z)(U) = C(U, Z)`. -/
abbrev contPresheaf (Z : Type) [TopologicalSpace Z] : Stageᵒᵖ ⥤ Type where
  obj U := C(U.unop.X, Z)
  map f := ↾fun φ => φ.comp (toCont f.unop)
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem contPresheaf_map_apply (Z : Type) [TopologicalSpace Z] {U V : Stageᵒᵖ}
    (f : U ⟶ V) (φ : C(U.unop.X, Z)) (x : V.unop.X) :
    ((contPresheaf Z).map f φ) x = φ (f.unop x) := rfl

/-- The constant map at a point of a stage. -/
def pointAt {U : Stage} (u : U.X) : point ⟶ U := ofHom (ContinuousMap.const _ u)

@[simp] theorem pointAt_apply {U : Stage} (u : U.X) (z : point.X) : pointAt u z = u := rfl

/-- **`T(Z)` is a sheaf** for every topological space `Z`. -/
theorem contPresheaf_isSheaf (Z : Type) [TopologicalSpace Z] :
    Presieve.IsSheaf topology (contPresheaf Z) := by
  intro U S hS x hx
  have hS' : Covers S := hS
  -- values along arrows of the sieve agree at points with the same image
  have key : ∀ {V₁ V₂ : Stage} (f₁ : V₁ ⟶ U) (f₂ : V₂ ⟶ U) (h₁ : S f₁) (h₂ : S f₂)
      (v₁ : V₁.X) (v₂ : V₂.X), f₁ v₁ = f₂ v₂ →
        (x f₁ h₁ : C(V₁.X, Z)) v₁ = (x f₂ h₂ : C(V₂.X, Z)) v₂ := by
    intro V₁ V₂ f₁ f₂ h₁ h₂ v₁ v₂ he
    have := hx (pointAt v₁) (pointAt v₂) h₁ h₂ (hom_ext fun _ => he)
    exact congrArg (fun φ : C(point.X, Z) => φ default) this
  choose V h hSh hH v hv using hS'
  let t : U.X → Z := fun u => (x (h u) (hSh u) : C((V u).X, Z)) (v u)
  have ht : ∀ {V' : Stage} (f : V' ⟶ U) (hf : S f) (y : V'.X),
      t (f y) = (x f hf : C(V'.X, Z)) y := by
    intro V' f hf y
    exact key _ _ _ _ _ _ (hv (f y))
  have hcont : Continuous t := by
    rw [continuous_def]
    intro O hO
    have e : t ⁻¹' O = ⋃ u, (h u) '' ((x (h u) (hSh u) : C((V u).X, Z)) ⁻¹' O) := by
      ext y
      constructor
      · intro hy
        exact mem_iUnion.mpr ⟨y, v y, hy, hv y⟩
      · intro hy
        obtain ⟨u, z, hz, rfl⟩ := mem_iUnion.mp hy
        change t (h u z) ∈ O
        rw [ht]; exact hz
    rw [e]
    exact isOpen_iUnion fun u =>
      (hH u).isOpenMap _ (hO.preimage (x (h u) (hSh u) : C((V u).X, Z)).continuous)
  refine ⟨(⟨t, hcont⟩ : C(U.X, Z)), fun V' f hf => ?_, fun y hy => ?_⟩
  · apply ContinuousMap.ext
    intro z
    exact ht f hf z
  · apply ContinuousMap.ext
    intro u
    have h1 : (contPresheaf Z).map (h u).op y = x (h u) (hSh u) := hy (h u) (hSh u)
    have h2 := congrArg (fun φ : C((V u).X, Z) => φ (v u)) h1
    calc (y : C(U.X, Z)) u = (y : C(U.X, Z)) (h u (v u)) := congrArg _ (hv u).symm
      _ = t u := h2

/-- **The topology is subcanonical**: representables are sheaves. -/
theorem isSheaf_yoneda_obj (U : Stage) : Presieve.IsSheaf topology (yoneda.obj U) :=
  contPresheaf_isSheaf U.X

instance : topology.Subcanonical :=
  GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj _ isSheaf_yoneda_obj

end Stage

end RealContinuity
