import PointlessEnd.Charts
import Mathlib.CategoryTheory.Sites.Coverage
import Mathlib.CategoryTheory.Sites.Canonical
import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# The open-cover topology on charts

A presieve on a chart `U` is an **open cover** when it consists of open embeddings whose
images join to `⊤` in `O(U)`. Open covers form a coverage: the pullback of an open cover
along any chart map is refined by the open embeddings below the pulled-back images (chart
basis), each of which factors through a member of the cover. The topology is the
generated Grothendieck topology, and a sieve covers exactly when its open embeddings have
images joining to `⊤` (`mem_topology_iff`).

* **Subcanonical**: representables are sheaves. A compatible family of maps `T_f ⟶ V` on an
  open cover glues to the frame homomorphism `w ↦ ⨆ {c ≤ a_f | f^* c ≤ x_f^* w}`
  (`glue`), using the chart basis to compare members on overlaps.
* **Constant presheaves are sheaves**: charts are connected and images of open embeddings
  are nonzero.
* **Codiscrete presheaves** `U ↦ (points of U → K)` are sheaves: every point of `U` factors
  through a member of an open cover.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory Limits Opposite

namespace PointlessEnd

namespace Chart

/-! ### Open covers -/

/-- The join of the images of the open embeddings in a presieve. -/
def imgSup {U : Chart} (R : Presieve U) : O U :=
  sSup {a | ∃ (T : Chart) (f : T ⟶ U), R f ∧ IsOpenEmb f a}

theorem le_imgSup {U T : Chart} {R : Presieve U} {f : T ⟶ U} (hf : R f) {a : O U}
    (ha : IsOpenEmb f a) : a ≤ imgSup R :=
  le_sSup ⟨T, f, hf, ha⟩

theorem imgSup_mono {U : Chart} {R R' : Presieve U} (h : R ≤ R') : imgSup R ≤ imgSup R' :=
  sSup_le_sSup fun _ ⟨T, f, hf, ha⟩ => ⟨T, f, h _ f hf, ha⟩

/-- **Open covers.** -/
def IsOpenCover {U : Chart} (R : Presieve U) : Prop :=
  (∀ ⦃T⦄ (f : T ⟶ U), R f → ∃ a, IsOpenEmb f a) ∧ imgSup R = ⊤

/-- An open embedding `m` lies below `y` iff `m^* y = ⊤`. -/
theorem IsOpenEmb.le_iff {T U : Chart} {m : T ⟶ U} {b : O U} (hm : IsOpenEmb m b) (y : O U) :
    b ≤ y ↔ m y = ⊤ := by
  constructor
  · intro h
    exact top_unique (hm.map_img.symm.le.trans (hom_mono m h))
  · intro h
    have := hm.inv_map y
    rw [h, hm.inv_top] at this
    exact this ▸ inf_le_left

/-- The pullback of an open cover along any map is refined by an open cover. -/
theorem pullback_refine {U V : Chart} (g : V ⟶ U) (y : O U) :
    g y = sSup {a | ∃ (T : Chart) (k : T ⟶ V), IsOpenEmb k a ∧ a ≤ g y} := by
  conv_lhs => rw [basis V (g y)]
  congr 1
  ext a
  exact ⟨fun ⟨h1, T, k, hk⟩ => ⟨T, k, hk, h1⟩, fun ⟨T, k, hk, h1⟩ => ⟨h1, T, k, hk⟩⟩

/-- **The coverage of open covers.** -/
def coverage : Coverage Chart where
  coverings U := {R | IsOpenCover R}
  pullback := by
    intro U V g R hR
    refine ⟨fun W k => ∃ a, IsOpenEmb k a ∧ ∃ (T : Chart) (f : T ⟶ U) (b : O U),
      R f ∧ IsOpenEmb f b ∧ a ≤ g b, ⟨fun W k ⟨a, hk, _⟩ => ⟨a, hk⟩, ?_⟩, ?_⟩
    · apply top_unique
      have hR2 := hR.2
      calc (⊤ : O V) = g (imgSup R) := by rw [hR2, map_top]
        _ = ⨆ b ∈ {a | ∃ (T : Chart) (f : T ⟶ U), R f ∧ IsOpenEmb f a}, g b := by
            rw [imgSup, map_sSup, sSup_image]
        _ ≤ _ := by
            refine iSup₂_le fun b ⟨T, f, hf, hb⟩ => ?_
            rw [pullback_refine g b]
            refine sSup_le fun a ⟨T', k, hk, hle⟩ => ?_
            exact le_imgSup ⟨a, hk, T, f, b, hf, hb, hle⟩ hk
    · intro W k ⟨a, hk, T, f, b, hf, hb, hle⟩
      have htop : (k ≫ g) b = ⊤ := by
        rw [comp_apply]
        exact (hk.le_iff (g b)).mp hle
      exact ⟨T, hb.lift (k ≫ g) htop, f, hf, hb.lift_comp _ _⟩

/-- **The open-cover topology.** -/
def topology : GrothendieckTopology Chart := coverage.toGrothendieck

/-- **Covering sieves**: their open embeddings have images joining to `⊤`. -/
theorem mem_topology_iff {U : Chart} {S : Sieve U} : S ∈ topology U ↔ imgSup S.arrows = ⊤ := by
  constructor
  · intro h
    induction h with
    | of X R hR =>
      exact top_unique (hR.2.ge.trans (imgSup_mono (Sieve.le_generate R)))
    | top X =>
      exact top_unique (le_imgSup (R := (⊤ : Sieve X).arrows) trivial (isOpenEmb_id X))
    | transitive X R S _ _ hR hS =>
      apply top_unique
      rw [← hR]
      refine sSup_le fun a ⟨T, f, hf, ha⟩ => ?_
      have h1 : imgSup (S.pullback f).arrows = ⊤ := hS hf
      rw [← ha.inv_top, ← h1, imgSup, ha.inv_sSup]
      refine iSup₂_le fun b ⟨T', k, hk, hb⟩ => ?_
      exact le_imgSup (R := S.arrows) hk (hb.comp ha)
  · intro h
    apply Coverage.mem_toGrothendieck_sieves_of_superset coverage
      (R := fun T f => S f ∧ ∃ a, IsOpenEmb f a)
    · intro T f hf
      exact hf.1
    · refine ⟨fun T f hf => hf.2, ?_⟩
      rw [← h]
      apply le_antisymm (imgSup_mono fun _ _ hf => hf.1)
      exact sSup_le_sSup fun a ⟨T, f, hf, ha⟩ => ⟨T, f, ⟨hf, a, ha⟩, ha⟩

/-- Covering sieves contain an open embedding through every point. -/
theorem exists_mem_of_point {U : Chart} {S : Sieve U} (hS : S ∈ topology U) (p : pt ⟶ U) :
    ∃ (T : Chart) (f : T ⟶ U) (a : O U), S f ∧ IsOpenEmb f a ∧ p a := by
  have h := mem_topology_iff.mp hS
  have hp : p (imgSup S.arrows) := by rw [h, map_top]; trivial
  rw [imgSup, map_sSup, sSup_image] at hp
  simp only [iSup_Prop_eq] at hp
  obtain ⟨a, ⟨T, f, hf, ha⟩, hpa⟩ := hp
  exact ⟨T, f, a, hf, ha, hpa⟩

/-- Covering sieves are nonempty. -/
theorem cover_nonempty {U : Chart} {S : Sieve U} (hS : S ∈ topology U) :
    ∃ (T : Chart) (f : T ⟶ U), S f := by
  obtain ⟨p⟩ := nonempty_point U
  obtain ⟨T, f, -, hf, -, -⟩ := exists_mem_of_point hS p
  exact ⟨T, f, hf⟩

/-- Covering sieves of the point contain the identity. -/
theorem point_cover {S : Sieve pt} (hS : S ∈ topology pt) : S (𝟙 pt) := by
  obtain ⟨T, f, hf⟩ := cover_nonempty hS
  obtain ⟨q⟩ := nonempty_point T
  have : q ≫ f = 𝟙 pt := (toPt_eq _).trans (toPt_eq _).symm
  rw [← this]
  exact S.downward_closed hf q

/-! ### Separation along open covers -/

/-- Two maps agreeing along a family of open embeddings with images joining to `⊤` are
equal. -/
theorem hom_eq_of_cover {U V : Chart} {R : Presieve U} (hR : imgSup R = ⊤) {φ ψ : U ⟶ V}
    (h : ∀ ⦃T⦄ (f : T ⟶ U), R f → (∃ a, IsOpenEmb f a) → f ≫ φ = f ≫ ψ) : φ = ψ := by
  ext w
  have key : ∀ χ : U ⟶ V, χ w = ⨆ a ∈ {a | ∃ (T : Chart) (f : T ⟶ U), R f ∧ IsOpenEmb f a},
      χ w ⊓ a := by
    intro χ
    rw [← inf_iSup₂_eq, ← sSup_eq_iSup, ← imgSup, hR, inf_top_eq]
  rw [key φ, key ψ]
  refine iSup_congr fun a => iSup_congr fun ha' => ?_
  obtain ⟨T, f, hf, ha⟩ := ha'
  rw [ha.inf_img, ha.inf_img]
  have := congrArg (fun m : T ⟶ V => m w) (h f hf ⟨a, ha⟩)
  simp only [comp_apply] at this
  rw [this]

/-! ### Representables are sheaves -/

section Glue

variable {U V : Chart} {R : Presieve U} (hR : IsOpenCover R)
  (x : ∀ ⦃T⦄ (f : T ⟶ U), R f → (T ⟶ V))
  (hx : ∀ ⦃T₁ T₂ Z : Chart⦄ (g₁ : Z ⟶ T₁) (g₂ : Z ⟶ T₂) ⦃f₁ : T₁ ⟶ U⦄ ⦃f₂ : T₂ ⟶ U⦄
    (h₁ : R f₁) (h₂ : R f₂), g₁ ≫ f₁ = g₂ ≫ f₂ → g₁ ≫ x f₁ h₁ = g₂ ≫ x f₂ h₂)

include hx in
/-- **Comparison on overlaps.** If `c ≤ a'` and `f'^* c ≤ x_{f'}^* w`, then
`f^* c ≤ x_f^* w`. -/
theorem glue_overlap {T T' : Chart} {f : T ⟶ U} {f' : T' ⟶ U} (hf : R f) (hf' : R f')
    {a a' : O U} (_ha : IsOpenEmb f a) (ha' : IsOpenEmb f' a') {c : O U} (hca' : c ≤ a') (w : O V)
    (hc : f' c ≤ x f' hf' w) : f c ≤ x f hf w := by
  rw [basis T (f c)]
  refine sSup_le fun b ⟨hb, W, m, hm⟩ => ?_
  rw [hm.le_iff]
  -- `m ≫ f` lands in `a'`
  have himg : (m ≫ f) a' = ⊤ := by
    rw [comp_apply]
    refine top_unique ((hm.le_iff (f c)).mp hb ▸ hom_mono m (hom_mono f hca'))
  have hfac := ha'.lift_comp (m ≫ f) himg
  have hcomp := hx m (ha'.lift (m ≫ f) himg) hf hf' hfac.symm
  have e1 : m (x f hf w) = (ha'.lift (m ≫ f) himg) (x f' hf' w) := by
    have := congrArg (fun φ : W ⟶ V => φ w) hcomp
    simpa only [comp_apply] using this
  rw [e1]
  apply top_unique
  calc (⊤ : O W) = m (f c) := ((hm.le_iff (f c)).mp hb).symm
    _ = (ha'.lift (m ≫ f) himg) (f' c) := by
        have := congrArg (fun φ : W ⟶ U => φ c) hfac
        simp only [comp_apply] at this
        exact this.symm
    _ ≤ _ := hom_mono _ hc

/-- The candidates for the glued value at `w`. -/
def glueSet (w : O V) : Set (O U) :=
  {c | ∃ (T : Chart) (f : T ⟶ U) (hf : R f) (a : O U), IsOpenEmb f a ∧ c ≤ a ∧ f c ≤ x f hf w}

/-- The glued value. -/
def glueFun (w : O V) : O U := sSup (glueSet x w)

include hx in
theorem glue_restrict {T : Chart} {f : T ⟶ U} (hf : R f) {a : O U} (ha : IsOpenEmb f a) (w : O V) :
    f (glueFun x w) = x f hf w := by
  apply le_antisymm
  · rw [glueFun, map_sSup, sSup_image]
    refine iSup₂_le fun c ⟨T', f', hf', a', ha', hca', hc⟩ => ?_
    exact glue_overlap x hx hf hf' ha ha' hca' w hc
  · have hmem : ha.inv (x f hf w) ∈ glueSet x w :=
      ⟨T, f, hf, a, ha, ha.inv_le _, by rw [ha.map_inv]⟩
    calc x f hf w = f (ha.inv (x f hf w)) := (ha.map_inv _).symm
      _ ≤ f (glueFun x w) := hom_mono f (le_sSup hmem)

theorem glueFun_mono {w w' : O V} (h : w ≤ w') : glueFun x w ≤ glueFun x w' :=
  sSup_le_sSup fun _ ⟨T, f, hf, a, ha, hca, hc⟩ =>
    ⟨T, f, hf, a, ha, hca, hc.trans (hom_mono _ h)⟩

include hR hx in
/-- **The glued map.** -/
def glue : U ⟶ V where
  toFun := glueFun x
  map_inf' w w' := by
    apply le_antisymm
    · exact le_inf (glueFun_mono x inf_le_left) (glueFun_mono x inf_le_right)
    · rw [glueFun, glueFun, sSup_inf_sSup]
      refine iSup₂_le fun p hp => ?_
      obtain ⟨⟨T, f, hf, a, ha, hca, hc⟩, ⟨T', f', hf', a', ha', hca', hc'⟩⟩ := hp
      refine le_sSup ⟨T, f, hf, a, ha, inf_le_left.trans hca, ?_⟩
      rw [map_inf, map_inf]
      exact inf_le_inf hc (glue_overlap x hx hf hf' ha ha' hca' w' hc')
  map_top' := by
    apply top_unique
    rw [← hR.2]
    refine sSup_le fun a ⟨T, f, hf, ha⟩ => le_sSup ⟨T, f, hf, a, ha, le_rfl, ?_⟩
    rw [ha.map_img, map_top]
  map_sSup' S := by
    apply le_antisymm
    · rw [sSup_image]
      refine sSup_le fun c ⟨T, f, hf, a, ha, hca, hc⟩ => ?_
      rw [map_sSup, sSup_image] at hc
      calc c = ha.inv (f c) := by rw [ha.inv_map, inf_eq_left.mpr hca]
        _ ≤ ha.inv (⨆ w ∈ S, x f hf w) := ha.inv_mono hc
        _ = ⨆ w ∈ S, ha.inv (x f hf w) := by
            rw [ha.inv_iSup]
            exact iSup_congr fun w => ha.inv_iSup _
        _ ≤ ⨆ w ∈ S, glueFun x w := iSup₂_mono fun w _ =>
            le_sSup ⟨T, f, hf, a, ha, ha.inv_le _, by rw [ha.map_inv]⟩
    · exact sSup_le (by rintro _ ⟨w, hw, rfl⟩; exact glueFun_mono x (le_sSup hw))

theorem glue_comp {T : Chart} {f : T ⟶ U} (hf : R f) : f ≫ glue hR x hx = x f hf := by
  obtain ⟨a, ha⟩ := hR.1 f hf
  ext w
  exact glue_restrict x hx hf ha w

end Glue

/-- **Representables are sheaves.** -/
theorem isSheaf_yoneda_obj (V : Chart) : Presieve.IsSheaf topology (yoneda.obj V) := by
  rw [topology, Presieve.isSheaf_coverage]
  intro U R hR x hx
  have hx' : ∀ ⦃T₁ T₂ Z : Chart⦄ (g₁ : Z ⟶ T₁) (g₂ : Z ⟶ T₂) ⦃f₁ : T₁ ⟶ U⦄ ⦃f₂ : T₂ ⟶ U⦄
      (h₁ : R f₁) (h₂ : R f₂), g₁ ≫ f₁ = g₂ ≫ f₂ → g₁ ≫ x f₁ h₁ = g₂ ≫ x f₂ h₂ :=
    fun _ _ _ g₁ g₂ _ _ h₁ h₂ he => hx g₁ g₂ h₁ h₂ he
  refine ⟨glue hR x hx', fun T f hf => glue_comp hR x hx' hf, fun t ht => ?_⟩
  apply hom_eq_of_cover hR.2
  intro T f hf _
  rw [glue_comp hR x hx' hf]
  exact ht f hf

instance : topology.Subcanonical :=
  GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj _ isSheaf_yoneda_obj

/-! ### Constant and codiscrete presheaves are sheaves -/

/-- A nonzero open contains the image of an open embedding. -/
theorem exists_openEmb_le {U : Chart} {y : O U} (hy : y ≠ ⊥) :
    ∃ (T : Chart) (m : T ⟶ U) (b : O U), IsOpenEmb m b ∧ b ≤ y := by
  by_contra h
  apply hy
  rw [basis U y]
  refine le_antisymm (sSup_le fun b ⟨hb, T, m, hm⟩ => ?_) bot_le
  exact absurd ⟨T, m, b, hm, hb⟩ h

theorem const_isSheaf (K : Type) :
    Presieve.IsSheaf topology ((Functor.const Chartᵒᵖ).obj K) := by
  rw [topology, Presieve.isSheaf_coverage]
  intro U R hR x hx
  -- any two members whose images meet carry the same label
  have hmeet : ∀ ⦃T T' : Chart⦄ (f : T ⟶ U) (f' : T' ⟶ U) (hf : R f) (hf' : R f') (a a' : O U),
      IsOpenEmb f a → IsOpenEmb f' a' → a ⊓ a' ≠ ⊥ → x f hf = x f' hf' := by
    intro T T' f f' hf hf' a a' ha ha' hne
    obtain ⟨W, m, b, hm, hb⟩ := exists_openEmb_le hne
    have h1 : m a = ⊤ := (hm.le_iff a).mp (hb.trans inf_le_left)
    have h2 : m a' = ⊤ := (hm.le_iff a').mp (hb.trans inf_le_right)
    have := hx (ha.lift m h1) (ha'.lift m h2) hf hf' (by rw [ha.lift_comp, ha'.lift_comp])
    exact this
  -- a chosen member
  have hne : ∃ (T : Chart) (f : T ⟶ U), R f := by
    by_contra h
    have : imgSup R = ⊥ := le_antisymm (sSup_le fun a ⟨T, f, hf, _⟩ => absurd ⟨T, f, hf⟩ h) bot_le
    exact bot_ne_top U (this.symm.trans hR.2)
  obtain ⟨T₀, f₀, hf₀⟩ := hne
  obtain ⟨a₀, ha₀⟩ := hR.1 f₀ hf₀
  have hall : ∀ ⦃T⦄ (f : T ⟶ U) (hf : R f), x f hf = x f₀ hf₀ := by
    intro T f hf
    by_contra hdiff
    let A := sSup {a | ∃ (T : Chart) (f : T ⟶ U) (hf : R f), IsOpenEmb f a ∧ x f hf = x f₀ hf₀}
    let B := sSup {a | ∃ (T : Chart) (f : T ⟶ U) (hf : R f), IsOpenEmb f a ∧ x f hf ≠ x f₀ hf₀}
    have hAB : A ⊓ B = ⊥ := by
      rw [sSup_inf_sSup]
      refine le_antisymm (iSup₂_le fun p hp => ?_) bot_le
      obtain ⟨⟨T₁, f₁, hf₁, ha₁, e₁⟩, ⟨T₂, f₂, hf₂, ha₂, e₂⟩⟩ := hp
      by_contra hne'
      exact e₂ ((hmeet f₂ f₁ hf₂ hf₁ _ _ ha₂ ha₁ (fun h => hne' (by rw [inf_comm]; exact h.le))).trans e₁)
    have hAB' : A ⊔ B = ⊤ := by
      apply top_unique
      rw [← hR.2]
      refine sSup_le fun a ⟨T₁, f₁, hf₁, ha₁⟩ => ?_
      by_cases e : x f₁ hf₁ = x f₀ hf₀
      · exact le_sup_of_le_left (le_sSup ⟨T₁, f₁, hf₁, ha₁, e⟩)
      · exact le_sup_of_le_right (le_sSup ⟨T₁, f₁, hf₁, ha₁, e⟩)
    rcases eq_bot_or_eq_bot U hAB hAB' with hA | hB
    · have hmem : a₀ ∈ {a | ∃ (T : Chart) (f : T ⟶ U) (hf : R f), IsOpenEmb f a ∧
          x f hf = x f₀ hf₀} := ⟨T₀, f₀, hf₀, ha₀, rfl⟩
      have : a₀ ≤ A := le_sSup hmem
      rw [hA] at this
      exact ha₀.img_ne_bot (le_bot_iff.mp this)
    · obtain ⟨a, ha⟩ := hR.1 f hf
      have hmem : a ∈ {a | ∃ (T : Chart) (f : T ⟶ U) (hf : R f), IsOpenEmb f a ∧
          x f hf ≠ x f₀ hf₀} := ⟨T, f, hf, ha, hdiff⟩
      have : a ≤ B := le_sSup hmem
      rw [hB] at this
      exact ha.img_ne_bot (le_bot_iff.mp this)
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : K, t₀ = x f₀ hf₀ := ⟨_, rfl⟩
  refine ⟨t₀, fun T f hf => ?_, fun t ht => ?_⟩
  · rw [ht₀]
    exact (hall f hf).symm
  · rw [ht₀]
    exact ht f₀ hf₀

/-- The codiscrete presheaf: functions on points. -/
abbrev codiscPresheaf (K : Type) : Chartᵒᵖ ⥤ Type where
  obj U := (pt ⟶ U.unop) → K
  map f := ↾fun φ p => φ (p ≫ f.unop)
  map_id _ := rfl
  map_comp _ _ := rfl

theorem codisc_isSheaf (K : Type) : Presieve.IsSheaf topology (codiscPresheaf K) := by
  rw [topology, Presieve.isSheaf_coverage]
  intro U R hR x hx
  -- every point factors through a member
  have hpt : ∀ p : pt ⟶ U, ∃ (T : Chart) (f : T ⟶ U) (hf : R f) (a : O U),
      IsOpenEmb f a ∧ p a := by
    intro p
    have hp : p (imgSup R) := by rw [hR.2, map_top]; trivial
    rw [imgSup, map_sSup, sSup_image] at hp
    simp only [iSup_Prop_eq] at hp
    obtain ⟨a, ⟨T, f, hf, ha⟩, hpa⟩ := hp
    exact ⟨T, f, hf, a, ha, hpa⟩
  choose T f hf a ha hpa' using hpt
  have hpa : ∀ p : pt ⟶ U, p (a p) = ⊤ := fun p => eq_true (hpa' p)
  have key : ∀ (p : pt ⟶ U) {T' : Chart} (f' : T' ⟶ U) (hf' : R f') (q : pt ⟶ T'),
      q ≫ f' = p → x f' hf' q = x (f p) (hf p) ((ha p).lift p (hpa p)) := by
    intro p T' f' hf' q hq
    have := hx q ((ha p).lift p (hpa p)) hf' (hf p) (by rw [(ha p).lift_comp, hq])
    have := congrFun this (𝟙 pt)
    simpa using this
  refine ⟨fun p => x (f p) (hf p) ((ha p).lift p (hpa p)), fun T' f' hf' => ?_, fun t ht => ?_⟩
  · funext q
    exact (key (q ≫ f') f' hf' q rfl).symm
  · funext p
    have h1 := congrFun (ht (f p) (hf p)) ((ha p).lift p (hpa p))
    change t ((ha p).lift p (hpa p) ≫ f p) = _ at h1
    rw [(ha p).lift_comp] at h1
    exact h1

end Chart

end PointlessEnd
