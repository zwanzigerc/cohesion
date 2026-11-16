import RealContinuity.LongRayGood

/-!
# The designated maps `q_T` and `r_T`

For an allowed tail `T` (all of `L`, or `(a, ∞]` with `a` finite):

* `q_T : T → S` sends finite points to `o = True` and `∞` to `c = False`;
* `r_T : P_T → K_T` is endpoint evaluation on paths in `T`.

Both are `GoodMap`s: open surjections with path-connected fibres and a basis of
good restrictions (bounded order-convex intervals and smaller tails for `q_T`;
uniform chart balls and smaller tail path spaces for `r_T`). The path-connected
fibres of `r_T` come from the order-theoretic relative homotopy.
-/

noncomputable section

open Set Topology Filter unitInterval

namespace RealContinuity

/-! ### Tails and subspace paths -/

/-- Allowed tails: `L` itself, or `(a, ∞]` for a finite point `a`. -/
def tailOf : Option L₀ → Set L
  | none => univ
  | some a => Ioi (a : L)

theorem upperTail_tailOf : ∀ o, UpperTail (tailOf o)
  | none => upperTail_univ
  | some a => upperTail_Ioi (WithTop.coe_lt_top a)

theorem isOpen_tailOf : ∀ o, IsOpen (tailOf o)
  | none => isOpen_univ
  | some _ => isOpen_Ioi

/-- A path in `X` inside `S ⊆ X` whose values lie in `val '' F` gives a path in the
subspace `S` inside `F`. -/
theorem joinedIn_subtype {X : Type*} [TopologicalSpace X] {S : Set X} {F : Set S} {x y : S}
    (h : JoinedIn (Subtype.val '' F) (x : X) y) : JoinedIn F x y := by
  obtain ⟨γ, hγ⟩ := h
  have hS : ∀ t, γ t ∈ S := fun t => by obtain ⟨z, -, hz⟩ := hγ t; rw [← hz]; exact z.2
  refine ⟨⟨⟨fun t => ⟨γ t, hS t⟩, γ.continuous.subtype_mk _⟩, Subtype.ext γ.source,
    Subtype.ext γ.target⟩, fun t => ?_⟩
  obtain ⟨z, hzF, hz⟩ := hγ t
  have : (⟨γ t, hS t⟩ : S) = z := Subtype.ext hz.symm
  change (⟨γ t, hS t⟩ : S) ∈ F
  rw [this]; exact hzF

/-! ### `q_T` -/

/-- `q_T : T → S`. -/
def qT (o : Option L₀) : C(tailOf o, Prop) := qMap.comp ⟨Subtype.val, continuous_subtype_val⟩

theorem qT_apply (o : Option L₀) (x : tailOf o) : qT o x = ((x : L) ≠ ⊤) := rfl

/-- Two finite points of an upper set are joined inside it, through finite points. -/
theorem joinedIn_finite_of_upper {T : Set L} (hT : IsUpperSet T) {x y : L} (hx : x ∈ T)
    (hy : y ∈ T) (hxf : IsFin x) (hyf : IsFin y) :
    JoinedIn {z | z ∈ T ∧ IsFin z ∧ min x y ≤ z ∧ z ≤ max x y} x y := by
  obtain ⟨x₀, rfl⟩ := isFin_iff.mp hxf
  obtain ⟨y₀, rfl⟩ := isFin_iff.mp hyf
  obtain ⟨γ, h0, h1, hγ⟩ := exists_path_between x₀ y₀
  refine ⟨⟨γ, h0, h1⟩, fun t => ⟨hT (hγ t).1 (UpperTail.min_mem hx hy), ?_, (hγ t).1, (hγ t).2⟩⟩
  exact isFin_of_between hxf hyf (hγ t).2

theorem goodMap_qT (o : Option L₀) : GoodMap (qT o) := by
  have hT := upperTail_tailOf o
  have hTo := isOpen_tailOf o
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- surjective
    intro P
    by_cases hP : P
    · obtain ⟨z, hzT, -⟩ := hT.cofinal (ordPt (Classical.arbitrary W)) (ordPt_lt_top _)
      refine ⟨⟨z, hzT⟩, ?_⟩
      rw [qT_apply, eq_iff_iff, iff_true_intro hP, iff_true]
      exact WithTop.coe_ne_top
    · refine ⟨⟨⊤, hT.top_mem⟩, ?_⟩
      rw [qT_apply]
      simp [hP]
  · -- open
    exact qMap_isOpenMap.comp hTo.isOpenMap_subtype_val
  · -- path-connected fibres
    intro d d' hdd'
    rw [qT_apply, qT_apply, eq_iff_iff] at hdd'
    by_cases hd : IsFin (d : L)
    · have hd' : IsFin (d' : L) := hdd'.mp hd
      apply joinedIn_subtype
      refine (joinedIn_finite_of_upper hT.upper d.2 d'.2 hd hd').mono ?_
      rintro z ⟨hzT, hzf, -⟩
      refine ⟨⟨z, hzT⟩, ?_, rfl⟩
      change qT o ⟨z, hzT⟩ = qT o d
      rw [qT_apply, qT_apply, eq_iff_iff]
      exact ⟨fun _ => hd, fun _ => hzf⟩
    · have hd' : ¬ IsFin (d' : L) := fun h => hd (hdd'.mpr h)
      have : d = d' := Subtype.ext ((not_not.mp hd).trans (not_not.mp hd').symm)
      subst this
      exact JoinedIn.refl rfl
  · -- good restrictions
    intro d N hN
    have hN' : Subtype.val '' N ∈ 𝓝 (d : L) := by
      rw [← hTo.isOpenEmbedding_subtypeVal.map_nhds_eq d]
      exact image_mem_map hN
    by_cases hd : IsFin (d : L)
    · obtain ⟨W, hWo, hdW, hWN, hWc⟩ := exists_ordConnected_open
        (inter_mem hN' (isOpen_Iio.mem_nhds (lt_top_iff_ne_top.mpr hd)))
      refine ⟨Subtype.val ⁻¹' W, hWo.preimage continuous_subtype_val, hdW, ?_, ?_⟩
      · intro v hv
        obtain ⟨z, hzN, hz⟩ := (hWN hv).1
        rwa [Subtype.val_injective hz] at hzN
      · intro v v' hv hv' _
        have hvf : IsFin (v : L) := (hWN hv).2.ne
        have hpc := isPathConnected_of_ordConnected hWc (fun y hy => (hWN hy).2.ne) ⟨_, hv⟩
        obtain ⟨γ, hγ⟩ := hpc.joinedIn _ hv _ hv'
        apply joinedIn_subtype
        refine ⟨γ, fun t => ?_⟩
        have hzW := hγ t
        have hzT : γ t ∈ tailOf o := by
          obtain ⟨z, -, hz⟩ := (hWN hzW).1; rw [← hz]; exact z.2
        refine ⟨⟨γ t, hzT⟩, ⟨hzW, ?_⟩, rfl⟩
        change qT o ⟨γ t, hzT⟩ = qT o v
        rw [qT_apply, qT_apply, eq_iff_iff]
        exact ⟨fun _ => hvf, fun _ => (hWN hzW).2.ne⟩
    · have hd' : (d : L) = ⊤ := not_not.mp hd
      rw [hd'] at hN'
      obtain ⟨l, hl, hlN⟩ := (nhds_top_basis (α := L)).mem_iff.mp hN'
      refine ⟨Subtype.val ⁻¹' Ioi l, isOpen_Ioi.preimage continuous_subtype_val,
        show l < (d : L) by rw [hd']; exact hl, ?_, ?_⟩
      · intro v hv
        obtain ⟨z, hzN, hz⟩ := hlN hv
        rwa [Subtype.val_injective hz] at hzN
      · intro v v' hv hv' hvv'
        rw [qT_apply, qT_apply, eq_iff_iff] at hvv'
        by_cases hvf : IsFin (v : L)
        · have hvf' : IsFin (v' : L) := hvv'.mp hvf
          apply joinedIn_subtype
          refine (joinedIn_finite_of_upper (isUpperSet_Ioi l) hv hv' hvf hvf').mono ?_
          rintro z ⟨hzl, hzf, -⟩
          have hzT : z ∈ tailOf o := (hlN hzl).choose_spec.2 ▸ (hlN hzl).choose.2
          refine ⟨⟨z, hzT⟩, ⟨hzl, ?_⟩, rfl⟩
          change qT o ⟨z, hzT⟩ = qT o v
          rw [qT_apply, qT_apply, eq_iff_iff]
          exact ⟨fun _ => hvf, fun _ => hzf⟩
        · have hvf' : ¬ IsFin (v' : L) := fun h => hvf (hvv'.mpr h)
          have : v = v' := Subtype.ext ((not_not.mp hvf).trans (not_not.mp hvf').symm)
          subst this
          exact JoinedIn.refl ⟨hv, rfl⟩

/-! ### `r_T` -/

/-- `r_T : P_T → K_T`, endpoint evaluation on paths in `T`. -/
def rT (o : Option L₀) : C(PT (tailOf o), KT (tailOf o)) :=
  ⟨fun γ => ⟨⟨endpointMap L γ.1, endpointMap_mem_Kset γ.1⟩, γ.2 0, γ.2 1⟩,
    (((endpointMap L).continuous.comp continuous_subtype_val).subtype_mk _).subtype_mk _⟩

theorem rT_apply (o : Option L₀) (γ : PT (tailOf o)) :
    ((rT o γ : Kset) : L × L) = ((γ : C(I, L)) 0, (γ : C(I, L)) 1) := rfl

/-- Two paths of `P_T` with the same endpoints, as a pair with a common start. -/
def rTPair {o : Option L₀} {v v' : PT (tailOf o)} (h : rT o v = rT o v') :
    OrderHomotopy.SameStart (T := L) :=
  ⟨((v : C(I, L)), (v' : C(I, L))), congrArg (fun p : KT (tailOf o) => p.1.1.1) h⟩

/-- **Fibres of `r_T`.** The relative homotopy joins two paths of `P_T` with the same
endpoints inside the fibre of `r_T`, and inside any set of paths containing the
whole homotopy. -/
theorem rT_joinedIn {o : Option L₀} {v v' : PT (tailOf o)} (h : rT o v = rT o v')
    {V : Set C(I, L)} (hV : ∀ u, OrderHomotopy.relHomotopy (rTPair h, u) ∈ V) :
    JoinedIn (Subtype.val ⁻¹' V ∩ {e | rT o e = rT o v}) v v' := by
  have hT := upperTail_tailOf o
  have h1 : (v : C(I, L)) 1 = (v' : C(I, L)) 1 := congrArg (fun p : KT (tailOf o) => p.1.1.2) h
  have hmem : ∀ u, OrderHomotopy.relHomotopy (rTPair h, u) ∈ PT (tailOf o) := fun u t =>
    hT.upper (OrderHomotopy.relHomotopy_bounds _ u t).1 (UpperTail.min_mem (v.2 t) (v'.2 t))
  have hc : Continuous fun u : I => OrderHomotopy.relHomotopy (rTPair h, u) :=
    OrderHomotopy.relHomotopy.continuous.comp (continuous_const.prodMk continuous_id)
  refine ⟨⟨⟨fun u => ⟨_, hmem u⟩, hc.subtype_mk _⟩, ?_, ?_⟩, fun u => ⟨hV u, ?_⟩⟩
  · exact Subtype.ext (OrderHomotopy.relHomotopy_zero _)
  · exact Subtype.ext (OrderHomotopy.relHomotopy_one _)
  · change rT o ⟨_, hmem u⟩ = rT o v
    exact Subtype.ext (Subtype.ext (BottomChart.endpointMap_relHomotopy (rTPair h) h1 u))

theorem goodMap_rT (o : Option L₀) : GoodMap (rT o) := by
  have hT := upperTail_tailOf o
  have hPo : IsOpen (PT (tailOf o)) := isOpen_PT (isOpen_tailOf o)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- surjective
    rintro ⟨⟨⟨x, y⟩, hK⟩, hxT, hyT⟩
    by_cases hx : x = ⊤
    · have hy : y = ⊤ := hK.mp hx
      subst hx; subst hy
      exact ⟨⟨constTop, fun _ => hT.top_mem⟩, rfl⟩
    · have hy : y ≠ ⊤ := fun h => hx (hK.mpr h)
      obtain ⟨x₀, rfl⟩ := WithTop.ne_top_iff_exists.mp hx
      obtain ⟨y₀, rfl⟩ := WithTop.ne_top_iff_exists.mp hy
      obtain ⟨γ, h0, h1, hγ⟩ := exists_path_between x₀ y₀
      refine ⟨⟨γ, fun t => hT.upper (hγ t).1 (UpperTail.min_mem hxT hyT)⟩, ?_⟩
      apply Subtype.ext; apply Subtype.ext
      change (γ 0, γ 1) = _
      rw [h0, h1]
  · -- open
    intro U hU
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨γ, hγU, rfl⟩
    have hU' : IsOpen (Subtype.val '' U : Set C(I, L)) := hPo.isOpenMap_subtype_val U hU
    obtain ⟨O, hO, hγO, hOK⟩ := endpointMap_open hU' (γ := (γ : C(I, L))) ⟨γ, hγU, rfl⟩
    have hOo : IsOpen ((fun p : KT (tailOf o) => ((p : Kset) : L × L)) ⁻¹' O) :=
      hO.preimage (continuous_subtype_val.comp continuous_subtype_val)
    refine Filter.mem_of_superset (hOo.mem_nhds hγO) ?_
    intro p hp
    obtain ⟨δ, ⟨δ', hδ'U, rfl⟩, hδ⟩ := hOK ⟨hp, p.1.2⟩
    exact ⟨δ', hδ'U, Subtype.ext (Subtype.ext hδ)⟩
  · -- path-connected fibres
    intro d d' hdd'
    exact (rT_joinedIn hdd' (V := univ) fun _ => mem_univ _).mono inter_subset_right
  · -- good restrictions
    intro d N hN
    have hN' : Subtype.val '' N ∈ 𝓝 (d : C(I, L)) := by
      rw [← hPo.isOpenEmbedding_subtypeVal.map_nhds_eq d]
      exact image_mem_map hN
    have back : ∀ {S : Set C(I, L)}, S ⊆ Subtype.val '' N → Subtype.val ⁻¹' S ⊆ N := by
      intro S hS v hv
      obtain ⟨z, hzN, hz⟩ := hS hv
      rwa [Subtype.val_injective hz] at hzN
    by_cases hd : (d : C(I, L)) ∈ PB
    · obtain ⟨b, hb⟩ := exists_bound_of_PB hd
      obtain ⟨ε, hε, hV⟩ := exists_chartBall_subset hb hN'
      refine ⟨Subtype.val ⁻¹' (Chart.chart b).V d ε,
        ((Chart.chart b).isOpen_V _ ε).preimage continuous_subtype_val, ?_, back hV, ?_⟩
      · change dist _ _ < ε
        rw [dist_self]; exact hε.pos
      · intro v v' hv hv' hvv'
        have hv0 : (rTPair hvv').1.1 ∈ (Chart.chart b).V d ε := hv
        have hv1 : (rTPair hvv').1.2 ∈ (Chart.chart b).V d ε := hv'
        exact rT_joinedIn hvv' fun u =>
          BottomChart.relHomotopy_mem_V (Chart.chart_mono b) hε.pos (rTPair hvv') hv0 hv1 u
    · have hd' : (d : C(I, L)) = constTop := by
        rcases path_const_top_or_bounded (d : C(I, L)) with h | ⟨b, hb⟩
        · exact ContinuousMap.ext h
        · exact absurd (fun t => ((hb t).trans (ordPt_lt_top b)).ne) hd
      rw [hd'] at hN'
      obtain ⟨a, ha, haN⟩ := exists_tail_subset hN'
      refine ⟨Subtype.val ⁻¹' PT (Ioi a), (isOpen_PT isOpen_Ioi).preimage continuous_subtype_val,
        ?_, back haN, ?_⟩
      · intro t
        change a < (d : C(I, L)) t
        rw [hd']; exact ha
      · intro v v' hv hv' hvv'
        have hv0 : ∀ t, a < (rTPair hvv').1.1 t := hv
        have hv1 : ∀ t, a < (rTPair hvv').1.2 t := hv'
        refine rT_joinedIn hvv' fun u t => ?_
        exact lt_of_lt_of_le (lt_min (hv0 t) (hv1 t))
          (OrderHomotopy.relHomotopy_bounds (rTPair hvv') u t).1

/-! ### Controlled bounded restrictions

The designated family also contains the controlled bounded restrictions of `q`
and `r`, corestricted to their actual open images: bounded open order-convex
sets `J` of finite points (image `{o}`) and uniform chart balls `V` (image the
endpoint ball `W`, as in `EndpointCharts`). Restrictions to smaller tails are
again maps `q_U` and `r_U`. -/

/-- A bounded open order-convex set of finite points. -/
structure QBox where
  J : Set L
  isOpen : IsOpen J
  ordConnected : J.OrdConnected
  nonempty : J.Nonempty
  bound : W
  lt_bound : ∀ x ∈ J, x < ordPt bound

namespace QBox

variable (B : QBox)

theorem isFin {x : L} (hx : x ∈ B.J) : IsFin x := ((B.lt_bound x hx).trans (ordPt_lt_top _)).ne

/-- The actual image `{o}`. -/
abbrev Img : Set Prop := {True}

/-- The restriction of `q` to `J`, corestricted to `{o}`. -/
def map : C(B.J, Img) := ContinuousMap.const _ ⟨True, rfl⟩

theorem isPathConnected : IsPathConnected B.J :=
  isPathConnected_of_ordConnected B.ordConnected (fun _ hx => B.isFin hx) B.nonempty

theorem goodMap : GoodMap B.map := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨x, hx⟩ := B.nonempty
    exact ⟨⟨x, hx⟩, Subsingleton.elim _ _⟩
  · intro U _
    by_cases h : (B.map '' U).Nonempty
    · obtain ⟨y, hy⟩ := h
      have : B.map '' U = univ := eq_univ_of_forall fun z => Subsingleton.elim y z ▸ hy
      rw [this]; exact isOpen_univ
    · rw [not_nonempty_iff_eq_empty.mp h]; exact isOpen_empty
  · intro d d' _
    apply joinedIn_subtype
    obtain ⟨γ, hγ⟩ := B.isPathConnected.joinedIn _ d.2 _ d'.2
    exact ⟨γ, fun t => ⟨⟨γ t, hγ t⟩, rfl, rfl⟩⟩
  · intro d N hN
    have hN' : Subtype.val '' N ∈ 𝓝 (d : L) := by
      rw [← B.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq d]
      exact image_mem_map hN
    obtain ⟨V, hVo, hdV, hVN, hVc⟩ := exists_ordConnected_open hN'
    have hVJ : V ⊆ B.J := fun y hy => by obtain ⟨z, -, hz⟩ := hVN hy; rw [← hz]; exact z.2
    refine ⟨Subtype.val ⁻¹' V, hVo.preimage continuous_subtype_val, hdV, ?_, ?_⟩
    · intro v hv
      obtain ⟨z, hzN, hz⟩ := hVN hv
      rwa [Subtype.val_injective hz] at hzN
    · intro v v' hv hv' _
      have hpc := isPathConnected_of_ordConnected hVc (fun y hy => B.isFin (hVJ hy)) ⟨_, hv⟩
      obtain ⟨γ, hγ⟩ := hpc.joinedIn _ hv _ hv'
      apply joinedIn_subtype
      exact ⟨γ, fun t => ⟨⟨γ t, hVJ (hγ t)⟩, ⟨hγ t, rfl⟩, rfl⟩⟩

end QBox

/-- A controlled uniform chart ball. -/
structure RBall where
  b : W
  p : C(I, L)
  ε : ℝ
  adm : (Chart.chart b).Admissible p ε

namespace RBall

variable (B : RBall)

/-- The chart. -/
abbrev c : BottomChart L := Chart.chart B.b

/-- The ball `V`. -/
abbrev V : Set C(I, L) := B.c.V B.p B.ε

/-- Its actual endpoint image, inside `K`. -/
def Img : Set Kset := {x | (x : L × L) ∈ B.c.W B.p B.ε}

theorem endpoint_mem (γ : B.V) : endpointMap L γ ∈ B.c.W B.p B.ε := by
  rw [← BottomChart.endpointMap_image_V B.adm]; exact ⟨γ, γ.2, rfl⟩

/-- The restriction of `r` to `V`, corestricted to its actual image. -/
def map : C(B.V, B.Img) :=
  ⟨fun γ => ⟨⟨endpointMap L γ, endpointMap_mem_Kset γ⟩, B.endpoint_mem γ⟩,
    (((endpointMap L).continuous.comp continuous_subtype_val).subtype_mk _).subtype_mk _⟩

theorem map_val (γ : B.V) : ((B.map γ : Kset) : L × L) = endpointMap L γ := rfl

/-- Two paths of `V` with the same endpoints, as a pair with a common start. -/
def pair {v v' : B.V} (h : B.map v = B.map v') : OrderHomotopy.SameStart (T := L) :=
  ⟨((v : C(I, L)), (v' : C(I, L))), congrArg (fun x : B.Img => x.1.1.1) h⟩

theorem relHomotopy_mem {v v' : B.V} (h : B.map v = B.map v') (u : I) :
    OrderHomotopy.relHomotopy (B.pair h, u) ∈ B.V :=
  BottomChart.relHomotopy_mem_V (Chart.chart_mono B.b) B.adm.pos (B.pair h) v.2 v'.2 u

/-- **Fibres of the ball restriction.** The relative homotopy joins two paths of `V`
with the same endpoints inside the fibre, and inside any set containing it. -/
theorem joinedIn {v v' : B.V} (h : B.map v = B.map v') {S : Set C(I, L)}
    (hS : ∀ u, OrderHomotopy.relHomotopy (B.pair h, u) ∈ S) :
    JoinedIn (Subtype.val ⁻¹' S ∩ {e | B.map e = B.map v}) v v' := by
  have h1 : (v : C(I, L)) 1 = (v' : C(I, L)) 1 := congrArg (fun x : B.Img => x.1.1.2) h
  have hc : Continuous fun u : I => OrderHomotopy.relHomotopy (B.pair h, u) :=
    OrderHomotopy.relHomotopy.continuous.comp (continuous_const.prodMk continuous_id)
  refine ⟨⟨⟨fun u => ⟨_, B.relHomotopy_mem h u⟩, hc.subtype_mk _⟩, ?_, ?_⟩,
    fun u => ⟨hS u, ?_⟩⟩
  · exact Subtype.ext (OrderHomotopy.relHomotopy_zero _)
  · exact Subtype.ext (OrderHomotopy.relHomotopy_one _)
  · change B.map ⟨_, B.relHomotopy_mem h u⟩ = B.map v
    exact Subtype.ext (Subtype.ext (BottomChart.endpointMap_relHomotopy (B.pair h) h1 u))

theorem lt_ordPt_of_mem {γ : C(I, L)} (hγ : γ ∈ B.V) (t : I) : γ t < ordPt B.b :=
  Chart.lt_ordPt_of_Φfun_lt_S B.b
    ((BottomChart.coord_le_top' B.adm hγ t).trans (BottomChart.top'_lt B.adm))

theorem goodMap : GoodMap B.map := by
  have hVo : IsOpen B.V := B.c.isOpen_V _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨x, hx⟩
    have hx' : (x : L × L) ∈ endpointMap L '' B.V := by
      rw [BottomChart.endpointMap_image_V B.adm]; exact hx
    obtain ⟨γ, hγ, hγx⟩ := hx'
    exact ⟨⟨γ, hγ⟩, Subtype.ext (Subtype.ext hγx)⟩
  · intro U hU
    have hU' : IsOpen (Subtype.val '' U : Set C(I, L)) := hVo.isOpenMap_subtype_val U hU
    have hO := BottomChart.isOpen_image_of_subset_V B.adm hU'
      (by rintro _ ⟨γ, -, rfl⟩; exact γ.2)
    have e : B.map '' U =
        (fun x : B.Img => ((x : Kset) : L × L)) ⁻¹' (endpointMap L '' (Subtype.val '' U)) := by
      ext x
      constructor
      · rintro ⟨γ, hγ, rfl⟩; exact ⟨γ, ⟨γ, hγ, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨γ, hγ, rfl⟩, hx⟩; exact ⟨γ, hγ, Subtype.ext (Subtype.ext hx)⟩
    rw [e]
    exact hO.preimage (continuous_subtype_val.comp continuous_subtype_val)
  · intro d d' h
    exact (B.joinedIn h (S := univ) fun _ => mem_univ _).mono inter_subset_right
  · intro d N hN
    have hN' : Subtype.val '' N ∈ 𝓝 (d : C(I, L)) := by
      rw [← hVo.isOpenEmbedding_subtypeVal.map_nhds_eq d]
      exact image_mem_map hN
    obtain ⟨ε', hε', hV'⟩ := exists_chartBall_subset (B.lt_ordPt_of_mem d.2) hN'
    refine ⟨Subtype.val ⁻¹' B.c.V d ε', (B.c.isOpen_V _ ε').preimage continuous_subtype_val,
      ?_, ?_, ?_⟩
    · change dist _ _ < ε'
      rw [dist_self]; exact hε'.pos
    · intro v hv
      obtain ⟨z, hzN, hz⟩ := hV' hv
      rwa [Subtype.val_injective hz] at hzN
    · intro v v' hv hv' h
      have hv0 : (B.pair h).1.1 ∈ B.c.V d ε' := hv
      have hv1 : (B.pair h).1.2 ∈ B.c.V d ε' := hv'
      exact B.joinedIn h fun u =>
        BottomChart.relHomotopy_mem_V (Chart.chart_mono B.b) hε'.pos (B.pair h) hv0 hv1 u

end RBall

end RealContinuity
