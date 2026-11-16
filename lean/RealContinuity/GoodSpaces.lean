import RealContinuity.FiniteHeight
import Mathlib.Topology.Connected.LocallyConnected

/-!
# The inductive invariant of stages

A space is *good* when it is nonempty and connected and has a neighbourhood
basis of connected open sets of pairwise finite `Q`-height. Good spaces are
closed under the three closure operations of the site:

* nonempty connected open subspaces;
* finite products;
* topological pullbacks `U ×_B D` of a map `g : D → B` that is an open
  surjection with path-connected fibres and has a basis of *good
  restrictions* (open sets `V` on which the fibres of `g` stay path
  connected).

Consequently every good space has pairwise finite height (`Good.pairwise`).
This replaces the separate dense-finite-part argument for the initial closure
and the overlap chains of the draft by one induction.
-/

noncomputable section

open Set Topology

namespace RealContinuity

universe u

/-! ### Topological pullbacks -/

section Pullback

variable {U D B : Type u} [TopologicalSpace U] [TopologicalSpace D] [TopologicalSpace B]
variable (f : C(U, B)) (g : C(D, B))

/-- The topological pullback `U ×_B D`. -/
def TopPullback : Set (U × D) := {p | f p.1 = g p.2}

/-- The projection `U ×_B D → U`. -/
def pbFst : C(TopPullback f g, U) := ⟨fun p => p.1.1, continuous_fst.comp continuous_subtype_val⟩

/-- The projection `U ×_B D → D`. -/
def pbSnd : C(TopPullback f g, D) := ⟨fun p => p.1.2, continuous_snd.comp continuous_subtype_val⟩

variable {f g}

theorem pbFst_surjective_of_cover (hcov : ∀ x, ∃ d, g d = f x) :
    Function.Surjective (pbFst f g) := by
  intro x
  obtain ⟨d, hd⟩ := hcov x
  exact ⟨⟨(x, d), hd.symm⟩, rfl⟩

theorem pbFst_surjective (hg : Function.Surjective g) : Function.Surjective (pbFst f g) :=
  pbFst_surjective_of_cover fun x => hg (f x)

/-- Base change of an open map is open. -/
theorem pbFst_isOpenMap (hg : IsOpenMap g) : IsOpenMap (pbFst f g) := by
  intro N hN
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨p, hpN, rfl⟩
  -- a basic open box around `p` inside `N`
  obtain ⟨M, hM, hMN⟩ := isOpen_induced_iff.mp hN
  have hpM : (p : U × D) ∈ M := by rw [← hMN] at hpN; exact hpN
  obtain ⟨A, E, hA, hE, hpA, hpE, hAE⟩ := isOpen_prod_iff.mp hM p.1.1 p.1.2 hpM
  have hO : IsOpen (A ∩ f ⁻¹' (g '' E)) := hA.inter ((hg E hE).preimage f.continuous)
  have hpO : p.1.1 ∈ A ∩ f ⁻¹' (g '' E) := ⟨hpA, ⟨p.1.2, hpE, p.2.symm⟩⟩
  refine Filter.mem_of_superset (hO.mem_nhds hpO) ?_
  rintro x ⟨hxA, ⟨e, heE, hex⟩⟩
  refine ⟨⟨(x, e), hex.symm⟩, ?_, rfl⟩
  rw [← hMN]
  exact hAE ⟨hxA, heE⟩

/-- Path-connected fibres of `g` give path-connected fibres of the base change. -/
theorem pbFst_joined_of_fibres
    (hfib : ∀ ⦃d d' : D⦄, g d = g d' → JoinedIn {e | g e = g d} d d')
    {p p' : TopPullback f g} (h : pbFst f g p = pbFst f g p') :
    JoinedIn {q | pbFst f g q = pbFst f g p} p p' := by
  obtain ⟨⟨x, d⟩, hp⟩ := p
  obtain ⟨⟨x', d'⟩, hp'⟩ := p'
  change x = x' at h
  subst h
  change f x = g d at hp
  change f x = g d' at hp'
  obtain ⟨γ, hγ⟩ := hfib (hp.symm.trans hp')
  let δ : Path (⟨(x, d), hp⟩ : TopPullback f g) ⟨(x, d'), hp'⟩ :=
    { toFun := fun t => ⟨(x, γ t), by
        change f x = g (γ t)
        rw [hp]; exact (hγ t).symm⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact continuous_const.prodMk γ.continuous
      source' := by ext <;> simp
      target' := by ext <;> simp }
  exact ⟨δ, fun t => rfl⟩

/-- A pullback of an open surjection with connected fibres over a connected base
is connected. -/
theorem connectedSpace_pullback [ConnectedSpace U] (hgo : IsOpenMap g)
    (hcov : ∀ x, ∃ d, g d = f x)
    (hfib : ∀ ⦃d d' : D⦄, g d = g d' → JoinedIn {e | g e = g d} d d') :
    ConnectedSpace (TopPullback f g) := by
  have hgs := pbFst_surjective_of_cover (f := f) hcov
  have hq : IsQuotientMap (pbFst f g) :=
    (pbFst_isOpenMap hgo).isQuotientMap (pbFst f g).continuous hgs
  have hfibc : ∀ x : U, IsConnected (pbFst f g ⁻¹' {x}) := by
    intro x
    obtain ⟨p, hp⟩ := hgs x
    refine IsPathConnected.isConnected ⟨p, by simp [hp], fun {p'} hp' => ?_⟩
    have h : pbFst f g p = pbFst f g p' := by
      simp only [mem_preimage, mem_singleton_iff] at hp'
      rw [hp, hp']
    have := pbFst_joined_of_fibres hfib h
    refine this.mono ?_
    intro q hq'
    simp only [mem_preimage, mem_singleton_iff] at hq' ⊢
    change pbFst f g q = pbFst f g p at hq'
    rw [hq', hp]
  have := hq.isCoinducing.isConnected_preimage_of_isClosed hfibc isClosed_univ isConnected_univ
  rw [preimage_univ] at this
  exact connectedSpace_iff_univ.mpr this

end Pullback

/-! ### Subspaces of subspaces -/

/-- For `W ⊆ V`, the preimage of `W` in the subspace `V` is homeomorphic to `W`. -/
def preimageValHomeo {X : Type u} [TopologicalSpace X] {V W : Set X} (hsub : W ⊆ V) :
    (Subtype.val ⁻¹' W : Set V) ≃ₜ W where
  toFun y := ⟨y.1.1, y.2⟩
  invFun y := ⟨⟨y.1, hsub y.2⟩, y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem connectedSpace_of_homeomorph {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) [ConnectedSpace X] : ConnectedSpace Y :=
  e.surjective.connectedSpace e.continuous

/-! ### Good spaces -/

/-- The inductive invariant of stages. -/
structure Good (X : Type u) [TopologicalSpace X] : Prop where
  connected : ConnectedSpace X
  basis : ∀ x : X, ∀ N ∈ 𝓝 x, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ W ⊆ N ∧ ConnectedSpace W ∧
    PairwiseFiniteHeight (TopCat.of W)

namespace Good

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem nonempty (h : Good X) : Nonempty X := h.connected.toNonempty

/-- Good spaces have pairwise finite height. -/
theorem pairwise (h : Good X) : PairwiseFiniteHeight (TopCat.of X) := by
  have := h.connected
  apply PairwiseFiniteHeight.of_openCover
  intro x
  obtain ⟨W, hW, hxW, -, -, hFH⟩ := h.basis x univ Filter.univ_mem
  exact ⟨W, hW, hxW, hFH⟩

/-- Good spaces are locally connected. -/
theorem locallyConnected (h : Good X) : LocallyConnectedSpace X := by
  refine locallyConnectedSpace_iff_subsets_isOpen_isConnected.mpr fun x N hN => ?_
  obtain ⟨W, hW, hxW, hWN, hWc, -⟩ := h.basis x N hN
  exact ⟨W, hWN, hW, hxW, isConnected_iff_connectedSpace.mpr hWc⟩

/-- Nonempty connected open subspaces of good spaces are good. -/
theorem subspace (h : Good X) {V : Set X} (hV : IsOpen V) [ConnectedSpace V] : Good V := by
  refine ⟨inferInstance, fun x N hN => ?_⟩
  have hN' : Subtype.val '' N ∈ 𝓝 (x : X) := by
    have := hV.isOpenEmbedding_subtypeVal.map_nhds_eq x
    rw [← this]
    exact Filter.image_mem_map hN
  obtain ⟨W, hW, hxW, hWN, hWc, hFH⟩ := h.basis x _ hN'
  have hsub : W ⊆ V := fun y hy => by
    obtain ⟨z, -, rfl⟩ := hWN hy; exact z.2
  refine ⟨Subtype.val ⁻¹' W, hW.preimage continuous_subtype_val, hxW, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨z, hzN, hz⟩ := hWN hy
    rwa [Subtype.val_injective hz] at hzN
  · exact connectedSpace_of_homeomorph (preimageValHomeo hsub).symm
  · exact hFH.of_homeomorph (preimageValHomeo hsub).symm

/-- Finite products of good spaces are good. -/
theorem prod (hX : Good X) (hY : Good Y) : Good (X × Y) := by
  have := hX.connected
  have := hY.connected
  refine ⟨inferInstance, fun p N hN => ?_⟩
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp hN
  obtain ⟨W₁, hW₁, hx, hW₁A, hc₁, hf₁⟩ := hX.basis p.1 A hA
  obtain ⟨W₂, hW₂, hy, hW₂B, hc₂, hf₂⟩ := hY.basis p.2 B hB
  have e : (W₁ ×ˢ W₂ : Set (X × Y)) ≃ₜ W₁ × W₂ := Homeomorph.Set.prod W₁ W₂
  refine ⟨W₁ ×ˢ W₂, hW₁.prod hW₂, ⟨hx, hy⟩, fun q hq => hAB ⟨hW₁A hq.1, hW₂B hq.2⟩, ?_, ?_⟩
  · exact connectedSpace_of_homeomorph e.symm
  · exact (PairwiseFiniteHeight.prod hf₁ hf₂).of_homeomorph e.symm

end Good

/-! ### Good maps and pullbacks -/

/-- The properties of a designated map used by the closure under pullback: an
open surjection with path-connected fibres and a basis of open sets on which
the fibres stay path connected. -/
structure GoodMap {D B : Type u} [TopologicalSpace D] [TopologicalSpace B] (g : C(D, B)) :
    Prop where
  surj : Function.Surjective g
  isOpenMap : IsOpenMap g
  fibres : ∀ ⦃d d' : D⦄, g d = g d' → JoinedIn {e | g e = g d} d d'
  basis : ∀ d : D, ∀ N ∈ 𝓝 d, ∃ V : Set D, IsOpen V ∧ d ∈ V ∧ V ⊆ N ∧
    ∀ ⦃v v' : D⦄, v ∈ V → v' ∈ V → g v = g v' → JoinedIn (V ∩ {e | g e = g v}) v v'

section PullbackGood

variable {U D B : Type u} [TopologicalSpace U] [TopologicalSpace D] [TopologicalSpace B]

/-- The part of a pullback over `W ⊆ U` and `V ⊆ D` is the pullback of the
restrictions. -/
def subPullbackHomeo (f : C(U, B)) (g : C(D, B)) (W : Set U) (V : Set D) :
    (Subtype.val ⁻¹' (W ×ˢ V) : Set (TopPullback f g)) ≃ₜ
      TopPullback (f.comp ⟨Subtype.val, continuous_subtype_val⟩ : C(W, B))
        (g.comp ⟨Subtype.val, continuous_subtype_val⟩ : C(V, B)) where
  toFun q := ⟨(⟨q.1.1.1, q.2.1⟩, ⟨q.1.1.2, q.2.2⟩), q.1.2⟩
  invFun q := ⟨⟨(q.1.1.1, q.1.2.1), q.2⟩, ⟨q.1.1.2, q.1.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · exact (continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
    · exact (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val))

/-- **Closure under designated pullbacks.** -/
theorem Good.pullback (hU : Good U) {g : C(D, B)} (hg : GoodMap g) (f : C(U, B)) :
    Good (TopPullback f g) := by
  have := hU.connected
  refine ⟨connectedSpace_pullback hg.isOpenMap (fun x => hg.surj (f x)) hg.fibres,
    fun p N hN => ?_⟩
  obtain ⟨⟨x, d⟩, hp⟩ := p
  -- a box around `p` inside `N`
  obtain ⟨M, hM, hMN⟩ := mem_nhds_induced Subtype.val _ N |>.mp hN
  obtain ⟨A, hA, E, hE, hAE⟩ := mem_nhds_prod_iff.mp hM
  obtain ⟨V, hVo, hdV, hVE, hVfib⟩ := hg.basis d E hE
  have hgV : IsOpen (g '' V) := hg.isOpenMap V hVo
  have hA' : A ∩ f ⁻¹' (g '' V) ∈ 𝓝 x := by
    refine Filter.inter_mem hA ((hgV.preimage f.continuous).mem_nhds ?_)
    exact ⟨d, hdV, hp.symm⟩
  obtain ⟨W, hWo, hxW, hWA, hWc, hWf⟩ := hU.basis x _ hA'
  set Y : Set (TopPullback f g) := Subtype.val ⁻¹' (W ×ˢ V)
  have e := subPullbackHomeo f g W V
  -- the restricted pullback over `W`
  let fW : C(W, B) := f.comp ⟨Subtype.val, continuous_subtype_val⟩
  let gV : C(V, B) := g.comp ⟨Subtype.val, continuous_subtype_val⟩
  have hgVo : IsOpenMap gV := hg.isOpenMap.comp hVo.isOpenMap_subtype_val
  have hcov : ∀ w : W, ∃ v : V, gV v = fW w := by
    intro w
    obtain ⟨v, hv, hvw⟩ := (hWA w.2).2
    exact ⟨⟨v, hv⟩, hvw⟩
  have hfibV : ∀ ⦃v v' : V⦄, gV v = gV v' → JoinedIn {e | gV e = gV v} v v' := by
    intro v v' h
    obtain ⟨γ, hγ⟩ := hVfib v.2 v'.2 h
    let δ : Path v v' :=
      { toFun := fun t => ⟨γ t, (hγ t).1⟩
        continuous_toFun := γ.continuous.subtype_mk _
        source' := Subtype.ext γ.source
        target' := Subtype.ext γ.target }
    exact ⟨δ, fun t => (hγ t).2⟩
  have : ConnectedSpace W := hWc
  have hconn : ConnectedSpace (TopPullback fW gV) := connectedSpace_pullback hgVo hcov hfibV
  have hFH : PairwiseFiniteHeight (TopCat.of (TopPullback fW gV)) := by
    refine PairwiseFiniteHeight.of_openSurjection (B := TopCat.of (TopPullback fW gV))
      (U := TopCat.of W) (pbFst fW gV) (pbFst_isOpenMap hgVo)
      (pbFst_surjective_of_cover hcov) ?_ hWf
    intro q q' hqq'
    exact (pbFst_joined_of_fibres hfibV hqq').joined
  refine ⟨Y, (hWo.prod hVo).preimage continuous_subtype_val, ⟨hxW, hdV⟩, ?_,
    connectedSpace_of_homeomorph e.symm, hFH.of_homeomorph e.symm⟩
  intro q hq
  exact hMN (hAE ⟨(hWA hq.1).1, hVE hq.2⟩)

end PullbackGood


end RealContinuity
