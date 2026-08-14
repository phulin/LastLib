import LastLib.Book06GlobalClassFieldTheory.Chapter10.Section01PassingOverAllFiniteAbelianExtensions

namespace LastLib.Book06GlobalClassFieldTheory.Chapter10

noncomputable section

open CategoryTheory

universe u v w

/-!
## 10.2. The connected component of the idele class group
-/

/-- The identity component of a topological idele class group, as the
canonical subgroup supplied by Mathlib. -/
def chapter10IdentityComponent
    (C : Type u) [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] : Subgroup C :=
  Subgroup.connectedComponentOfOne C

@[simp]
theorem chapter10IdentityComponent_carrier
    (C : Type u) [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] :
    (chapter10IdentityComponent C : Set C) = connectedComponent (1 : C) :=
  rfl

/-- The norm-one subgroup `C_K^1`. -/
abbrev chapter10NormOneSubgroup
    {C : Type u} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] (T : Chapter10IdeleClassTopologyData C) : Subgroup C :=
  T.normOneSubgroup

/-- The component quotient `C_K/C_K^0`. -/
abbrev chapter10IdeleClassComponentQuotient
    (C : Type u) [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] := C ⧸ chapter10IdentityComponent C

theorem chapter10_identityComponent_le_openFiniteIndex
    {C : Type u} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] (H : Chapter10OpenFiniteIndexNormalSubgroup C) :
    chapter10IdentityComponent C ≤ H.toSubgroup := by
  intro c hc
  change c ∈ connectedComponent (1 : C) at hc
  let hdisc : DiscreteTopology (C ⧸ H.toSubgroup) :=
    QuotientGroup.discreteTopology H.isOpen
  have hclopen :
      IsClopen ({(QuotientGroup.mk' H.toSubgroup) 1} :
        Set (C ⧸ H.toSubgroup)) :=
    ⟨@isClosed_discrete _ _ hdisc _, @isOpen_discrete _ _ hdisc _⟩
  have hsubset :
      connectedComponent ((QuotientGroup.mk' H.toSubgroup) 1) ⊆
        ({(QuotientGroup.mk' H.toSubgroup) 1} :
          Set (C ⧸ H.toSubgroup)) :=
    hclopen.connectedComponent_subset (by simp)
  have hq :
      QuotientGroup.mk' H.toSubgroup c ∈
        connectedComponent ((QuotientGroup.mk' H.toSubgroup) 1) :=
    (Continuous.image_connectedComponent_subset
      (QuotientGroup.continuous_mk) 1) ⟨c, hc, rfl⟩
  have hq' := hsubset hq
  have hq_eq :
      QuotientGroup.mk' H.toSubgroup c =
        QuotientGroup.mk' H.toSubgroup 1 :=
    Set.mem_singleton_iff.mp hq'
  have hq_one : QuotientGroup.mk' H.toSubgroup c = 1 := by
    simpa using hq_eq
  simpa only [SetLike.mem_coe] using (QuotientGroup.eq_one_iff c).mp hq_one

theorem chapter10_identityComponent_maps_trivially_to_finite_quotient
    {C : Type u} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] (H : Chapter10OpenFiniteIndexNormalSubgroup C) :
    (QuotientGroup.mk' H.toSubgroup).comp
        (chapter10IdentityComponent C).subtype = 1 := by
  apply MonoidHom.ext
  intro c
  change (c : C ⧸ H.toSubgroup) = 1
  exact (QuotientGroup.eq_one_iff (N := H.toSubgroup) (c : C)).mpr
    (chapter10_identityComponent_le_openFiniteIndex H c.property)

theorem chapter10_norm_exact_sequence
    {C : Type u} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] (T : Chapter10IdeleClassTopologyData C) :
    Function.MulExact (T.normOneSubgroup.subtype : T.normOneSubgroup → C) T.norm ∧
      Function.Surjective T.norm :=
  T.norm_exact_sequence

/- LOCAL_DEPENDENCY_GUESS: the archimedean positive one-parameter subgroup is
the continuous splitting used to identify the idele class group with its
compact norm-one part times the positive real factor. -/
noncomputable def chapter10IdeleClassProductEquiv
    {C : Type u} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] (T : Chapter10IdeleClassTopologyData C) :
    C ≃ₜ* T.normOneSubgroup × Chapter10PositiveReal := by
  let s : Chapter10PositiveReal →* C := Classical.choose T.split
  have hs : T.norm.comp s = MonoidHom.id _ :=
    (Classical.choose_spec T.split).1
  have hsc : Continuous s :=
    (Classical.choose_spec T.split).2
  have hs_apply (x : Chapter10PositiveReal) : T.norm (s x) = x := by
    simpa using DFunLike.congr_fun hs x
  let a : C → T.normOneSubgroup := fun c =>
    ⟨c * (s (T.norm c))⁻¹, by
      change T.norm (c * (s (T.norm c))⁻¹) = 1
      rw [map_mul, map_inv, hs_apply]
      simp⟩
  let e : C ≃* T.normOneSubgroup × Chapter10PositiveReal :=
    { toFun := fun c => (a c, T.norm c)
      invFun := fun p => (p.1 : C) * s p.2
      left_inv := by
        intro c
        dsimp [a]
        simp [mul_assoc]
      right_inv := by
        rintro ⟨k, x⟩
        apply Prod.ext
        · apply Subtype.ext
          dsimp [a]
          have hk : T.norm (k : C) = 1 := k.property
          simp [hs_apply, hk, mul_assoc]
        · have hk : T.norm (k : C) = 1 := k.property
          simp [hs_apply, hk]
      map_mul' := by
        intro c d
        apply Prod.ext
        · apply Subtype.ext
          dsimp [a]
          simp [mul_assoc, mul_comm, mul_left_comm]
        · exact map_mul T.norm c d }
  have ha : Continuous a := by
    apply Continuous.subtype_mk
    exact continuous_id.mul ((hsc.comp T.norm_continuous).inv)
  have he : Continuous e := by
    change Continuous (fun c : C => (a c, T.norm c))
    exact ha.prodMk T.norm_continuous
  have he_inv : Continuous e.symm := by
    change Continuous (fun p : T.normOneSubgroup × Chapter10PositiveReal =>
      (p.1 : C) * s p.2)
    exact (continuous_subtype_val.comp continuous_fst).mul
      (hsc.comp continuous_snd)
  exact ⟨e, he, he_inv⟩

theorem chapter10_ideleClass_product_has_compact_factor
    {C : Type u} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] (T : Chapter10IdeleClassTopologyData C) :
    IsCompact (T.normOneSubgroup : Set C) :=
  T.normOneSubgroup_compact

theorem chapter10_positiveRealComponent_le_identityComponent
    {C : Type u} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] (T : Chapter10IdeleClassTopologyData C) :
    T.positiveRealComponent ≤ chapter10IdentityComponent C := by
  intro c hc
  change c ∈ connectedComponent (1 : C)
  let s : Chapter10PositiveReal →* C := Classical.choose T.split
  have hsc : Continuous s :=
    (Classical.choose_spec T.split).2
  have hpos : ConnectedSpace {r : ℝ // 0 < r} :=
    Subtype.connectedSpace (isConnected_Ioi : IsConnected (Set.Ioi (0 : ℝ)))
  have hunit : ConnectedSpace Chapter10PositiveReal := by
    exact (Homeomorph.connectedSpace_iff
      (Nonneg.unitsHomeomorphPos ℝ)).mpr hpos
  have hsr : IsConnected (Set.range s) :=
    @isConnected_range Chapter10PositiveReal C _ _ hunit s hsc
  have hsubset' : Set.range s ⊆ connectedComponent (s 1) :=
    hsr.subset_connectedComponent ⟨1, rfl⟩
  have hsubset : Set.range s ⊆ connectedComponent (1 : C) := by
    simpa using hsubset'
  change c ∈ Set.range s at hc
  exact hsubset hc

theorem chapter10_identityComponent_quotient_compact
    {C : Type u} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] (T : Chapter10IdeleClassTopologyData C) :
    IsCompact (Set.univ : Set (chapter10IdeleClassComponentQuotient C)) := by
  let s : Chapter10PositiveReal →* C := Classical.choose T.split
  have hs : T.norm.comp s = MonoidHom.id _ :=
    (Classical.choose_spec T.split).1
  have hs_apply (x : Chapter10PositiveReal) : T.norm (s x) = x := by
    simpa using DFunLike.congr_fun hs x
  have hcompact :
      IsCompact ((QuotientGroup.mk' (chapter10IdentityComponent C)) ''
        (T.normOneSubgroup : Set C)) :=
    T.normOneSubgroup_compact.image QuotientGroup.continuous_mk
  have himage :
      (QuotientGroup.mk' (chapter10IdentityComponent C)) ''
          (T.normOneSubgroup : Set C) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    rcases QuotientGroup.mk'_surjective (chapter10IdentityComponent C) y with ⟨c, rfl⟩
    let k : C := c * (s (T.norm c))⁻¹
    have hk : k ∈ T.normOneSubgroup := by
      change T.norm k = 1
      dsimp [k]
      rw [map_mul, map_inv, hs_apply]
      simp
    have hsC0 : s (T.norm c) ∈ chapter10IdentityComponent C := by
      apply chapter10_positiveRealComponent_le_identityComponent T
      change s (T.norm c) ∈ Set.range s
      exact ⟨T.norm c, rfl⟩
    have hq :
        QuotientGroup.mk' (chapter10IdentityComponent C) k =
          QuotientGroup.mk' (chapter10IdentityComponent C) c := by
      apply (QuotientGroup.mk'_eq_mk' (chapter10IdentityComponent C)).2
      refine ⟨s (T.norm c), hsC0, ?_⟩
      dsimp [k]
      simp [mul_assoc]
    exact ⟨k, hk, hq⟩
  rw [← himage]
  exact hcompact

theorem chapter10_identityComponent_quotient_totallyDisconnected
    {C : Type u} [CommGroup C] [TopologicalSpace C] [T2Space C]
    [IsTopologicalGroup C] :
    TotallyDisconnectedSpace (chapter10IdeleClassComponentQuotient C) := by
  let H : Subgroup C := chapter10IdentityComponent C
  let q : C → C ⧸ H := QuotientGroup.mk
  have h_fibers : ∀ y : C ⧸ H, IsConnected (q ⁻¹' {y}) := by
    intro y
    rcases QuotientGroup.mk_surjective y with ⟨c, rfl⟩
    have hfiber :
        q ⁻¹' {q c} =
          (fun z : C => c * z) '' connectedComponent (1 : C) := by
      ext x
      constructor
      · intro hx
        have hxeq : q x = q c := Set.mem_singleton_iff.mp hx
        have hxeq' :
            QuotientGroup.mk' H x = QuotientGroup.mk' H c := by
          simpa [q] using hxeq
        rcases (QuotientGroup.mk'_eq_mk' H).mp hxeq' with ⟨z, hz, hxz⟩
        change z ∈ connectedComponent (1 : C) at hz
        refine ⟨z⁻¹, inv_mem_connectedComponent_one hz, ?_⟩
        calc
          c * z⁻¹ = (x * z) * z⁻¹ := by rw [hxz]
          _ = x := by simp [mul_assoc]
      · rintro ⟨z, hz, rfl⟩
        have hzeq : z ∈ H := hz
        have hqeq : q (c * z) = q c := by
          simpa [q] using
            (QuotientGroup.mk'_eq_mk' H (x := c * z) (y := c)).2
              ⟨z⁻¹, H.inv_mem hzeq, by
                rw [mul_assoc, mul_inv_cancel, mul_one]⟩
        exact Set.mem_singleton_iff.mpr hqeq
    rw [hfiber]
    exact isConnected_connectedComponent.image _ (continuous_const_mul c).continuousOn
  have hcoind : Topology.IsCoinducing q :=
    (QuotientGroup.isQuotientMap_mk H).isCoinducing
  have himage :
      q '' connectedComponent (1 : C) =
        connectedComponent (q 1) :=
    hcoind.image_connectedComponent h_fibers 1
  have hsingleton :
      q '' connectedComponent (1 : C) = {q 1} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : x ∈ H := hx
      have hqone : q x = 1 := by
        simpa [q] using (QuotientGroup.eq_one_iff (N := H) x).2 hx'
      calc
        q x = 1 := hqone
        _ = q 1 := by simp [q]
    · intro hy
      have hy' : y = q 1 := Set.mem_singleton_iff.mp hy
      exact ⟨1, mem_connectedComponent, hy'.symm⟩
  have hcomp : connectedComponent (q 1) = {q 1} :=
    himage.symm.trans hsingleton
  apply totallyDisconnectedSpace_iff_connectedComponent_one.mpr
  simpa [q] using hcomp

/- The previous two assertions are packaged as the profinite quotient used in
the completion comparison. -/
noncomputable def chapter10IdeleClassComponentProfiniteQuotient
    {C : Type u} [CommGroup C] [TopologicalSpace C] [T2Space C]
    [IsTopologicalGroup C] (T : Chapter10IdeleClassTopologyData C) : ProfiniteGrp := by
  letI : CompactSpace (chapter10IdeleClassComponentQuotient C) :=
    ⟨by simpa only [isCompact_univ] using chapter10_identityComponent_quotient_compact T⟩
  letI : TotallyDisconnectedSpace (chapter10IdeleClassComponentQuotient C) :=
    chapter10_identityComponent_quotient_totallyDisconnected
  exact ProfiniteGrp.of (chapter10IdeleClassComponentQuotient C)

def chapter10OpenFiniteIndexResidualKernel
    (C : Type u) [CommGroup C] [TopologicalSpace C] : Subgroup C :=
  ⨅ H : Chapter10OpenFiniteIndexNormalSubgroup C, H.toSubgroup

theorem chapter10_identityComponent_le_residualKernel
    {C : Type u} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] :
    chapter10IdentityComponent C ≤ chapter10OpenFiniteIndexResidualKernel C := by
  intro c hc
  simp only [chapter10OpenFiniteIndexResidualKernel, Subgroup.mem_iInf]
  intro H
  exact chapter10_identityComponent_le_openFiniteIndex H hc

theorem chapter10_finite_quotient_detects_nonidentityComponent
    {C : Type u} [CommGroup C] [TopologicalSpace C] [T2Space C]
    [IsTopologicalGroup C] (T : Chapter10IdeleClassTopologyData C)
    {c : C} (hc : c ∉ chapter10IdentityComponent C) :
    ∃ H : Chapter10OpenFiniteIndexNormalSubgroup C, c ∉ H.toSubgroup := by
  let hcompact : CompactSpace (chapter10IdeleClassComponentQuotient C) :=
    ⟨by simpa only [isCompact_univ] using
        chapter10_identityComponent_quotient_compact T⟩
  let htds : TotallyDisconnectedSpace (chapter10IdeleClassComponentQuotient C) :=
    chapter10_identityComponent_quotient_totallyDisconnected
  let q : C →* chapter10IdeleClassComponentQuotient C :=
    QuotientGroup.mk' (chapter10IdentityComponent C)
  have hqc : q c ≠ 1 := by
    intro hqc
    apply hc
    exact (QuotientGroup.eq_one_iff (N := chapter10IdentityComponent C) c).mp hqc
  let U : Set (chapter10IdeleClassComponentQuotient C) := {q c}ᶜ
  have hUopen : IsOpen U := by
    exact isClosed_singleton.isOpen_compl
  have hUone : (1 : chapter10IdeleClassComponentQuotient C) ∈ U := by
    change (1 : chapter10IdeleClassComponentQuotient C) ∉ {q c}
    simpa using hqc.symm
  obtain ⟨V, hVU⟩ :=
    @ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      (chapter10IdeleClassComponentQuotient C) _ _ _ hcompact htds U hUopen hUone
  let N₀ : FiniteIndexNormalSubgroup C :=
    FiniteIndexNormalSubgroup.comap q V.toFiniteIndexNormalSubgroup
  let N : Chapter10OpenFiniteIndexNormalSubgroup C :=
    { toSubgroup := N₀.toSubgroup
      isNormal' := N₀.isNormal'
      isFiniteIndex' := N₀.isFiniteIndex'
      isOpen := by
        change IsOpen (q ⁻¹' (V.toSubgroup : Set _))
        exact V.toOpenSubgroup.isOpen.preimage QuotientGroup.continuous_mk }
  refine ⟨N, ?_⟩
  intro hqcV
  apply hqc
  have : q c ∈ (V : Set (chapter10IdeleClassComponentQuotient C)) := hqcV
  exfalso
  exact (hVU this) (by simp)

theorem chapter10_residualKernel_le_identityComponent
    {C : Type u} [CommGroup C] [TopologicalSpace C] [T2Space C]
    [IsTopologicalGroup C] (T : Chapter10IdeleClassTopologyData C) :
    chapter10OpenFiniteIndexResidualKernel C ≤ chapter10IdentityComponent C := by
  intro c hc
  by_contra hnot
  obtain ⟨H, hH⟩ := chapter10_finite_quotient_detects_nonidentityComponent T hnot
  have hc' : ∀ H : Chapter10OpenFiniteIndexNormalSubgroup C,
      c ∈ H.toSubgroup := by
    simpa only [chapter10OpenFiniteIndexResidualKernel, Subgroup.mem_iInf] using hc
  exact hH (hc' H)

theorem chapter10_intersection_openFiniteIndex_eq_identityComponent
    {C : Type u} [CommGroup C] [TopologicalSpace C] [T2Space C]
    [IsTopologicalGroup C] (T : Chapter10IdeleClassTopologyData C) :
    chapter10OpenFiniteIndexResidualKernel C = chapter10IdentityComponent C := by
  apply le_antisymm
  · exact chapter10_residualKernel_le_identityComponent T
  · exact chapter10_identityComponent_le_residualKernel

theorem chapter10_identityComponent_le_completion_kernel
    {C : Type u} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] :
    chapter10IdentityComponent C ≤
      (chapter10ProfiniteCompletionEta C).ker := by
  intro c hc
  change chapter10ProfiniteCompletionEta C c = 1
  apply ProfiniteGrp.limit_ext
  intro H
  change QuotientGroup.mk c = 1
  exact (QuotientGroup.eq_one_iff c).mpr
    (chapter10_identityComponent_le_openFiniteIndex H hc)

noncomputable def chapter10ComponentToCompletion
    {C : Type u} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] :
    chapter10IdeleClassComponentQuotient C →*
      chapter10ProfiniteCompletion C := by
  exact QuotientGroup.lift _ (chapter10ProfiniteCompletionEta C)
    chapter10_identityComponent_le_completion_kernel

/- LOCAL_DEPENDENCY_GUESS: compactness of the component quotient and the
finite-quotient separation above make the quotient-to-completion map a
topological group isomorphism. -/
noncomputable def chapter10ComponentCompletionEquiv
    {C : Type u} [CommGroup C] [TopologicalSpace C] [T2Space C]
    [IsTopologicalGroup C] (T : Chapter10IdeleClassTopologyData C) :
    chapter10IdeleClassComponentQuotient C ≃ₜ*
      chapter10ProfiniteCompletion C := by
  let hcompact : CompactSpace (chapter10IdeleClassComponentQuotient C) :=
    ⟨by simpa only [isCompact_univ] using
        chapter10_identityComponent_quotient_compact T⟩
  let f : chapter10IdeleClassComponentQuotient C →*
      chapter10ProfiniteCompletion C :=
    chapter10ComponentToCompletion
  have hfq (c : C) :
      f (QuotientGroup.mk c) = chapter10ProfiniteCompletionEta C c := by
    dsimp [f, chapter10ComponentToCompletion]
  have hfcont : Continuous f := by
    apply (QuotientGroup.isQuotientMap_mk
      (chapter10IdentityComponent C)).continuous_iff.mpr
    have hfun : f ∘ (QuotientGroup.mk : C →
        chapter10IdeleClassComponentQuotient C) =
        chapter10ProfiniteCompletionEta C := by
      funext c
      exact hfq c
    rw [hfun]
    exact chapter10ProfiniteCompletionEta_continuous C
  have hfinj : Function.Injective f := by
    intro x y hxy
    obtain ⟨c, rfl⟩ :=
      QuotientGroup.mk'_surjective (chapter10IdentityComponent C) x
    obtain ⟨d, rfl⟩ :=
      QuotientGroup.mk'_surjective (chapter10IdentityComponent C) y
    have hcd_eta : chapter10ProfiniteCompletionEta C c =
        chapter10ProfiniteCompletionEta C d := by
      rw [← hfq c, ← hfq d]
      exact hxy
    have hdiv_eta : chapter10ProfiniteCompletionEta C (c / d) = 1 := by
      rw [map_div, hcd_eta]
      simp
    have hres : c / d ∈ chapter10OpenFiniteIndexResidualKernel C := by
      simp only [chapter10OpenFiniteIndexResidualKernel, Subgroup.mem_iInf]
      intro H
      have hcoord := congrArg
        (chapter10ProfiniteCompletionProjection C H) hdiv_eta
      change (chapter10ProfiniteCompletionProjection C H)
          (chapter10ProfiniteCompletionEta C (c / d)) = 1 at hcoord
      rw [chapter10ProfiniteCompletionProjection_eta] at hcoord
      apply (QuotientGroup.eq_one_iff (c / d)).mp
      exact hcoord
    apply (QuotientGroup.eq_iff_div_mem).mpr
    exact chapter10_residualKernel_le_identityComponent T hres
  have hfclosed : IsClosedMap f :=
    @Continuous.isClosedMap _ _ _ _ hcompact inferInstance f hfcont
  have hrange_sub : Set.range (chapter10ProfiniteCompletionEta C) ⊆
      Set.range f := by
    rintro z ⟨c, rfl⟩
    exact ⟨QuotientGroup.mk c, hfq c⟩
  have hdense : Dense (Set.range f) := by
    apply dense_iff_closure_eq.mpr
    refine Set.Subset.antisymm (fun _ _ ↦ Set.mem_univ _) ?_
    rw [← (chapter10ProfiniteCompletionEta_denseRange C).closure_range]
    exact closure_mono hrange_sub
  have hsurj : Function.Surjective f := by
    rw [← Set.range_eq_univ]
    calc
      Set.range f = closure (Set.range f) := hfclosed.isClosed_range.closure_eq.symm
      _ = Set.univ := hdense.closure_eq
  let e : chapter10IdeleClassComponentQuotient C ≃*
      chapter10ProfiniteCompletion C :=
    MulEquiv.ofBijective f ⟨hfinj, hsurj⟩
  have hefun : (e : chapter10IdeleClassComponentQuotient C →
      chapter10ProfiniteCompletion C) = f := by
    funext x
    exact MulEquiv.ofBijective_apply f ⟨hfinj, hsurj⟩ x
  let eTop : chapter10IdeleClassComponentQuotient C ≃ₜ
      chapter10ProfiniteCompletion C :=
    @Continuous.homeoOfEquivCompactToT2 _ _ _ _ hcompact inferInstance e
      (by
        change Continuous (e : chapter10IdeleClassComponentQuotient C →
          chapter10ProfiniteCompletion C)
        rw [hefun]
        exact hfcont)
  exact ContinuousMulEquiv.mk' eTop (by
    intro x y
    change f (x * y) = f x * f y
    exact map_mul f x y)

theorem chapter10ComponentCompletionEquiv_comp_quotientMap
    {C : Type u} [CommGroup C] [TopologicalSpace C] [T2Space C]
    [IsTopologicalGroup C] (T : Chapter10IdeleClassTopologyData C) (c : C) :
    chapter10ComponentCompletionEquiv T (QuotientGroup.mk c) =
      chapter10ProfiniteCompletionEta C c := by
  change (chapter10ComponentToCompletion (C := C))
      (QuotientGroup.mk c) = chapter10ProfiniteCompletionEta C c
  rfl

theorem chapter10_component_quotient_is_complete
    {C : Type u} [CommGroup C] [TopologicalSpace C] [T2Space C]
    [IsTopologicalGroup C] (T : Chapter10IdeleClassTopologyData C) :
    @CompleteSpace (chapter10IdeleClassComponentQuotient C)
      (IsTopologicalGroup.rightUniformSpace
        (chapter10IdeleClassComponentQuotient C)) := by
  let hcompact : CompactSpace (chapter10IdeleClassComponentQuotient C) :=
    ⟨by simpa only [isCompact_univ] using
        chapter10_identityComponent_quotient_compact T⟩
  exact @complete_of_compact _
    (IsTopologicalGroup.rightUniformSpace (chapter10IdeleClassComponentQuotient C))
    hcompact

theorem chapter10_globalArtinMap_kernel_eq_identityComponent
    {C : Type u} {K : Type v} {Kab : Type w}
    [CommGroup C] [TopologicalSpace C] [T2Space C]
    [IsTopologicalGroup C] [Field K] [Field Kab] [Algebra K Kab]
    [IsGalois K Kab] (T : Chapter10IdeleClassTopologyData C)
    (F : Chapter10FiniteArtinFamily C K Kab)
    (R : Chapter10FiniteReciprocityData F) :
    (chapter10GlobalArtinMap F).ker = chapter10IdentityComponent C := by
  apply le_antisymm
  · intro c hc
    have hglobal : chapter10GlobalArtinMap F c = 1 := hc
    have hlim : chapter10ArtinLimitMap F c = 1 := by
      simpa [chapter10GlobalArtinMap] using
        congrArg (InfiniteGalois.mulEquivToLimit K Kab) hglobal
    have hres : c ∈ chapter10OpenFiniteIndexResidualKernel C := by
      simp only [chapter10OpenFiniteIndexResidualKernel, Subgroup.mem_iInf]
      intro H
      obtain ⟨L, hL⟩ := R.kernel_cofinal H
      rw [hL]
      apply MonoidHom.mem_ker.mpr
      have hcoord := congrArg
        (fun g : ProfiniteGrp.limit
          (InfiniteGalois.asProfiniteGaloisGroupFunctor K Kab) =>
          g.val (Opposite.op L)) hlim
      change F.map L c = 1 at hcoord
      exact hcoord
    exact chapter10_residualKernel_le_identityComponent T hres
  · intro c hc
    have hlim : chapter10ArtinLimitMap F c = 1 := by
      apply ProfiniteGrp.limit_ext
      intro L
      change F.map L.unop c = 1
      let H : Chapter10OpenFiniteIndexNormalSubgroup C :=
        { toSubgroup := (F.map L.unop).ker
          isNormal' := inferInstance
          isFiniteIndex' := F.map_kernel_finiteIndex L.unop
          isOpen := F.map_kernel_open L.unop }
      exact MonoidHom.mem_ker.mp
        (chapter10_identityComponent_le_openFiniteIndex H hc)
    change chapter10GlobalArtinMap F c = 1
    apply (InfiniteGalois.mulEquivToLimit K Kab).injective
    simp [chapter10GlobalArtinMap, hlim]

theorem chapter10_globalArtinMap_surjective
    {C : Type u} {K : Type v} {Kab : Type w}
    [CommGroup C] [TopologicalSpace C] [T2Space C]
    [IsTopologicalGroup C] [Field K] [Field Kab] [Algebra K Kab]
    [IsGalois K Kab] (T : Chapter10IdeleClassTopologyData C)
    (F : Chapter10FiniteArtinFamily C K Kab)
    (R : Chapter10FiniteReciprocityData F) :
    Function.Surjective (chapter10GlobalArtinMap F) := by
  let q : chapter10IdeleClassComponentQuotient C ≃ₜ* Gal(Kab / K) :=
    (chapter10ComponentCompletionEquiv T).trans
      (chapter10InfiniteReciprocityEquiv F R)
  have hq (c : C) :
      q (QuotientGroup.mk c) = chapter10GlobalArtinMap F c := by
    change chapter10InfiniteReciprocityEquiv F R
        (chapter10ComponentCompletionEquiv T (QuotientGroup.mk c)) =
      chapter10GlobalArtinMap F c
    rw [chapter10ComponentCompletionEquiv_comp_quotientMap,
      chapter10InfiniteReciprocityEquiv_apply_eta]
  intro g
  obtain ⟨x, hx⟩ := q.surjective g
  obtain ⟨c, rfl⟩ :=
    QuotientGroup.mk'_surjective (chapter10IdentityComponent C) x
  exact ⟨c, (hq c).symm.trans hx⟩

noncomputable def chapter10GlobalArtinQuotientEquiv
    {C : Type u} {K : Type v} {Kab : Type w}
    [CommGroup C] [TopologicalSpace C] [T2Space C]
    [IsTopologicalGroup C] [Field K] [Field Kab] [Algebra K Kab]
    [IsGalois K Kab] (T : Chapter10IdeleClassTopologyData C)
    (F : Chapter10FiniteArtinFamily C K Kab)
    (R : Chapter10FiniteReciprocityData F) :
    chapter10IdeleClassComponentQuotient C ≃ₜ* Gal(Kab / K) := by
  exact (chapter10ComponentCompletionEquiv T).trans
    (chapter10InfiniteReciprocityEquiv F R)

theorem chapter10GlobalArtinQuotientEquiv_comp_quotientMap
    {C : Type u} {K : Type v} {Kab : Type w}
    [CommGroup C] [TopologicalSpace C] [T2Space C]
    [IsTopologicalGroup C] [Field K] [Field Kab] [Algebra K Kab]
    [IsGalois K Kab] (T : Chapter10IdeleClassTopologyData C)
    (F : Chapter10FiniteArtinFamily C K Kab)
    (R : Chapter10FiniteReciprocityData F) (c : C) :
    chapter10GlobalArtinQuotientEquiv T F R (QuotientGroup.mk c) =
      chapter10GlobalArtinMap F c := by
  change chapter10InfiniteReciprocityEquiv F R
      (chapter10ComponentCompletionEquiv T (QuotientGroup.mk c)) =
    chapter10GlobalArtinMap F c
  rw [chapter10ComponentCompletionEquiv_comp_quotientMap,
    chapter10InfiniteReciprocityEquiv_apply_eta]

theorem chapter10_global_reciprocity_scope_summary
    {C : Type u} {K : Type v} {Kab : Type w}
    [CommGroup C] [TopologicalSpace C] [T2Space C]
    [IsTopologicalGroup C] [Field K] [Field Kab] [Algebra K Kab]
    [IsGalois K Kab] (T : Chapter10IdeleClassTopologyData C)
    (F : Chapter10FiniteArtinFamily C K Kab)
    (R : Chapter10FiniteReciprocityData F) :
    (chapter10GlobalArtinMap F).ker = chapter10IdentityComponent C ∧
      Function.Surjective (chapter10GlobalArtinMap F) ∧
      Nonempty (chapter10ProfiniteCompletion C ≃ₜ* Gal(Kab / K)) := by
  exact ⟨chapter10_globalArtinMap_kernel_eq_identityComponent T F R,
    chapter10_globalArtinMap_surjective T F R,
    ⟨chapter10InfiniteReciprocityEquiv (C := C) (K := K) (Kab := Kab) F R⟩⟩

end

end LastLib.Book06GlobalClassFieldTheory.Chapter10
