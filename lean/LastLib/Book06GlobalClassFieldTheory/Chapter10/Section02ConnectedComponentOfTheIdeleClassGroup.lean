import LastLib.Book06GlobalClassFieldTheory.Chapter10.Section01PassingOverAllFiniteAbelianExtensions

namespace LastLib.Book06GlobalClassFieldTheory.Chapter10

noncomputable section

open CategoryTheory

universe u

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
  sorry

theorem chapter10_identityComponent_maps_trivially_to_finite_quotient
    {C : Type u} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] (H : Chapter10OpenFiniteIndexNormalSubgroup C) :
    (QuotientGroup.mk' H.toSubgroup).comp
        (chapter10IdentityComponent C).subtype = 1 := by
  sorry

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
  sorry

theorem chapter10_ideleClass_product_has_compact_factor
    {C : Type u} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] (T : Chapter10IdeleClassTopologyData C) :
    IsCompact (T.normOneSubgroup : Set C) :=
  T.normOneSubgroup_compact

theorem chapter10_positiveRealComponent_le_identityComponent
    {C : Type u} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] (T : Chapter10IdeleClassTopologyData C) :
    T.positiveRealComponent ≤ chapter10IdentityComponent C := by
  sorry

theorem chapter10_identityComponent_quotient_compact
    {C : Type u} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] (T : Chapter10IdeleClassTopologyData C) :
    IsCompact (Set.univ : Set (chapter10IdeleClassComponentQuotient C)) := by
  sorry

theorem chapter10_identityComponent_quotient_totallyDisconnected
    {C : Type u} [CommGroup C] [TopologicalSpace C] [T2Space C]
    [IsTopologicalGroup C] :
    TotallyDisconnectedSpace (chapter10IdeleClassComponentQuotient C) := by
  sorry

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
  sorry

theorem chapter10_residualKernel_le_identityComponent
    {C : Type u} [CommGroup C] [TopologicalSpace C] [T2Space C]
    [IsTopologicalGroup C] (T : Chapter10IdeleClassTopologyData C) :
    chapter10OpenFiniteIndexResidualKernel C ≤ chapter10IdentityComponent C := by
  sorry

theorem chapter10_intersection_openFiniteIndex_eq_identityComponent
    {C : Type u} [CommGroup C] [TopologicalSpace C] [T2Space C]
    [IsTopologicalGroup C] (T : Chapter10IdeleClassTopologyData C) :
    chapter10OpenFiniteIndexResidualKernel C = chapter10IdentityComponent C := by
  apply le_antisymm
  · exact chapter10_residualKernel_le_identityComponent T
  · exact chapter10_identityComponent_le_residualKernel

theorem chapter10_identityComponent_le_completion_kernel
    {C : Type u} [CommGroup C] [TopologicalSpace C] [T2Space C]
    [IsTopologicalGroup C] (T : Chapter10IdeleClassTopologyData C) :
    chapter10IdentityComponent C ≤
      (chapter10ProfiniteCompletionEta C).ker := by
  sorry

noncomputable def chapter10ComponentToCompletion
    {C : Type u} [CommGroup C] [TopologicalSpace C] [T2Space C]
    [IsTopologicalGroup C] (T : Chapter10IdeleClassTopologyData C) :
    chapter10IdeleClassComponentQuotient C →*
      chapter10ProfiniteCompletion C := by
  exact QuotientGroup.lift _ (chapter10ProfiniteCompletionEta C)
    (chapter10_identityComponent_le_completion_kernel T)

/- LOCAL_DEPENDENCY_GUESS: compactness of the component quotient and the
finite-quotient separation above make the quotient-to-completion map a
topological group isomorphism. -/
noncomputable def chapter10ComponentCompletionEquiv
    {C : Type u} [CommGroup C] [TopologicalSpace C] [T2Space C]
    [IsTopologicalGroup C] (T : Chapter10IdeleClassTopologyData C) :
    chapter10IdeleClassComponentQuotient C ≃ₜ*
      chapter10ProfiniteCompletion C := by
  sorry

theorem chapter10ComponentCompletionEquiv_comp_quotientMap
    {C : Type u} [CommGroup C] [TopologicalSpace C] [T2Space C]
    [IsTopologicalGroup C] (T : Chapter10IdeleClassTopologyData C) (c : C) :
    chapter10ComponentCompletionEquiv T (QuotientGroup.mk c) =
      chapter10ProfiniteCompletionEta C c := by
  sorry

theorem chapter10_component_quotient_is_complete
    {C : Type u} [CommGroup C] [TopologicalSpace C] [T2Space C]
    [IsTopologicalGroup C] (T : Chapter10IdeleClassTopologyData C) :
    @CompleteSpace (chapter10IdeleClassComponentQuotient C)
      (IsTopologicalGroup.rightUniformSpace
        (chapter10IdeleClassComponentQuotient C)) := by
  sorry

/- SOURCE_ISSUE: In §10.2, the paragraph beginning “The dimension count can be
upgraded to an irreducibility proof” introduces `G_M`, `R`, and `Γ_θ` without
defining them, then asserts “Therefore ker Art_K = C_K^0” without a statement
linking that representation-theoretic discussion to the Artin map. This is an
unattached argument, not a valid proof of the preceding idele-class claim; the
declarations below use the finite-quotient separation argument instead. -/

theorem chapter10_globalArtinMap_kernel_eq_identityComponent
    {C K Kab : Type u} [CommGroup C] [TopologicalSpace C] [T2Space C]
    [IsTopologicalGroup C] [Field K] [Field Kab] [Algebra K Kab]
    [IsGalois K Kab] (T : Chapter10IdeleClassTopologyData C)
    (F : Chapter10FiniteArtinFamily C K Kab)
    (R : Chapter10FiniteReciprocityData F) :
    (chapter10GlobalArtinMap F).ker = chapter10IdentityComponent C := by
  sorry

theorem chapter10_globalArtinMap_surjective
    {C K Kab : Type u} [CommGroup C] [TopologicalSpace C] [T2Space C]
    [IsTopologicalGroup C] [Field K] [Field Kab] [Algebra K Kab]
    [IsGalois K Kab] (T : Chapter10IdeleClassTopologyData C)
    (F : Chapter10FiniteArtinFamily C K Kab)
    (R : Chapter10FiniteReciprocityData F) :
    Function.Surjective (chapter10GlobalArtinMap F) := by
  sorry

noncomputable def chapter10GlobalArtinQuotientEquiv
    {C K Kab : Type u} [CommGroup C] [TopologicalSpace C] [T2Space C]
    [IsTopologicalGroup C] [Field K] [Field Kab] [Algebra K Kab]
    [IsGalois K Kab] (T : Chapter10IdeleClassTopologyData C)
    (F : Chapter10FiniteArtinFamily C K Kab)
    (R : Chapter10FiniteReciprocityData F) :
    chapter10IdeleClassComponentQuotient C ≃ₜ* Gal(Kab / K) := by
  sorry

theorem chapter10GlobalArtinQuotientEquiv_comp_quotientMap
    {C K Kab : Type u} [CommGroup C] [TopologicalSpace C] [T2Space C]
    [IsTopologicalGroup C] [Field K] [Field Kab] [Algebra K Kab]
    [IsGalois K Kab] (T : Chapter10IdeleClassTopologyData C)
    (F : Chapter10FiniteArtinFamily C K Kab)
    (R : Chapter10FiniteReciprocityData F) (c : C) :
    chapter10GlobalArtinQuotientEquiv T F R (QuotientGroup.mk c) =
      chapter10GlobalArtinMap F c := by
  sorry

theorem chapter10_global_reciprocity_scope_summary
    {C K Kab : Type u} [CommGroup C] [TopologicalSpace C] [T2Space C]
    [IsTopologicalGroup C] [Field K] [Field Kab] [Algebra K Kab]
    [IsGalois K Kab] (T : Chapter10IdeleClassTopologyData C)
    (F : Chapter10FiniteArtinFamily C K Kab)
    (R : Chapter10FiniteReciprocityData F) :
    (chapter10GlobalArtinMap F).ker = chapter10IdentityComponent C ∧
      Function.Surjective (chapter10GlobalArtinMap F) ∧
      Nonempty (chapter10ProfiniteCompletion C ≃ₜ* Gal(Kab / K)) := by
  exact ⟨chapter10_globalArtinMap_kernel_eq_identityComponent T F R,
    chapter10_globalArtinMap_surjective T F R,
    ⟨chapter10InfiniteReciprocityEquiv F R⟩⟩

end

end LastLib.Book06GlobalClassFieldTheory.Chapter10
