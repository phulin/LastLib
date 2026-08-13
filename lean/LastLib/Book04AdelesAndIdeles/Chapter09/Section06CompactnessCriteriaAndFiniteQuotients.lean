import LastLib.Book04AdelesAndIdeles.Chapter09.Section04StructureOfIdeleClassGroup

namespace LastLib.Book04AdelesAndIdeles.Chapter09

noncomputable section

open NumberField IsDedekindDomain

/-!
## 9.6. Compactness criteria and finite quotients
-/

theorem chapter09_finite_range_of_continuous_map_from_compact_to_discrete
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [CompactSpace G]
    [TopologicalSpace H] [DiscreteTopology H]
    (f : G →* H) (hf : Continuous f) :
    (Set.range f).Finite := by
  have hcompact : IsCompact (Set.range f) := by
    rw [← Set.image_univ]
    exact isCompact_univ.image hf
  exact hcompact.finite_of_discrete

structure Chapter09DiscreteArithmeticQuotient
    (G : Type*) [Group G] [TopologicalSpace G]
    (H : Type*) [Group H] [TopologicalSpace H] [DiscreteTopology H] where
  map : G →* H
  continuous_map : Continuous map

theorem chapter09_discrete_arithmetic_quotient_has_finite_image
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [CompactSpace G]
    [TopologicalSpace H] [DiscreteTopology H]
    (Q : Chapter09DiscreteArithmeticQuotient G H) :
    (Set.range Q.map).Finite := by
  exact chapter09_finite_range_of_continuous_map_from_compact_to_discrete
    Q.map Q.continuous_map

theorem chapter09NormOneClassIdealClassMap_continuous
    (K : Type*) [Field K] [NumberField K] :
    Continuous (chapter09NormOneClassIdealClassMap K) := by
  sorry

theorem chapter09_ideal_class_group_is_finite
    (K : Type*) [Field K] [NumberField K] :
    Finite (ClassGroup (𝓞 K)) := by
  infer_instance

theorem chapter09_ideal_class_group_is_finite_as_set
    (K : Type*) [Field K] [NumberField K] :
    (Set.univ : Set (ClassGroup (𝓞 K))).Finite := by
  exact Set.toFinite _

theorem chapter09_normOne_class_maps_to_finite_ideal_class_group
    (K : Type*) [Field K] [NumberField K] :
    (Set.range (chapter09NormOneClassIdealClassMap K)).Finite := by
  exact chapter09_finite_range_of_continuous_map_from_compact_to_discrete
    (chapter09NormOneClassIdealClassMap K)
    (chapter09NormOneClassIdealClassMap_continuous K)

abbrev Chapter09ArchMagnitudeQuotient
    (K : Type*) [Field K] [NumberField K] :=
  Chapter09Idele K ⧸ chapter09PrincipalTimesFiniteUnits K

def chapter09ArchMagnitudeModule
    (K : Type*) [Field K] [NumberField K] :
    Chapter09ArchMagnitudeQuotient K →* Chapter09PositiveReal :=
  QuotientGroup.lift (chapter09PrincipalTimesFiniteUnits K)
    (chapter09IdeleModuleHom K) (by
      intro x hx
      sorry)

theorem chapter09ArchMagnitudeModule_apply
    {K : Type*} [Field K] [NumberField K] (x : Chapter09Idele K) :
    chapter09ArchMagnitudeModule K (QuotientGroup.mk x) =
      chapter09IdeleModuleHom K x := by
  rfl

theorem chapter09ArchMagnitudeModule_surjective
    (K : Type*) [Field K] [NumberField K] :
    Function.Surjective (chapter09ArchMagnitudeModule K) := by
  sorry

theorem chapter09ArchMagnitudeQuotient_is_not_compact
    (K : Type*) [Field K] [NumberField K] :
    ¬ IsCompact (Set.univ : Set (Chapter09ArchMagnitudeQuotient K)) := by
  sorry

/- The full idele class group has the same obstruction: its positive real
module quotient cannot be made finite by a discrete quotient argument. -/
theorem chapter09_full_idele_class_group_is_not_compact
    (K : Type*) [Field K] [NumberField K] :
    ¬ IsCompact (Set.univ : Set (Chapter09IdeleClassGroup K)) :=
  chapter09_idele_class_group_is_not_compact K

theorem chapter09_compactness_requires_norm_one_or_archimedean_quotient
    (K : Type*) [Field K] [NumberField K] :
    IsCompact (Set.univ : Set (chapter09ClassNormOne K)) ∧
      ¬ IsCompact (Set.univ : Set (Chapter09ArchMagnitudeQuotient K)) := by
  exact ⟨chapter09_normOne_class_compact K,
    chapter09ArchMagnitudeQuotient_is_not_compact K⟩

end

end LastLib.Book04AdelesAndIdeles.Chapter09
