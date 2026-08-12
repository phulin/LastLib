import LastLib.Book04AdelesAndIdeles.Chapter14.Dependencies

/-!
# 14.2. Finite levels and ray neighborhoods
-/

noncomputable section

namespace LastLib.Book04AdelesAndIdeles.Chapter14

theorem chapter14_ray_level_is_open_and_finite {K : Type*} [Field K] [NumberField K]
    (D : Chapter14IdeleLevelData K) (R : Chapter14RaySubgroupFamily D)
    (m : Chapter14Modulus K) :
    IsOpen ((chapter14RayFiniteLevel D R m).subgroup :
      Set (chapter14IdeleGroup K)) ∧
      (chapter14PrincipalIdeleSubgroup K ⊔
        (chapter14RayFiniteLevel D R m).subgroup).FiniteIndex := by
  exact ⟨(chapter14RayFiniteLevel D R m).isOpen',
    (chapter14RayFiniteLevel D R m).finiteIndex'⟩

theorem chapter14_ray_class_group_is_finite {K : Type*} [Field K] [NumberField K]
    (D : Chapter14IdeleLevelData K) (R : Chapter14RaySubgroupFamily D)
    (m : Chapter14Modulus K) : Finite (chapter14RayClassGroup D R m) := by
  infer_instance

theorem chapter14_ray_class_group_is_the_canonical_idele_quotient
    {K : Type*} [Field K] [NumberField K]
    (D : Chapter14IdeleLevelData K) (R : Chapter14RaySubgroupFamily D)
    (m : Chapter14Modulus K) :
    Nonempty (chapter14RayClassGroup D R m ≃*
      chapter14IdeleLevelQuotient D (chapter14RayFiniteLevel D R m)) :=
  ⟨chapter14IdeleClassLevelToIdeleLevelEquiv D (chapter14RayFiniteLevel D R m)⟩

theorem chapter14_ray_subgroups_are_cofinal {K : Type*} [Field K] [NumberField K]
    (D : Chapter14IdeleLevelData K) (R : Chapter14RaySubgroupFamily D)
    (U : Chapter14FiniteLevel D) :
    ∃ m : Chapter14Modulus K, R.raySubgroup m ≤ U.subgroup := by
  exact R.ray_subgroup_cofinal U

/-!
Every continuous finite quotient factors through a sufficiently small ray quotient.  This is the
precise finite-quotient form of the neighborhood statement in the source.
-/

theorem chapter14_continuous_finite_quotient_factors_through_ray {K H : Type*}
    [Field K] [NumberField K] [Group H] [Finite H] [TopologicalSpace H]
    [DiscreteTopology H] (D : Chapter14IdeleLevelData K)
    (R : Chapter14RaySubgroupFamily D) (f : chapter14IdeleClassGroup K →* H)
    (hf : Continuous f) :
    ∃ m : Chapter14Modulus K,
      ∃ g : chapter14RayClassGroup D R m →* H,
        f = g.comp (chapter14RayClassQuotientMap D R m) := by
  sorry

theorem chapter14_modulus_has_only_real_sign_part {K : Type*} [Field K] [NumberField K]
    (m : Chapter14Modulus K) :
    m.realPart ⊆ {w | NumberField.InfinitePlace.IsReal w} :=
  m.realPart_isReal

theorem chapter14_modulus_has_no_complex_exponent {K : Type*} [Field K] [NumberField K]
    (m : Chapter14Modulus K) :
    chapter14ModulusComplexPart m = ∅ :=
  rfl

end LastLib.Book04AdelesAndIdeles.Chapter14
