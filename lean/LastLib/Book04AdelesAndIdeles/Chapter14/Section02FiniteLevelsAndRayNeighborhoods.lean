import LastLib.Book04AdelesAndIdeles.Chapter14.Dependencies

/-!
# 14.2. Finite levels and ray neighborhoods
-/

noncomputable section

namespace LastLib.Book04AdelesAndIdeles.Chapter14

theorem chapter14_ray_level_is_open_and_finite {K : Type*} [Field K] [NumberField K]
    (m : Chapter14Modulus K) :
    IsOpen ((chapter14RayFiniteLevel m).subgroup :
      Set (chapter14IdeleGroup K)) ∧
      (chapter14PrincipalIdeleSubgroup K ⊔
        (chapter14RayFiniteLevel m).subgroup).FiniteIndex := by
  exact ⟨(chapter14RayFiniteLevel m).isOpen',
    (chapter14RayFiniteLevel m).finiteIndex'⟩

theorem chapter14_ray_class_group_is_finite {K : Type*} [Field K] [NumberField K]
    (m : Chapter14Modulus K) : Finite (chapter14RayClassGroup m) := by
  exact Chapter11.chapter11_ray_class_group_is_finite m

theorem chapter14_ray_class_group_is_the_canonical_idele_quotient
    {K : Type*} [Field K] [NumberField K]
    (m : Chapter14Modulus K) :
    chapter14RayClassGroup m =
      (chapter14IdeleGroup K ⧸
        (chapter14PrincipalIdeleSubgroup K ⊔ Chapter11.chapter11RayUnitSubgroup m)) := by
  rfl

theorem chapter14_ray_subgroups_are_cofinal {K : Type*} [Field K] [NumberField K]
    (D : Chapter14LocalComponentData K) (U : Chapter14FiniteLevel K)
    (hpositive : chapter14ContainsPositiveMagnitudeDirections D U)
    (htail : chapter14ContainsIntegralUnitTail D U) :
    ∃ m : Chapter14Modulus K, (chapter14RayFiniteLevel m).subgroup ≤ U.subgroup := by
  sorry

/-!
Every continuous finite quotient factors through a sufficiently small ray quotient.  This is the
precise finite-quotient form of the neighborhood statement in the source.
-/

theorem chapter14_continuous_finite_quotient_factors_through_ray {K H : Type*}
    [Field K] [NumberField K] [Group H] [Finite H] [TopologicalSpace H]
    [DiscreteTopology H] (f : chapter14IdeleClassGroup K →* H)
    (hf : Continuous f) :
    ∃ m : Chapter14Modulus K,
      ∃ g : chapter14RayClassGroup m →* H,
        f = g.comp (chapter14RayClassQuotientMap m) := by
  sorry

theorem chapter14_modulus_has_only_real_sign_part {K : Type*} [Field K] [NumberField K]
    (m : Chapter14Modulus K) :
    (m.infinitePart : Set (NumberField.InfinitePlace K)) ⊆
      {w | NumberField.InfinitePlace.IsReal w} := by
  exact m.infinitePart_isReal

theorem chapter14_modulus_has_no_complex_exponent {K : Type*} [Field K] [NumberField K]
    (m : Chapter14Modulus K) :
    chapter14ModulusComplexPart m = ∅ :=
  rfl

/-! A finite-order continuous local character at a complex place has finite
image, hence factors through a finite discrete quotient; connectedness of
`ℂˣ` forces that quotient map to be trivial. -/
theorem chapter14_complex_finite_continuous_quotient_is_trivial
    {H : Type*} [CommGroup H] [Finite H] [TopologicalSpace H] [DiscreteTopology H]
    (f : ℂˣ →* H) (hf : Continuous f) :
    ∀ z, f z = 1 := by
  sorry

end LastLib.Book04AdelesAndIdeles.Chapter14
