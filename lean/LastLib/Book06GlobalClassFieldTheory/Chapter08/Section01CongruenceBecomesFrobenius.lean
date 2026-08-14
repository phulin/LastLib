import LastLib.Book06GlobalClassFieldTheory.Chapter08.Dependencies

namespace LastLib.Book06GlobalClassFieldTheory.Chapter08

noncomputable section

open NumberField

universe u

/-! ## 8.1. Congruence becomes Frobenius -/

theorem chapter08_conductor_divides_iff_modulus_divides
    {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (E : Chapter08AbelianExtensionData K L)
    (m : Chapter08Modulus K) :
    chapter08ConductorDivides E m ↔
      chapter08ModulusDivides E.conductor m := Iff.rfl

/-- The ideal-group Artin map is the restriction of global reciprocity. -/
theorem chapter08_ideal_group_artin_surjective
    {K L I C : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] [CommGroup I] [CommGroup C]
    (R : Chapter08RayClassPresentation K I C)
    (E : Chapter08AbelianExtensionData K L)
    (A : Chapter08GlobalArtinData K L I C R E)
    (hcond : chapter08ConductorDivides E R.modulus) :
    Function.Surjective (chapter08ArtinMap R E A hcond) := by
  exact chapter08_artin_map_surjective R E A hcond

theorem chapter08_prime_away_from_modulus_is_in_artin_domain
    {K L I C : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] [CommGroup I] [CommGroup C]
    (R : Chapter08RayClassPresentation K I C)
    (E : Chapter08AbelianExtensionData K L)
    (A : Chapter08GlobalArtinData K L I C R E)
    {p : Ideal (𝓞 K)}
    (hp : chapter08PrimeAwayFromModulus R.modulus p) :
    p ∈ A.primeAway := by
  exact A.primeAway_spec.mpr hp

theorem chapter08_idele_representative_has_divisor_and_unit_tail
    {K L I C : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] [CommGroup I] [CommGroup C]
    (R : Chapter08RayClassPresentation K I C)
    (E : Chapter08AbelianExtensionData K L)
    (A : Chapter08GlobalArtinData K L I C R E)
    {p : Ideal (𝓞 K)} (hp : p ∈ A.primeAway) :
    A.ideleFiniteValuation (A.ideleOfIdeal hp) = p ∧
      A.ideleTailIsOne (A.ideleOfIdeal hp) := by
  exact ⟨A.ideleOfIdeal_finiteValuation hp, A.ideleOfIdeal_tail_is_one hp⟩

/-- At a prime away from the modulus, the ideal-group map is arithmetic Frobenius. -/
theorem chapter08_ideal_group_artin_prime_eq_arithmetic_frobenius
    {K L I C : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] [CommGroup I] [CommGroup C]
    (R : Chapter08RayClassPresentation K I C)
    (E : Chapter08AbelianExtensionData K L)
    (A : Chapter08GlobalArtinData K L I C R E)
    (hcond : chapter08ConductorDivides E R.modulus)
    {p : Ideal (𝓞 K)} (hp : p ∈ A.primeAway) :
    chapter08ArtinMap R E A hcond (R.idealClass p) = A.frobenius hp := by
  exact chapter08_artin_map_eq_arithmetic_frobenius R E A hcond hp

theorem chapter08_ideal_group_artin_prime_eq_arithmetic_frobenius_of_prime_away
    {K L I C : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] [CommGroup I] [CommGroup C]
    (R : Chapter08RayClassPresentation K I C)
    (E : Chapter08AbelianExtensionData K L)
    (A : Chapter08GlobalArtinData K L I C R E)
    (hcond : chapter08ConductorDivides E R.modulus)
    {p : Ideal (𝓞 K)}
    (hp : chapter08PrimeAwayFromModulus R.modulus p) :
    chapter08ArtinMap R E A hcond (R.idealClass p) =
      A.frobenius (chapter08_prime_away_from_modulus_is_in_artin_domain R E A hp) := by
  exact chapter08_ideal_group_artin_prime_eq_arithmetic_frobenius R E A hcond
    (chapter08_prime_away_from_modulus_is_in_artin_domain R E A hp)

/-- The principal ray subgroup is killed by the Artin map. -/
theorem chapter08_principal_ray_subgroup_in_artin_kernel
    {K L I C : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] [CommGroup I] [CommGroup C]
    (R : Chapter08RayClassPresentation K I C)
    (E : Chapter08AbelianExtensionData K L)
    (A : Chapter08GlobalArtinData K L I C R E)
    (hcond : chapter08ConductorDivides E R.modulus) :
    R.principalSubgroup ≤ (chapter08ArtinMap R E A hcond).ker := by
  exact chapter08_artin_map_kernel_contains_principal R E A hcond

/-- The Artin map factors through the ray class group. -/
theorem chapter08_artin_factors_through_ray_class_group
    {K L I C : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] [CommGroup I] [CommGroup C]
    (R : Chapter08RayClassPresentation K I C)
    (E : Chapter08AbelianExtensionData K L)
    (A : Chapter08GlobalArtinData K L I C R E)
    (hcond : chapter08ConductorDivides E R.modulus) :
    ∃ φ : chapter08RayClassGroup R →* Gal(L / K),
      φ.comp (chapter08RayClassQuotientMap R) =
        chapter08ArtinMap R E A hcond := by
  refine ⟨chapter08ArtinFactor R E A hcond, ?_⟩
  exact chapter08_artin_factor_comp_quotientMap R E A hcond

/-- In the full ray class field, the factor is the ray-class reciprocity isomorphism. -/
noncomputable def chapter08_full_ray_class_factor_isomorphism
    {K : Type u} [Field K] [NumberField K]
    {I C : Type u} [CommGroup I] [CommGroup C]
    (R : Chapter08RayClassPresentation K I C)
    (F : Chapter08RayClassFieldData K R) :
    letI : Field F.carrier := F.carrierField
    letI : Algebra K F.carrier := F.carrierAlgebra
    letI : NumberField F.carrier := F.carrierNumberField
    letI : FiniteDimensional K F.carrier := F.carrierFinite
    letI : IsAbelianGalois K F.carrier := F.carrierAbelianGalois
    chapter08RayClassGroup R ≃* Gal(F.carrier / K) := by
  exact F.artinEquiv

/-- A prime away from the modulus splits completely in the full ray field exactly when
its ray class is trivial. -/
theorem chapter08_full_ray_field_splitting_iff_ray_class_trivial
    {K : Type u} [Field K] [NumberField K]
    {I C : Type u} [CommGroup I] [CommGroup C]
    (R : Chapter08RayClassPresentation K I C)
    (F : Chapter08RayClassFieldData K R)
    {p : Ideal (𝓞 K)} [p.IsPrime]
    (hp : chapter08PrimeAwayFromModulus R.modulus p) :
    letI : Field F.carrier := F.carrierField
    letI : Algebra K F.carrier := F.carrierAlgebra
    letI : NumberField F.carrier := F.carrierNumberField
    letI : FiniteDimensional K F.carrier := F.carrierFinite
    letI : IsAbelianGalois K F.carrier := F.carrierAbelianGalois
    letI : Algebra (𝓞 K) (𝓞 F.carrier) := inferInstance
    chapter08SplitsCompletely K F.carrier p ↔
      chapter08RayClassOfIdeal R p = 1 := by
  sorry

/-- The ray-class triviality criterion is the ideal-theoretic congruence-and-sign condition. -/
theorem chapter08_ray_class_trivial_iff_principal_congruence
    {K : Type u} [Field K] [NumberField K]
    {I C : Type u} [CommGroup I] [CommGroup C]
    (R : Chapter08RayClassPresentation K I C)
    {p : Ideal (𝓞 K)}
    (hp : chapter08PrimeAwayFromModulus R.modulus p) :
    chapter08RayClassOfIdeal R p = 1 ↔
      ∃ a : 𝓞 K, chapter08PrincipalRayCondition R.modulus p a := by
  sorry

/-- For a subfield corresponding to a ray subgroup, complete splitting is subgroup membership. -/
theorem chapter08_subfield_splitting_iff_ray_class_mem
    {K L I C : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] [Algebra (𝓞 K) (𝓞 L)] [CommGroup I] [CommGroup C]
    (R : Chapter08RayClassPresentation K I C)
    (S : Chapter08RaySubfieldData K L I C R)
    {p : Ideal (𝓞 K)} [p.IsPrime]
    (hp : chapter08PrimeAwayFromModulus R.modulus p) :
    chapter08SplitsCompletely K L p ↔
      chapter08RayClassOfIdeal R p ∈ S.correspondingSubgroup := by
  sorry

end
end LastLib.Book06GlobalClassFieldTheory.Chapter08
