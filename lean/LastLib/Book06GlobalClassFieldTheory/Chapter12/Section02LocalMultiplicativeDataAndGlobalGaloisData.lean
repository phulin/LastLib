import LastLib.Book06GlobalClassFieldTheory.Chapter12.Dependencies

namespace LastLib.Book06GlobalClassFieldTheory.Chapter12

noncomputable section

/-! ## 12.2. Local multiplicative data and global Galois data -/

theorem chapter12_local_units_map_to_inertia
    {K_v G : Type*} [Field K_v] [CommGroup G] [Finite G]
    (D : Chapter12FinitePlaceLocalData K_v G) :
    Subgroup.map D.localArtin D.integralUnits = D.inertia := by
  exact D.inertia_range

theorem chapter12_local_principal_units_map_to_upper_ramification
    {K_v G : Type*} [Field K_v] [CommGroup G] [Finite G]
    (D : Chapter12FinitePlaceLocalData K_v G) (n : ℕ) :
    Subgroup.map D.localArtin (D.unitFiltration n) =
      D.upperRamification n := by
  exact D.upper_ramification_range n

theorem chapter12_local_uniformizer_maps_to_frobenius_modulo_inertia
    {K_v G : Type*} [Field K_v] [CommGroup G] [Finite G]
    (D : Chapter12FinitePlaceLocalData K_v G) :
    QuotientGroup.mk' D.inertia (D.localArtin D.uniformizer) =
      D.arithmeticFrobenius := by
  exact D.uniformizer_frobenius

theorem chapter12_local_norm_group_is_local_artin_kernel
    {K_v L_w G : Type*} [Field K_v] [CommGroup L_w]
    [CommGroup G] [Finite G]
    (D : Chapter12LocalNormKernelData K_v L_w G) :
    D.localNorm.range = D.localArtin.ker := by
  exact D.local_norm_kernel

theorem chapter12_unramified_units_are_trivial
    {K_v G : Type*} [Field K_v] [CommGroup G] [Finite G]
    (D : Chapter12UnramifiedLocalData K_v G) {u : K_vˣ}
    (hu : u ∈ D.integralUnits) :
    D.localArtin u = 1 := by
  exact D.units_trivial u hu

theorem chapter12_unramified_uniformizer_is_canonical_arithmetic_frobenius
    {K_v G : Type*} [Field K_v] [CommGroup G] [Finite G]
    (D : Chapter12UnramifiedLocalData K_v G) :
    D.localArtin D.uniformizer = D.arithmeticFrobenius := by
  exact D.uniformizer_frobenius

/- In the ramified case the lift, rather than its residue class, depends on a
uniformizer.  The quotient statement is the normalization-independent form.
-/
theorem chapter12_ramified_uniformizer_change_is_inertia
    {K_v G : Type*} [Field K_v] [CommGroup G] [Finite G]
    (D : Chapter12FinitePlaceLocalData K_v G) (u : K_vˣ)
    (hu : u ∈ D.integralUnits) :
    QuotientGroup.mk' D.inertia
        (D.localArtin (u * D.uniformizer)) =
      QuotientGroup.mk' D.inertia (D.localArtin D.uniformizer) := by
  sorry

theorem chapter12_real_positive_component_is_trivial
    {G : Type*} [CommGroup G] [Finite G]
    (D : Chapter12RealPlaceLocalData G) :
    D.positive_subgroup ≤ D.localArtin.ker := by
  exact D.positive_killed

theorem chapter12_real_sign_is_complex_conjugation
    {G : Type*} [CommGroup G] [Finite G]
    (D : Chapter12RealPlaceLocalData G) :
    D.localArtin (-1 : ℝˣ) = D.complexConjugation := by
  exact D.minus_one_is_complex_conjugation

theorem chapter12_real_place_complexifies_exactly_when_sign_is_nontrivial
    {G : Type*} [CommGroup G] [Finite G]
    (D : Chapter12RealPlaceLocalData G) :
    D.placeComplexifies ↔ D.localArtin (-1 : ℝˣ) ≠ 1 := by
  exact D.complexifies_iff_nontrivial_sign

theorem chapter12_complex_place_local_reciprocity_is_trivial
    {G : Type*} [Group G]
    (D : Chapter12ComplexPlaceLocalData G) :
    D.localArtin = 1 := by
  exact D.local_trivial

/- The canonical arithmetic/geometric conversion is inversion of the isolated
Frobenius element; all subgroup and kernel statements are unchanged. -/
theorem chapter12_geometric_frobenius_is_inverse
    {G : Type*} [Group G] (σ : G) :
    chapter12GeometricFrobenius σ = σ⁻¹ :=
  rfl

end

end LastLib.Book06GlobalClassFieldTheory.Chapter12
