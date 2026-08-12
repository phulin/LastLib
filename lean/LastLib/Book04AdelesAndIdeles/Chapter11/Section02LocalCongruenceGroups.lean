import LastLib.Book04AdelesAndIdeles.Chapter11.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter11

open NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-! ## 11.2 Local congruence groups -/

theorem chapter11_local_unit_level_zero_is_full_unit_group
    {A : Type*} [CommRing A] [IsLocalRing A] :
    chapter11LocalUnitFiltration (A := A) 0 = ⊤ := by
  exact chapter11LocalUnitFiltration_zero

theorem chapter11_local_unit_positive_level_is_one_plus_maximal_power
    {A : Type*} [CommRing A] [IsLocalRing A] {n : ℕ} (hn : n ≠ 0) (u : Aˣ) :
    u ∈ chapter11LocalUnitFiltration (A := A) n ↔
      (u : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ n := by
  rw [chapter11LocalUnitFiltration_mem_iff]
  simp [hn]

theorem chapter11_local_unit_positive_level_is_one_plus_an_element_of_the_power
    {A : Type*} [CommRing A] [IsLocalRing A] {n : ℕ} (hn : n ≠ 0) (u : Aˣ) :
    u ∈ chapter11LocalUnitFiltration (A := A) n ↔
      ∃ z : A, z ∈ (IsLocalRing.maximalIdeal A) ^ n ∧ (u : A) = 1 + z := by
  sorry

theorem chapter11_finite_local_level_zero_is_integral_unit_condition
    (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    chapter11FiniteLocalUnitGroup K v 0 =
      (v.adicCompletionIntegers K).unitGroup := by
  exact chapter11FiniteLocalUnitGroup_zero K v

theorem chapter11_finite_local_level_one_is_principal_unit_condition
    (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    chapter11FiniteLocalUnitGroup K v 1 =
      (v.adicCompletionIntegers K).principalUnitGroup := by
  exact chapter11FiniteLocalUnitGroup_one K v

theorem chapter11_ray_unit_subgroup_mem_iff (m : RayModulus K)
    (x : Chapter11IdeleGroup K) :
    x ∈ chapter11RayUnitSubgroup m ↔
      ((∀ v, chapter11IdeleFiniteComponent K v x ∈
          chapter11FiniteLocalUnitGroup K v (m.finiteExponent v)) ∧
        (∀ v (hv : v ∈ m.infinitePart),
          chapter11RealSignComponent K v (m.infinitePart_isReal v hv) x = 1)) := by
  rfl

theorem chapter11_ray_unit_condition_at_selected_real_place
    (m : RayModulus K) {v : NumberField.InfinitePlace K}
    (hv : v ∈ m.infinitePart) {x : Chapter11IdeleGroup K} :
    x ∈ chapter11RayUnitSubgroup m →
      chapter11RealSignComponent K v (m.infinitePart_isReal v hv) x = 1 := by
  intro hx
  exact hx.2 v hv

theorem chapter11_ray_unit_subgroup_is_open (m : RayModulus K) :
    IsOpen (chapter11RayUnitSubgroup m : Set (Chapter11IdeleGroup K)) := by
  sorry

theorem chapter11_ray_class_group_is_the_idelic_quotient (m : RayModulus K) :
    chapter11RayClassGroup m =
      (Chapter11IdeleGroup K ⧸
        (chapter11PrincipalIdeleSubgroup (K := K) ⊔ chapter11RayUnitSubgroup m)) := by
  rfl

end
