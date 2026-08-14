import LastLib.Book04AdelesAndIdeles.Chapter11.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter11

open NumberField
open scoped nonZeroDivisors

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-! ## 11.3 The ideal-theoretic description -/

theorem chapter11_ideal_prime_to_modulus_mem_iff (m : RayModulus K)
    (I : Chapter11FractionalIdealUnitGroup K) :
    I ∈ chapter11IdealPrimeToModulus m ↔
      ∀ v, m.finiteExponent v ≠ 0 →
        FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
  rfl

theorem chapter11_ray_principal_ideal_mem_iff (m : RayModulus K)
    (I : Chapter11IdealGroup m) :
    I ∈ chapter11RayPrincipalIdealSubgroup m ↔
      ∃ a : Kˣ, chapter11RayGenerator m a ∧
        ((I : Chapter11FractionalIdealUnitGroup K) : FractionalIdeal (𝓞 K)⁰ K) =
          (toPrincipalIdeal (𝓞 K) K a : FractionalIdeal (𝓞 K)⁰ K) := by
  rfl

theorem chapter11_ray_generator_is_local_congruence (m : RayModulus K)
    (a : Kˣ) :
    chapter11RayGenerator m a ↔
      ((∀ v, m.finiteExponent v ≠ 0 →
          chapter11FiniteGlobalComponent K v a ∈
            chapter11FiniteLocalUnitGroup K v (m.finiteExponent v)) ∧
        (∀ v (hv : v ∈ m.infinitePart),
          chapter11RealSignHom
              (chapter11RealGlobalComponent K v (m.infinitePart_isReal v hv) a) = 1)) := by
  rfl

theorem chapter11_ray_generator_principal_ideal_is_prime_to_modulus
    (m : RayModulus K) {a : Kˣ} (ha : chapter11RayGenerator m a) :
    toPrincipalIdeal (𝓞 K) K a ∈ chapter11IdealPrimeToModulus m := by
  intro v hv
  have hcount :=
    (chapter11CanonicalIdeleIdealMap K).count_eq_zero_of_local_unit
      (chapter11PrincipalIdeleHom (K := K) a) v (m.finiteExponent v) (by
        change chapter11FiniteGlobalComponent K v a ∈
          chapter11FiniteLocalUnitGroup K v (m.finiteExponent v)
        exact ha.1 v hv)
  rw [(chapter11CanonicalIdeleIdealMap K).map_principal a] at hcount
  exact hcount

theorem chapter11_exists_ray_normalizer (m : RayModulus K)
    (x : Chapter11IdeleGroup K) :
    ∃ a : Kˣ, Chapter11RayNormalizer m x a := by
  sorry

theorem chapter11_normalized_idele_has_prime_to_modulus_ideal
    (m : RayModulus K)
    (x : Chapter11IdeleGroup K) :
    ∃ a : Kˣ,
      Chapter11RayNormalizer m x a ∧
        (chapter11CanonicalIdeleIdealMap K).toIdeal
            (chapter11PrincipalIdeleHom (K := K) a * x) ∈
          chapter11IdealPrimeToModulus m := by
  obtain ⟨a, ha⟩ := chapter11_exists_ray_normalizer m x
  refine ⟨a, ha, ?_⟩
  intro v hv
  exact (chapter11CanonicalIdeleIdealMap K).count_eq_zero_of_local_unit
    (chapter11PrincipalIdeleHom (K := K) a * x) v (m.finiteExponent v) (ha.1 v hv)

theorem chapter11_ray_class_quotient_map_is_unchanged_by_principal_and_ray_units
    (m : RayModulus K) (x : Chapter11IdeleGroup K) (a : Kˣ)
    (u : chapter11RayUnitSubgroup m) :
    chapter11RayClassProjection m
        (chapter11PrincipalIdeleHom (K := K) a * x * u) =
      chapter11RayClassProjection m x := by
  let S := chapter11PrincipalIdeleSubgroup (K := K) ⊔ chapter11RayUnitSubgroup m
  change QuotientGroup.mk' S
      (chapter11PrincipalIdeleHom (K := K) a * x * (u : Chapter11IdeleGroup K)) =
    QuotientGroup.mk' S x
  apply (QuotientGroup.mk'_eq_mk' S).2
  refine ⟨(u : Chapter11IdeleGroup K)⁻¹ *
      (chapter11PrincipalIdeleHom (K := K) a)⁻¹, ?_, ?_⟩
  · exact S.mul_mem
      (S.inv_mem (Subgroup.mem_sup_right u.property))
      (S.inv_mem (Subgroup.mem_sup_left ⟨a, rfl⟩))
  · simp [mul_assoc, mul_comm, mul_left_comm]

theorem chapter11_idele_ray_quotient_equiv_ideal_ray_quotient
    (m : RayModulus K) :
    Nonempty (chapter11RayClassGroup m ≃* chapter11IdealRayClassGroup m) := by
  sorry

/- The preliminary principal adjustment above is essential: the ideal map
attached to an arbitrary idele is not, by itself, an API assertion that its
ideal is prime to the finite part of the modulus. -/
theorem chapter11_prime_to_modulus_ideal_requires_normalization
    (m : RayModulus K)
    (x : Chapter11IdeleGroup K) :
    ∃ a : Kˣ,
      Chapter11RayNormalizer m x a ∧
        (chapter11CanonicalIdeleIdealMap K).toIdeal
            (chapter11PrincipalIdeleHom (K := K) a * x) ∈
          chapter11IdealPrimeToModulus m := by
  exact chapter11_normalized_idele_has_prime_to_modulus_ideal m x

end
