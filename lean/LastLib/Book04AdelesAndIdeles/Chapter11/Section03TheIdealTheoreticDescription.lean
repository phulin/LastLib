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
          chapter11RealGlobalComponent K v (m.infinitePart_isReal v hv) a = 1)) := by
  rfl

theorem chapter11_ray_generator_principal_ideal_is_prime_to_modulus
    (m : RayModulus K) {a : Kˣ} (ha : chapter11RayGenerator m a) :
    toPrincipalIdeal (𝓞 K) K a ∈ chapter11IdealPrimeToModulus m := by
  sorry

theorem chapter11_exists_ray_normalizer (m : RayModulus K)
    (x : Chapter11IdeleGroup K) :
    ∃ a : Kˣ, Chapter11RayNormalizer m x a := by
  sorry

theorem chapter11_normalized_idele_has_prime_to_modulus_ideal
    (m : RayModulus K) (h : Chapter11IdeleIdealMap K)
    (x : Chapter11IdeleGroup K) :
    ∃ a : Kˣ,
      Chapter11RayNormalizer m x a ∧
        h.toIdeal (chapter11PrincipalIdeleHom (K := K) a * x) ∈
          chapter11IdealPrimeToModulus m := by
  sorry

theorem chapter11_ray_class_quotient_map_is_unchanged_by_principal_and_ray_units
    (m : RayModulus K) (x : Chapter11IdeleGroup K) (a : Kˣ)
    (u : chapter11RayUnitSubgroup m) :
    chapter11RayClassProjection m
        (chapter11PrincipalIdeleHom (K := K) a * x * u) =
      chapter11RayClassProjection m x := by
  sorry

theorem chapter11_idele_ray_quotient_equiv_ideal_ray_quotient
    (m : RayModulus K) (h : Chapter11IdeleIdealMap K) :
    Nonempty (chapter11RayClassGroup m ≃* chapter11IdealRayClassGroup m) := by
  sorry

/- The preliminary principal adjustment above is essential: the ideal map
attached to an arbitrary idele is not, by itself, an API assertion that its
ideal is prime to the finite part of the modulus. -/
theorem chapter11_prime_to_modulus_ideal_requires_normalization
    (m : RayModulus K) (h : Chapter11IdeleIdealMap K)
    (x : Chapter11IdeleGroup K) :
    ∃ a : Kˣ,
      Chapter11RayNormalizer m x a ∧
        h.toIdeal (chapter11PrincipalIdeleHom (K := K) a * x) ∈
          chapter11IdealPrimeToModulus m := by
  exact chapter11_normalized_idele_has_prime_to_modulus_ideal m h x

end
