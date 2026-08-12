import LastLib.Book04AdelesAndIdeles.Chapter11.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter11

open NumberField

noncomputable section

open scoped Classical

variable {K : Type*} [Field K] [NumberField K]

/-! ## 11.1 Why ideals need local unit data -/

theorem chapter11_modulus_finite_part_is_finitely_supported (m : RayModulus K) :
    (m.finiteExponent.support : Set
      (IsDedekindDomain.HeightOneSpectrum (𝓞 K))).Finite := by
  sorry

theorem chapter11_modulus_selected_archimedean_places_are_real (m : RayModulus K) :
    ∀ v ∈ m.infinitePart, NumberField.InfinitePlace.IsReal v := by
  exact m.infinitePart_isReal

theorem chapter11_modulus_has_no_complex_sign_component (m : RayModulus K) :
    ∀ v, NumberField.InfinitePlace.IsComplex v → v ∉ m.infinitePart := by
  sorry

theorem chapter11_modulus_is_finite_part_times_real_part (m : RayModulus K) :
    m.finiteIdeal =
      Finset.prod m.finiteExponent.support (fun v => v.asIdeal ^ m.finiteExponent v) := by
  rfl

abbrev Chapter11NarrowClassGroup (K : Type*) [Field K] [NumberField K] :=
  chapter11IdealRayClassGroup (RayModulus.narrow (K := K))

theorem chapter11_trivial_modulus_ray_class_group_equiv_ordinary_class_group
    (K : Type*) [Field K] [NumberField K] :
    Nonempty
      (chapter11RayClassGroup (RayModulus.trivial (K := K)) ≃*
        Chapter11OrdinaryClassGroup K) := by
  sorry

theorem chapter11_narrow_modulus_ray_class_group_equiv_narrow_class_group
    (K : Type*) [Field K] [NumberField K] :
    Nonempty
      (chapter11RayClassGroup (RayModulus.narrow (K := K)) ≃*
        Chapter11NarrowClassGroup K) := by
  sorry

theorem chapter11_trivial_modulus_has_no_finite_or_infinite_condition
    (K : Type*) [Field K] [NumberField K] :
    (RayModulus.trivial (K := K)).finiteExponent = 0 ∧
      (RayModulus.trivial (K := K)).infinitePart = ∅ := by
  simp [RayModulus.trivial]

theorem chapter11_narrow_modulus_has_all_real_places
    (K : Type*) [Field K] [NumberField K] :
    (RayModulus.narrow (K := K)).finiteExponent = 0 ∧
      (RayModulus.narrow (K := K)).infinitePart =
        Finset.univ.filter NumberField.InfinitePlace.IsReal := by
  simp [RayModulus.narrow]

end
