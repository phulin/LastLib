import LastLib.Book04AdelesAndIdeles.Chapter11.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter11

open NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-! ## 11.6 Conductors at the elementary level -/

structure Chapter11FiniteOrderIdeleClassCharacter
    (K : Type*) [Field K] [NumberField K] where
  toMonoidHom : Chapter11IdeleClassGroup K →* ℂˣ
  continuous_toMonoidHom : Continuous toMonoidHom
  finite_order : ∃ n : ℕ, 0 < n ∧ ∀ x, toMonoidHom x ^ n = 1

def chapter11CharacterFactorsThrough (χ : Chapter11FiniteOrderIdeleClassCharacter K)
    (m : RayModulus K) : Prop :=
  ∃ ψ : chapter11RayClassGroup m →* ℂˣ,
    ∀ x : Chapter11IdeleClassGroup K,
      χ.toMonoidHom x =
        ψ (chapter11IdeleClassToRayClass m x)

def chapter11FiniteLocalCharacterTrivialAtLevel
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (ψ : (v.adicCompletion K)ˣ →* ℂˣ)
    (n : ℕ) : Prop :=
  ∀ u, u ∈ chapter11FiniteLocalUnitGroup K v n → ψ u = 1

theorem chapter11_finite_local_character_has_open_kernel
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (ψ : (v.adicCompletion K)ˣ →* ℂˣ)
    (hcontinuous : Continuous ψ)
    (hfinite : ∃ n : ℕ, 0 < n ∧ ∀ x, ψ x ^ n = 1) :
    ∃ n : ℕ, chapter11FiniteLocalCharacterTrivialAtLevel v ψ n := by
  sorry

theorem chapter11_finite_local_character_levels_are_monotone
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (ψ : (v.adicCompletion K)ˣ →* ℂˣ) {m n : ℕ} (hmn : m ≤ n)
    (hn : chapter11FiniteLocalCharacterTrivialAtLevel v ψ m) :
    chapter11FiniteLocalCharacterTrivialAtLevel v ψ n := by
  sorry

theorem chapter11_exists_least_conductor
    (χ : Chapter11FiniteOrderIdeleClassCharacter K) :
    ∃ m : RayModulus K,
      chapter11CharacterFactorsThrough χ m ∧
        ∀ n : RayModulus K, chapter11CharacterFactorsThrough χ n →
          RayModulus.LE m n := by
  sorry

noncomputable def chapter11Conductor
    (χ : Chapter11FiniteOrderIdeleClassCharacter K) : RayModulus K :=
  Classical.choose (chapter11_exists_least_conductor χ)

theorem chapter11_conductor_factors_character
    (χ : Chapter11FiniteOrderIdeleClassCharacter K) :
    chapter11CharacterFactorsThrough χ (chapter11Conductor χ) := by
  exact (Classical.choose_spec (chapter11_exists_least_conductor χ)).1

theorem chapter11_conductor_is_least
    (χ : Chapter11FiniteOrderIdeleClassCharacter K) (m : RayModulus K)
    (hm : chapter11CharacterFactorsThrough χ m) :
    RayModulus.LE (chapter11Conductor χ) m := by
  exact (Classical.choose_spec (chapter11_exists_least_conductor χ)).2 m hm

theorem chapter11_real_finite_order_character_factors_through_sign
    (ψ : ℝˣ →* ℂˣ) (hcontinuous : Continuous ψ)
    (hfinite : ∃ n : ℕ, 0 < n ∧ ∀ x, ψ x ^ n = 1) :
    ∃ ε : SignTypeˣ →* ℂˣ, ∀ x, ψ x = ε (chapter11RealSignHom x) := by
  sorry

theorem chapter11_complex_finite_order_character_is_trivial
    (ψ : ℂˣ →* ℂˣ) (hcontinuous : Continuous ψ)
    (hfinite : ∃ n : ℕ, 0 < n ∧ ∀ x, ψ x ^ n = 1) :
    ψ = 1 := by
  sorry

def chapter11RealSignClassEmbedding (K : Type*) [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K)
    (hv : NumberField.InfinitePlace.IsReal v) :
    SignTypeˣ →* Chapter11IdeleClassGroup K := by
  sorry

def chapter11CharacterDetectsRealSign
    (χ : Chapter11FiniteOrderIdeleClassCharacter K)
    (v : NumberField.InfinitePlace K)
    (hv : NumberField.InfinitePlace.IsReal v) : Prop :=
  ∃ s : SignTypeˣ, s ≠ 1 ∧
    χ.toMonoidHom (chapter11RealSignClassEmbedding K v hv s) ≠ 1

theorem chapter11_conductor_real_part_iff_sign_is_detected
    (χ : Chapter11FiniteOrderIdeleClassCharacter K)
    {v : NumberField.InfinitePlace K}
    (hv : NumberField.InfinitePlace.IsReal v) :
    v ∈ (chapter11Conductor χ).infinitePart ↔
      chapter11CharacterDetectsRealSign χ v hv := by
  sorry

theorem chapter11_complex_places_do_not_contribute_to_the_conductor
    (χ : Chapter11FiniteOrderIdeleClassCharacter K)
    {v : NumberField.InfinitePlace K}
    (hv : NumberField.InfinitePlace.IsComplex v) :
    v ∉ (chapter11Conductor χ).infinitePart := by
  sorry

theorem chapter11_character_has_almost_everywhere_level_zero
    (χ : Chapter11FiniteOrderIdeleClassCharacter K) :
    ((chapter11Conductor χ).finiteExponent.support : Set
      (IsDedekindDomain.HeightOneSpectrum (𝓞 K))).Finite := by
  exact RayModulus.finiteExponent_support_finite (chapter11Conductor χ)

def chapter11CharacterOfRayClassHom (m : RayModulus K)
    (ψ : chapter11RayClassGroup m →* ℂˣ) :
    Chapter11FiniteOrderIdeleClassCharacter K where
  toMonoidHom := ψ.comp (chapter11IdeleClassToRayClass m)
  continuous_toMonoidHom := by
    sorry
  finite_order := by
    sorry

theorem chapter11_ray_class_character_has_conductor_dividing_modulus
    (m : RayModulus K) (ψ : chapter11RayClassGroup m →* ℂˣ) :
    RayModulus.LE (chapter11Conductor (chapter11CharacterOfRayClassHom m ψ)) m := by
  apply chapter11_conductor_is_least
  refine ⟨ψ, ?_⟩
  intro x
  rfl

/- No reciprocity or Galois-theoretic assertion is used in this elementary
conductor API. -/

end
