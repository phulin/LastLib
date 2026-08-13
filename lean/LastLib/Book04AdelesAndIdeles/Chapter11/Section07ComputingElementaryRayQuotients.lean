import LastLib.Book04AdelesAndIdeles.Chapter11.Section06ConductorsAtTheElementaryLevel

namespace LastLib.Book04AdelesAndIdeles.Chapter11

open NumberField
open scoped nonZeroDivisors

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-! ## 11.7 Computing elementary ray quotients -/

inductive Chapter11RationalArchimedeanPart
  | omitted
  | included
  deriving DecidableEq, Repr

theorem chapter11_exists_rational_modulus (N : ℕ) (hN : 0 < N)
    (ε : Chapter11RationalArchimedeanPart) :
    ∃ m : RayModulus ℚ,
      m.finiteIdeal = Ideal.span ({(N : 𝓞 ℚ)} : Set (𝓞 ℚ)) ∧
        m.infinitePart =
          match ε with
          | .omitted => ∅
          | .included => {Rat.infinitePlace} := by
  sorry

noncomputable def chapter11RationalModulus (N : ℕ) (hN : 0 < N)
    (ε : Chapter11RationalArchimedeanPart) : RayModulus ℚ :=
  Classical.choose (chapter11_exists_rational_modulus N hN ε)

theorem chapter11_rational_modulus_spec (N : ℕ) (hN : 0 < N)
    (ε : Chapter11RationalArchimedeanPart) :
    (chapter11RationalModulus N hN ε).finiteIdeal =
        Ideal.span ({(N : 𝓞 ℚ)} : Set (𝓞 ℚ)) ∧
      (chapter11RationalModulus N hN ε).infinitePart =
        match ε with
        | .omitted => ∅
        | .included => {Rat.infinitePlace} := by
  exact Classical.choose_spec (chapter11_exists_rational_modulus N hN ε)

abbrev chapter11RationalRayClassGroup (N : ℕ) (hN : 0 < N)
    (ε : Chapter11RationalArchimedeanPart) :=
  chapter11RayClassGroup (chapter11RationalModulus N hN ε)

theorem chapter11_rational_fractional_ideal_has_unique_positive_generator
    (N : ℕ) (hN : 0 < N) (I : Chapter11IdealGroup
      (chapter11RationalModulus N hN .included)) :
    ∃! a : ℚ,
      0 < a ∧
        ((I : Chapter11FractionalIdealUnitGroup ℚ) : FractionalIdeal (𝓞 ℚ)⁰ ℚ) =
          FractionalIdeal.spanSingleton (𝓞 ℚ)⁰ a := by
  sorry

theorem chapter11_rational_infinite_ray_class_group_equiv_residue_units
    (N : ℕ) (hN : 0 < N) :
    Nonempty
      (chapter11RationalRayClassGroup N hN .included ≃* (ZMod N)ˣ) := by
  sorry

def chapter11ModFiveRepresentative (i : Fin 4) : (ZMod 5)ˣ :=
  ZMod.unitOfCoprime (i.1 + 1) (by sorry)

theorem chapter11_mod_five_representatives_are_all_residue_units :
    Function.Bijective chapter11ModFiveRepresentative := by
  sorry

def chapter11QuadraticResidueModFive (a : (ZMod 5)ˣ) : Prop :=
  ∃ x : (ZMod 5)ˣ, x * x = a

def chapter11QuadraticCharacterModFive : (ZMod 5)ˣ →* SignTypeˣ := by
  sorry

theorem chapter11_mod_five_quadratic_character_values :
    (∀ a, chapter11QuadraticResidueModFive a →
      chapter11QuadraticCharacterModFive a = 1) ∧
      (∀ a, ¬chapter11QuadraticResidueModFive a →
        chapter11QuadraticCharacterModFive a = (-1 : SignTypeˣ)) := by
  sorry

theorem chapter11_mod_five_quadratic_character_has_finite_conductor :
    ∃ χ : Chapter11FiniteOrderIdeleClassCharacter ℚ,
      chapter11Conductor χ =
        chapter11RationalModulus 5 (Nat.zero_lt_succ 4) .omitted := by
  sorry

def chapter11ResidueSignSubgroup (N : ℕ) : Subgroup (ZMod N)ˣ :=
  Subgroup.closure {(-1 : (ZMod N)ˣ)}

theorem chapter11_rational_omitting_infinity_quotients_by_signs
    (N : ℕ) (hN : 0 < N) :
    Nonempty
      (chapter11RationalRayClassGroup N hN .omitted ≃*
        (ZMod N)ˣ ⧸ chapter11ResidueSignSubgroup N) := by
  sorry

theorem chapter11_general_ray_class_computation_is_controlled_by_finite_data
    (m : RayModulus K) :
    Finite (Chapter11OrdinaryClassGroup K) ∧
      Finite (chapter11RayResidueSignGroup m) ∧
      Function.Surjective (chapter11RayClassToOrdinaryClassHom m) := by
  sorry

theorem chapter11_ray_unit_subgroup_anti_mono_of_le
    {m n : RayModulus K} (h : RayModulus.LE m n) :
    chapter11RayUnitSubgroup n ≤ chapter11RayUnitSubgroup m := by
  sorry

def chapter11RayClassProjectionOfLE
    {m n : RayModulus K} (h : RayModulus.LE m n) :
    chapter11RayClassGroup n →* chapter11RayClassGroup m := by
  refine QuotientGroup.map
    (chapter11PrincipalIdeleSubgroup (K := K) ⊔ chapter11RayUnitSubgroup n)
    (chapter11PrincipalIdeleSubgroup (K := K) ⊔ chapter11RayUnitSubgroup m)
    (MonoidHom.id _) ?_
  simpa only [Subgroup.comap_id] using
    (sup_le_sup le_rfl (chapter11_ray_unit_subgroup_anti_mono_of_le h))

theorem chapter11RayClassProjectionOfLE_surjective
    {m n : RayModulus K} (h : RayModulus.LE m n) :
    Function.Surjective (chapter11RayClassProjectionOfLE h) := by
  sorry

theorem chapter11_exists_ray_class_projection_of_le
    {m n : RayModulus K} (h : RayModulus.LE m n) :
    ∃ f : chapter11RayClassGroup n →* chapter11RayClassGroup m,
      Function.Surjective f := by
  refine ⟨chapter11RayClassProjectionOfLE h, chapter11RayClassProjectionOfLE_surjective h⟩

def chapter11RayModulusSingleFiniteStep
    (m n : RayModulus K)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : Prop :=
  RayModulus.LE m n ∧
    (∀ w, w ≠ v → m.finiteExponent w = n.finiteExponent w) ∧
    n.finiteExponent v = m.finiteExponent v + 1 ∧
    m.infinitePart = n.infinitePart

theorem chapter11_ray_tower_step_kernel_is_locally_controlled
    {m n : RayModulus K}
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hstep : chapter11RayModulusSingleFiniteStep m n v)
    (hm : 0 < m.finiteExponent v) :
    ∃ f :
        (chapter11RayClassProjectionOfLE hstep.1).ker →*
          chapter11MultiplicativeLocalLayer
            (A := v.adicCompletionIntegers K) (m.finiteExponent v),
      Function.Injective f := by
  sorry

theorem chapter11_local_principal_unit_layer_is_the_additive_residue_field
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {n : ℕ} (hn : 0 < n) :
    Nonempty
      (chapter11MultiplicativeLocalLayer
          (A := v.adicCompletionIntegers K) n ≃*
        Multiplicative (Additive (IsLocalRing.ResidueField (v.adicCompletionIntegers K)))) := by
  sorry

noncomputable def chapter11LocalPrincipalUnitLayerEquiv
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {n : ℕ} (hn : 0 < n) :
    chapter11MultiplicativeLocalLayer
        (A := v.adicCompletionIntegers K) n ≃*
      Multiplicative (Additive (IsLocalRing.ResidueField (v.adicCompletionIntegers K))) :=
  Classical.choice (chapter11_local_principal_unit_layer_is_the_additive_residue_field v hn)

end
