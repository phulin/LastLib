import Mathlib.Data.NNReal.Basic
import LastLib.Book04AdelesAndIdeles.Chapter13.Section02AssemblingMultiplicativeCharacters

open scoped NNReal NumberField.AdeleRing RestrictedProduct

namespace LastLib.Book04AdelesAndIdeles.Chapter13

noncomputable section

/-!
## 13.3 Unitary characters and modulus twists
-/

def chapter13IsUnitaryCharacter {G : Type*} [Monoid G] [TopologicalSpace G]
    (χ : G →ₜ* ℂˣ) : Prop :=
  ∀ x, ‖(χ x : ℂ)‖ = 1

def chapter13CharacterAbsoluteValue (K : Type*) [Field K] [NumberField K]
    (χ : Chapter13ClassCharacter K) :
    Chapter13IdeleClass K →ₜ* ℝ :=
  { toMonoidHom :=
      { toFun := fun x => ‖(χ x : ℂ)‖
        map_one' := by sorry
        map_mul' := by sorry }
    continuous_toFun := by sorry }

theorem chapter13CharacterAbsoluteValue_apply
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter13ClassCharacter K) (x : Chapter13IdeleClass K) :
    chapter13CharacterAbsoluteValue K χ x = ‖(χ x : ℂ)‖ :=
  rfl

theorem chapter13CharacterAbsoluteValue_positive
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter13ClassCharacter K) (x : Chapter13IdeleClass K) :
    0 < chapter13CharacterAbsoluteValue K χ x := by
  sorry

def chapter13NormOneSubgroup (K : Type*) [Field K] [NumberField K] :
    Subgroup (Chapter13IdeleClass K) :=
  (chapter13IdeleClassModule K).ker

/- The norm-one class group is the kernel itself.  Its quotient is the positive
   magnitude direction, so keep the two objects distinct in the interface. -/
abbrev Chapter13NormOneClass (K : Type*) [Field K] [NumberField K] :=
  chapter13NormOneSubgroup K

abbrev Chapter13PositiveNormQuotient (K : Type*) [Field K] [NumberField K] :=
  Chapter13IdeleClass K ⧸ chapter13NormOneSubgroup K

theorem chapter13_norm_one_iff_module_one
    (K : Type*) [Field K] [NumberField K] (x : Chapter13IdeleClass K) :
    x ∈ chapter13NormOneSubgroup K ↔ chapter13IdeleClassModule K x = 1 :=
  Iff.rfl

/- DEPENDENCY_GUESS: the compactness and quotient identification are the precise interface supplied
by the earlier idele-class-group chapters; the positive-real quotient model is chosen explicitly here. -/

/- The compactness and quotient identification are the precise interface supplied by the earlier
idele-class-group chapters.  They are hypotheses here so that the character theorem remains useful
before those chapters are merged. -/

structure Chapter13NormDirectionData (K : Type*) [Field K] [NumberField K] where
  normOne_compact : IsCompact (chapter13NormOneSubgroup K : Set (Chapter13IdeleClass K))
  quotient_equiv :
    Chapter13PositiveNormQuotient K ≃ₜ* ℝ≥0ˣ
  quotient_module :
    ∀ x : Chapter13IdeleClass K,
      (((quotient_equiv (QuotientGroup.mk' (chapter13NormOneSubgroup K) x) : ℝ≥0ˣ) : ℝ≥0) : ℝ) =
        chapter13IdeleClassModule K x

theorem chapter13_character_absolute_value_trivial_on_norm_one
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter13NormDirectionData K)
    (χ : Chapter13ClassCharacter K) :
    ∀ x : chapter13NormOneSubgroup K,
      chapter13CharacterAbsoluteValue K χ x = 1 := by
  sorry

theorem chapter13_character_absolute_value_factors_through_norm_one_quotient
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter13NormDirectionData K)
    (χ : Chapter13ClassCharacter K) :
    ∃ f : Chapter13PositiveNormQuotient K →ₜ* ℝ,
      ∀ x : Chapter13IdeleClass K,
        f (QuotientGroup.mk' (chapter13NormOneSubgroup K) x) =
          chapter13CharacterAbsoluteValue K χ x := by
  sorry

def chapter13RealModulusPower (r : ℝ) (σ : ℝ) : ℝ :=
  Real.rpow r σ

theorem chapter13_continuous_positive_real_hom_is_power
    (f : ℝ≥0ˣ →ₜ* ℝ≥0ˣ) :
    ∃! σ : ℝ, ∀ x : ℝ≥0ˣ,
      (((f x : ℝ≥0ˣ) : ℝ≥0) : ℝ) =
        Real.rpow (((x : ℝ≥0ˣ) : ℝ≥0) : ℝ) σ := by
  sorry

theorem chapter13_character_absolute_value_is_modulus_power
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter13NormDirectionData K)
    (χ : Chapter13ClassCharacter K) :
    ∃! σ : ℝ, ∀ x : Chapter13IdeleClass K,
      chapter13CharacterAbsoluteValue K χ x =
        chapter13RealModulusPower (chapter13IdeleClassModule K x) σ := by
  sorry

def chapter13PositiveRealPowerUnit (r : ℝ) (hr : 0 < r) (σ : ℝ) : ℂˣ :=
  Units.mk0 (Real.rpow r σ : ℂ) (by sorry)

def chapter13CharacterUnitaryPart
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter13ClassCharacter K) (σ : ℝ) : Chapter13ClassCharacter K :=
  { toMonoidHom :=
      { toFun := fun x =>
          χ x * (chapter13PositiveRealPowerUnit
            (chapter13IdeleClassModule K x)
            (chapter13_idele_class_module_positive K x) σ)⁻¹
        map_one' := by sorry
        map_mul' := by sorry }
    continuous_toFun := by sorry }

theorem chapter13CharacterUnitaryPart_apply
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter13ClassCharacter K) (σ : ℝ) (x : Chapter13IdeleClass K) :
    chapter13CharacterUnitaryPart K χ σ x =
      χ x * (chapter13PositiveRealPowerUnit
        (chapter13IdeleClassModule K x)
        (chapter13_idele_class_module_positive K x) σ)⁻¹ :=
  rfl

theorem chapter13CharacterUnitaryPart_is_unitary
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter13ClassCharacter K) (σ : ℝ)
    (hσ : ∀ x, chapter13CharacterAbsoluteValue K χ x =
      chapter13RealModulusPower (chapter13IdeleClassModule K x) σ) :
    chapter13IsUnitaryCharacter (chapter13CharacterUnitaryPart K χ σ) := by
  sorry

theorem chapter13_character_has_canonical_unitary_decomposition
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter13NormDirectionData K)
    (χ : Chapter13ClassCharacter K) :
    ∃ σ : ℝ,
      (∀ x, chapter13CharacterAbsoluteValue K χ x =
        chapter13RealModulusPower (chapter13IdeleClassModule K x) σ) ∧
      chapter13IsUnitaryCharacter (chapter13CharacterUnitaryPart K χ σ) := by
  sorry

def chapter13ComplexPower (r : ℝ) (_hr : 0 < r) (s : ℂ) : ℂˣ :=
  Units.mk0 (Complex.exp (s * Complex.log (r : ℂ))) (by
    exact Complex.exp_ne_zero _)

def chapter13ComplexModulusTwist
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter13ClassCharacter K) (s : ℂ) : Chapter13ClassCharacter K :=
  { toMonoidHom :=
      { toFun := fun x =>
          χ x * chapter13ComplexPower (chapter13IdeleClassModule K x)
            (chapter13_idele_class_module_positive K x) s
        map_one' := by sorry
        map_mul' := by sorry }
    continuous_toFun := by sorry }

theorem chapter13ComplexModulusTwist_apply
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter13ClassCharacter K) (s : ℂ) (x : Chapter13IdeleClass K) :
    chapter13ComplexModulusTwist K χ s x =
      χ x * chapter13ComplexPower (chapter13IdeleClassModule K x)
        (chapter13_idele_class_module_positive K x) s :=
  rfl

theorem chapter13_positive_real_complex_character_is_complex_power
    (χ : ℝ≥0ˣ →ₜ* ℂˣ) :
    ∃ s : ℂ, ∀ t : ℝ≥0ˣ,
      χ t = chapter13ComplexPower
        (((t : ℝ≥0ˣ) : ℝ≥0) : ℝ) (by sorry) s := by
  sorry

theorem chapter13_imaginary_modulus_twist_unitary
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter13ClassCharacter K) (hχ : chapter13IsUnitaryCharacter χ)
    (t : ℝ) :
    chapter13IsUnitaryCharacter
      (chapter13ComplexModulusTwist K χ (Complex.I * t)) := by
  sorry

/-! The rational example is stated through the product decomposition supplied by the book.  The
finite factor may then be identified with the profinite unit group and its finite quotients. -/

theorem chapter13_rational_class_character_decomposes_on_product
    {F : Type*} [CommGroup F] [TopologicalSpace F]
    (e : Chapter13IdeleClass ℚ ≃ₜ* (F × ℝ≥0ˣ))
    (χ : Chapter13ClassCharacter ℚ) :
    ∃ χf : F →ₜ* ℂˣ, ∃ χinf : ℝ≥0ˣ →ₜ* ℂˣ,
      ∀ x, χ x = χf ((e x).1) * χinf ((e x).2) := by
  sorry

theorem chapter13_finite_character_factors_through_finite_quotient
    {F Q : Type*} [CommGroup F] [CommGroup Q]
    (q : F →* Q) (hsurj : Function.Surjective q) (χ : F →* ℂˣ)
    (hq : ∀ x, q x = 1 → χ x = 1) :
    ∃ θ : Q →* ℂˣ, θ.comp q = χ := by
  sorry

def chapter13DirichletCharacter (N : ℕ) := (ZMod N)ˣ →* ℂˣ

theorem chapter13_profinite_factor_is_dirichlet_character
    {F : Type*} [CommGroup F] (N : ℕ)
    (q : F →* (ZMod N)ˣ) (hsurj : Function.Surjective q) (χ : F →* ℂˣ)
    (hq : ∀ x, q x = 1 → χ x = 1) :
    ∃ θ : chapter13DirichletCharacter N, θ.comp q = χ := by
  sorry

theorem chapter13_dirichlet_character_is_finite_order
    (N : ℕ) (χ : chapter13DirichletCharacter N) [Finite (ZMod N)ˣ] :
    ∃ n : ℕ, 0 < n ∧ ∀ x, χ.toFun x ^ n = 1 := by
  sorry

end
end LastLib.Book04AdelesAndIdeles.Chapter13
