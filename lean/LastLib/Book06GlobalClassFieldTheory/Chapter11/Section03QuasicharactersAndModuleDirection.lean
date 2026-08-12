import LastLib.Book06GlobalClassFieldTheory.Chapter11.Section02FiniteOrderCharactersAndGaloisCharacters

namespace LastLib.Book06GlobalClassFieldTheory.Chapter11

open scoped BigOperators NNReal NumberField.AdeleRing RestrictedProduct
open NumberField

noncomputable section

/-! ## 11.3. Quasicharacters and the module direction -/

def chapter11IsUnitaryCharacter
    {G : Type*} [Monoid G] [TopologicalSpace G] (χ : G →ₜ* ℂˣ) : Prop :=
  ∀ x, ‖(χ x : ℂ)‖ = 1

def chapter11CharacterAbsoluteValue
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter11HeckeCharacter K) :
    Chapter11IdeleClass K →ₜ* ℝ :=
  LastLib.Book04AdelesAndIdeles.Chapter13.chapter13CharacterAbsoluteValue K χ

theorem chapter11CharacterAbsoluteValue_apply
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter11HeckeCharacter K) (x : Chapter11IdeleClass K) :
    chapter11CharacterAbsoluteValue K χ x = ‖(χ x : ℂ)‖ :=
  rfl

theorem chapter11CharacterAbsoluteValue_positive
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter11HeckeCharacter K) (x : Chapter11IdeleClass K) :
    0 < chapter11CharacterAbsoluteValue K χ x := by
  exact LastLib.Book04AdelesAndIdeles.Chapter13.chapter13CharacterAbsoluteValue_positive
    K χ x

abbrev Chapter11NormDirectionData
    (K : Type*) [Field K] [NumberField K] :=
  LastLib.Book04AdelesAndIdeles.Chapter13.Chapter13NormDirectionData K

theorem chapter11_character_absolute_value_is_modulus_power
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter11NormDirectionData K)
    (χ : Chapter11HeckeCharacter K) :
    ∃! σ : ℝ, ∀ x : Chapter11IdeleClass K,
      chapter11CharacterAbsoluteValue K χ x =
        Real.rpow (chapter11IdeleClassModule K x) σ := by
  sorry

def chapter11CharacterUnitaryPart
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter11HeckeCharacter K) (σ : ℝ) : Chapter11HeckeCharacter K :=
  LastLib.Book04AdelesAndIdeles.Chapter13.chapter13CharacterUnitaryPart K χ σ

theorem chapter11CharacterUnitaryPart_apply
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter11HeckeCharacter K) (σ : ℝ) (x : Chapter11IdeleClass K) :
    chapter11CharacterUnitaryPart K χ σ x =
      χ x * (LastLib.Book04AdelesAndIdeles.Chapter13.chapter13PositiveRealPowerUnit
        (chapter11IdeleClassModule K x)
        (chapter11_idele_class_module_positive K x) σ)⁻¹ := by
  rfl

theorem chapter11CharacterUnitaryPart_is_unitary
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter11NormDirectionData K)
    (χ : Chapter11HeckeCharacter K) (σ : ℝ)
    (hσ : ∀ x, chapter11CharacterAbsoluteValue K χ x =
      Real.rpow (chapter11IdeleClassModule K x) σ) :
    chapter11IsUnitaryCharacter (chapter11CharacterUnitaryPart K χ σ) := by
  sorry

theorem chapter11_character_has_canonical_unitary_decomposition
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter11NormDirectionData K)
    (χ : Chapter11HeckeCharacter K) :
    ∃ σ : ℝ,
      (∀ x, chapter11CharacterAbsoluteValue K χ x =
        Real.rpow (chapter11IdeleClassModule K x) σ) ∧
      chapter11IsUnitaryCharacter (chapter11CharacterUnitaryPart K χ σ) := by
  sorry

def chapter11ModuleCharacter
    (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    Chapter11HeckeCharacter K :=
  LastLib.Book04AdelesAndIdeles.Chapter13.chapter13ComplexModulusTwist
    K (1 : Chapter11HeckeCharacter K) s

theorem chapter11ModuleCharacter_apply
    (K : Type*) [Field K] [NumberField K] (s : ℂ)
    (x : Chapter11IdeleClass K) :
    chapter11ModuleCharacter K s x =
      (1 : ℂˣ) * LastLib.Book04AdelesAndIdeles.Chapter13.chapter13ComplexPower
        (chapter11IdeleClassModule K x)
        (chapter11_idele_class_module_positive K x) s := by
  rfl

theorem chapter11ModuleCharacter_trivial_on_principal_ideles
    (K : Type*) [Field K] [NumberField K] (s : ℂ) (a : Kˣ) :
    chapter11ModuleCharacter K s
      (QuotientGroup.mk' (LastLib.Book04AdelesAndIdeles.Chapter13.chapter13PrincipalIdeleSubgroup K)
        (LastLib.Book04AdelesAndIdeles.Chapter13.chapter13PrincipalIdele K a)) = 1 := by
  sorry

structure Chapter11ModuleLocalNormalizationData
    (K : Type*) [Field K] [NumberField K] where
  residueCardinality : Chapter11FinitePlaceIndex K → ℕ
  uniformizer : ∀ v : Chapter11FinitePlaceIndex K, v.adicCompletion K
  uniformizer_is_uniformizer : ∀ v : Chapter11FinitePlaceIndex K,
    Chapter11LocalUniformizer v (uniformizer v)
  localModuleValue : ∀ v : Chapter11FinitePlaceIndex K, (v.adicCompletion K)ˣ → ℂˣ
  localModuleValue_uniformizer : ∀ v : Chapter11FinitePlaceIndex K,
    localModuleValue v (Units.mk0 (uniformizer v) (by sorry)) =
      (residueCardinality v : ℂ)⁻¹

theorem chapter11_module_uniformizer_value
    {K : Type*} [Field K] [NumberField K]
    (D : Chapter11ModuleLocalNormalizationData K) (v : Chapter11FinitePlaceIndex K) :
    D.localModuleValue v (Units.mk0 (D.uniformizer v) (by sorry)) =
      (D.residueCardinality v : ℂ)⁻¹ := by
  exact D.localModuleValue_uniformizer v

def chapter11RealSignCharacter (ε : Fin 2) : ℝˣ →ₜ* ℂˣ := by
  refine
    { toMonoidHom :=
        { toFun := fun x => Units.mk0
            (if ε = 0 then 1 else if (x : ℝ) < 0 then -1 else 1) (by sorry)
          map_one' := by sorry
          map_mul' := by sorry }
      continuous_toFun := by sorry }

def chapter11RealArchimedeanCharacter
    (ε : Fin 2) (s : ℂ) : ℝˣ →ₜ* ℂˣ := by
  refine
    { toMonoidHom :=
        { toFun := fun x => chapter11RealSignCharacter ε x *
            LastLib.Book04AdelesAndIdeles.Chapter13.chapter13ComplexPower
              ‖(x : ℝ)‖ (by sorry) s
          map_one' := by sorry
          map_mul' := by sorry }
      continuous_toFun := by sorry }

def chapter11ComplexArchimedeanCharacter
    (m : ℤ) (s : ℂ) : ℂˣ →ₜ* ℂˣ := by
  refine
    { toMonoidHom :=
        { toFun := fun z => Units.mk0
            (((z : ℂ) / ‖(z : ℂ)‖) ^ m *
              Complex.exp (2 * s * Complex.log (‖(z : ℂ)‖ : ℂ))) (by sorry)
          map_one' := by sorry
          map_mul' := by sorry }
      continuous_toFun := by sorry }

theorem chapter11_real_archimedean_character_classification
    (χ : ℝˣ →ₜ* ℂˣ) :
    ∃ ε : Fin 2, ∃ s : ℂ,
      χ = chapter11RealArchimedeanCharacter ε s := by
  sorry

theorem chapter11_complex_archimedean_character_classification
    (χ : ℂˣ →ₜ* ℂˣ) :
    ∃ m : ℤ, ∃ s : ℂ,
      χ = chapter11ComplexArchimedeanCharacter m s := by
  sorry

theorem chapter11_finite_order_complex_place_character_trivial
    (χ : ℂˣ →ₜ* ℂˣ)
    (hχ : chapter11FiniteOrder χ.toMonoidHom) :
    χ = 1 := by
  sorry

theorem chapter11_finite_order_real_place_factors_through_sign
    (χ : ℝˣ →ₜ* ℂˣ)
    (hχ : chapter11FiniteOrder χ.toMonoidHom) :
    ∃ ε : Fin 2, χ = chapter11RealSignCharacter ε := by
  sorry

theorem chapter11_positive_real_character_is_complex_power
    (χ : ℝ≥0ˣ →ₜ* ℂˣ) :
    ∃ s : ℂ, ∀ t : ℝ≥0ˣ,
      χ t = LastLib.Book04AdelesAndIdeles.Chapter13.chapter13ComplexPower
        (((t : ℝ≥0ˣ) : ℝ≥0) : ℝ) (by sorry) s := by
  exact LastLib.Book04AdelesAndIdeles.Chapter13.chapter13_positive_real_complex_character_is_complex_power
    χ

theorem chapter11_imaginary_modulus_twist_unitary
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter11HeckeCharacter K) (hχ : chapter11IsUnitaryCharacter χ)
    (t : ℝ) :
    chapter11IsUnitaryCharacter
      (LastLib.Book04AdelesAndIdeles.Chapter13.chapter13ComplexModulusTwist
        K χ (Complex.I * t)) := by
  sorry

theorem chapter11_quasicharacter_decomposition
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter11NormDirectionData K)
    (χ : Chapter11HeckeCharacter K) :
    ∃ σ : ℝ,
      (∀ x, chapter11CharacterAbsoluteValue K χ x =
        Real.rpow (chapter11IdeleClassModule K x) σ) ∧
      chapter11IsUnitaryCharacter (chapter11CharacterUnitaryPart K χ σ) := by
  exact chapter11_character_has_canonical_unitary_decomposition K D χ

structure Chapter11PositiveModuleSection (K : Type*) [Field K] [NumberField K] where
  moduleSection : ℝ≥0ˣ → Chapter11IdeleClass K
  section_module : ∀ t, chapter11IdeleClassModule K (moduleSection t) =
    (((t : ℝ≥0ˣ) : ℝ≥0) : ℝ)

theorem chapter11_complex_exponent_unique_on_positive_section
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter11PositiveModuleSection K)
    {s t : ℂ}
    (h : ∀ x : ℝ≥0ˣ,
      LastLib.Book04AdelesAndIdeles.Chapter13.chapter13ComplexPower
        (chapter11IdeleClassModule K (D.moduleSection x))
          (chapter11_idele_class_module_positive K (D.moduleSection x)) s =
      LastLib.Book04AdelesAndIdeles.Chapter13.chapter13ComplexPower
        (chapter11IdeleClassModule K (D.moduleSection x))
          (chapter11_idele_class_module_positive K (D.moduleSection x)) t) :
    s = t := by
  sorry

end

end LastLib.Book06GlobalClassFieldTheory.Chapter11
