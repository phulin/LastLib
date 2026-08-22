import LastLib.Book05LocalClassFieldTheory.Chapter11.Dependencies
import LastLib.Book05LocalClassFieldTheory.Chapter11.Section01ExactTopologicalStatement
import LastLib.Book05LocalClassFieldTheory.Chapter11.Section02FiniteOrderCharacters
import LastLib.Book05LocalClassFieldTheory.Chapter11.Section03UnramifiedCharacters
import LastLib.Book05LocalClassFieldTheory.Chapter11.Section04RamifiedCharactersAndConductors
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicNumbers

namespace LastLib.Book05LocalClassFieldTheory.Chapter11

noncomputable section

open scoped Topology

/-! ## 11.6. Coefficient fields and standard characters -/

def chapter11ReciprocityCharacter
    {K G A : Type*} [Field K] [Group G] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace G] [TopologicalSpace A]
    [IsTopologicalGroup G] [IsTopologicalGroup A]
    (R : Chapter11ReciprocityData K G)
    (ρ : TopologicalAbelianization G →ₜ* A) : Kˣ →ₜ* A :=
  ρ.comp R.reciprocity

/-!
The valuation-zero subgroup is the book's `O_Eˣ`.  The surrounding data
packages the standard nonarchimedean coefficient-field facts which are used
to turn the abstract target `Eˣ` into the unit target in the classification.
-/

def chapter11CoefficientValuationZeroSubgroup
    {E : Type*} [Field E]
    (v : Eˣ →* Multiplicative ℤ) : Subgroup Eˣ :=
  v.ker

structure Chapter11CoefficientValuationData
    (E : Type*) [Field E] [TopologicalSpace Eˣ]
    [TopologicalSpace (Multiplicative ℤ)] [DiscreteTopology (Multiplicative ℤ)]
    where
  valuation : Eˣ →* Multiplicative ℤ
  valuation_continuous : Continuous valuation
  units : Chapter11CoefficientUnitData E
  units_eq_valuation_zero :
    units.unitGroup = chapter11CoefficientValuationZeroSubgroup valuation

/- LOCAL_DEPENDENCY_GUESS: the preceding local-field chapters should supply
  this valuation/unit package for every finite extension of `Q_p`. -/
structure Chapter11FinitePAdicCoefficientData
    (p : ℕ) [Fact p.Prime] (E : Type*) [Field E]
    [Algebra (ℚ_[p]) E] [FiniteDimensional (ℚ_[p]) E]
    [TopologicalSpace Eˣ] where
  valuationData : Chapter11CoefficientValuationData E

theorem chapter11_finite_padic_extension_has_coefficient_unit_data
    (p : ℕ) [Fact p.Prime] {E : Type*} [Field E]
    [Algebra (ℚ_[p]) E] [FiniteDimensional (ℚ_[p]) E]
    [TopologicalSpace Eˣ]
    (hlocal :
      ∃ v : Eˣ →* Multiplicative ℤ,
        Continuous v ∧ IsCompact (v.ker : Set Eˣ) ∧
          TotallyDisconnectedSpace v.ker ∧ T2Space v.ker) :
    Nonempty (Chapter11FinitePAdicCoefficientData p E) := by
  sorry

theorem chapter11_finite_padic_coefficient_units_are_profinite
    (p : ℕ) [Fact p.Prime] {E : Type*} [Field E]
    [Algebra (ℚ_[p]) E] [FiniteDimensional (ℚ_[p]) E]
    [TopologicalSpace Eˣ]
    (C : Chapter11FinitePAdicCoefficientData p E) :
    IsCompact (C.valuationData.units.unitGroup : Set Eˣ) ∧
      TotallyDisconnectedSpace C.valuationData.units.unitGroup ∧
        T2Space C.valuationData.units.unitGroup := by
  exact ⟨C.valuationData.units.unitGroup_compact,
    C.valuationData.units.unitGroup_totallyDisconnected,
    C.valuationData.units.unitGroup_t2⟩

abbrev Chapter11CoefficientUnitGroup
    {E : Type*} [Field E] [TopologicalSpace Eˣ]
    (C : Chapter11CoefficientValuationData E) : Type _ := C.units.unitGroup

def chapter11CoefficientCharacterLandsInUnits
    {G E : Type*} [Group G] [Field E]
    [TopologicalSpace G] [TopologicalSpace Eˣ]
    (C : Chapter11CoefficientValuationData E) (ρ : G →ₜ* Eˣ) : Prop :=
  ∀ g : G, ρ g ∈ C.units.unitGroup

theorem chapter11_compact_coefficient_character_lands_in_units
    {G E : Type*} [Group G] [Field E]
    [TopologicalSpace G] [TopologicalSpace Eˣ]
    [IsTopologicalGroup G] [CompactSpace G]
    (C : Chapter11CoefficientValuationData E) (ρ : G →ₜ* Eˣ) :
    IsCompact (Set.range ρ) ∧
      chapter11CoefficientCharacterLandsInUnits C ρ := by
  sorry

/-!
This is the coefficient-field form of the character classification.  The
right-hand codomain is the subgroup type itself, so the assertion records the
book's `O_Eˣ` rather than merely a character into `Eˣ` whose image happens to
be bounded.
-/

noncomputable def chapter11EValuedCharacterEquiv
    {K G E : Type*} [Field K] [Group G] [Field E]
    [TopologicalSpace Kˣ] [TopologicalSpace G] [TopologicalSpace Eˣ]
    [IsTopologicalGroup G] [IsTopologicalGroup Eˣ] [CompactSpace G]
    (R : Chapter11ReciprocityData K G)
    (C : Chapter11CoefficientValuationData E) :
    (G →ₜ* Eˣ) ≃ (Kˣ →ₜ* C.units.unitGroup) := by
  sorry

theorem chapter11_E_valued_characters_are_classified_by_unit_characters
    {K G E : Type*} [Field K] [Group G] [Field E]
    [TopologicalSpace Kˣ] [TopologicalSpace G] [TopologicalSpace Eˣ]
    [IsTopologicalGroup G] [IsTopologicalGroup Eˣ] [CompactSpace G]
    (R : Chapter11ReciprocityData K G)
    (C : Chapter11CoefficientValuationData E) :
    Nonempty ((G →ₜ* Eˣ) ≃ (Kˣ →ₜ* C.units.unitGroup)) := by
  exact ⟨chapter11EValuedCharacterEquiv R C⟩

theorem chapter11_complex_galois_character_has_finite_image
    {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (ρ : G →ₜ* ℂˣ) :
    chapter11FiniteImage ρ := by
  sorry

noncomputable def chapter11ComplexFiniteImageCharacterEquiv
    {K G : Type*} [Field K] [Group G]
    [TopologicalSpace Kˣ] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (R : Chapter11ReciprocityData K G) :
    {ρ : G →ₜ* ℂˣ // chapter11FiniteImage ρ} ≃
      {χ : Kˣ →ₜ* ℂˣ // chapter11FiniteImage χ} := by
  sorry

def chapter11ComplexUnramifiedQuasicharacter
    {K : Type*} [Field K] [TopologicalSpace Kˣ]
    (D : Chapter11LocalFieldData K) (α : ℂˣ) : Kˣ →ₜ* ℂˣ :=
  chapter11UnramifiedCharacterOfValue D α

theorem chapter11_complex_quasicharacter_with_nonfinite_parameter_is_not_galois
    {K : Type*} [Field K] [TopologicalSpace Kˣ]
    (D : Chapter11LocalFieldData K) (α : ℂˣ)
    (hα : ¬ IsOfFinOrder α) :
    ¬ chapter11ProfiniteExtensionOf
        (chapter11ComplexUnramifiedQuasicharacter D α) ∧
      ¬ chapter11FiniteImage (chapter11ComplexUnramifiedQuasicharacter D α) := by
  sorry

/-!
The next structure is the normalization package for the prime-to-residue-
characteristic cyclotomic calculation.  `parameter` is the image of the
residue-field cardinality `q` in the coefficient target.
-/

structure Chapter11PrimeToResidueCyclotomicData
    {K G A : Type*} [Field K] [Group G] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace G] [TopologicalSpace A]
    [IsTopologicalGroup G] [IsTopologicalGroup A]
    (D : Chapter11LocalFieldData K) (R : Chapter11ReciprocityData K G)
    where
  residueCharacteristic : ℕ
  residueCharacteristic_prime : Nat.Prime residueCharacteristic
  residueCharacteristic_eq_base :
    residueCharacteristic =
      LastLib.Book05LocalClassFieldTheory.Chapter08.chapter08ResidueCharacteristic
        D.base.valuation
  coefficientPrime : ℕ
  coefficientPrime_prime : Nat.Prime coefficientPrime
  primes_distinct : coefficientPrime ≠ residueCharacteristic
  residueCardinality : ℕ
  residueCardinality_eq_base :
    residueCardinality =
      Nat.card (LastLib.Book05LocalClassFieldTheory.Chapter08.Chapter08ResidueField
        D.base.valuation)
  residueCardinalityImage : A
  parameter : A
  parameter_eq_residueCardinalityImage :
    parameter = residueCardinalityImage
  character : TopologicalAbelianization G →ₜ* A
  trivial_on_units :
    ∀ u : D.unitGroup,
      chapter11ReciprocityCharacter R character (u : Kˣ) = 1
  parameter_at_uniformizer :
    chapter11ReciprocityCharacter R character D.uniformizer = parameter

theorem chapter11_prime_to_residue_cyclotomic_formula
    {K G A : Type*} [Field K] [Group G] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace G] [TopologicalSpace A]
    [IsTopologicalGroup G] [IsTopologicalGroup A]
    (D : Chapter11LocalFieldData K) (R : Chapter11ReciprocityData K G)
    (C : Chapter11PrimeToResidueCyclotomicData D R)
    (r : ℤ) (u : D.unitGroup) :
    chapter11ReciprocityCharacter (K := K) (G := G) (A := A) R C.character
        (D.uniformizer ^ r * (u : Kˣ)) = C.parameter ^ r := by
  sorry

def chapter11PadicPrimeUnit
    (p : ℕ) [Fact p.Prime] : (ℚ_[p])ˣ :=
  Units.mk0 (p : ℚ_[p]) (by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)

def chapter11PadicUnitInclusion
    (p : ℕ) [Fact p.Prime] : (ℤ_[p])ˣ →* (ℚ_[p])ˣ :=
  Units.map (algebraMap (ℤ_[p]) (ℚ_[p])).toMonoidHom

/-!
`unitPart` is the map `y ↦ ⟨y⟩` to `Z_pˣ`.  The two fields at the prime and
on embedded units isolate the total-ramification normalization used in the
source formula.
-/

structure Chapter11PadicCyclotomicFormulaData
    (p : ℕ) [Fact p.Prime] (A : Type*) [CommGroup A]
    [TopologicalSpace A] [IsTopologicalGroup A] where
  character : (ℚ_[p])ˣ →ₜ* A
  unitPart : (ℚ_[p])ˣ →* (ℤ_[p])ˣ
  unitCharacter : (ℤ_[p])ˣ →ₜ* A
  character_on_units :
    ∀ u : (ℤ_[p])ˣ,
      character (chapter11PadicUnitInclusion p u) = (unitCharacter u)⁻¹
  unitPart_on_units :
    ∀ u : (ℤ_[p])ˣ,
      unitPart (chapter11PadicUnitInclusion p u) = u
  unitPart_on_prime_unit_decomposition :
    ∀ (r : ℤ) (u : (ℤ_[p])ˣ),
      unitPart
          (chapter11PadicPrimeUnit p ^ r * chapter11PadicUnitInclusion p u) = u
  unit_decomposition :
    ∀ x : (ℚ_[p])ˣ, ∃ (r : ℤ) (u : (ℤ_[p])ˣ),
      x = chapter11PadicPrimeUnit p ^ r * chapter11PadicUnitInclusion p u
  prime_is_trivial : character (chapter11PadicPrimeUnit p) = 1

theorem chapter11_padic_cyclotomic_formula_Qp
    (p : ℕ) [Fact p.Prime] (A : Type*) [CommGroup A]
    [TopologicalSpace A] [IsTopologicalGroup A]
    (C : Chapter11PadicCyclotomicFormulaData p A)
    (r : ℤ) (u : (ℤ_[p])ˣ) :
    C.character
        (chapter11PadicPrimeUnit p ^ r * chapter11PadicUnitInclusion p u) =
      (C.unitCharacter u)⁻¹ := by
  sorry

theorem chapter11_padic_cyclotomic_formula_Qp_standard
    (p : ℕ) [Fact p.Prime]
    [TopologicalSpace (ℚ_[p])ˣ] [TopologicalSpace (ℤ_[p])ˣ]
    [IsTopologicalGroup (ℤ_[p])ˣ]
    (χp : (ℚ_[p])ˣ →ₜ* (ℤ_[p])ˣ)
    (hunit : ∀ u : (ℤ_[p])ˣ,
      χp (chapter11PadicUnitInclusion p u) = u⁻¹)
    (hprime : χp (chapter11PadicPrimeUnit p) = 1)
    (r : ℤ) (u : (ℤ_[p])ˣ) :
    χp (chapter11PadicPrimeUnit p ^ r * chapter11PadicUnitInclusion p u) =
      u⁻¹ := by
  sorry

def chapter11PadicNormPullbackCharacter
    {p : ℕ} {K A : Type*} [Fact p.Prime] [Field K]
    [Algebra (ℚ_[p]) K] [FiniteDimensional (ℚ_[p]) K]
    [CommGroup A] [TopologicalSpace Kˣ] [TopologicalSpace A]
    [IsTopologicalGroup A]
    (hcont : Continuous (chapter11NormHom (ℚ_[p]) K))
    (C : Chapter11PadicCyclotomicFormulaData p A) : Kˣ →ₜ* A :=
  C.character.comp (chapter11ContinuousNormHom (ℚ_[p]) K hcont)

theorem chapter11_padic_cyclotomic_formula_finite_extension
    {p : ℕ} {K A : Type*} [Fact p.Prime] [Field K]
    [Algebra (ℚ_[p]) K] [FiniteDimensional (ℚ_[p]) K]
    [CommGroup A] [TopologicalSpace Kˣ] [TopologicalSpace A]
    [IsTopologicalGroup A]
    (hcont : Continuous (chapter11NormHom (ℚ_[p]) K))
    (C : Chapter11PadicCyclotomicFormulaData p A) (x : Kˣ) :
    chapter11PadicNormPullbackCharacter hcont C x =
      (C.unitCharacter
      (C.unitPart (chapter11NormHom (ℚ_[p]) K x)))⁻¹ := by
  sorry

theorem chapter11_padic_cyclotomic_formula_finite_extension_standard
    {p : ℕ} {K : Type*} [Fact p.Prime] [Field K]
    [Algebra (ℚ_[p]) K] [FiniteDimensional (ℚ_[p]) K]
    [TopologicalSpace Kˣ] [TopologicalSpace (ℚ_[p])ˣ]
    [TopologicalSpace (ℤ_[p])ˣ] [IsTopologicalGroup (ℤ_[p])ˣ]
    (hcont : Continuous (chapter11NormHom (ℚ_[p]) K))
    (χp : (ℚ_[p])ˣ →ₜ* (ℤ_[p])ˣ)
    (unitPart : (ℚ_[p])ˣ →* (ℤ_[p])ˣ)
    (hunitPart : ∀ y : (ℚ_[p])ˣ, χp y = (unitPart y)⁻¹)
    (χK : Kˣ →ₜ* (ℤ_[p])ˣ)
    (hcompat :
      χK = χp.comp (chapter11ContinuousNormHom (ℚ_[p]) K hcont))
    (x : Kˣ) :
    χK x = (unitPart (chapter11NormHom (ℚ_[p]) K x))⁻¹ := by
  sorry

/-!
The fixed field is now expressed using Mathlib's absolute Galois group and
`IntermediateField.fixedField`; this is the canonical field-side object
behind the book's phrase “the fixed field of the kernel”.
-/

def chapter11FixedFieldOfGaloisCharacter
    {K A : Type*} [Field K] [CommGroup A] [TopologicalSpace A]
    (ρ : Chapter11GaloisGroup K →ₜ* A) :
    IntermediateField K (AlgebraicClosure K) :=
  IntermediateField.fixedField ρ.toMonoidHom.ker

noncomputable def chapter11FiniteCharacterGaloisCounterpart
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A]
    [IsTopologicalGroup A] [T2Space A] [CompactSpace A]
    [TotallyDisconnectedSpace A]
    (R : Chapter11ReciprocityData K (Chapter11GaloisGroup K))
    (χ : Kˣ →ₜ* A) (_hχ : chapter11FiniteImage χ) :
    Chapter11GaloisGroup K →ₜ* A :=
  (chapter11ContinuousCharacterEquiv R).symm χ

def chapter11FiniteCharacterFixedField
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A]
    [IsTopologicalGroup A] [T2Space A] [CompactSpace A]
    [TotallyDisconnectedSpace A]
    (R : Chapter11ReciprocityData K (Chapter11GaloisGroup K))
    (χ : Kˣ →ₜ* A) (hχ : chapter11FiniteImage χ) :
    IntermediateField K (AlgebraicClosure K) :=
  chapter11FixedFieldOfGaloisCharacter
    (chapter11FiniteCharacterGaloisCounterpart R χ hχ)

theorem chapter11_finite_character_fixed_field_is_kernel_fixed_field
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A]
    [IsTopologicalGroup A] [T2Space A] [CompactSpace A]
    [TotallyDisconnectedSpace A]
    (R : Chapter11ReciprocityData K (Chapter11GaloisGroup K))
    (χ : Kˣ →ₜ* A) (hχ : chapter11FiniteImage χ) :
    chapter11FiniteCharacterFixedField R χ hχ =
      chapter11FixedFieldOfGaloisCharacter
        (chapter11FiniteCharacterGaloisCounterpart R χ hχ) := by
  rfl

/- LOCAL_DEPENDENCY_GUESS: the merged class-field API must identify the
  abstract `residueDegree` field with the quotient order computed from the
  unit image; Chapters 1--10 are absent in this checkout. -/
theorem chapter11_finite_character_recovers_extension_invariants
    {K A : Type*} [Field K] [CommGroup A] [Finite A]
    [TopologicalSpace Kˣ] [TopologicalSpace A] [DiscreteTopology A]
    (C : Chapter11ClassFieldExistenceData K)
    (χ : Kˣ →ₜ* A)
    (hχ : chapter11FiniteImage χ) :
    ∃ e : C.extension,
      C.normGroup e = chapter11CharacterKernel χ ∧
          C.degree e = Nat.card (Set.range χ) ∧
          C.residueDegree e =
            chapter11ResidueDegreeOfCharacter C.localFieldData χ hχ := by
  sorry

theorem chapter11_finite_character_recovers_ramification_images
    {K G A : Type*} [Field K] [Group G] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace G] [TopologicalSpace A]
    [IsTopologicalGroup G] [IsTopologicalGroup A] [T2Space A]
    [CompactSpace A] [TotallyDisconnectedSpace A]
    (D : Chapter11LocalFieldData K) (R : Chapter11ReciprocityData K G)
    (F : Chapter11GaloisRamificationFiltration (TopologicalAbelianization G))
    (χ : Kˣ →ₜ* A)
    (hfiltration :
      ∀ n, F.group n = (D.unitFiltration n).map R.reciprocity.toMonoidHom)
    (n : ℕ) :
    (F.group n).map
        (chapter11CorrespondingAbelianGaloisCharacter R χ).toMonoidHom =
      chapter11UnitImage D χ n := by
  sorry

end
end LastLib.Book05LocalClassFieldTheory.Chapter11
