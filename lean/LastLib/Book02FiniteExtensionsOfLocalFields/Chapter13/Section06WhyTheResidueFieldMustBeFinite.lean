import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter13.Section05WildEqualCharacteristicAnInfiniteFamily

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter13

noncomputable section

universe uK uL uGamma

open IntermediateField
open scoped WithZero

/-! ## 13.6. Why the residue field must be finite -/

theorem chapter13_infinite_residue_field_integer_ring_not_compact
    {A : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    [Infinite (IsLocalRing.ResidueField A)] :
    ¬@CompactSpace A (IsLocalRing.maximalIdeal A).adicTopology := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter06.chapter06_infinite_residue_field_integer_not_compact

/-- A valuation witness for an unramified finite extension. -/
structure Chapter13UnramifiedExtensionWitness
    {K : Type uK} {L : Type uL} {ΓK : Type uGamma} [Field K] [Field L]
    [Algebra K L] [LinearOrderedCommGroupWithZero ΓK]
    (vK : Valuation K ΓK) where
  valueGroup : Type uL
  [valueGroupOrder : LinearOrderedCommGroupWithZero valueGroup]
  valuation : Valuation L valueGroup
  [extension : vK.HasExtension valuation]
  [discrete : Valuation.IsRankOneDiscrete valuation]
  [finite : FiniteDimensional K L]
  [residue_algebra :
    Algebra (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField valuation.valuationSubring)]
  [residue_finite :
    FiniteDimensional (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField valuation.valuationSubring)]
  residue_separable :
    Algebra.IsSeparable
      (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField valuation.valuationSubring)
  degree_eq_residue_degree :
    Module.finrank K L =
      Module.finrank (IsLocalRing.ResidueField vK.valuationSubring)
        (IsLocalRing.ResidueField valuation.valuationSubring)
  ramification_index_eq_one :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
      vK.valuationSubring valuation.valuationSubring
      (IsLocalRing.maximalIdeal valuation.valuationSubring) = 1

def chapter13UnramifiedDegreeClasses
    {K : Type u} [Field K] (vK : Valuation K ℤᵐ⁰) (d : ℕ) :
    Set (Chapter13FiniteExtensionClass K) :=
  {c | ∃ E : Chapter13FiniteExtensionModel K,
      chapter13FiniteExtensionClassOf E = c ∧
        chapter13FiniteExtensionDegree E = d ∧
        letI : Field E.carrier := E.field_carrier
        letI : Algebra K E.carrier := E.algebra
        letI : FiniteDimensional K E.carrier := E.finite_dimensional
        Nonempty (Chapter13UnramifiedExtensionWitness vK
          (L := E.carrier))}

def chapter13FiniteSeparableDegreeClasses
    (k : Type u) [Field k] (d : ℕ) :
    Set (Chapter13FiniteExtensionClass k) :=
  {c | ∃ E : Chapter13FiniteExtensionModel k,
      chapter13FiniteExtensionClassOf E = c ∧
        chapter13FiniteExtensionDegree E = d ∧
        letI : Field E.carrier := E.field_carrier
        letI : Algebra k E.carrier := E.algebra
        letI : FiniteDimensional k E.carrier := E.finite_dimensional
        Algebra.IsSeparable k E.carrier}

/- DEPENDENCY_GUESS: This is the precise class-level form of the Chapter 7
   unramified lifting/classification theorem.  Completeness supplies the
   Henselian hypothesis, and the residue field is used without assuming it
   is finite. -/
theorem chapter13_unramified_classes_correspond_to_separable_residue_classes
    {K : Type u} [Field K]
    (vK : Valuation K ℤᵐ⁰)
    [Valuation.IsRankOneDiscrete vK]
    (d : ℕ)
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring) :
    Nonempty (
      (chapter13UnramifiedDegreeClasses vK d : Type _) ≃
        (chapter13FiniteSeparableDegreeClasses
          (IsLocalRing.ResidueField vK.valuationSubring) d : Type _)) := by
  sorry

/-- The fixed-degree consequence of the residue-field classification. -/
theorem chapter13_infinite_residue_separable_classes_lift_to_unramified_classes
    {K : Type u} [Field K]
    (vK : Valuation K ℤᵐ⁰)
    [Valuation.IsRankOneDiscrete vK]
    (d : ℕ)
    (hresidue_infinite :
      Set.Infinite (chapter13FiniteSeparableDegreeClasses
        (IsLocalRing.ResidueField vK.valuationSubring) d))
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring) :
    Set.Infinite (chapter13UnramifiedDegreeClasses vK d) := by
  sorry

/-- The residue-field-free finite-degree part of the complete DVR package.
The perfectness hypothesis is explicit because it is the standard
defectless hypothesis used by the earlier degree theorem. -/
theorem chapter13_complete_perfect_residue_extension_has_fundamental_equality
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ) (e f : ℕ)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    [PerfectField (IsLocalRing.ResidueField vK.valuationSubring)]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (he :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
        vK.valuationSubring vL.valuationSubring
        (IsLocalRing.maximalIdeal vL.valuationSubring) = e)
    (hf :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree
        vK.valuationSubring vL.valuationSubring
        (IsLocalRing.maximalIdeal vL.valuationSubring) = f) :
    Module.finrank K L = e * f := by
  rw [← he, ← hf]
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.complete_extension_defectless_without_separability
    vK vL hcomplete

/- SOURCE_ISSUE: The last hierarchy bullet says “completeness and
   discreteness give ... `[L : K] = e f`” without a defectless or perfect
   residue-field hypothesis.  That equality is false for complete discretely
   valued fields with imperfect residue field and defect extensions.  The
   corrected declaration above assumes a perfect base residue field, while
   the other consequences are recorded separately below. -/

theorem chapter13_complete_discrete_extension_has_unique_valuation_and_finite_integral_closure
    {K L Γ : Type uK} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring) :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.hasUniqueValuationExtension vK L ∧
      (integralClosure vK.valuationSubring L : Set L) =
        (vL.valuationSubring : Set L) ∧
      Module.Finite vK.valuationSubring vL.valuationSubring := by
  sorry

theorem chapter13_finite_residue_adds_integer_ring_compactness
    {A : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    [Finite (IsLocalRing.ResidueField A)]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal A) A) :
    @CompactSpace A (IsLocalRing.maximalIdeal A).adicTopology := by
  exact @LastLib.Book01ValuationsDVRsAndCompletions.Chapter06.chapter06_complete_dvr_integer_compact
    A _ _ _ _ hcomplete

theorem chapter13_characteristic_zero_finite_extensions_are_separable
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [CharZero K] [FiniteDimensional K L] :
    Algebra.IsSeparable K L := by
  infer_instance

theorem chapter13_tame_positive_characteristic_and_wild_equal_characteristic
    (k : Type*) [Field k] [Fintype k]
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    Set.Infinite (chapter13DegreeClasses (K := LaurentSeries k) p) := by
  exact chapter13_laurent_series_has_infinitely_many_degree_p_separable_extensions
    k p

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter13
