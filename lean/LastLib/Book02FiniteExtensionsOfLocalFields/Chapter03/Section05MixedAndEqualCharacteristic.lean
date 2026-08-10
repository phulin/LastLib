import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.Section04ScalarExtensionOfALocalField

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03

noncomputable section

open Polynomial
open scoped WithZero

/-! ## 3.5. Mixed/equal characteristic -/

/-- The normalized mixed-characteristic local-field profile. -/
def chapter03MixedCharacteristicProfile
    (p : ℕ) (K : Type*) [Fact p.Prime] [Field K] [Algebra (ℚ_[p]) K]
    [FiniteDimensional (ℚ_[p]) K]
    (vK : AddValuation K (WithTop ℤ)) (e f : ℕ) : Prop :=
  Module.finrank (ℚ_[p]) K = e * f ∧
    vK (algebraMap (ℚ_[p]) K (p : ℚ_[p])) = (e : WithTop ℤ)

/--
For a finite extension of Q_p, the degree and the normalized value of p are
the ramification/residue factors.  The restriction hypothesis identifies the
chosen normalized valuation with the p-adic one.
-/
theorem chapter03_mixed_characteristic_degree_and_prime_value
    (p : ℕ) (K : Type*) [Fact p.Prime] [Field K] [Algebra (ℚ_[p]) K]
    [FiniteDimensional (ℚ_[p]) K]
    (vK : AddValuation K (WithTop ℤ))
    [(Padic.addValuation (p := p)).HasExtension vK]
    [Valuation.IsRankOneDiscrete (Padic.addValuation (p := p))]
    [Valuation.IsRankOneDiscrete vK] (e f : ℕ)
    (he : chapter03RamificationIndex (Padic.addValuation (p := p)) vK = e)
    (hf : chapter03ResidueDegree (Padic.addValuation (p := p)) vK = f)
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal (Padic.addValuation (p := p)).valuationSubring)
      (Padic.addValuation (p := p)).valuationSubring)
    (hrestriction :
      ∀ x : ℚ_[p],
        vK (algebraMap (ℚ_[p]) K x) =
          e • Padic.addValuation x) :
    chapter03MixedCharacteristicProfile p K vK e f := by
  sorry

/-- Finite residue fields are perfect, so finite residue extensions are separable. -/
theorem chapter03_finite_residue_field_is_perfect
    (k : Type*) [Field k] [Fintype k] :
    PerfectField k := by
  exact PerfectField.ofFinite k

theorem chapter03_finite_residue_extensions_are_separable
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l] [Fintype k] [Fintype l] :
    Algebra.IsSeparable k l := by
  letI : PerfectField k := PerfectField.ofFinite k
  infer_instance

/--
The Laurent-series field is the canonical equal-characteristic model once a
coefficient field has been chosen.
-/
abbrev chapter03EqualCharacteristicModel (k : Type*) [Field k] :=
  LaurentSeries k

/-- A coefficient field is modeled as an injective section of constants. -/
def chapter03HasCoefficientField
    (A k K : Type*) [CommRing A] [IsLocalRing A]
    [Field k] [Field K] [Algebra A K] : Prop :=
  ∃ s : k →+* A, Function.Injective s ∧
    ∃ e : A ⧸ IsLocalRing.maximalIdeal A ≃+* k,
      (e.toRingHom.comp
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))).comp s =
        RingHom.id k

/-- The parameter t in the Laurent-series model. -/
def chapter03EqualCharacteristicUniformizer
    (k : Type*) [Field k] : LaurentSeries k :=
  (PowerSeries.X : PowerSeries k)

theorem chapter03_equal_characteristic_model_is_complete
    (k : Type*) [Field k] :
    CompleteSpace (chapter03EqualCharacteristicModel k) := by
  infer_instance

/-- The residue-case purely inseparable polynomial X^p-a. -/
def chapter03PurelyInseparableResiduePolynomial
    (k : Type*) [Ring k] (p : ℕ) (a : k) : k[X] :=
  ((X : k[X]) ^ p - (C a : k[X]) : k[X])

/-- The uniformizer-case purely inseparable polynomial X^p-t. -/
def chapter03PurelyInseparableUniformizerPolynomial
    (k : Type*) [Field k] (p : ℕ) :
    (LaurentSeries k)[X] :=
  X ^ p - C (chapter03EqualCharacteristicUniformizer k)

/--
An imperfect residue element produces a purely inseparable residue extension
with e=1 and f=p.
-/
-- STATEMENT_NEEDS_UPDATE: The field k and element a are not related to the residue field of vK or to a compatible unit lift in K, so the root and restriction hypotheses do not determine the residue degree; specify the residue-field identification and compatible residue/unit data (or state the theorem directly for the residue field of vK).
theorem chapter03_purely_inseparable_residue_root_has_e_one
    (k K L : Type*) [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
    (p : ℕ) [ExpChar k p] (a : k) (α : L)
    (ha : ¬ ∃ b : k, b ^ p = a)
    (hroot :
      aeval α (chapter03PurelyInseparableResiduePolynomial k p a) = 0)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    [FiniteDimensional K L] (hdegree : Module.finrank K L = p)
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    [vK.HasExtension vL]
    [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (hrestriction : chapter03ValuationRestrictionScale vK vL 1) :
    ∃ data : Chapter03FiniteLocalExtensionData K L _ vK vL,
      data.e = 1 ∧ data.f = p := by
  sorry

/--
The analogous root of X^p-t is purely inseparable and totally ramified, with
e=p and f=1.
-/
-- STATEMENT_NEEDS_UPDATE: The hypotheses do not identify vK with the canonical Laurent-series t-adic valuation or assert vK (chapter03EqualCharacteristicUniformizer k) = 1, so the root equation and restriction scale do not force e = p; add that valuation normalization/value-of-t hypothesis.
theorem chapter03_purely_inseparable_uniformizer_root_has_e_p
    (k L : Type*) [Field k] [Field L]
    [Algebra (LaurentSeries k) L] [FiniteDimensional (LaurentSeries k) L]
    [IsPurelyInseparable (LaurentSeries k) L]
    (p : ℕ) [ExpChar (LaurentSeries k) p] (α : L)
    (hroot :
      aeval α (chapter03PurelyInseparableUniformizerPolynomial k p) = 0)
    (hgen : Algebra.adjoin (LaurentSeries k) ({α} : Set L) = ⊤)
    (hdegree : Module.finrank (LaurentSeries k) L = p)
    (vK : AddValuation (LaurentSeries k) (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    [vK.HasExtension vL]
    [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (hrestriction : chapter03ValuationRestrictionScale vK vL p) :
    ∃ data : Chapter03FiniteLocalExtensionData (LaurentSeries k) L _ vK vL,
      data.e = p ∧ data.f = 1 := by
  sorry

/-- A nontrivial finite purely inseparable extension is not separable/Galois. -/
theorem chapter03_purely_inseparable_extension_is_not_separable
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsPurelyInseparable K L]
    (hdegree : Module.finrank K L ≠ 1) :
    ¬ Algebra.IsSeparable K L ∧ ¬ IsGalois K L := by
  constructor
  · intro hsep
    letI : Algebra.IsSeparable K L := hsep
    apply hdegree
    exact Module.finrank_of_bijective_algebraMap
      (IsPurelyInseparable.bijective_algebraMap_of_isSeparable K L)
  · intro hgal
    letI : IsGalois K L := hgal
    letI : Algebra.IsSeparable K L := inferInstance
    apply hdegree
    exact Module.finrank_of_bijective_algebraMap
      (IsPurelyInseparable.bijective_algebraMap_of_isSeparable K L)

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03
