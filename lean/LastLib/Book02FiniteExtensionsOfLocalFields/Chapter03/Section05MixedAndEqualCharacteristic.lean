import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.Section01WhyTowerFormulasMatter
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.LaurentSeries

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03

noncomputable section

open Polynomial
open scoped WithZero

open LastLib.Book01ValuationsDVRsAndCompletions.Chapter12

/-! ## 3.5. Mixed and equal characteristic -/

/-- The normalized mixed-characteristic profile over `ℚ_[p]`. -/
def chapter03MixedCharacteristicProfile
    (p : ℕ) (K : Type*) [Fact p.Prime] [Field K] [Algebra (ℚ_[p]) K]
    [FiniteDimensional (ℚ_[p]) K]
    (vK : AddValuation K (WithTop ℤ)) (e f : ℕ) : Prop :=
  Module.finrank (ℚ_[p]) K = e * f ∧
    vK (algebraMap (ℚ_[p]) K (p : ℚ_[p])) = (e : WithTop ℤ)

@[simp] theorem chapter03MixedCharacteristicProfile_iff
    (p : ℕ) (K : Type*) [Fact p.Prime] [Field K] [Algebra (ℚ_[p]) K]
    [FiniteDimensional (ℚ_[p]) K]
    (vK : AddValuation K (WithTop ℤ)) (e f : ℕ) :
    chapter03MixedCharacteristicProfile p K vK e f ↔
      Module.finrank (ℚ_[p]) K = e * f ∧
        vK (algebraMap (ℚ_[p]) K (p : ℚ_[p])) = (e : WithTop ℤ) := Iff.rfl

/-- In mixed characteristic, the degree and the normalized value of `p` are
the ramification and residue factors. -/
theorem chapter03_mixed_characteristic_degree_and_prime_value
    (p : ℕ) (K : Type*) [Fact p.Prime] [Field K] [Algebra (ℚ_[p]) K]
    [FiniteDimensional (ℚ_[p]) K]
    (vK : AddValuation K (WithTop ℤ))
    [(AddValuation.toValuation (Padic.addValuation (p := p))).HasExtension
      (AddValuation.toValuation vK)]
    [Valuation.IsRankOneDiscrete (AddValuation.toValuation vK)]
    (e f : ℕ)
    (he : chapterRamificationIndex
      (AddValuation.toValuation (Padic.addValuation (p := p))).valuationSubring
      (AddValuation.toValuation vK).valuationSubring
      (IsLocalRing.maximalIdeal (AddValuation.toValuation vK).valuationSubring) = e)
    (hf : chapterResidueDegree
      (AddValuation.toValuation (Padic.addValuation (p := p))).valuationSubring
      (AddValuation.toValuation vK).valuationSubring
      (IsLocalRing.maximalIdeal (AddValuation.toValuation vK).valuationSubring) = f)
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal (Padic.addValuation (p := p)).valuationSubring)
      (Padic.addValuation (p := p)).valuationSubring)
    (hrestriction :
      ∀ x : ℚ_[p],
        vK (algebraMap (ℚ_[p]) K x) =
          e • Padic.addValuation x) :
    chapter03MixedCharacteristicProfile p K vK e f := by
  sorry

/-- A finite field is perfect. -/
theorem chapter03_finite_residue_field_is_perfect
    (k : Type*) [Field k] [Fintype k] :
    PerfectField k := by
  sorry

/-- Every finite extension of a finite field is separable. -/
theorem chapter03_finite_residue_extensions_are_separable
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l] [Fintype k] :
    Algebra.IsSeparable k l := by
  sorry

/-- The Laurent-series model for equal characteristic. -/
abbrev chapter03EqualCharacteristicModel (k : Type*) [Field k] :=
  LaurentSeries k

/-- A coefficient field is an injective residue-section compatible with the
chosen fraction field. -/
def chapter03HasCoefficientField
    (A k K : Type*) [CommRing A] [IsLocalRing A]
    [Field k] [Field K] [Algebra A K] [Algebra k K] : Prop :=
  ∃ s : k →+* A, Function.Injective s ∧
    ∃ e : A ⧸ IsLocalRing.maximalIdeal A ≃+* k,
      ((e.toRingHom.comp
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))).comp s =
        RingHom.id k) ∧
      (∀ a : k, algebraMap k K a = algebraMap A K (s a))

/-- The distinguished parameter in the Laurent-series model. -/
def chapter03EqualCharacteristicUniformizer
    (k : Type*) [Field k] : LaurentSeries k :=
  ((PowerSeries.X : PowerSeries k) : LaurentSeries k)

theorem chapter03_equal_characteristic_model_is_complete
    (k : Type*) [Field k] :
    CompleteSpace (chapter03EqualCharacteristicModel k) := by
  sorry

/-- The residue-case purely inseparable polynomial `X^p-a`. -/
def chapter03PurelyInseparableResiduePolynomial
    (k : Type*) [Ring k] (p : ℕ) (a : k) : k[X] :=
  ((X : k[X]) ^ p - (C a : k[X]) : k[X])

/-- The uniformizer-case purely inseparable polynomial `X^p-t`. -/
def chapter03PurelyInseparableUniformizerPolynomial
    (k : Type*) [Field k] (p : ℕ) :
    (LaurentSeries k)[X] :=
  X ^ p - C (chapter03EqualCharacteristicUniformizer k)

/-- A lift of residue coefficients into the chosen valuation ring. -/
structure Chapter03ResidueLift
    (k K : Type*) [Field k] [Field K] [Algebra k K]
    (vK : AddValuation K (WithTop ℤ)) where
  lift : k →+* vK.toValuation.valuationSubring
  residueEquiv :
    IsLocalRing.ResidueField vK.toValuation.valuationSubring ≃+* k
  section_compatibility :
    (residueEquiv.toRingHom.comp
        (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal vK.toValuation.valuationSubring))).comp lift =
      RingHom.id k
  algebra_compatibility :
    ∀ a : k, algebraMap k K a = (lift a : K)

/-- A purely inseparable residue root has `e=1` and `f=p`. -/
-- The general interface records the coefficient lift explicitly; in the
-- Laurent-series model this is supplied by the constant coefficient field.
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
    (residueLift : Chapter03ResidueLift k K vK)
    (hnot_power_K : ¬ ∃ b : K, b ^ p = algebraMap k K a)
    [IsPurelyInseparable K L]
    [Valuation.HasExtension vK.toValuation vL.toValuation]
    [Valuation.IsRankOneDiscrete vK.toValuation]
    [Valuation.IsRankOneDiscrete vL.toValuation]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.toValuation.valuationSubring)
      vK.toValuation.valuationSubring)
    (hrestriction : chapter03ValuationRestrictionScale vK vL 1) :
    ∃ data : Chapter03FiniteLocalExtensionData K L _
      vK.toValuation vL.toValuation,
      data.e = 1 ∧ data.f = p := by
  sorry

/-- A root of `X^p-t` is purely inseparable and totally ramified. -/
-- The `hvalue` hypothesis records the source's normalization `v(t)=1`.
theorem chapter03_purely_inseparable_uniformizer_root_has_e_p
    (k L : Type*) [Field k] [Field L]
    [Algebra (LaurentSeries k) L] [FiniteDimensional (LaurentSeries k) L]
    [IsPurelyInseparable (LaurentSeries k) L]
    (p : ℕ) [ExpChar k p] (α : L)
    (hroot :
      aeval α (chapter03PurelyInseparableUniformizerPolynomial k p) = 0)
    (hgen : Algebra.adjoin (LaurentSeries k) ({α} : Set L) = ⊤)
    (hdegree : Module.finrank (LaurentSeries k) L = p)
    (vK : AddValuation (LaurentSeries k) (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (hvalue : vK (chapter03EqualCharacteristicUniformizer k) = 1)
    [Valuation.HasExtension vK.toValuation vL.toValuation]
    [Valuation.IsRankOneDiscrete vK.toValuation]
    [Valuation.IsRankOneDiscrete vL.toValuation]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.toValuation.valuationSubring)
      vK.toValuation.valuationSubring)
    (hrestriction : chapter03ValuationRestrictionScale vK vL p) :
    ∃ data : Chapter03FiniteLocalExtensionData (LaurentSeries k) L _
      vK.toValuation vL.toValuation,
      data.e = p ∧ data.f = 1 := by
  sorry

/-- A nontrivial finite purely inseparable extension is neither separable nor
Galois. -/
theorem chapter03_purely_inseparable_extension_is_not_separable
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsPurelyInseparable K L]
    (hdegree : Module.finrank K L ≠ 1) :
    ¬ Algebra.IsSeparable K L ∧ ¬ IsGalois K L := by
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03
