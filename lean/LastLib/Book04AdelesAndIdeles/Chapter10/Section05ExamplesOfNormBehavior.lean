import LastLib.Book04AdelesAndIdeles.Chapter10.Section04LocalConditionsVersusGlobalNorm
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

namespace LastLib.Book04AdelesAndIdeles.Chapter10

noncomputable section

open scoped BigOperators

/-! ## 10.5. Examples of norm behavior -/

theorem chapter10_complex_real_norm_formula (z : ℂ) :
    Algebra.norm ℝ z = Complex.normSq z := by
  sorry

theorem chapter10_complex_real_norm_formula_expanded (z : ℂ) :
    Algebra.norm ℝ z = z.re ^ 2 + z.im ^ 2 := by
  sorry

theorem chapter10_complex_real_norm_positive (z : ℂ) (hz : z ≠ 0) :
    0 < Algebra.norm ℝ z := by
  sorry

theorem chapter10_negative_real_not_a_complex_norm (r : ℝ) (hr : r < 0) :
    ¬ ∃ z : ℂ, z ≠ 0 ∧ Algebra.norm ℝ z = r := by
  sorry

/-- A complexified real place is represented by a map into the complex local
factor together with the local determinant compatibility. -/
theorem chapter10_global_norm_positive_at_a_complexified_real_place
    {G : Type*} [CommGroup G]
    (place : G →* ℂˣ) (placeNorm : ℂˣ →* ℝˣ)
    (hcompat : placeNorm.comp place =
      (chapter10LocalNormUnitHom ℝ ℂ).comp place) (a : G) :
    0 < (placeNorm (place a) : ℝ) := by
  sorry

/-! ### Unramified and totally ramified local obstructions -/

/-- The full multiplicative norm subgroup of `Fˣ`.  For a field, `Fˣ` is
the group of all nonzero elements, so this records the valuation obstruction
as well as the unit obstruction. -/
def chapter10NormSubgroup
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] : Subgroup Fˣ :=
  Subgroup.map (chapter10LocalNormUnitHom F E) ⊤

abbrev chapter10FullNormQuotient
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] : Type _ :=
  Fˣ ⧸ chapter10NormSubgroup F E

theorem chapter10_unramified_full_norm_quotient_cyclic_of_order
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (vF : AddValuation F (WithTop ℤ)) (vE : AddValuation E (WithTop ℤ))
    (d : ℕ) (hunram : chapter10UnramifiedLocalExtension vF vE)
    (hdegree : Module.finrank F E = d) (πF : F)
    (hπF : chapter10NormalizedUniformizer vF πF)
    [Finite (chapter10ResidueField vF)]
    [Algebra (chapter10ResidueField vF) (chapter10ResidueField vE)]
    [FiniteDimensional (chapter10ResidueField vF) (chapter10ResidueField vE)]
    [Algebra.IsSeparable (chapter10ResidueField vF) (chapter10ResidueField vE)] :
    IsCyclic (chapter10FullNormQuotient F E) ∧
      Nat.card (chapter10FullNormQuotient F E) = d := by
  sorry

def chapter10NormValuationImage
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (vF : AddValuation F (WithTop ℤ)) : Set ℤ :=
  {z | ∃ y : E, y ≠ 0 ∧ vF (chapter10LocalNorm F E y) = z}

theorem chapter10_totally_ramified_norm_valuation_unrestricted
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E]
    (vF : AddValuation F (WithTop ℤ)) (vE : AddValuation E (WithTop ℤ))
    (hformula : chapter10NormValuationFormula F E vF vE 1)
    (πE : E) (hπE : chapter10NormalizedUniformizer vE πE) :
    chapter10NormValuationImage F E vF = Set.univ := by
  sorry

/-! The source warns that this image need not be the whole base unit set. -/
def chapter10TotallyRamifiedUnitNormIsProper
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E]
    (vF : AddValuation F (WithTop ℤ))
    (vE : AddValuation E (WithTop ℤ))
    (_hformula : chapter10NormValuationFormula F E vF vE 1) : Prop :=
  chapter10ValuationUnitNormImage F E vF vE ≠ chapter10LocalUnitSet vF

theorem chapter10_totally_ramified_unit_norm_properness_is_an_extra_condition
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E]
    (vF : AddValuation F (WithTop ℤ))
    (vE : AddValuation E (WithTop ℤ))
    (hformula : chapter10NormValuationFormula F E vF vE 1) :
    chapter10TotallyRamifiedUnitNormIsProper F E vF vE hformula ↔
      chapter10ValuationUnitNormImage F E vF vE ≠ chapter10LocalUnitSet vF := Iff.rfl

/-! ### The Gaussian rational example -/

def chapter10GaussianRational := ℚ × ℚ

def chapter10GaussianRationalNorm (z : chapter10GaussianRational) : ℚ :=
  z.1 ^ 2 + z.2 ^ 2

theorem chapter10_gaussian_rational_norm_formula (a b : ℚ) :
    chapter10GaussianRationalNorm (a, b) = a ^ 2 + b ^ 2 := by
  rfl

theorem chapter10_three_not_a_gaussian_rational_norm :
    ¬ ∃ z : chapter10GaussianRational,
      chapter10GaussianRationalNorm z = 3 := by
  sorry

theorem chapter10_prime_three_divides_gaussian_sum_implies_both_divisible
    (a b : ℤ) (h : 3 ∣ a ^ 2 + b ^ 2) : 3 ∣ a ∧ 3 ∣ b := by
  sorry

theorem chapter10_three_gaussian_obstruction_by_parity :
    ¬ ∃ a b : ℚ, a ^ 2 + b ^ 2 = 3 := by
  sorry

theorem chapter10_three_not_a_three_adic_gaussian_norm :
    ¬ ∃ a b : ℚ_[3], a ^ 2 + b ^ 2 = 3 := by
  sorry

end
end LastLib.Book04AdelesAndIdeles.Chapter10
