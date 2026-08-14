import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08.Section01TheLocalResidue

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u v

/-! ### 8.2 Independence of parameter -/

variable (k : Type u) [Field k]
variable (C : Chapter08SmoothIntegralCurve k)
variable (x : Chapter08ClosedPoint C.carrier)

def chapter08LogDifferential
    {F : Type v} [Field F] [Algebra k F] (a : F) : Ω[F⁄k] :=
  a⁻¹ • KaehlerDifferential.D k F a

structure Chapter08LocalParameter
    [Algebra k C.carrier.functionField] where
  oldParameter : C.carrier.functionField
  newParameter : C.carrier.functionField
  unitFactor : C.carrier.functionField
  parameter_change : newParameter = oldParameter * unitFactor
  oldParameter_isUnit : IsUnit oldParameter
  newParameter_isUnit : IsUnit newParameter
  unitFactor_isUnit : IsUnit unitFactor
  unitFactor_isUnit_at : Chapter08UnitAt C x unitFactor

theorem chapter08_log_differential_product
    {F : Type v} [Field F] [Algebra k F]
    {t v u : F} (hu : u = t * v) (ht : IsUnit t) (hv : IsUnit v) :
    chapter08LogDifferential k u =
      chapter08LogDifferential k t + chapter08LogDifferential k v := by
  sorry

theorem chapter08_parameter_unit_log_differential_regular
    [Algebra k C.carrier.functionField]
    (R : Chapter08LocalResidueSystem k C x)
    (p : Chapter08LocalParameter k C x) :
    chapter08LogDifferential k p.unitFactor ∈ R.regularDifferentials := by
  sorry

theorem chapter08_residue_log_differential_parameter_change
    [Algebra k C.carrier.functionField]
    (R : Chapter08LocalResidueSystem k C x)
    (p : Chapter08LocalParameter k C x) :
    chapter08ResidueAt k C x R (chapter08LogDifferential k p.oldParameter) =
      chapter08ResidueAt k C x R
        (chapter08LogDifferential k p.newParameter) := by
  sorry

theorem chapter08_residue_parameter_change_regular_correction
    [Algebra k C.carrier.functionField]
    (R : Chapter08LocalResidueSystem k C x)
    {t v : C.carrier.functionField}
    (ht : IsUnit t) (hv : IsUnit v)
    (hregular : chapter08LogDifferential k v ∈ R.regularDifferentials) :
    chapter08ResidueAt k C x R (chapter08LogDifferential k (t * v)) =
      chapter08ResidueAt k C x R (chapter08LogDifferential k t) := by
  sorry

theorem chapter08_laurent_derivative_termwise
    {E : Type v} [Field E] (b : LaurentSeries E) (m : ℤ) :
    (LaurentSeries.derivative E b).coeff m =
      Ring.choose (m + 1) 1 • b.coeff (m + 1) := by
  sorry

theorem chapter08_laurent_derivative_minus_one_coefficient
    {E : Type v} [Field E] (b : LaurentSeries E) :
    (LaurentSeries.derivative E b).coeff (-1) = 0 := by
  sorry

structure Chapter08CoordinateResidue
    [Algebra k C.carrier.functionField]
    (R : Chapter08LocalResidueSystem k C x)
    {E : Type v} [Field E] [Algebra k E]
    (η : Chapter08RationalDifferentials k C.carrier) where
  expansion : Chapter08LaurentExpansion k C x E η
  coordinateResidue : k
  coordinateFormula :
    coordinateResidue = Algebra.trace k E expansion.residueCoefficient

def chapter08_coordinate_residue
    [Algebra k C.carrier.functionField]
    {E : Type v} [Field E] [Algebra k E]
    {η : Chapter08RationalDifferentials k C.carrier}
    (c : Chapter08CoordinateResidue k C x R E η) : k :=
  c.coordinateResidue

theorem chapter08_coordinate_residue_parameter_independent
    [Algebra k C.carrier.functionField]
    (R : Chapter08LocalResidueSystem k C x)
    {E : Type v} [Field E] [Algebra k E] [FiniteDimensional k E]
    [Algebra.IsSeparable k E]
    {η : Chapter08RationalDifferentials k C.carrier}
    (c₁ c₂ : Chapter08CoordinateResidue k C x R E η)
    (h₁ : c₁.expansion.parameter_is_uniformizer)
    (h₂ : c₂.expansion.parameter_is_uniformizer) :
    chapter08_coordinate_residue k C x R c₁ =
      chapter08_coordinate_residue k C x R c₂ := by
  sorry

theorem chapter08_residue_is_parameter_independent
    [Algebra k C.carrier.functionField]
    (R : Chapter08LocalResidueSystem k C x)
    {E : Type v} [Field E] [Algebra k E] [FiniteDimensional k E]
    [Algebra.IsSeparable k E]
    {η : Chapter08RationalDifferentials k C.carrier}
    (c : Chapter08CoordinateResidue k C x R E η) :
    chapter08_coordinate_residue k C x R c =
      chapter08ResidueAt k C x R η := by
  sorry

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08
