import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Section04MultiplicationPowersAndResidueCharacteristic

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10

noncomputable section

open Ideal IsLocalRing

/-! ## 10.5. Equal-characteristic example -/

/-- The equal-characteristic local ring and its Laurent-series fraction field. -/
abbrev Chapter10EqualCharacteristicRing (k : Type*) [Field k] := PowerSeries k

abbrev Chapter10EqualCharacteristicField (k : Type*) [Field k] := LaurentSeries k

/-- The `t`-adic filtration on `k[[t]]ˣ`. -/
def chapter10PowerSeriesUnitFiltration
    (k : Type*) [Field k] (n : ℕ) : Subgroup (PowerSeries k)ˣ :=
  chapter10IdealUnitFiltration (PowerSeries k)
    (Ideal.span ({PowerSeries.X} : Set (PowerSeries k))) n

/-- A coefficientwise version of the unit expansion `a₀(1+a₁t+a₂t²+⋯)`. -/
def Chapter10EqualCharacteristicUnitExpansion
    {k : Type*} [Field k] (u : (PowerSeries k)ˣ) : Prop :=
    ∃ a₀ : k, a₀ ≠ 0 ∧ ∃ a : ℕ → k,
    PowerSeries.constantCoeff (u : PowerSeries k) = a₀ ∧
      ∀ n : ℕ,
        PowerSeries.coeff (n + 1) (u : PowerSeries k) = a₀ * a n

/-- Every power-series unit has the displayed constant-plus-higher-coefficients form. -/
theorem chapter10_equal_characteristic_units_have_expansions
    {k : Type*} [Field k] (u : (PowerSeries k)ˣ) :
    Chapter10EqualCharacteristicUnitExpansion u := by
  sorry

/-- The coefficient recorded by the `n`th equal-characteristic layer. -/
def chapter10PowerSeriesLayerCoefficient
    {k : Type*} [Field k] (u : (PowerSeries k)ˣ) (n : ℕ) : k :=
  PowerSeries.coeff n (u : PowerSeries k)

/-- The `p`th-power Frobenius identity in characteristic `p`. -/
theorem chapter10_equal_characteristic_frobenius_identity
    {k : Type*} [Field k] (p : ℕ) [CharP k p] (x : PowerSeries k) :
    (1 + x) ^ p = 1 + x ^ p := by
  sorry

/-- Frobenius sends the `t`-adic principal-unit filtration from depth `n` to `pn`. -/
theorem chapter10_equal_characteristic_power_depth_jump
    {k : Type*} [Field k] (p n : ℕ) [CharP k p]
    (u : (PowerSeries k)ˣ)
    (hu : u ∈ chapter10PowerSeriesUnitFiltration k n) :
    u ^ p ∈ chapter10PowerSeriesUnitFiltration k (p * n) := by
  sorry

/-- The equal-characteristic layer is literally the next power-series coefficient. -/
theorem chapter10_equal_characteristic_layer_records_coefficient
    {k : Type*} [Field k] (u : (PowerSeries k)ˣ) (n : ℕ) :
    chapter10PowerSeriesLayerCoefficient u n =
      PowerSeries.coeff n (u : PowerSeries k) := by
  rfl

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10
