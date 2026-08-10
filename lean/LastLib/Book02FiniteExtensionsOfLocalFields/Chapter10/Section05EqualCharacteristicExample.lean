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
  have hunit : IsUnit (PowerSeries.constantCoeff (u : PowerSeries k)) := by
    exact (PowerSeries.isUnit_iff_constantCoeff.mp u.isUnit)
  have hne : PowerSeries.constantCoeff (u : PowerSeries k) ≠ 0 :=
    (isUnit_iff_ne_zero.mp hunit)
  refine ⟨PowerSeries.constantCoeff (u : PowerSeries k), hne,
    fun n => PowerSeries.coeff (n + 1) (u : PowerSeries k) /
      PowerSeries.constantCoeff (u : PowerSeries k), rfl, ?_⟩
  intro n
  dsimp
  field_simp

/-- The coefficient recorded by the `n`th equal-characteristic layer. -/
def chapter10PowerSeriesLayerCoefficient
    {k : Type*} [Field k] (u : (PowerSeries k)ˣ) (n : ℕ) : k :=
  PowerSeries.coeff n (u : PowerSeries k)

/-- The `p`th-power Frobenius identity in characteristic `p`. -/
-- STATEMENT_NEEDS_UPDATE: `[CharP k p]` permits `p = 0` for a characteristic-zero
-- field, but then the displayed identity is false (for example at `x = 0`);
-- require `p ≠ 0` or `[Fact p.Prime]` as the minimal correction.
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
  by_cases hp0 : p = 0
  · subst p
    simpa [chapter10PowerSeriesUnitFiltration]
  · letI : NeZero p := ⟨hp0⟩
    letI : Fact p.Prime := CharP.char_is_prime_of_pos (R := k) p
    let J : Ideal (PowerSeries k) :=
      Ideal.span ({PowerSeries.X} : Set (PowerSeries k))
    change ((u : PowerSeries k) - 1) ∈ J ^ n at hu
    change (((u ^ p : (PowerSeries k)ˣ) : PowerSeries k) - 1) ∈ J ^ (p * n)
    have hpow : ((u : PowerSeries k) - 1) ^ p ∈ (J ^ n) ^ p :=
      Ideal.pow_mem_pow hu p
    have hident :
        ((u ^ p : (PowerSeries k)ˣ) : PowerSeries k) - 1 =
          ((u : PowerSeries k) - 1) ^ p := by
      letI : CharP (PowerSeries k) p :=
        charP_of_injective_algebraMap (R := k) (A := PowerSeries k)
          (fun a b h => by
            have h₀ := congrArg (PowerSeries.coeff 0) h
            simpa [PowerSeries.algebraMap_apply] using h₀)
          p
      have h := add_pow_char (R := PowerSeries k)
        (1 : PowerSeries k) ((u : PowerSeries k) - 1) p
      have h' : ((u : PowerSeries k) ^ p) =
          1 + ((u : PowerSeries k) - 1) ^ p := by
        convert h using 1 <;> ring
      calc
        ((u ^ p : (PowerSeries k)ˣ) : PowerSeries k) - 1 =
            ((u : PowerSeries k) ^ p) - 1 := by rfl
        _ = (1 + ((u : PowerSeries k) - 1) ^ p) - 1 := by rw [h']
        _ = ((u : PowerSeries k) - 1) ^ p := by ring
    have hideal : J ^ (p * n) = (J ^ n) ^ p := by
      rw [Nat.mul_comm p n, pow_mul]
    rw [hident, hideal]
    exact hpow

/-- The equal-characteristic layer is literally the next power-series coefficient. -/
theorem chapter10_equal_characteristic_layer_records_coefficient
    {k : Type*} [Field k] (u : (PowerSeries k)ˣ) (n : ℕ) :
    chapter10PowerSeriesLayerCoefficient u n =
      PowerSeries.coeff n (u : PowerSeries k) := by
  rfl

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10
