import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Dependencies

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10

noncomputable section

open Ideal IsLocalRing

/-! ## 10.5. Equal-characteristic example -/

/-- The equal-characteristic local ring and its Laurent-series fraction field. -/
abbrev Chapter10EqualCharacteristicRing (k : Type*) [Field k] :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter08.Chapter08FormalPowerSeries k

abbrev Chapter10EqualCharacteristicField (k : Type*) [Field k] :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter08.Chapter08FormalLaurentSeries k

/-- The equal-characteristic field is the fraction field of its power-series ring. -/
theorem chapter10_equal_characteristic_fraction_field
    (k : Type*) [Field k] :
    IsFractionRing (Chapter10EqualCharacteristicRing k)
      (Chapter10EqualCharacteristicField k) := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter08.chapter08_power_series_is_fraction_field_of_power_series k

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

/-- The normalized coefficient recorded by the `n`th equal-characteristic layer. -/
def chapter10PowerSeriesLayerCoefficient
    {k : Type*} [Field k] (u : (PowerSeries k)ˣ) (n : ℕ) : k :=
  PowerSeries.coeff (n + 1) (u : PowerSeries k) /
    PowerSeries.constantCoeff (u : PowerSeries k)

/-- The `p`th-power Frobenius identity in characteristic `p`. -/
theorem chapter10_equal_characteristic_frobenius_identity
    {k : Type*} [Field k] (p : ℕ) (hp : 0 < p) [CharP k p]
    (x : PowerSeries k) :
    (1 + x) ^ p = 1 + x ^ p := by
  have hchar : CharP (PowerSeries k) p :=
    charP_of_injective_algebraMap (R := k) (A := PowerSeries k)
      (fun a b h => by
        have h₀ := congrArg (PowerSeries.coeff 0) h
        simpa [PowerSeries.algebraMap_apply] using h₀)
      p
  have hprime : Fact p.Prime :=
    ⟨CharP.char_prime_of_ne_zero (R := k) (by omega)⟩
  simpa using (@add_pow_char (PowerSeries k) inferInstance
    (1 : PowerSeries k) x p hprime hchar)

/-- Frobenius sends the `t`-adic principal-unit filtration from depth `n` to `pn`. -/
theorem chapter10_equal_characteristic_power_depth_jump
    {k : Type*} [Field k] (p n : ℕ) (hp : 0 < p) [CharP k p]
    (u : (PowerSeries k)ˣ)
    (hu : u ∈ chapter10PowerSeriesUnitFiltration k n) :
    u ^ p ∈ chapter10PowerSeriesUnitFiltration k (p * n) := by
  let J : Ideal (PowerSeries k) :=
    Ideal.span ({PowerSeries.X} : Set (PowerSeries k))
  change ((u : PowerSeries k) - 1) ∈ J ^ n at hu
  change (((u ^ p : (PowerSeries k)ˣ) : PowerSeries k) - 1) ∈ J ^ (p * n)
  have hpow : ((u : PowerSeries k) - 1) ^ p ∈ (J ^ n) ^ p :=
    Ideal.pow_mem_pow hu p
  have hident :
      ((u ^ p : (PowerSeries k)ˣ) : PowerSeries k) - 1 =
        ((u : PowerSeries k) - 1) ^ p := by
    have hchar : CharP (PowerSeries k) p :=
      charP_of_injective_algebraMap (R := k) (A := PowerSeries k)
        (fun a b h => by
          have h₀ := congrArg (PowerSeries.coeff 0) h
          simpa [PowerSeries.algebraMap_apply] using h₀)
        p
    have hprime : Fact p.Prime :=
      ⟨CharP.char_prime_of_ne_zero (R := k) (by omega)⟩
    have h := @add_pow_char (PowerSeries k) inferInstance
      (1 : PowerSeries k) ((u : PowerSeries k) - 1) p hprime hchar
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

/-- The equal-characteristic layer is the normalized next power-series coefficient. -/
theorem chapter10_equal_characteristic_layer_records_coefficient
    {k : Type*} [Field k] (u : (PowerSeries k)ˣ) (n : ℕ) :
    chapter10PowerSeriesLayerCoefficient u n =
      PowerSeries.coeff (n + 1) (u : PowerSeries k) /
        PowerSeries.constantCoeff (u : PowerSeries k) := by
  rfl

/-- On a principal-unit layer, the normalized coefficient is the raw next digit. -/
theorem chapter10_equal_characteristic_principal_layer_coefficient
    {k : Type*} [Field k] (u : (PowerSeries k)ˣ) (n : ℕ)
    (hu : u ∈ chapter10PowerSeriesUnitFiltration k (n + 1)) :
    PowerSeries.constantCoeff (u : PowerSeries k) = 1 ∧
      chapter10PowerSeriesLayerCoefficient u n =
        PowerSeries.coeff (n + 1) (u : PowerSeries k) := by
  change ((u : PowerSeries k) - 1) ∈
    (Ideal.span ({PowerSeries.X} : Set (PowerSeries k))) ^ (n + 1) at hu
  have hmem : ((u : PowerSeries k) - 1) ∈
      Ideal.span ({PowerSeries.X} : Set (PowerSeries k)) := by
    simpa only [pow_one] using
      (Ideal.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le n))) hu
  have hdiv : PowerSeries.X ∣ ((u : PowerSeries k) - 1) :=
    (Ideal.mem_span_singleton).mp hmem
  obtain ⟨q, hq⟩ := hdiv
  have hconst : PowerSeries.constantCoeff ((u : PowerSeries k) - 1) = 0 := by
    rw [hq]
    simp
  have hcoeff : PowerSeries.constantCoeff (u : PowerSeries k) = 1 := by
    simpa only [map_sub, map_one, sub_eq_zero] using hconst
  refine ⟨hcoeff, ?_⟩
  simp [chapter10PowerSeriesLayerCoefficient, hcoeff]

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10
