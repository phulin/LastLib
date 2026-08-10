import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Section05EqualCharacteristicExample

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10

noncomputable section

open scoped BigOperators

/-! ## 10.6. Mixed-characteristic example -/

/-- The additive-depth predicate for a principal unit. -/
def Chapter10AdditiveUnitDepth
    {L : Type*} [Field L]
    (v : AddValuation L (WithTop ℤ)) (n : ℕ) (u : L) : Prop :=
  v (u - 1) ≥ (n : WithTop ℤ)

/-- The lower bound predicted by the two extreme terms of a `p`th power. -/
def chapter10MixedCharacteristicDepth (e p n : ℕ) : ℕ :=
  min (e + n) (p * n)

/-- The two principal valuation bounds `v(px) ≥ e+n` and `v(xᵖ) ≥ pn`. -/
theorem chapter10_mixed_characteristic_term_bounds
    {L : Type*} [Field L]
    (v : AddValuation L (WithTop ℤ)) (p e n : ℕ)
    (hp0 : (p : L) ≠ 0)
    (he : v (p : L) = (e : WithTop ℤ))
    (x : L) (hx : v x ≥ (n : WithTop ℤ)) :
    v ((p : L) * x) ≥ (e + n : ℕ) ∧
      v (x ^ p) ≥ (p * n : ℕ) := by
  sorry

/-- The `p`th-power estimate for a unit of depth at least `n`. -/
theorem chapter10_mixed_characteristic_p_power_depth_estimate
    {L : Type*} [Field L]
    (v : AddValuation L (WithTop ℤ)) (p e n : ℕ)
    (hp : Nat.Prime p) (he : v (p : L) = (e : WithTop ℤ))
    (x : L) (hx : v x ≥ (n : WithTop ℤ)) :
    v ((1 + x) ^ p - 1) ≥
      (chapter10MixedCharacteristicDepth e p n : WithTop ℤ) := by
  sorry

/-- For large depths the linear term controls the minimum. -/
theorem chapter10_mixed_characteristic_linear_term_eventually_controls
    (p e : ℕ) (hp : 1 < p) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      chapter10MixedCharacteristicDepth e p n = e + n := by
  sorry

/-- When the nonlinear term is no larger, the depth is `pn`. -/
theorem chapter10_mixed_characteristic_nonlinear_term_controls
    (p e n : ℕ) (h : p * n ≤ e + n) :
    chapter10MixedCharacteristicDepth e p n = p * n := by
  simp [chapter10MixedCharacteristicDepth, min_eq_right h]

/-- The depth estimate expressed as an inclusion of additive principal-unit sets. -/
theorem chapter10_mixed_characteristic_power_sends_depth_to_min
    {L : Type*} [Field L]
    (v : AddValuation L (WithTop ℤ)) (p e n : ℕ)
    (hp : Nat.Prime p) (he : v (p : L) = (e : WithTop ℤ))
    {x : L} (hx : Chapter10AdditiveUnitDepth v n (1 + x)) :
    Chapter10AdditiveUnitDepth v
      (chapter10MixedCharacteristicDepth e p n) ((1 + x) ^ p) := by
  sorry

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10
