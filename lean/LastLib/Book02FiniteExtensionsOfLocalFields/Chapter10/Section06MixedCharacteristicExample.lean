import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Dependencies

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
    (_hp0 : (p : L) ≠ 0)
    (he : v (p : L) = (e : WithTop ℤ))
    (x : L) (hx : v x ≥ (n : WithTop ℤ)) :
    v ((p : L) * x) ≥ (e + n : ℕ) ∧
      v (x ^ p) ≥ (p * n : ℕ) := by
  constructor
  · rw [AddValuation.map_mul, he]
    simpa only [Nat.cast_add, add_comm] using
      (add_le_add_left hx (e : WithTop ℤ))
  · rw [AddValuation.map_pow]
    have hcast : p • (n : WithTop ℤ) = ((p * n : ℕ) : WithTop ℤ) := by
      calc
        p • (n : WithTop ℤ) = ((p • (n : ℤ) : ℤ) : WithTop ℤ) :=
          (WithTop.coe_nsmul (n : ℤ) p).symm
        _ = ((p * n : ℕ) : WithTop ℤ) := by
          congr 1
    have h := nsmul_le_nsmul_right hx p
    rw [hcast] at h
    exact h

/-- The `p`th-power estimate for a unit of depth at least `n`. -/
theorem chapter10_mixed_characteristic_p_power_depth_estimate
    {L : Type*} [Field L]
    (v : AddValuation L (WithTop ℤ)) (p e n : ℕ)
    (hp : Nat.Prime p) (he : v (p : L) = (e : WithTop ℤ))
    (x : L) (hx : v x ≥ (n : WithTop ℤ)) :
    v ((1 + x) ^ p - 1) ≥
      (chapter10MixedCharacteristicDepth e p n : WithTop ℤ) := by
  have hnat : ∀ k : ℕ, (0 : WithTop ℤ) ≤ v (k : L) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        simpa [Nat.cast_succ] using
          (v.map_le_add (g := (0 : WithTop ℤ)) (x := (k : L)) (y := (1 : L))
            ih (by simp))
  let S : L := Finset.sum (Finset.Ioo 0 p) (fun k =>
    (1 : L) ^ k * x ^ (p - k) * ((p.choose k / p : ℕ) : L))
  have hS : (n : WithTop ℤ) ≤ v S := by
    apply v.map_le_sum
    intro k hk
    have hk' := Finset.mem_Ioo.mp hk
    have hpow : (n : WithTop ℤ) ≤ v (x ^ (p - k)) := by
      rw [AddValuation.map_pow]
      have hx_nonneg : (0 : WithTop ℤ) ≤ v x := by
        exact (show (0 : WithTop ℤ) ≤ (n : WithTop ℤ) by positivity).trans hx
      calc
        (n : WithTop ℤ) ≤ v x := hx
        _ = 1 • v x := (one_nsmul _).symm
        _ ≤ (p - k) • v x :=
          nsmul_le_nsmul_left hx_nonneg (by omega)
    have hcoef : (0 : WithTop ℤ) ≤
        v ((p.choose k / p : ℕ) : L) := hnat _
    calc
      (n : WithTop ℤ) ≤ v (x ^ (p - k)) := hpow
      _ ≤ v (x ^ (p - k)) +
          v ((p.choose k / p : ℕ) : L) :=
        le_add_of_nonneg_right hcoef
      _ = v ((1 : L) ^ k * x ^ (p - k) *
          ((p.choose k / p : ℕ) : L)) := by
        simp only [AddValuation.map_mul, AddValuation.map_pow,
          AddValuation.map_one, nsmul_zero, zero_add]
  have hxp : (p * n : ℕ) ≤ v (x ^ p) := by
    rw [AddValuation.map_pow]
    have hcast : p • (n : WithTop ℤ) = ((p * n : ℕ) : WithTop ℤ) := by
      calc
        p • (n : WithTop ℤ) = ((p • (n : ℤ) : ℤ) : WithTop ℤ) :=
          (WithTop.coe_nsmul (n : ℤ) p).symm
        _ = ((p * n : ℕ) : WithTop ℤ) := by
          congr 1
    have h := nsmul_le_nsmul_right hx p
    rw [hcast] at h
    exact h
  have hpS : (e + n : ℕ) ≤ v ((p : L) * S) := by
    rw [AddValuation.map_mul, he]
    simpa only [Nat.cast_add, add_comm] using
      (add_le_add_left hS (e : WithTop ℤ))
  have hrewrite : (1 + x) ^ p - 1 = x ^ p + (p : L) * S := by
    rw [add_pow_prime_eq' hp]
    simp [S]
    ring
  rw [chapter10MixedCharacteristicDepth]
  rw [hrewrite]
  have hbound := (min_le_min hxp hpS).trans (v.map_add _ _)
  by_cases h : e + n ≤ p * n
  · rw [min_eq_left h]
    have hcast : ((e + n : ℕ) : WithTop ℤ) ≤
        ((p * n : ℕ) : WithTop ℤ) := by
      exact_mod_cast h
    rw [min_eq_right hcast] at hbound
    exact hbound
  · have h' : p * n ≤ e + n := Nat.le_of_not_ge h
    rw [min_eq_right h']
    have hcast : ((p * n : ℕ) : WithTop ℤ) ≤
        ((e + n : ℕ) : WithTop ℤ) := by
      exact_mod_cast h'
    rw [min_eq_left hcast] at hbound
    exact hbound

/-- For large depths the linear term controls the minimum. -/
theorem chapter10_mixed_characteristic_linear_term_eventually_controls
    (p e : ℕ) (hp : 1 < p) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      chapter10MixedCharacteristicDepth e p n = e + n := by
  refine ⟨e, ?_⟩
  intro n hn
  apply min_eq_left
  have hp2 : 2 ≤ p := by omega
  have hpn : 2 * n ≤ p * n := Nat.mul_le_mul_right n hp2
  have hen : e + n ≤ n + n := by omega
  have h2n : n + n ≤ p * n := by simpa [two_mul] using hpn
  exact hen.trans h2n

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
  apply chapter10_mixed_characteristic_p_power_depth_estimate v p e n hp he x
  simpa [Chapter10AdditiveUnitDepth] using hx

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10
