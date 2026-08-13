import LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.Section01BoundedElements

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter03

open Set
open scoped BigOperators WithZero LaurentSeries PowerSeries

/-!
# Chapter 3: Valuation rings and divisibility

Mathlib uses multiplicative valuations, so bounded elements are written `v x ≤ 1`.
The additive convention in the book is recorded below with `AddValuation`; under the
usual sign change, `v x ≤ 1` is the same assertion as `0 ≤ v x`.
-/

universe u v w

/-! # Book 1, Chapter 3, Section 3.6: Residues and Leading Coefficients
-/

section ResiduesAndAngularComponents

variable {K : Type*} [Field K]

/-! ### 3.6. Residues and leading coefficients -/

/-- A discrete valuation normalized so that a uniformizer has value `exp (-1)`. -/
def IsUniformizerFor (v : Valuation K ℤᵐ⁰) (π : K) : Prop :=
  π ≠ 0 ∧ v π = WithZero.exp (-1 : ℤ)

/-- The integer value of a nonzero element for a `ℤᵐ⁰`-valued valuation. -/
def discreteUnitValue (v : Valuation K ℤᵐ⁰) (x : Kˣ) : ℤ :=
  -WithZero.log (v (x : K))

theorem discreteUnitValue_mul (v : Valuation K ℤᵐ⁰) (x y : Kˣ) :
    discreteUnitValue v (x * y) = discreteUnitValue v x + discreteUnitValue v y := by
  simp [discreteUnitValue, WithZero.log_mul]
  abel

theorem discreteUnitValue_inv (v : Valuation K ℤᵐ⁰) (x : Kˣ) :
    discreteUnitValue v x⁻¹ = -discreteUnitValue v x := by
  simp [discreteUnitValue]

/-- The normalized value-zero representative `π⁻ᵛ x`. -/
noncomputable def normalizedElement (v : Valuation K ℤᵐ⁰) (π : K)
    (hπ : IsUniformizerFor v π) (x : K) (hx : x ≠ 0) : valuationRingOf v := by
  refine ⟨π ^ (-discreteUnitValue v (Units.mk0 x hx)) * x, ?_⟩
  have hxv0 : v x ≠ 0 := v.ne_zero_iff.mpr hx
  apply (mem_valuationRingOf_iff v _).2
  rw [v.map_mul, map_zpow₀, hπ.2, ← WithZero.exp_zsmul,
    ← WithZero.exp_log hxv0]
  simp [discreteUnitValue]

theorem normalizedElement_isUnit (v : Valuation K ℤᵐ⁰) (π : K)
    (hπ : IsUniformizerFor v π) {x : K} (hx : x ≠ 0) :
    IsUnit (normalizedElement v π hπ x hx) := by
  apply (valuationRingOf_isUnit_iff v _).2
  dsimp [normalizedElement]
  rw [v.map_mul, map_zpow₀, hπ.2, ← WithZero.exp_zsmul,
    ← WithZero.exp_log (v.ne_zero_iff.mpr hx)]
  simp [discreteUnitValue]

/-- The angular component, with zero sent to zero. -/
noncomputable def angularComponent (v : Valuation K ℤᵐ⁰) (π : K)
    (hπ : IsUniformizerFor v π) (x : K) : residueFieldOf v := by
  classical
  exact if hx : x = 0 then 0 else
    residueMapOf v (normalizedElement v π hπ x hx)

theorem angularComponent_zero (v : Valuation K ℤᵐ⁰) (π : K)
    (hπ : IsUniformizerFor v π) : angularComponent v π hπ 0 = 0 := by
  unfold angularComponent
  simp

theorem discrete_uniformizer_decomposition (v : Valuation K ℤᵐ⁰) (π : K)
    (hπ : IsUniformizerFor v π) {x : K} (hx : x ≠ 0) :
    ∃! u : (valuationRingOf v)ˣ,
      x = π ^ discreteUnitValue v (Units.mk0 x hx) * ((u : valuationRingOf v) : K) := by
  classical
  let d := discreteUnitValue v (Units.mk0 x hx)
  let n : valuationRingOf v := normalizedElement v π hπ x hx
  have hnval : v (n : K) = 1 := by
    dsimp [n, normalizedElement]
    rw [v.map_mul, map_zpow₀, hπ.2, ← WithZero.exp_zsmul,
      ← WithZero.exp_log (v.ne_zero_iff.mpr hx)]
    simp [discreteUnitValue]
  have hnunit : IsUnit n := (valuationRingOf_isUnit_iff v n).2 hnval
  let u := hnunit.unit
  have hu : (u : valuationRingOf v) = n := IsUnit.unit_spec hnunit
  have hdecomp : x = π ^ d * (n : K) := by
    dsimp [n, normalizedElement]
    calc
      x = 1 * x := by simp
      _ = (π ^ d * π ^ (-d)) * x := by
        rw [← zpow_add₀ hπ.1, add_neg_cancel, zpow_zero]
      _ = π ^ d * (π ^ (-d) * x) := by ring
  refine ⟨u, ?_, ?_⟩
  · change x = π ^ d * ((u : valuationRingOf v) : K)
    rw [hu]
    exact hdecomp
  · intro u' hu'
    apply Units.ext
    apply Subtype.ext
    apply mul_left_cancel₀ (zpow_ne_zero _ hπ.1)
    calc
      π ^ d * ((u' : valuationRingOf v) : K) = x := by
        exact hu'.symm
      _ = π ^ d * (n : K) := hdecomp
      _ = π ^ d * ((u : valuationRingOf v) : K) := by rw [hu]

theorem angularComponent_eq_reduction_of_normalizedElement
    (v : Valuation K ℤᵐ⁰) (π : K) (hπ : IsUniformizerFor v π) {x : K} (hx : x ≠ 0) :
    angularComponent v π hπ x = residueMapOf v (normalizedElement v π hπ x hx) := by
  simp only [angularComponent, dif_neg hx]

theorem angularComponent_ne_zero (v : Valuation K ℤᵐ⁰) (π : K)
    (hπ : IsUniformizerFor v π) {x : K} (hx : x ≠ 0) :
    angularComponent v π hπ x ≠ 0 := by
  rw [angularComponent_eq_reduction_of_normalizedElement v π hπ hx]
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2
    (normalizedElement_isUnit v π hπ hx)

theorem angularComponent_mul (v : Valuation K ℤᵐ⁰) (π : K)
    (hπ : IsUniformizerFor v π) (x y : K) :
    angularComponent v π hπ (x * y) =
      angularComponent v π hπ x * angularComponent v π hπ y := by
  classical
  by_cases hx : x = 0
  · subst x
    simp [angularComponent_zero]
  by_cases hy : y = 0
  · subst y
    simp [angularComponent_zero]
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  have hunit : Units.mk0 (x * y) hxy = Units.mk0 x hx * Units.mk0 y hy := by
    apply Units.ext
    rfl
  have hnorm : normalizedElement v π hπ (x * y) hxy =
      normalizedElement v π hπ x hx * normalizedElement v π hπ y hy := by
    apply Subtype.ext
    dsimp [normalizedElement]
    rw [hunit, discreteUnitValue_mul, neg_add, zpow_add₀ hπ.1]
    ring
  rw [angularComponent_eq_reduction_of_normalizedElement v π hπ hxy,
    angularComponent_eq_reduction_of_normalizedElement v π hπ hx,
    angularComponent_eq_reduction_of_normalizedElement v π hπ hy,
    hnorm, map_mul]

noncomputable def residueUnitOf (v : Valuation K ℤᵐ⁰) (u : (valuationRingOf v)ˣ) :
    (residueFieldOf v)ˣ :=
  Units.map (residueMapOf v).toMonoidHom u

theorem angularComponent_parameter_change
    (v : Valuation K ℤᵐ⁰) (π : K) (hπ : IsUniformizerFor v π)
    (u : (valuationRingOf v)ˣ)
    (hπ' : IsUniformizerFor v (((u : valuationRingOf v) : K) * π))
    {x : K} (hx : x ≠ 0) :
    angularComponent v (((u : valuationRingOf v) : K) * π) hπ' x =
      (residueUnitOf v u) ^ (-discreteUnitValue v (Units.mk0 x hx)) *
        angularComponent v π hπ x := by
  classical
  let d := discreteUnitValue v (Units.mk0 x hx)
  have hpow :
      (((u : valuationRingOf v) : K) * π) ^ (-d) =
        ((u : valuationRingOf v) : K) ^ (-d) * π ^ (-d) := by
    let U : Kˣ := Units.map (algebraMap (valuationRingOf v) K).toMonoidHom u
    let P : Kˣ := Units.mk0 π hπ.1
    calc
      (((u : valuationRingOf v) : K) * π) ^ (-d) =
          ((U * P : Kˣ) : K) ^ (-d) := by rfl
      _ = (((U * P) ^ (-d) : Kˣ) : K) := by
        rw [Units.val_zpow_eq_zpow_val]
      _ = (((U ^ (-d) * P ^ (-d) : Kˣ) : Kˣ) : K) := by
        rw [mul_zpow]
      _ = ((u : valuationRingOf v) : K) ^ (-d) * π ^ (-d) := by
        have hU : (U : K) = ((u : valuationRingOf v) : K) := by
          rfl
        have hP : (P : K) = π := by
          rfl
        rw [Units.val_mul, Units.val_zpow_eq_zpow_val,
          Units.val_zpow_eq_zpow_val, hU, hP]
  have hnorm : normalizedElement v (((u : valuationRingOf v) : K) * π) hπ' x hx =
      ((u ^ (-d) : (valuationRingOf v)ˣ) : valuationRingOf v) *
        normalizedElement v π hπ x hx := by
    apply Subtype.ext
    dsimp [normalizedElement]
    have hu_pow :
        (((u ^ (-d) : (valuationRingOf v)ˣ) : valuationRingOf v) : K) =
          ((u : valuationRingOf v) : K) ^ (-d) := by
      let U : Kˣ := Units.map (algebraMap (valuationRingOf v) K).toMonoidHom u
      calc
        (((u ^ (-d) : (valuationRingOf v)ˣ) : valuationRingOf v) : K) =
            ((Units.map (algebraMap (valuationRingOf v) K).toMonoidHom
              (u ^ (-d) : (valuationRingOf v)ˣ) : Kˣ) : K) := by
          rfl
        _ = ((U ^ (-d) : Kˣ) : K) := by
          rw [map_zpow]
        _ = ((u : valuationRingOf v) : K) ^ (-d) := by
          rw [Units.val_zpow_eq_zpow_val]
          rw [show (U : K) = ((u : valuationRingOf v) : K) by rfl]
    rw [hpow, hu_pow]
    ring
  have hres : residueMapOf v
      (((u ^ (-d) : (valuationRingOf v)ˣ) : valuationRingOf v)) =
    (residueUnitOf v u : residueFieldOf v) ^ (-d) := by
    change
      (Units.map (residueMapOf v).toMonoidHom
          (u ^ (-d) : (valuationRingOf v)ˣ) : residueFieldOf v) =
        (Units.map (residueMapOf v).toMonoidHom u : residueFieldOf v) ^ (-d)
    rw [map_zpow, Units.val_zpow_eq_zpow_val]
  rw [angularComponent_eq_reduction_of_normalizedElement v _ hπ' hx,
    angularComponent_eq_reduction_of_normalizedElement v π hπ hx,
    hnorm, map_mul, hres]

/- A local associated-graded-symbol interface records the coordinate change above. -/

/- The parameter belongs to a coordinate presentation.  Omitting it would identify
   all residue coefficients of a fixed value after quotienting by units, and would
   therefore lose the leading term that the associated graded construction is meant
   to retain. -/
structure LeadingTermCoordinateData (v : Valuation K ℤᵐ⁰) where
  parameter : K
  parameter_isUniformizer : IsUniformizerFor v parameter
  value : ℤ
  residue : residueFieldOf v

def leadingTermCoordinateRelation (v : Valuation K ℤᵐ⁰)
    (p q : LeadingTermCoordinateData v) : Prop :=
  p.value = q.value ∧ ∃ u : (valuationRingOf v)ˣ,
    q.parameter = ((u : valuationRingOf v) : K) * p.parameter ∧
      q.residue = (residueUnitOf v u) ^ (-p.value) * p.residue

noncomputable def leadingTermCoordinateSetoid (v : Valuation K ℤᵐ⁰) :
    Setoid (LeadingTermCoordinateData v) :=
  { r := leadingTermCoordinateRelation v
    iseqv := by
      constructor
      · intro p
        refine ⟨rfl, 1, ?_, ?_⟩
        · simp
        · simp [residueUnitOf]
      · intro p q hpq
        rcases hpq with ⟨hpq_value, u, hpq_parameter, hpq_residue⟩
        refine ⟨hpq_value.symm, u⁻¹, ?_, ?_⟩
        · rw [hpq_parameter]
          have huinv :
              (((u⁻¹ : (valuationRingOf v)ˣ) : valuationRingOf v) : K) *
                  ((u : valuationRingOf v) : K) = 1 := by
            exact congrArg (fun z : valuationRingOf v => (z : K)) u.inv_val
          rw [← mul_assoc, huinv, one_mul]
        · rw [hpq_residue, ← hpq_value]
          have hu_residue : residueUnitOf v (u⁻¹) = (residueUnitOf v u)⁻¹ := by
            simp [residueUnitOf]
          have hu_residue_val :
              (residueUnitOf v (u⁻¹) : residueFieldOf v) =
                (residueUnitOf v u : residueFieldOf v)⁻¹ := by
            rw [hu_residue, Units.val_inv_eq_inv_val]
          rw [hu_residue_val, ← mul_assoc, ← mul_zpow]
          simp
      · intro p q r hpq hqr
        rcases hpq with ⟨hpq_value, u, hpq_parameter, hpq_residue⟩
        rcases hqr with ⟨hqr_value, w, hqr_parameter, hqr_residue⟩
        refine ⟨hpq_value.trans hqr_value, w * u, ?_, ?_⟩
        · rw [hqr_parameter, hpq_parameter]
          simp [mul_assoc]
        · rw [hqr_residue, hpq_residue, ← hpq_value]
          have hwu_residue : residueUnitOf v (w * u) =
              residueUnitOf v w * residueUnitOf v u := by
            simp [residueUnitOf]
          rw [hwu_residue, Units.val_mul]
          calc
            ((residueUnitOf v w : residueFieldOf v) ^ (-p.value) *
                ((residueUnitOf v u : residueFieldOf v) ^ (-p.value) *
                  p.residue)) =
                ((residueUnitOf v w : residueFieldOf v) ^ (-p.value) *
                  (residueUnitOf v u : residueFieldOf v) ^ (-p.value)) *
                  p.residue := by ring
            _ = ((residueUnitOf v w : residueFieldOf v) *
                (residueUnitOf v u : residueFieldOf v)) ^ (-p.value) *
                p.residue := by rw [mul_zpow] }

abbrev intrinsicLeadingTermClass (v : Valuation K ℤᵐ⁰) :=
  Quotient (leadingTermCoordinateSetoid v)

noncomputable def leadingTermCoordinate (v : Valuation K ℤᵐ⁰) (π : K)
    (hπ : IsUniformizerFor v π) (x : Kˣ) : LeadingTermCoordinateData v :=
  { parameter := π
    parameter_isUniformizer := hπ
    value := discreteUnitValue v x
    residue := angularComponent v π hπ (x : K) }

noncomputable def associatedGradedSymbol (v : Valuation K ℤᵐ⁰) (π : K)
    (hπ : IsUniformizerFor v π) (x : Kˣ) : intrinsicLeadingTermClass v :=
  Quotient.mk (leadingTermCoordinateSetoid v)
    (leadingTermCoordinate v π hπ x)

theorem associatedGradedSymbol_parameter_independent
    (v : Valuation K ℤᵐ⁰) (π₁ π₂ : K)
    (hπ₁ : IsUniformizerFor v π₁) (hπ₂ : IsUniformizerFor v π₂) (x : Kˣ) :
    associatedGradedSymbol v π₁ hπ₁ x = associatedGradedSymbol v π₂ hπ₂ x := by
  classical
  have hπ₁0 : π₁ ≠ 0 := hπ₁.1
  have hπ₂0 : π₂ ≠ 0 := hπ₂.1
  have hr0 : π₂ / π₁ ≠ 0 := div_ne_zero hπ₂0 hπ₁0
  have hrval : v (π₂ / π₁) = 1 := by
    rw [v.map_div, hπ₂.2, hπ₁.2]
    simp
  let rA : valuationRingOf v :=
    ⟨π₂ / π₁, (mem_valuationRingOf_iff v _).2 hrval.le⟩
  have hrunit : IsUnit rA :=
    (valuationRingOf_isUnit_iff v rA).2 (by simpa [rA] using hrval)
  let u := hrunit.unit
  have hu : ((u : valuationRingOf v) : K) = π₂ / π₁ := by
    have h := IsUnit.unit_spec hrunit
    exact congrArg Subtype.val h
  have hπrel : π₂ = ((u : valuationRingOf v) : K) * π₁ := by
    rw [hu]
    field_simp [hπ₁0]
  have hπ₂' : IsUniformizerFor v (((u : valuationRingOf v) : K) * π₁) := by
    rw [← hπrel]
    exact hπ₂
  apply Quotient.sound
  dsimp [associatedGradedSymbol, leadingTermCoordinate]
  refine ⟨rfl, u, hπrel, ?_⟩
  have hmk : Units.mk0 (x : K) x.ne_zero = x := by
    apply Units.ext
    rfl
  have hangle :
      angularComponent v π₂ hπ₂ (x : K) =
        angularComponent v (((u : valuationRingOf v) : K) * π₁) hπ₂' (x : K) := by
    simp only [hπrel]
  rw [hangle]
  simpa [hmk] using
    (angularComponent_parameter_change v π₁ hπ₁ u hπ₂' (x := (x : K)) x.ne_zero)

/- The Laurent-series realization: first nonzero coefficient and angular component. -/

noncomputable def laurentSeriesValuation (k : Type*) [Field k] :
    Valuation (LaurentSeries k) ℤᵐ⁰ :=
  Valued.v

noncomputable def laurentSeriesValuationRingEquiv (k : Type*) [Field k] :
    k⟦X⟧ ≃+* valuationRingOf (laurentSeriesValuation k) := by
  letI : IsLocalRing (valuationRingOf (laurentSeriesValuation k)) :=
    valuationRingOf_isLocal (laurentSeriesValuation k)
  let e : k⟦X⟧ →+* valuationRingOf (laurentSeriesValuation k) :=
    (HahnSeries.ofPowerSeries ℤ k).codRestrict
      (valuationRingOf (laurentSeriesValuation k)) (fun F =>
        (mem_valuationRingOf_iff (laurentSeriesValuation k)
          (F : LaurentSeries k)).2 (by
            simpa [laurentSeriesValuation] using
              (LaurentSeries.val_le_one_iff_eq_coe k (F : LaurentSeries k)).2 ⟨F, rfl⟩))
  apply RingEquiv.ofBijective e
  constructor
  · intro F G hFG
    apply PowerSeries.ext
    intro n
    have hFG' := congrArg
      (fun z : valuationRingOf (laurentSeriesValuation k) => (z : LaurentSeries k)) hFG
    simpa [e] using congrArg (fun z : LaurentSeries k => z.coeff n) hFG'
  · intro z
    have hz : Valued.v (z : LaurentSeries k) ≤ (1 : ℤᵐ⁰) := by
      simpa [laurentSeriesValuation] using
        (mem_valuationRingOf_iff (laurentSeriesValuation k)
          (z : LaurentSeries k)).mp z.property
    obtain ⟨F, hF⟩ := (LaurentSeries.val_le_one_iff_eq_coe k
      (z : LaurentSeries k)).mp hz
    refine ⟨F, ?_⟩
    apply Subtype.ext
    exact hF

noncomputable def laurentSeriesResidueEquiv (k : Type*) [Field k] :
    residueFieldOf (laurentSeriesValuation k) ≃+* k := by
  letI : IsLocalRing (valuationRingOf (laurentSeriesValuation k)) :=
    valuationRingOf_isLocal (laurentSeriesValuation k)
  exact (IsLocalRing.ResidueField.mapEquiv
    (laurentSeriesValuationRingEquiv k)).symm.trans
      PowerSeries.residueFieldOfPowerSeries

theorem laurentSeriesResidueEquiv_exists (k : Type*) [Field k] :
    Nonempty (residueFieldOf (laurentSeriesValuation k) ≃+* k) := by
  exact ⟨laurentSeriesResidueEquiv k⟩

theorem laurentSeries_value_is_first_nonzero_coefficient
    (k : Type*) [Field k] (f : LaurentSeries k) (hf : f ≠ 0) :
    ∃ N : ℤ, f.order = N ∧ f.coeff N ≠ 0 ∧
      (∀ n : ℤ, n < N → f.coeff n = 0) ∧
      laurentSeriesValuation k f = WithZero.exp (-N) := by
  classical
  refine ⟨f.order, rfl, ?_, ?_, ?_⟩
  · intro hzero
    exact hf ((HahnSeries.coeff_order_eq_zero).mp hzero)
  · intro n hn
    exact HahnSeries.coeff_eq_zero_of_lt_order hn
  · have hvne : laurentSeriesValuation k f ≠ 0 :=
      (Valuation.ne_zero_iff (laurentSeriesValuation k)).2 hf
    have hle : laurentSeriesValuation k f ≤ WithZero.exp (-f.order) := by
      apply (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero k).2
      exact fun n hn => HahnSeries.coeff_eq_zero_of_lt_order hn
    have hlog_le : WithZero.log (laurentSeriesValuation k f) ≤ -f.order := by
      apply (WithZero.exp_le_exp).mp
      rw [WithZero.exp_log hvne]
      exact hle
    have hlog_ge : -f.order ≤ WithZero.log (laurentSeriesValuation k f) := by
      apply le_of_not_gt
      intro hlt
      have hnext : WithZero.log (laurentSeriesValuation k f) ≤ -(f.order + 1) := by
        omega
      have hvalnext : laurentSeriesValuation k f ≤
          WithZero.exp (-(f.order + 1)) := by
        rw [← WithZero.exp_log hvne, WithZero.exp_le_exp]
        exact hnext
      have hcoeff :=
        (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero k).mp hvalnext
          f.order (by omega)
      exact (show f.coeff f.order ≠ 0 from by
        intro hzero
        exact hf ((HahnSeries.coeff_order_eq_zero).mp hzero)) hcoeff
    have hlog : WithZero.log (laurentSeriesValuation k f) = -f.order :=
      le_antisymm hlog_le hlog_ge
    rw [← WithZero.exp_log hvne, hlog]

noncomputable def laurentSeriesUniformizer (k : Type*) [Field k] : LaurentSeries k :=
  HahnSeries.single 1 1

theorem laurentSeriesUniformizer_isUniformizer (k : Type*) [Field k] :
    IsUniformizerFor (laurentSeriesValuation k) (laurentSeriesUniformizer k) := by
  refine ⟨HahnSeries.single_ne_zero one_ne_zero, ?_⟩
  simpa [laurentSeriesValuation, laurentSeriesUniformizer] using
    (LaurentSeries.valuation_single_zpow (K := k) (1 : ℤ))

theorem laurentSeries_angularComponent_is_first_coefficient
    (k : Type*) [Field k] {f : LaurentSeries k} (hf : f ≠ 0) :
    (laurentSeriesResidueEquiv k)
        (angularComponent (laurentSeriesValuation k)
          (laurentSeriesUniformizer k)
          (laurentSeriesUniformizer_isUniformizer k) f) =
      f.coeff f.order := by
  classical
  have hvalue := laurentSeries_value_is_first_nonzero_coefficient k f hf
  have hd : discreteUnitValue (laurentSeriesValuation k) (Units.mk0 f hf) = f.order := by
    unfold discreteUnitValue
    change -WithZero.log (laurentSeriesValuation k f) = f.order
    have hN : hvalue.choose = f.order := hvalue.choose_spec.1.symm
    have hval : laurentSeriesValuation k f = WithZero.exp (-f.order) := by
      calc
        laurentSeriesValuation k f = WithZero.exp (-hvalue.choose) :=
          hvalue.choose_spec.2.2.2
        _ = WithZero.exp (-f.order) := by rw [hN]
    rw [hval]
    simp
  let F0 : valuationRingOf (laurentSeriesValuation k) :=
    ⟨(f.powerSeriesPart : LaurentSeries k),
      (mem_valuationRingOf_iff (laurentSeriesValuation k)
        (f.powerSeriesPart : LaurentSeries k)).2 (by
          simpa [laurentSeriesValuation] using
            (LaurentSeries.val_le_one_iff_eq_coe k
              (f.powerSeriesPart : LaurentSeries k)).2
              ⟨f.powerSeriesPart, rfl⟩)⟩
  have hnorm :
      normalizedElement (laurentSeriesValuation k) (laurentSeriesUniformizer k)
        (laurentSeriesUniformizer_isUniformizer k) f hf = F0 := by
    apply Subtype.ext
    dsimp [normalizedElement]
    rw [hd, laurentSeriesUniformizer, ← RatFunc.single_zpow (F := k) (-f.order)]
    exact (LaurentSeries.ofPowerSeries_powerSeriesPart f).symm
  rw [angularComponent_eq_reduction_of_normalizedElement
    (laurentSeriesValuation k) (laurentSeriesUniformizer k)
    (laurentSeriesUniformizer_isUniformizer k) hf, hnorm]
  change PowerSeries.residueFieldOfPowerSeries
      ((IsLocalRing.ResidueField.mapEquiv (laurentSeriesValuationRingEquiv k)).symm
        (residueMapOf (laurentSeriesValuation k) F0)) = f.coeff f.order
  have hresidue :
      (IsLocalRing.ResidueField.mapEquiv (laurentSeriesValuationRingEquiv k)).symm
          (residueMapOf (laurentSeriesValuation k) F0) =
        IsLocalRing.residue k⟦X⟧ f.powerSeriesPart := by
    apply (IsLocalRing.ResidueField.mapEquiv
      (laurentSeriesValuationRingEquiv k)).injective
    calc
      (IsLocalRing.ResidueField.mapEquiv (laurentSeriesValuationRingEquiv k))
          ((IsLocalRing.ResidueField.mapEquiv
            (laurentSeriesValuationRingEquiv k)).symm
            (residueMapOf (laurentSeriesValuation k) F0)) =
          residueMapOf (laurentSeriesValuation k) F0 :=
        (IsLocalRing.ResidueField.mapEquiv
          (laurentSeriesValuationRingEquiv k)).apply_symm_apply _
      _ = (IsLocalRing.ResidueField.mapEquiv
          (laurentSeriesValuationRingEquiv k))
          (IsLocalRing.residue k⟦X⟧ f.powerSeriesPart) := by
        change residueMapOf (laurentSeriesValuation k) F0 =
          residueMapOf (laurentSeriesValuation k)
            (laurentSeriesValuationRingEquiv k f.powerSeriesPart)
        congr 1
  rw [hresidue]
  change
    ((Ideal.quotEquivOfEq (PowerSeries.ker_coeff_eq_max_ideal (k := k)).symm).trans
      (RingHom.quotientKerEquivOfSurjective PowerSeries.constantCoeff_surj))
        (Ideal.Quotient.mk _ f.powerSeriesPart) = f.coeff f.order
  simp only [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    LaurentSeries.powerSeriesPart_coeff]
  simp

/- The rational p-adic realization. -/

theorem padicResidueEquiv_exists (p : ℕ) [Fact p.Prime] :
    Nonempty (residueFieldOf (pValuation p) ≃+* ZMod p) := by
  exact pValuationResidueField_equiv_finiteField p

theorem pValuation_isUniformizer (p : ℕ) [Fact p.Prime] :
    IsUniformizerFor (pValuation p) (p : ℚ) := by
  refine ⟨?_, ?_⟩
  · exact_mod_cast (Fact.out : p.Prime).ne_zero
  · simp [pValuation]

noncomputable def padicResidueEquiv (p : ℕ) [Fact p.Prime] :
    residueFieldOf (pValuation p) ≃+* ZMod p :=
  letI : IsLocalRing (pValuationRing p) := valuationRingOf_isLocal (pValuation p)
  letI : (pPrimeIdeal p).IsMaximal := by
    change (Ideal.span ({(p : ℤ)} : Set ℤ)).IsMaximal
    infer_instance
  let e := pValuationRingEquiv p
  let q := IsLocalization.AtPrime.equivQuotMaximalIdeal
    (pPrimeIdeal p) (pLocalIntegers p)
  (IsLocalRing.ResidueField.mapEquiv e).trans
    (q.symm.trans (Int.quotientSpanNatEquivZMod p))

theorem padic_angularComponent_formula (p : ℕ) [Fact p.Prime]
    (n : ℤ) (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hpa : ¬ (p : ℤ) ∣ a) (hpb : ¬ (p : ℤ) ∣ b) :
    padicResidueEquiv p
        (angularComponent (pValuation p) (p : ℚ) (pValuation_isUniformizer p)
          (((p : ℚ) ^ n) * (a : ℚ) / (b : ℚ))) =
      (a : ZMod p) * (b : ZMod p)⁻¹ := by
  classical
  let hp := pValuation_isUniformizer p
  let : IsLocalRing (pValuationRing p) := valuationRingOf_isLocal (pValuation p)
  let : (pPrimeIdeal p).IsMaximal := by
    change (Ideal.span ({(p : ℤ)} : Set ℤ)).IsMaximal
    infer_instance
  let e := pValuationRingEquiv p
  let q := IsLocalization.AtPrime.equivQuotMaximalIdeal
    (pPrimeIdeal p) (pLocalIntegers p)
  let : Field (ℤ ⧸ pPrimeIdeal p) := Ideal.Quotient.field _
  have hres_int (z : ℤ) :
      padicResidueEquiv p
          (residueMapOf (pValuation p)
            (algebraMap ℤ (valuationRingOf (pValuation p)) z)) =
        (z : ZMod p) := by
    change (Int.quotientSpanNatEquivZMod p)
        (q.symm ((IsLocalRing.ResidueField.mapEquiv e)
          (residueMapOf (pValuation p)
            (algebraMap ℤ (valuationRingOf (pValuation p)) z)))) =
      (z : ZMod p)
    have hq : q.symm
        (IsLocalRing.residue (pLocalIntegers p)
          (algebraMap ℤ (pLocalIntegers p) z)) =
        Ideal.Quotient.mk (pPrimeIdeal p) z := by
      rw [IsLocalRing.residue_def,
        ← IsLocalization.mk'_one (M := (pPrimeIdeal p).primeCompl)
          (S := pLocalIntegers p) z]
      rw [IsLocalization.AtPrime.equivQuotMaximalIdeal_symm_apply_mk]
      change (Ideal.Quotient.mk (pPrimeIdeal p) z) *
          (Ideal.Quotient.mk (pPrimeIdeal p) (1 : ℤ))⁻¹ = _
      rw [map_one, inv_one, mul_one]
    rw [show (IsLocalRing.ResidueField.mapEquiv e)
          (residueMapOf (pValuation p)
            (algebraMap ℤ (valuationRingOf (pValuation p)) z)) =
          IsLocalRing.residue (pLocalIntegers p)
            (algebraMap ℤ (pLocalIntegers p) z) by
          change IsLocalRing.ResidueField.map (e :
              pValuationRing p →+* pLocalIntegers p)
              (IsLocalRing.residue (pValuationRing p)
              (algebraMap ℤ (pValuationRing p) z)) = _
          rw [IsLocalRing.ResidueField.map_residue]
          congr 1
          simp [e, pValuationRingEquiv]
          ]
    rw [hq]
    change (Int.quotientSpanNatEquivZMod p)
        (Ideal.Quotient.mk (Ideal.span ({(p : ℤ)} : Set ℤ)) z) =
      (z : ZMod p)
    exact congrArg (fun f : ℤ →+* ZMod p => f z)
      (Int.quotientSpanNatEquivZMod_comp_Quotient_mk p)
  have hp0 : (p : ℚ) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have ha0 : (a : ℚ) ≠ 0 := by
    exact_mod_cast ha
  have hb0 : (b : ℚ) ≠ 0 := by
    exact_mod_cast hb
  have hvp : pValuation p (p : ℚ) = WithZero.exp (-1 : ℤ) := by
    simp [pValuation]
  have hva : pValuation p (a : ℚ) = 1 := by
    change Rat.padicValuation p (a : ℚ) = 1
    rw [Rat.padicValuation_cast]
    exact Int.padicValuation_eq_one_iff.mpr hpa
  have hvb : pValuation p (b : ℚ) = 1 := by
    change Rat.padicValuation p (b : ℚ) = 1
    rw [Rat.padicValuation_cast]
    exact Int.padicValuation_eq_one_iff.mpr hpb
  let x : ℚ := ((p : ℚ) ^ n) * (a : ℚ) / (b : ℚ)
  have hx : x ≠ 0 := by
    dsimp [x]
    exact div_ne_zero (mul_ne_zero (zpow_ne_zero n hp0) ha0) hb0
  have hvx : pValuation p x = WithZero.exp (-n : ℤ) := by
    dsimp [x]
    rw [map_div₀, map_mul, map_zpow₀, hvp, hva, hvb]
    simp [← WithZero.exp_zsmul]
  have hd : discreteUnitValue (pValuation p) (Units.mk0 x hx) = n := by
    unfold discreteUnitValue
    change -WithZero.log (pValuation p x) = n
    rw [hvx]
    simp
  have hqval : pValuation p ((a : ℚ) / (b : ℚ)) = 1 := by
    rw [map_div₀, hva, hvb]
    simp
  let qA : valuationRingOf (pValuation p) :=
    ⟨(a : ℚ) / (b : ℚ), (mem_valuationRingOf_iff (pValuation p) _).2 hqval.le⟩
  have hbunit : IsUnit (algebraMap ℤ (valuationRingOf (pValuation p)) b) := by
    apply (valuationRingOf_isUnit_iff (pValuation p) _).2
    exact hvb
  let qinv : valuationRingOf (pValuation p) :=
    (((IsUnit.unit hbunit)⁻¹).val)
  have hqinv : (qinv : ℚ) = (b : ℚ)⁻¹ := by
    have h := congrArg (fun y : valuationRingOf (pValuation p) => (y : ℚ))
      (IsUnit.mul_val_inv hbunit)
    have h' : (b : ℚ) * (qinv : ℚ) = 1 := by
      change (b : ℚ) * (qinv : ℚ) = 1 at h
      exact h
    calc
      (qinv : ℚ) = (qinv : ℚ) * 1 := by rw [mul_one]
      _ = (qinv : ℚ) * ((b : ℚ) * (b : ℚ)⁻¹) := by
        rw [mul_inv_cancel₀ hb0]
      _ = ((b : ℚ) * (qinv : ℚ)) * (b : ℚ)⁻¹ := by ring
      _ = (1 : ℚ) * (b : ℚ)⁻¹ := by rw [h']
      _ = (b : ℚ)⁻¹ := by rw [one_mul]
  have hqrepr : qA =
      algebraMap ℤ (valuationRingOf (pValuation p)) a *
        qinv := by
    apply Subtype.ext
    dsimp [qA]
    change (a : ℚ) / (b : ℚ) = (a : ℚ) * (qinv : ℚ)
    rw [hqinv]
    field_simp [hb0]
  have hmap_inv :
      residueMapOf (pValuation p)
          qinv =
        (residueMapOf (pValuation p)
          (algebraMap ℤ (valuationRingOf (pValuation p)) b))⁻¹ := by
    change (residueMapOf (pValuation p)).toMonoidHom
        (((IsUnit.unit hbunit)⁻¹ : (valuationRingOf (pValuation p))ˣ) :
          valuationRingOf (pValuation p)) = _
    rw [map_units_inv]
    congr 1
  have hres_q :
      padicResidueEquiv p (residueMapOf (pValuation p) qA) =
        (a : ZMod p) * (b : ZMod p)⁻¹ := by
    calc
      padicResidueEquiv p (residueMapOf (pValuation p) qA) =
          padicResidueEquiv p
            (residueMapOf (pValuation p)
              (algebraMap ℤ (valuationRingOf (pValuation p)) a * qinv)) := by
        rw [hqrepr]
      _ = padicResidueEquiv p
          (residueMapOf (pValuation p)
            (algebraMap ℤ (valuationRingOf (pValuation p)) a) *
            residueMapOf (pValuation p) qinv) := by
        rw [map_mul, map_mul]
      _ = padicResidueEquiv p
          (residueMapOf (pValuation p)
            (algebraMap ℤ (valuationRingOf (pValuation p)) a)) *
            padicResidueEquiv p (residueMapOf (pValuation p) qinv) := by
        simp only [map_mul]
      _ = (a : ZMod p) * (b : ZMod p)⁻¹ := by
        rw [hmap_inv, map_inv₀, hres_int a, hres_int b]
  have hnorm :
      normalizedElement (pValuation p) (p : ℚ) hp x hx = qA := by
    apply Subtype.ext
    change (p : ℚ) ^ (-discreteUnitValue (pValuation p) (Units.mk0 x hx)) * x =
      (a : ℚ) / (b : ℚ)
    rw [hd]
    dsimp [x]
    calc
      (p : ℚ) ^ (-n) * ((p : ℚ) ^ n * (a : ℚ) / (b : ℚ)) =
          ((p : ℚ) ^ (-n) * (p : ℚ) ^ n) * ((a : ℚ) / (b : ℚ)) := by ring
      _ = (a : ℚ) / (b : ℚ) := by
        rw [← zpow_add₀ hp0, neg_add_cancel, zpow_zero, one_mul]
  have hangular :
      padicResidueEquiv p
          (angularComponent (pValuation p) (p : ℚ) hp x) =
        (a : ZMod p) * (b : ZMod p)⁻¹ := by
    rw [angularComponent_eq_reduction_of_normalizedElement
      (pValuation p) (p : ℚ) hp hx, hnorm]
    exact hres_q
  simpa [x] using hangular

end ResiduesAndAngularComponents

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter03
