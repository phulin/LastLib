import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.Section02LinearizingTheNorm
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter04.Section01WhyDiscretenessIsDecisive
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.Section03WhatShouldCountAsIntegral
import Mathlib.FieldTheory.Finite.GaloisField

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11

noncomputable section

open Ideal IsLocalRing
open scoped BigOperators

/-! ## 11.3. The unramified case -/

/- A uniformizer is represented by a generator of the maximal ideal of the
   canonical valuation ring. -/
def chapter11IsUniformizer {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (π : K) : Prop :=
  π ≠ 0 ∧ v π = (1 : WithTop ℤ) ∧ ∃ p : chapter11ValuationRing v,
    (p : K) = π ∧
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter04.Chapter04Uniformizer
        (chapter11ValuationRing v) p

/- Residue separability for the canonical residue-field algebra induced by a
   chosen valuation extension.  This is kept explicit because the valuation
   extension itself is a proposition rather than a typeclass. -/
def chapter11ResidueSeparableValuedExtension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ)) : Prop :=
  ∀ hext : chapter11ValuationExtension vK vL,
    letI : Valuation.HasExtension vK.toValuation vL.toValuation := ⟨hext⟩
    Algebra.IsSeparable (chapter11ResidueField vK) (chapter11ResidueField vL)

/- The unramified valued-extension interface includes normalization,
   completeness, and separable residue growth. -/
def chapter11UnramifiedValuedExtension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ)) : Prop :=
  chapter11ValuationExtension vK vL ∧
    chapter11ValuationScaling vK vL 1 ∧
    chapter11ValuationComplete vK ∧ chapter11ValuationComplete vL ∧
      chapter11ResidueSeparableValuedExtension vK vL

/- A common uniformizer is the same element under the base embedding. -/
def chapter11CommonUniformizer
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (πK : K) (πL : L) : Prop :=
  chapter11IsUniformizer vK πK ∧ chapter11IsUniformizer vL πL ∧
    πL = algebraMap K L πK

/- The residue-class condition used to describe all unit norms.  The residue
   map has domain the valuation ring, since arbitrary field elements need not
   have a residue. -/
def chapter11ResidueConditionSet
    {K k : Type*} [Field K] [Field k]
    (vK : AddValuation K (WithTop ℤ))
    (ρK : chapter11ValuationRing vK →+* k) (S : Set k) : Set K :=
  {x | x ∈ chapter11UnitSet vK ∧
    ∃ y : chapter11ValuationRing vK, (y : K) = x ∧ ρK y ∈ S}

theorem chapter11_mem_residue_condition_set_iff
    {K k : Type*} [Field K] [Field k]
    (vK : AddValuation K (WithTop ℤ))
    (ρK : chapter11ValuationRing vK →+* k) (S : Set k) (x : K) :
    x ∈ chapter11ResidueConditionSet vK ρK S ↔
      x ∈ chapter11UnitSet vK ∧
        ∃ y : chapter11ValuationRing vK, (y : K) = x ∧ ρK y ∈ S := Iff.rfl

/- The residue trace is the additive map on the graded layer. -/
theorem chapter11_unramified_residue_trace_surjective
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l] [Algebra.IsSeparable k l] :
    Function.Surjective (Algebra.trace k l) := by
  exact Algebra.trace_surjective k l

/- On the `n`th graded layer the norm is the residue trace.  The coefficient
   is stated using an arbitrary integral lift `c`, avoiding a noncanonical
   Teichmüller section in mixed characteristic. -/
theorem chapter11_unramified_norm_first_layer_congruence
    (K L k l : Type*) [Field K] [Field L] [Field k] [Field l]
    [Algebra K L] [Algebra k l] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [FiniteDimensional k l] [Algebra.IsSeparable k l]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (hunram : chapter11UnramifiedValuedExtension vK vL)
    (ρK : chapter11ValuationRing vK →+* k)
    (ρL : chapter11ValuationRing vL →+* l)
    (_hdegree : Module.finrank K L = Module.finrank k l)
    (_hred : chapter11ResidueReductionCompatible vK vL ρK ρL)
    (πK : K) (πL : L) (hπ : chapter11CommonUniformizer vK vL πK πL)
    (hnorm : chapter11NormValuationFormula K L vK vL (Module.finrank k l))
    (T : chapter11ValuationRing vL →+ chapter11ValuationRing vK)
    (htrace : chapter11TraceLiftCompatibility K L vK vL T)
    (htracered : chapter11TraceResidueCompatibility K L k l vK vL ρK ρL 1 T)
    (n : ℕ) (hn : 1 ≤ n) (a : chapter11ValuationRing vL) :
    ∃ c : chapter11ValuationRing vK,
      ρK c = Algebra.trace k l (ρL a) ∧
        chapter11UnitCongruence vK (n + 1)
          (Algebra.norm K (1 + (a : L) * πL ^ n))
          (1 + (c : K) * πK ^ n) := by
  rcases hπ with ⟨hπK, hπL, hπmap⟩
  rcases hπK with ⟨_, hπKv, ⟨pK, hpK, hpKgen⟩⟩
  rcases hπL with ⟨_, hπLv, ⟨pL, hpL, hpLgen⟩⟩
  let mK := IsLocalRing.maximalIdeal (chapter11ValuationRing vK)
  let mL := IsLocalRing.maximalIdeal (chapter11ValuationRing vL)
  have mem_power_of_value
      (v : AddValuation K (WithTop ℤ))
      (π : K) (p : chapter11ValuationRing v) (hp : (p : K) = π)
      (hπv : v π = 1)
      (hgen : LastLib.Book01ValuationsDVRsAndCompletions.Chapter04.Chapter04Uniformizer
        (chapter11ValuationRing v) p)
      (q : ℕ) {y : K} (hy : v y ≥ ((q : ℤ) : WithTop ℤ)) :
      ∃ z : chapter11ValuationRing v,
        z ∈ (IsLocalRing.maximalIdeal (chapter11ValuationRing v)) ^ q ∧
          (z : K) = y := by
    have hy_nonneg : (0 : WithTop ℤ) ≤ v y := by
      exact le_trans (by exact_mod_cast (Nat.zero_le q)) hy
    have hymem : y ∈ v.toValuation.valuationSubring.toSubring := by
      apply (Valuation.mem_valuationSubring_iff v.toValuation y).2
      change Multiplicative.ofAdd (OrderDual.toDual (v y)) ≤ 1
      change OrderDual.toDual (v y) ≤ OrderDual.toDual (0 : WithTop ℤ)
      exact OrderDual.toDual_le_toDual.mpr hy_nonneg
    by_cases hy0 : y = 0
    · exact ⟨0, by simp, hy0.symm⟩
    · have hy_sub0 : (⟨y, hymem⟩ : chapter11ValuationRing v) ≠ 0 := by
        intro hz
        apply hy0
        exact congrArg (fun z : chapter11ValuationRing v => (z : K)) hz
      obtain ⟨t, u, hu⟩ :=
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.discrete_additive_valuation_factorization
          v π hπv
          ⟨y, hymem⟩ hy_sub0
      have huval : v (u : K) = 0 := by
        have huone : v.toValuation (u : K) = 1 := by
          rw [(Valuation.isEquiv_valuation_valuationSubring v.toValuation).eq_one_iff_eq_one]
          exact (ValuationSubring.valuation_eq_one_iff _ _).1 u.isUnit
        simpa [AddValuation.toValuation_apply] using huone
      have hyt : v y = (t : WithTop ℤ) := by
        have hu' : y = π ^ t * (u : K) := by simpa using hu
        rw [hu', v.map_mul, v.map_pow, hπv, huval]
        simp
      have hqt : (q : ℤ) ≤ (t : ℤ) := by
        apply WithTop.coe_le_coe.mp
        simpa [hyt] using hy
      have hqt' : q ≤ t := by exact_mod_cast hqt
      have hp_mem : p ∈ IsLocalRing.maximalIdeal (chapter11ValuationRing v) := by
        rw [hgen.2]
        exact Ideal.subset_span (by simp)
      have hpt : p ^ t ∈ (IsLocalRing.maximalIdeal (chapter11ValuationRing v)) ^ t :=
        Ideal.pow_mem_pow hp_mem t
      have hpq : p ^ t ∈
          (IsLocalRing.maximalIdeal (chapter11ValuationRing v)) ^ q :=
        (Ideal.pow_le_pow_right hqt') hpt
      let z : chapter11ValuationRing v := p ^ t * (u : chapter11ValuationRing v)
      refine ⟨z, ?_, ?_⟩
      · dsimp [z]
        simpa [mul_comm] using
          (Ideal.mul_mem_left _ (u : chapter11ValuationRing v) hpq)
      · change ((p : K) ^ t) * (u : K) = y
        rw [hp]
        exact hu.symm
  have hpKmem : pK ∈ mK := by
    change pK ∈ IsLocalRing.maximalIdeal (chapter11ValuationRing vK)
    rw [hpKgen.2]
    exact Ideal.subset_span (by simp)
  have hpLmem : pL ∈ mL := by
    change pL ∈ IsLocalRing.maximalIdeal (chapter11ValuationRing vL)
    rw [hpLgen.2]
    exact Ideal.subset_span (by simp)
  have hxa : (a : L) * πL ^ n ∈
      chapter11ValuationIdealPowerSet vL n := by
    apply (chapter11_mem_valuation_ideal_power_set_iff vL n _).2
    refine ⟨a * pL ^ n, ?_, ?_⟩
    · exact Ideal.mul_mem_left _ a (Ideal.pow_mem_pow hpLmem n)
    · rw [← hpL]
      simp
  have hremval : vK (chapter11NormRemainder K L ((a : L) * πL ^ n)) ≥
      (2 : WithTop ℤ) * (n : WithTop ℤ) := by
    simpa [chapter11CeilDiv] using
      (chapter11_norm_remainder_has_depth K L vK vL 1 (Module.finrank k l) (by simp)
        hunram.1 hunram.2.1 hnorm hunram.2.2.1 hunram.2.2.2.1 n hn
        ((a : L) * πL ^ n) hxa)
  have h2n : ((n + 1 : ℕ) : WithTop ℤ) ≤
      (2 : WithTop ℤ) * (n : WithTop ℤ) := by
    have h2n_nat : n + 1 ≤ 2 * n := by omega
    have h2n_top : ((n + 1 : ℕ) : WithTop ℤ) ≤
        ((2 * n : ℕ) : WithTop ℤ) := by exact_mod_cast h2n_nat
    calc
      ((n + 1 : ℕ) : WithTop ℤ) ≤ ((2 * n : ℕ) : WithTop ℤ) := h2n_top
      _ = (2 : WithTop ℤ) * (n : WithTop ℤ) := by norm_cast
  have hremval' : vK (chapter11NormRemainder K L ((a : L) * πL ^ n)) ≥
      ((n + 1 : ℕ) : WithTop ℤ) := h2n.trans hremval
  have hremval'' : vK (chapter11NormRemainder K L ((a : L) * πL ^ n)) ≥
      (((n + 1 : ℕ) : ℤ) : WithTop ℤ) := by
    simpa using hremval'
  obtain ⟨r, hrmem, hr⟩ := mem_power_of_value vK
    πK pK hpK hπKv hpKgen (n + 1)
    (y := chapter11NormRemainder K L ((a : L) * πL ^ n)) hremval''
  let c : chapter11ValuationRing vK := T a
  have hcres : ρK c = Algebra.trace k l (ρL a) := by
    simpa [c] using htracered a
  refine ⟨c, hcres, ?_⟩
  have htrace_a : (c : K) = Algebra.trace K L (a : L) := by
    exact htrace a
  have htrace_x : Algebra.trace K L ((a : L) * πL ^ n) =
      (c : K) * πK ^ n := by
    calc
      Algebra.trace K L ((a : L) * πL ^ n) =
          Algebra.trace K L (algebraMap K L (πK ^ n) * (a : L)) := by
            rw [hπmap, map_pow]
            ring_nf
      _ = Algebra.trace K L ((πK ^ n) • (a : L)) := by
            rw [Algebra.smul_def]
      _ = (πK ^ n) • Algebra.trace K L (a : L) := by
            exact (Algebra.trace K L).map_smul _ _
      _ = (c : K) * πK ^ n := by
            rw [htrace_a]
            simp [smul_eq_mul, mul_comm]
  have hnorm_exp : Algebra.norm K (1 + (a : L) * πL ^ n) =
      1 + (c : K) * πK ^ n + (r : K) := by
    calc
      Algebra.norm K (1 + (a : L) * πL ^ n) =
          1 + Algebra.trace K L ((a : L) * πL ^ n) +
            chapter11NormRemainder K L ((a : L) * πL ^ n) :=
        chapter11_norm_one_add_linearizes_to_trace K L ((a : L) * πL ^ n)
      _ = 1 + (c : K) * πK ^ n + (r : K) := by
        rw [htrace_x, ← hr]
  unfold chapter11UnitCongruence
  rw [chapter11_unit_filtration_succ]
  let q : chapter11ValuationRing vK := 1 + c * pK ^ n
  have hpKpow : pK ^ n ∈ mK ^ n := Ideal.pow_mem_pow hpKmem n
  have hpKpow_mem : pK ^ n ∈ mK :=
    (Ideal.pow_le_self (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn))) hpKpow
  have hsmall : c * pK ^ n ∈ mK := Ideal.mul_mem_left _ c hpKpow_mem
  have hq_unit : IsUnit q := by
    apply (ValuationSubring.valuation_eq_one_iff _ _).2
    have hlt : vK.toValuation.valuationSubring.valuation (c * pK ^ n) < 1 :=
      (ValuationSubring.valuation_lt_one_iff
        vK.toValuation.valuationSubring (c * pK ^ n)).1 hsmall
    dsimp [q]
    simpa [add_comm] using
      vK.toValuation.valuationSubring.valuation.map_one_add_of_lt hlt
  let Q : (chapter11ValuationRing vK)ˣ := hq_unit.unit
  have hQ : (Q : chapter11ValuationRing vK) = q := hq_unit.unit_spec
  let d : chapter11ValuationRing vK :=
    r * ((Q⁻¹ : (chapter11ValuationRing vK)ˣ) : chapter11ValuationRing vK)
  have hd : d ∈ mK ^ (n + 1) := by
    dsimp [d]
    simpa [mK, mul_comm] using
      (Ideal.mul_mem_left _
        ((Q⁻¹ : (chapter11ValuationRing vK)ˣ) : chapter11ValuationRing vK) hrmem)
  have hq0 : (q : K) ≠ 0 := by
    rw [← hQ]
    exact_mod_cast (Units.ne_zero Q)
  have hden : (q : K) = 1 + (c : K) * πK ^ n := by
    simp [q, hpK]
  have hdfield : (d : K) = (r : K) / (q : K) := by
    dsimp [d]
    rw [div_eq_mul_inv]
    congr 1
    have hprod : (q : K) *
        ((((Q⁻¹ : (chapter11ValuationRing vK)ˣ) : chapter11ValuationRing vK) : K)) = 1 := by
      rw [← hQ]
      change (((((Q * Q⁻¹ : (chapter11ValuationRing vK)ˣ) :
        chapter11ValuationRing vK) : K))) = 1
      simp
    exact ((inv_eq_iff_eq_inv).2 (eq_inv_of_mul_eq_one_left hprod)).symm
  refine ⟨d, hd, ?_⟩
  rw [hnorm_exp]
  calc
    (1 + (c : K) * πK ^ n + (r : K)) *
        (1 + (c : K) * πK ^ n)⁻¹ =
        (1 + (c : K) * πK ^ n + (r : K)) / (q : K) := by
          rw [div_eq_mul_inv, hden]
    _ = 1 + (r : K) / (q : K) := by
      field_simp [hq0]
      rw [hden]
    _ = 1 + (d : K) := by rw [← hdfield]

/- Proposition 11.1: completeness and finite separable residue extension make
   the norm onto on all positive principal-unit layers. -/
theorem proposition_11_1_unramified_principal_unit_norm_surjective
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (hunram : chapter11UnramifiedValuedExtension vK vL)
    [Algebra (chapter11ResidueField vK) (chapter11ResidueField vL)]
    [FiniteDimensional (chapter11ResidueField vK) (chapter11ResidueField vL)]
    [Algebra.IsSeparable (chapter11ResidueField vK) (chapter11ResidueField vL)]
    (hdegree : Module.finrank K L =
      Module.finrank (chapter11ResidueField vK) (chapter11ResidueField vL))
    (hred : chapter11ResidueReductionCompatible vK vL
      (chapter11ResidueMap vK) (chapter11ResidueMap vL)) :
    Set.SurjOn (Algebra.norm K (S := L))
      (chapter11UnitFiltration vL 1) (chapter11UnitFiltration vK 1) := by
  sorry

/- The complete unit image is exactly the inverse image of the residue norm
   image. -/
theorem proposition_11_1_unramified_all_unit_norm_image
    (K L k l : Type*) [Field K] [Field L] [Field k] [Field l]
    [Algebra K L] [Algebra k l] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [FiniteDimensional k l] [Algebra.IsSeparable k l]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (_hunram : chapter11UnramifiedValuedExtension vK vL)
    (ρK : chapter11ValuationRing vK →+* k)
    (ρL : chapter11ValuationRing vL →+* l)
    (_hdegree : Module.finrank K L = Module.finrank k l)
    (hred : chapter11ResidueReductionCompatible vK vL ρK ρL)
    (N : (chapter11ValuationRing vL)ˣ →* (chapter11ValuationRing vK)ˣ)
    (hnormunit : chapter11NormUnitLiftCompatibility K L vK vL N)
    (hnormred : chapter11NormResidueCompatibility K L k l vK vL ρK ρL 1 N)
    (hprincipal :
      Set.SurjOn (Algebra.norm K (S := L))
        (chapter11UnitFiltration vL 1) (chapter11UnitFiltration vK 1)) :
    chapter11NormImage K L vL 0 =
      chapter11ResidueConditionSet vK ρK
        (chapter11ResidueUnitNormImage k l) := by
  ext x
  constructor
  · intro hx
    rcases (chapter11_mem_norm_image_iff K L vL 0 x).mp hx with ⟨u, hu, hnormu⟩
    have hu0 : u ∈ chapter11UnitSet vL := by
      simpa [chapter11UnitFiltration] using hu
    rcases hu0 with ⟨u0, hu0⟩
    let U : (chapter11ValuationRing vL)ˣ :=
      vL.toValuation.valuationSubring.unitGroupMulEquiv u0
    let Y : (chapter11ValuationRing vK)ˣ := N U
    have hUfield : ((U : chapter11ValuationRing vL) : L) = u := by
      exact (vL.toValuation.valuationSubring.coe_unitGroupMulEquiv_apply u0).trans hu0.symm
    have hY : ((Y : chapter11ValuationRing vK) : K) = x := by
      calc
        ((Y : chapter11ValuationRing vK) : K) =
            Algebra.norm K ((U : chapter11ValuationRing vL) : L) := hnormunit U
        _ = Algebra.norm K u := by rw [hUfield]
        _ = x := hnormu
    refine ⟨?_, ?_⟩
    · refine ⟨vK.toValuation.valuationSubring.unitGroupMulEquiv.symm Y, ?_⟩
      exact hY.symm.trans
        (vK.toValuation.valuationSubring.coe_unitGroupMulEquiv_symm_apply Y).symm
    · refine ⟨(Y : chapter11ValuationRing vK), hY, ?_⟩
      refine ⟨Units.map ρL U, ?_⟩
      symm
      simpa [Y] using hnormred U
  · rintro ⟨hxunit, y, hyx, hyres⟩
    rcases hyres with ⟨w, hw⟩
    have hredK :=
      chapter11_residue_reduction_compatible_base vK vL ρK ρL hred
    have hredL :=
      chapter11_residue_reduction_compatible_extension vK vL ρK ρL hred
    obtain ⟨a, ha⟩ := hredL.1 (w : l)
    have haw0 : ρL a ≠ 0 := by
      rw [ha]
      exact w.ne_zero
    have ha_notmax : a ∉ IsLocalRing.maximalIdeal (chapter11ValuationRing vL) := by
      intro hamax
      apply haw0
      exact (hredL.2 a).2 hamax
    have ha_val : vL.toValuation.valuationSubring.valuation a = 1 := by
      apply le_antisymm (vL.toValuation.valuationSubring.valuation_le_one a)
      exact le_of_not_gt (fun hlt =>
        ha_notmax ((ValuationSubring.valuation_lt_one_iff _ _).mpr hlt))
    have ha_unit : IsUnit a :=
      (ValuationSubring.valuation_eq_one_iff _ _).2 ha_val
    let U : (chapter11ValuationRing vL)ˣ := ha_unit.unit
    have haU : (U : chapter11ValuationRing vL) = a := by
      exact ha_unit.unit_spec
    rcases hxunit with ⟨Y, hYx⟩
    let Y' : (chapter11ValuationRing vK)ˣ :=
      vK.toValuation.valuationSubring.unitGroupMulEquiv Y
    have hYx' : x = (Y' : chapter11ValuationRing vK) := by
      exact hYx.trans
        (vK.toValuation.valuationSubring.coe_unitGroupMulEquiv_apply Y).symm
    have hyY : y = (Y' : chapter11ValuationRing vK) := by
      apply Subtype.ext
      simpa using hyx.trans hYx'
    have hresNU : ρK (N U : chapter11ValuationRing vK) = ρK y := by
      calc
        ρK (N U : chapter11ValuationRing vK) =
            Algebra.norm k (ρL (U : chapter11ValuationRing vL)) ^ 1 := hnormred U
        _ = Algebra.norm k (w : l) := by simp [haU, ha]
        _ = ρK y := by simpa using hw
    let Q : (chapter11ValuationRing vK)ˣ :=
      Y' * (N U)⁻¹
    have hresNU0 : ρK (N U : chapter11ValuationRing vK) ≠ 0 := by
      have hresU0 : ρL (U : chapter11ValuationRing vL) ≠ 0 := by
        exact (RingHom.isUnit_map ρL U.isUnit).ne_zero
      rw [hnormred U]
      simpa only [pow_one] using (Algebra.norm_ne_zero_iff).2 hresU0
    have hresQ : ρK (Q : chapter11ValuationRing vK) = 1 := by
      have hy0 : ρK y ≠ 0 := by
        rw [← hresNU]
        exact hresNU0
      have hQeq : (Q : chapter11ValuationRing vK) *
          (N U : chapter11ValuationRing vK) = (Y' : chapter11ValuationRing vK) := by
        simp [Q]
      have hcancel : ρK (Q : chapter11ValuationRing vK) *
          ρK (N U : chapter11ValuationRing vK) =
          ρK (Y' : chapter11ValuationRing vK) := by
        rw [← map_mul, hQeq]
      have hYres : ρK (Y' : chapter11ValuationRing vK) =
          ρK (N U : chapter11ValuationRing vK) := by
        rw [← hyY, hresNU]
      rw [hYres] at hcancel
      apply mul_right_cancel₀ hresNU0
      simpa using hcancel
    have hQmem : (Q : chapter11ValuationRing vK) - 1 ∈
        IsLocalRing.maximalIdeal (chapter11ValuationRing vK) := by
      apply (hredK.2 _).mp
      rw [map_sub, hresQ]
      simp
    have hratio : x / Algebra.norm K ((U : chapter11ValuationRing vL) : L) ∈
        chapter11UnitFiltration vK 1 := by
      change x / Algebra.norm K ((U : chapter11ValuationRing vL) : L) ∈
        chapter11PrincipalUnitSet vK 1
      refine ⟨(Q : chapter11ValuationRing vK) - 1,
        (by simpa only [pow_one] using hQmem), ?_⟩
      rw [hYx', ← hnormunit U]
      change ((Y' : chapter11ValuationRing vK) : K) /
          ((N U : chapter11ValuationRing vK) : K) =
        1 + (((Q : chapter11ValuationRing vK) : K) - 1)
      have hInvK : ((N U : chapter11ValuationRing vK) : K)⁻¹ =
          ((((N U)⁻¹ : (chapter11ValuationRing vK)ˣ) :
            chapter11ValuationRing vK) : K) := by
        have hprod : ((N U : chapter11ValuationRing vK) : K) *
            ((((N U)⁻¹ : (chapter11ValuationRing vK)ˣ) :
              chapter11ValuationRing vK) : K) = 1 := by
          change (((((N U) * (N U)⁻¹ :
            (chapter11ValuationRing vK)ˣ) : chapter11ValuationRing vK) : K)) = 1
          simp
        exact (inv_eq_iff_eq_inv).2 (eq_inv_of_mul_eq_one_left hprod)
      simp [Q, div_eq_mul_inv]
      exact hInvK
    rcases hprincipal hratio with ⟨z, hz, hnormz⟩
    have hz' : z ∈ chapter11PrincipalUnitSet vL 1 := by
      simpa [chapter11UnitFiltration] using hz
    rcases hz' with ⟨d, hd, hdz⟩
    have hzdunit : IsUnit (1 + d) := by
      apply (ValuationSubring.valuation_eq_one_iff _ _).2
      have hd' : d ∈ IsLocalRing.maximalIdeal (chapter11ValuationRing vL) := by
        simpa only [pow_one] using hd
      have hdl : vL.toValuation.valuationSubring.valuation d < 1 :=
        (ValuationSubring.valuation_lt_one_iff
          vL.toValuation.valuationSubring d).1 hd'
      simpa [add_comm] using
        vL.toValuation.valuationSubring.valuation.map_one_add_of_lt hdl
    let V : (chapter11ValuationRing vL)ˣ := hzdunit.unit
    have hVz : ((V : chapter11ValuationRing vL) : L) = z := by
      rw [hzdunit.unit_spec, hdz]
      simp
    let UV : (chapter11ValuationRing vL)ˣ := U * V
    refine (chapter11_mem_norm_image_iff K L vL 0 x).2 ⟨
      ((UV : chapter11ValuationRing vL) : L), ?_, ?_⟩
    · rw [chapter11UnitFiltration]
      refine ⟨vL.toValuation.valuationSubring.unitGroupMulEquiv.symm UV, ?_⟩
      exact (vL.toValuation.valuationSubring.coe_unitGroupMulEquiv_symm_apply UV).symm
    · have hUV : ((UV : chapter11ValuationRing vL) : L) =
          ((U : chapter11ValuationRing vL) : L) * z := by
        dsimp [UV]
        change ((U : chapter11ValuationRing vL) : L) *
          ((V : chapter11ValuationRing vL) : L) = _
        rw [hVz]
      rw [hUV, map_mul, hnormz]
      have hnormU0 : Algebra.norm K ((U : chapter11ValuationRing vL) : L) ≠ 0 := by
        rw [← hnormunit U]
        exact_mod_cast (N U).ne_zero
      field_simp

/- For finite residue fields, the norm is the exponent map displayed in the
   chapter and is surjective on nonzero residue classes. -/
theorem chapter11_finite_residue_norm_surjective
    (k l : Type*) [Field k] [Field l] [Algebra k l] [Finite l]
    [FiniteDimensional k l] :
    Function.Surjective (Algebra.norm k (S := l)) := by
  exact FiniteField.norm_surjective k l

theorem chapter11_finite_residue_norm_is_exponent_map
    (k l : Type*) [Field k] [Field l] [Algebra k l] [Finite l]
    [FiniteDimensional k l] (x : l) :
    algebraMap k l (Algebra.norm k x) =
      x ^ ((Nat.card l - 1) / (Nat.card k - 1)) := by
  exact FiniteField.algebraMap_norm_eq_pow

/- The valuation coordinate is the only obstruction for the full norm group
   in the finite-residue unramified case. -/
theorem chapter11_unramified_full_norm_image
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (πK : K) (f : ℕ)
    (hunram : chapter11UnramifiedValuedExtension vK vL)
    (hπ : chapter11IsUniformizer vK πK)
    (hnorm : chapter11NormValuationFormula K L vK vL f)
    (hdegree : Module.finrank K L = f)
    (hfres : f =
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree
        vK vL hunram.1)
    [Finite (chapter11ResidueField vK)]
    [Algebra (chapter11ResidueField vK) (chapter11ResidueField vL)]
    [FiniteDimensional (chapter11ResidueField vK) (chapter11ResidueField vL)]
    [Algebra.IsSeparable (chapter11ResidueField vK) (chapter11ResidueField vL)]
    (hred : chapter11ResidueReductionCompatible vK vL
      (chapter11ResidueMap vK) (chapter11ResidueMap vL))
    (N : (chapter11ValuationRing vL)ˣ →* (chapter11ValuationRing vK)ˣ)
    (hnormunit : chapter11NormUnitLiftCompatibility K L vK vL N)
    (hnormred : chapter11NormResidueCompatibility K L
      (chapter11ResidueField vK) (chapter11ResidueField vL) vK vL
      (chapter11ResidueMap vK) (chapter11ResidueMap vL)
      1 N) :
    {x : K | ∃ y : L, y ≠ 0 ∧ x = Algebra.norm K y} =
      chapter11ValueUnitProductSet vK πK f := by
  sorry

/- In the same hypotheses the norm subgroup has index `f` in `Kˣ`. -/
theorem chapter11_unramified_norm_subgroup_index
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (πK : K) (f : ℕ)
    (hunram : chapter11UnramifiedValuedExtension vK vL)
    (hπ : chapter11IsUniformizer vK πK)
    (hnorm : chapter11NormValuationFormula K L vK vL f)
    (hdegree : Module.finrank K L = f)
    (hfres : f =
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree
        vK vL hunram.1)
    [Finite (chapter11ResidueField vK)]
    [Algebra (chapter11ResidueField vK) (chapter11ResidueField vL)]
    [FiniteDimensional (chapter11ResidueField vK) (chapter11ResidueField vL)]
    [Algebra.IsSeparable (chapter11ResidueField vK) (chapter11ResidueField vL)]
    (hred : chapter11ResidueReductionCompatible vK vL
      (chapter11ResidueMap vK) (chapter11ResidueMap vL))
    (N : (chapter11ValuationRing vL)ˣ →* (chapter11ValuationRing vK)ˣ)
    (hnormunit : chapter11NormUnitLiftCompatibility K L vK vL N)
    (hnormred : chapter11NormResidueCompatibility K L
      (chapter11ResidueField vK) (chapter11ResidueField vL) vK vL
      (chapter11ResidueMap vK) (chapter11ResidueMap vL)
      1 N) :
    Nat.card (Kˣ ⧸ chapter11NormSubgroup K L) = f := by
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11
