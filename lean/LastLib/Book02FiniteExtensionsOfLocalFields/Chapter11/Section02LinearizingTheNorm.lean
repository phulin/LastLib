import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.Section01TheLocalNormFiltration
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.Section03UniformizersAndMinimalPolynomials

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11

noncomputable section

open scoped BigOperators Polynomial
open Module

/-! ## 11.2. Linearizing the norm -/

/- The terms of degree at least two are represented by the exact remainder after
   subtracting the constant and trace terms. -/
def chapter11NormRemainder
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (x : L) : K :=
  Algebra.norm K (1 + x) - 1 - Algebra.trace K L x

/- The determinant identity is recorded at the coefficient level: the
   coefficient of degree one in `det(1 + X M)` is `tr(M)`. -/
theorem chapter11_det_one_add_has_trace_linear_coefficient
    (K : Type*) [CommRing K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) :
    (Matrix.det (1 + (Polynomial.X : K[X]) • M.map Polynomial.C)).coeff 1 =
      Matrix.trace M := by
  exact Matrix.coeff_det_one_add_X_smul_one M

/- The same coefficient calculation for multiplication by an element of a
   finite free algebra. -/
theorem chapter11_norm_determinant_has_trace_linear_coefficient
    (K L : Type*) [CommRing K] [CommRing L] [Algebra K L]
    [Module.Free K L] [Module.Finite K L]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L) (x : L) :
    (Matrix.det
        (1 + (Polynomial.X : K[X]) • (Algebra.leftMulMatrix b x).map Polynomial.C)).coeff 1 =
      Algebra.trace K L x := by
  simpa [Algebra.norm_eq_matrix_det b, Algebra.trace_eq_matrix_trace b] using
    chapter11_det_one_add_has_trace_linear_coefficient K (Algebra.leftMulMatrix b x)

/- The first-order norm expansion with its canonical higher-order remainder. -/
theorem chapter11_norm_one_add_linearizes_to_trace
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (x : L) :
    Algebra.norm K (1 + x) =
      1 + Algebra.trace K L x + chapter11NormRemainder K L x := by
  unfold chapter11NormRemainder
  ring

/- The omitted determinant terms have valuation at least `2n`, and restriction
   of an extension valuation turns that into the displayed ceiling bound. -/
theorem chapter11_norm_remainder_has_depth
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (e f : ℕ) (he : 0 < e)
    (hext : chapter11ValuationExtension vK vL)
    (hscale : chapter11ValuationScaling vK vL e)
    (hnorm : chapter11NormValuationFormula K L vK vL f)
    (hcompleteK : chapter11ValuationComplete vK)
    (hcompleteL : chapter11ValuationComplete vL)
    (n : ℕ) (hn : 1 ≤ n) (x : L)
    (hx : x ∈ chapter11ValuationIdealPowerSet vL n) :
    vK (chapter11NormRemainder K L x) ≥
      ((chapter11CeilDiv (2 * n) e : ℤ) : WithTop ℤ) := by
  sorry

/- Trace obeys the corresponding coarse depth bound. -/
theorem chapter11_trace_principal_ideal_depth_bound
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (e : ℕ) (he : 0 < e)
    (hext : chapter11ValuationExtension vK vL)
    (hscale : chapter11ValuationScaling vK vL e)
    (hcompleteK : chapter11ValuationComplete vK)
    (hcompleteL : chapter11ValuationComplete vL) (n : ℕ) (hn : 1 ≤ n) :
    chapter11TraceImage K L vL n ⊆
      chapter11ValuationIdealPowerSet vK (chapter11CeilDiv n e) := by
  classical
  let A := vK.toValuation.valuationSubring
  let B := vL.toValuation.valuationSubring
  let mA : Ideal A := IsLocalRing.maximalIdeal A
  let mB : Ideal B := IsLocalRing.maximalIdeal B
  have hdiscK :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vK :=
    hcompleteK.1
  have hdiscL :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vL :=
    hcompleteL.1
  have hrankK : Valuation.IsRankOneDiscrete vK.toValuation :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08_rank_one_discrete_of_add_valuation
      vK hdiscK
  have hrankL : Valuation.IsRankOneDiscrete vL.toValuation :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08_rank_one_discrete_of_add_valuation
      vL hdiscL
  let : Valuation.IsRankOneDiscrete vK.toValuation := hrankK
  let : Valuation.IsRankOneDiscrete vL.toValuation := hrankL
  let : Valuation.HasExtension vK.toValuation vL.toValuation := ⟨hext⟩
  let : Algebra A B :=
    Valuation.HasExtension.instAlgebra_valuationSubring
      vK.toValuation vL.toValuation
  have hstructure :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.finite_complete_extension_valuation_ring
      vK.toValuation vL.toValuation hcompleteK.2
  let : Module.Finite A B := hstructure.1
  let : Module.Free A B := hstructure.2.1
  let : IsDiscreteValuationRing B := hstructure.2.2.2.1
  let : IsIntegrallyClosed A :=
    Valuation.Integers.isIntegrallyClosed
      (Valuation.valuationSubring.integers vK.toValuation)
  let : IsIntegrallyClosed B := by infer_instance
  let : Algebra.IsIntegral A B := by infer_instance
  let : Module.IsTorsionFree A B := by infer_instance
  let : Field (A ⧸ mA) := Ideal.Quotient.field mA
  let : Field (B ⧸ mB) := Ideal.Quotient.field mB
  have htrace_mem (z : B) (hzmem : z ∈ mB) :
      Algebra.intTrace A B z ∈ mA := by
    have hresz :=
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11_finite_dvr_residue_trace_and_norm
        A B (A ⧸ mA) (B ⧸ mB) (IsLocalRing.residue A) (IsLocalRing.residue B)
        (by
          exact ⟨Ideal.Quotient.mk_surjective,
            fun x => IsLocalRing.residue_eq_zero_iff x⟩)
        (by
          exact ⟨Ideal.Quotient.mk_surjective,
            fun x => IsLocalRing.residue_eq_zero_iff x⟩)
        (by intro a; rfl) (mB.ramificationIdx A) z 0 rfl
    apply (IsLocalRing.residue_eq_zero_iff _).mp
    have hz := hresz.1
    change (IsLocalRing.residue A) (Algebra.intTrace A B z) =
      (mB.ramificationIdx A : A ⧸ mA) *
        Algebra.trace (A ⧸ mA) (B ⧸ mB) (Ideal.Quotient.mk mB z) at hz
    have hzres : Ideal.Quotient.mk mB z = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr hzmem
    rw [hzres, map_zero, mul_zero] at hz
    exact hz
  let : Algebra A L :=
    (algebraMap K L).comp (algebraMap A K) |>.toAlgebra
  have hAL_apply (a : A) : algebraMap A L a = algebraMap K L (a : K) := by
    rfl
  have hAL_applyB (a : A) :
      algebraMap A L a = algebraMap B L (algebraMap A B a) := by
    rw [hAL_apply]
    calc
      algebraMap K L (a : K) = ((algebraMap A B a : B) : L) :=
        (Valuation.HasExtension.coe_algebraMap_valuationSubring_eq
          vK.toValuation vL.toValuation a).symm
      _ = algebraMap B L (algebraMap A B a) := by rfl
  let : IsScalarTower A K L := by
    apply IsScalarTower.of_algebraMap_eq'
    ext a
    change algebraMap A L a = algebraMap K L (algebraMap A K a)
    rw [hAL_apply]
    rfl
  let : IsScalarTower A B L := by
    apply IsScalarTower.of_algebraMap_eq'
    ext a
    change algebraMap A L a = algebraMap B L (algebraMap A B a)
    exact hAL_applyB a
  let : IsFractionRing A K :=
    (Valuation.valuationSubring.integers vK.toValuation).isFractionRing
  let : IsFractionRing B L :=
    (Valuation.valuationSubring.integers vL.toValuation).isFractionRing
  have hintegralK : ∀ x : K, IsIntegral A x ↔ 0 ≤ vK x := by
    intro x
    constructor
    · intro hx
      obtain ⟨a, ha⟩ :=
        (IsIntegrallyClosed.isIntegral_iff (R := A)).mp hx
      have ha0 : 0 ≤ vK (a : K) := a.property
      have ha' : (a : K) = x := ha
      rw [ha'] at ha0
      exact ha0
    · intro hx
      apply (IsIntegrallyClosed.isIntegral_iff (R := A)).mpr
      exact ⟨⟨x, hx⟩, rfl⟩
  have hintegralL : ∀ x : L, IsIntegral B x ↔ 0 ≤ vL x := by
    intro x
    constructor
    · intro hx
      obtain ⟨a, ha⟩ :=
        (IsIntegrallyClosed.isIntegral_iff (R := B)).mp hx
      have ha0 : 0 ≤ vL (a : L) := a.property
      have ha' : (a : L) = x := ha
      rw [ha'] at ha0
      exact ha0
    · intro hx
      apply (IsIntegrallyClosed.isIntegral_iff (R := B)).mpr
      exact ⟨⟨x, hx⟩, rfl⟩
  have hdiscK' := hdiscK
  have hdiscL' := hdiscL
  obtain ⟨πK, hπK0, hπKv, hπKvalues⟩ := hdiscK'
  obtain ⟨πL, hπL0, hπLv, hπLvalues⟩ := hdiscL'
  let πA : A := ⟨πK, by change 0 ≤ vK πK; rw [hπKv]; simp⟩
  let πB : B := ⟨πL, by change 0 ≤ vL πL; rw [hπLv]; simp⟩
  have hπAval : vK (algebraMap A K πA) = 1 := by
    simpa [πA] using hπKv
  have hπBval : vL (algebraMap B L πB) = 1 := by
    simpa [πB] using hπLv
  have hmaxA : mA = Ideal.span ({πA} : Set A) := by
    exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08_value_one_generates_maximal_ideal
      vK hdiscK hintegralK πA hπAval
  have hmaxB : mB = Ideal.span ({πB} : Set B) := by
    exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08_value_one_generates_maximal_ideal
      vL hdiscL hintegralL πB hπBval
  have hπBirr : Irreducible πB :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer πB).2 hmaxB
  have hmap_ne_zero : algebraMap A B πA ≠ 0 := by
    intro hzero
    apply hπK0
    have hzeroL := congrArg (fun z : B => (z : L)) hzero
    have hzeroK : algebraMap K L πK = 0 := by
      calc
        algebraMap K L πK = ((algebraMap A B πA : B) : L) := by
          symm
          exact Valuation.HasExtension.coe_algebraMap_valuationSubring_eq
            vK.toValuation vL.toValuation πA
        _ = 0 := hzeroL
    apply FaithfulSMul.algebraMap_injective K L
    simpa using hzeroK
  obtain ⟨k, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hmap_ne_zero hπBirr
  have huval : vL (u : L) = 0 := by
    have hu' := (Valuation.valuationSubring.integers vL.toValuation).valuation_unit u
    change vL (u : L) = 0 at hu'
    exact hu'
  have hmapval : vL (algebraMap A B πA : L) = (e : WithTop ℤ) := by
    rw [Valuation.HasExtension.coe_algebraMap_valuationSubring_eq]
    rw [hscale πK, hπKv]
    simp
  have hk : k = e := by
    have hval := congrArg (fun z : B => vL (z : L)) hu
    change vL ((algebraMap A B πA : B) : L) =
      vL ((u : L) * (πB : L) ^ k) at hval
    have hπBval' : vL (πB : L) = 1 := by
      simpa using hπBval
    rw [hmapval, vL.map_mul, vL.map_pow, huval, hπBval'] at hval
    simpa using hval.symm
  have hmap : algebraMap A B πA = (u : B) * πB ^ e := by
    simpa [hk] using hu
  let r : ℕ := chapter11CeilDiv n e
  have hrpos : 0 < r := by
    have hnle : n ≤ e * r := by
      simpa [r, chapter11CeilDiv] using (le_smul_ceilDiv he : n ≤ e • (n ⌈/⌉ e))
    by_contra hr
    have hr0 : r = 0 := Nat.eq_zero_of_not_pos hr
    rw [hr0] at hnle
    omega
  have hprev : e * (r - 1) < n := by
    by_contra hbad
    have hbad' : n ≤ e * (r - 1) := Nat.le_of_not_gt hbad
    have hceil : n ⌈/⌉ e ≤ r - 1 :=
      (ceilDiv_le_iff_le_mul he).2 hbad'
    have : r ≤ r - 1 := by simpa [r, chapter11CeilDiv] using hceil
    omega
  have hqpos : 0 < n - e * (r - 1) := Nat.sub_pos_of_lt hprev
  have hqadd : e * (r - 1) + (n - e * (r - 1)) = n :=
    Nat.add_sub_of_le hprev.le
  intro x hx
  rcases hx with ⟨y, hy, hxy⟩
  rcases (chapter11_mem_valuation_ideal_power_set_iff vL n y).mp hy with
    ⟨z, hz, rfl⟩
  by_cases hz0 : z = 0
  · subst z
    have hx0 : x = 0 := by simpa using hxy.symm
    subst x
    exact ⟨0, by simp, by simp⟩
  have hzspan : z ∈ Ideal.span ({πB ^ n} : Set B) := by
    change z ∈ mB ^ n at hz
    simpa [hmaxB, Ideal.span_singleton_pow] using hz
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hzspan
  let w : B :=
    ((u⁻¹ : Bˣ) : B) ^ (r - 1) * πB ^ (n - e * (r - 1)) * c
  have hw : w ∈ mB := by
    have hπBmem : πB ∈ mB := by
      rw [hmaxB]
      exact Ideal.subset_span (by simp)
    have hπBpow : πB ^ (n - e * (r - 1)) ∈ mB :=
      (Ideal.pow_le_self (Nat.ne_of_gt hqpos))
        (Ideal.pow_mem_pow hπBmem (n - e * (r - 1)))
    have hmul := Ideal.mul_mem_left mB
      (((u⁻¹ : Bˣ) : B) ^ (r - 1) * c) hπBpow
    dsimp only [w]
    rw [mul_assoc, mul_comm (πB ^ (n - e * (r - 1))) c, ← mul_assoc]
    exact hmul
  have hid : (z : L) =
      algebraMap K L (algebraMap A K (πA ^ (r - 1))) * (w : L) := by
    have hidB : πB ^ n * c =
        ((u : B) * πB ^ e) ^ (r - 1) * w := by
      dsimp only [w]
      rw [mul_pow, ← pow_mul]
      have hu_cancel :
          (u : B) ^ (r - 1) * ((u⁻¹ : Bˣ) : B) ^ (r - 1) = 1 := by
        rw [← mul_pow]
        simp
      have hreorder :
          (u : B) ^ (r - 1) * πB ^ (e * (r - 1)) *
              (((u⁻¹ : Bˣ) : B) ^ (r - 1) *
                πB ^ (n - e * (r - 1)) * c) =
            ((u : B) ^ (r - 1) * ((u⁻¹ : Bˣ) : B) ^ (r - 1)) *
              (πB ^ (e * (r - 1)) * πB ^ (n - e * (r - 1))) * c := by
        ring
      rw [hreorder, hu_cancel, one_mul, ← pow_add, hqadd]
    have hbase : algebraMap K L (algebraMap A K (πA ^ (r - 1))) =
        ((algebraMap A B πA : B) : L) ^ (r - 1) := by
      calc
        algebraMap K L (algebraMap A K (πA ^ (r - 1))) =
            algebraMap A L (πA ^ (r - 1)) := by
              rw [hAL_apply]
              exact congrArg (algebraMap K L) (by rfl)
        _ = algebraMap A L πA ^ (r - 1) := by rw [map_pow]
        _ = ((algebraMap A B πA : B) : L) ^ (r - 1) := by
          rw [hAL_applyB]
          exact congrArg (fun q : L => q ^ (r - 1)) (by rfl)
    rw [hc, hbase, hmap]
    exact congrArg (fun q : B => (q : L)) hidB
  have hinter_trace (z : B) :
      algebraMap A K (Algebra.intTrace A B z) =
        Algebra.trace K L (algebraMap B L z) :=
    Algebra.algebraMap_intTrace (L := L) z
  have hfieldtrace :
      Algebra.trace K L (z : L) =
        algebraMap A K (πA ^ (r - 1) * Algebra.intTrace A B w) := by
    calc
      Algebra.trace K L (z : L) =
          Algebra.trace K L
            (algebraMap K L (algebraMap A K (πA ^ (r - 1))) * (w : L)) := by
        rw [hid]
      _ = Algebra.trace K L
          ((algebraMap A K (πA ^ (r - 1))) • (w : L)) := by
        rw [Algebra.smul_def]
      _ = (algebraMap A K (πA ^ (r - 1))) •
          Algebra.trace K L (w : L) := by
        exact (Algebra.trace K L).map_smul _ _
      _ = algebraMap A K (πA ^ (r - 1)) *
          algebraMap A K (Algebra.intTrace A B w) := by
        rw [hinter_trace]
        simp [smul_eq_mul]
      _ = algebraMap A K (πA ^ (r - 1) * Algebra.intTrace A B w) := by
        exact ((algebraMap A K).map_mul _ _).symm
  have hπAmem : πA ∈ mA := by
    rw [hmaxA]
    exact Ideal.subset_span (by simp)
  have hprod : πA ^ (r - 1) * Algebra.intTrace A B w ∈ mA ^ r := by
    have hmul := Ideal.mul_mem_mul
      (Ideal.pow_mem_pow hπAmem (r - 1)) (htrace_mem w hw)
    have hrpow : mA ^ (r - 1) * mA = mA ^ r := by
      calc
        mA ^ (r - 1) * mA = mA ^ ((r - 1) + 1) :=
          (pow_succ mA (r - 1)).symm
        _ = mA ^ r := by
          apply congrArg (fun t : ℕ => mA ^ t)
          exact Nat.sub_add_cancel (Nat.succ_le_of_lt hrpos)
    rw [← hrpow]
    exact hmul
  change x ∈ chapter11ValuationIdealPowerSet vK r
  refine (chapter11_mem_valuation_ideal_power_set_iff vK r x).2
    ⟨πA ^ (r - 1) * Algebra.intTrace A B w, hprod, ?_⟩
  exact hxy.symm.trans hfieldtrace

/- Inseparability can make the trace map vanish; this is the precise caveat
   behind the separability hypothesis in first-layer lifting. -/
theorem chapter11_trace_vanishes_for_nonseparable_extension
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (hsep : ¬Algebra.IsSeparable K L) :
    Algebra.trace K L = 0 := by
  exact Algebra.trace_eq_zero_of_not_isSeparable hsep

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11
