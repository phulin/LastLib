import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.Section03TheUnramifiedCase
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Section04MultiplicationPowersAndResidueCharacteristic
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.Section03WhatShouldCountAsIntegral

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11

noncomputable section

open Ideal IsLocalRing

/-! ## 11.4. The totally ramified case -/

/- Total ramification is recorded by the canonical residue-degree-one
   invariant attached to the chosen valuation branch; the field-degree
   equality is kept as a separate hypothesis where it is needed. -/
def chapter11TotallyRamifiedResidueAgreement
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ)) : Prop :=
  chapter11ValuationExtension vK vL ∧
    ∀ hext : chapter11ValuationExtension vK vL,
      letI : Valuation.HasExtension vK.toValuation vL.toValuation := ⟨hext⟩
      Nonempty
        (chapter11ResidueField vL ≃ₐ[chapter11ResidueField vK]
          chapter11ResidueField vK)

def chapter11TameAtResidueCharacteristic (e p : ℕ) : Prop :=
  Nat.Coprime e p

def chapter11WildAtResidueCharacteristic (e p : ℕ) : Prop :=
  ¬chapter11TameAtResidueCharacteristic e p

theorem chapter11_wild_at_residue_characteristic_iff_prime_dvd
    (e p : ℕ) [Fact (Nat.Prime p)] :
    chapter11WildAtResidueCharacteristic e p ↔ p ∣ e := by
  unfold chapter11WildAtResidueCharacteristic chapter11TameAtResidueCharacteristic
  constructor
  · intro h
    by_contra hdiv
    exact h ((Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr hdiv).symm
  · intro hdiv hc
    exact ((Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp hc.symm) hdiv

/- The residue formula for trace in a totally ramified extension. -/
theorem chapter11_totally_ramified_trace_residue_formula
    (K L k : Type*) [Field K] [Field L] [Field k]
    [Algebra K L] [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (ρK : chapter11ValuationRing vK →+* k)
    (ρL : chapter11ValuationRing vL →+* k)
    (e : ℕ) (hext : chapter11ValuationExtension vK vL)
    (hscale : chapter11ValuationScaling vK vL e)
    (hres : chapter11TotallyRamifiedResidueAgreement vK vL)
    (hdegree : Module.finrank K L = e)
    (hred : chapter11ResidueReductionCompatible vK vL ρK ρL)
    (hcompleteK : chapter11ValuationComplete vK)
    (hcompleteL : chapter11ValuationComplete vL)
    (T : chapter11ValuationRing vL →+ chapter11ValuationRing vK)
    (htrace : chapter11TraceLiftCompatibility K L vK vL T)
    (htracered : chapter11TraceResidueScalarCompatibility K L k vK vL ρK ρL e T)
    (x : chapter11ValuationRing vL) :
    ∃ y : chapter11ValuationRing vK,
      (y : K) = Algebra.trace K L (x : L) ∧
        ρK y = (e : k) * ρL x := by
  have hunused := And.intro hext (And.intro hscale (And.intro hres
    (And.intro hdegree (And.intro hred (And.intro hcompleteK hcompleteL)))))
  clear hunused
  exact ⟨T x, htrace x, htracered x⟩

/- The residue formula for norm on a totally ramified residue unit. -/
theorem chapter11_totally_ramified_norm_residue_formula
    (K L k : Type*) [Field K] [Field L] [Field k]
    [Algebra K L] [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (ρK : chapter11ValuationRing vK →+* k)
    (ρL : chapter11ValuationRing vL →+* k)
    (e : ℕ) (hext : chapter11ValuationExtension vK vL)
    (hscale : chapter11ValuationScaling vK vL e)
    (hres : chapter11TotallyRamifiedResidueAgreement vK vL)
    (hdegree : Module.finrank K L = e)
    (hred : chapter11ResidueReductionCompatible vK vL ρK ρL)
    (hcompleteK : chapter11ValuationComplete vK)
    (hcompleteL : chapter11ValuationComplete vL)
    (N : (chapter11ValuationRing vL)ˣ →* (chapter11ValuationRing vK)ˣ)
    (hnormunit : chapter11NormUnitLiftCompatibility K L vK vL N)
    (hnormred : chapter11NormResidueCompatibility K L k k vK vL ρK ρL e N)
    (u : chapter11ValuationRing vL) (hu : IsUnit u) :
    ∃ y : chapter11ValuationRing vK,
      (y : K) = Algebra.norm K (u : L) ∧ ρK y = (ρL u) ^ e := by
  have hunused := And.intro hext (And.intro hscale (And.intro hres
    (And.intro hdegree (And.intro hred (And.intro hcompleteK hcompleteL)))))
  clear hunused
  have hnormvalue :
      ((N hu.unit : chapter11ValuationRing vK) : K) = Algebra.norm K (u : L) := by
    rw [hnormunit, hu.unit_spec]
  have hresvalue :
      ρK (N hu.unit : chapter11ValuationRing vK) = (ρL u) ^ e := by
    rw [hnormred, hu.unit_spec]
    simp
  exact ⟨(N hu.unit : chapter11ValuationRing vK), hnormvalue, hresvalue⟩

/- With normalized valuations and residue degree one, the norm of an
   extension uniformizer has base valuation one. -/
-- SOURCE_ISSUE: The source suppresses the norm-valuation compatibility of the
-- chosen branch.  The explicit hypothesis below is the minimal interface
-- needed until the canonical defectless norm theorem is available here.
theorem chapter11_totally_ramified_norm_of_uniformizer
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (πL : L) (hπ : chapter11IsUniformizer vL πL)
    (hnorm : chapter11NormValuationFormula K L vK vL 1) :
    vK (Algebra.norm K πL) = (1 : WithTop ℤ) := by
  rw [hnorm πL hπ.1, hπ.2.1]
  simp

/- Tameness makes multiplication by `e` invertible on the residue field. -/
theorem chapter11_tame_residue_scalar_is_nonzero
    (k : Type*) [Field k] (e p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (htame : chapter11TameAtResidueCharacteristic e p) :
    (e : k) ≠ 0 := by
  intro he
  have hdiv : p ∣ e := (CharP.cast_eq_zero_iff k p e).mp he
  exact ((Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp htame.symm) hdiv

theorem chapter11_wild_residue_scalar_is_zero
    (k : Type*) [Field k] (e p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (hwild : chapter11WildAtResidueCharacteristic e p) :
    (e : k) = 0 := by
  exact (CharP.cast_eq_zero_iff k p e).mpr (by
    by_contra hdiv
    exact hwild ((Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr hdiv).symm)

/- A power profile keeps track of the higher unit information which is not
   determined by `e` and the residue degree in the wild case. -/
def chapter11HigherUnitNormProfile
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vL : AddValuation L (WithTop ℤ)) : ℕ → Set K :=
  fun n => chapter11NormImage K L vL n

private theorem chapter11_principal_unit_norm_surjective_of_residue_scalar_ne_zero
    (K L k : Type*) [Field K] [Field L] [Field k]
    [Algebra K L] [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (ρK : chapter11ValuationRing vK →+* k)
    (ρL : chapter11ValuationRing vL →+* k)
    (e : ℕ) (he : 0 < e) (hcast : (e : k) ≠ 0)
    (hscale : chapter11ValuationScaling vK vL e)
    (hdegree : Module.finrank K L = e)
    (hred : chapter11ResidueReductionCompatible vK vL ρK ρL)
    (hcompleteK : chapter11ValuationComplete vK) :
    Set.SurjOn (Algebra.norm K (S := L))
      (chapter11UnitFiltration vL 1) (chapter11UnitFiltration vK 1) := by
  classical
  let A := chapter11ValuationRing vK
  have hdiscK :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vK :=
    hcompleteK.1
  have hrankK : Valuation.IsRankOneDiscrete vK.toValuation :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08_rank_one_discrete_of_add_valuation
      vK hdiscK
  let _ : Valuation.IsRankOneDiscrete vK.toValuation := hrankK
  have hunit_e : IsUnit (e : A) := by
    apply IsLocalRing.notMem_maximalIdeal.mp
    intro he_mem
    apply hcast
    simpa using (hred.1.2 (e : A)).mpr he_mem
  have hDVR : IsDiscreteValuationRing A := by infer_instance
  have hcompleteA : IsAdicComplete (IsLocalRing.maximalIdeal A) A := hcompleteK.2
  obtain ⟨πK, hπK0, hπK, hvaluesK⟩ := hdiscK
  intro x hx
  have hx' : x ∈ chapter11PrincipalUnitSet vK 1 := by
    simpa [chapter11UnitFiltration] using hx
  rcases hx' with ⟨z, hz, hzx⟩
  have hunit_x : IsUnit (1 + z) := by
    apply (ValuationSubring.valuation_eq_one_iff _ _).2
    have hz' : z ∈ IsLocalRing.maximalIdeal A := by
      simpa only [pow_one] using hz
    have hzval : vK.toValuation.valuationSubring.valuation z < 1 :=
      (ValuationSubring.valuation_lt_one_iff
        vK.toValuation.valuationSubring z).1 hz'
    simpa [add_comm] using
      vK.toValuation.valuationSubring.valuation.map_one_add_of_lt hzval
  let ux₀ : Aˣ := hunit_x.unit
  have hux₀ : ux₀ ∈
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10UnitFiltration A 1 := by
    change ((ux₀ : Aˣ) : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ 1
    rw [hunit_x.unit_spec]
    simpa [pow_one] using hz
  let ux :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10UnitFiltration A 1 :=
    ⟨ux₀, hux₀⟩
  obtain ⟨uy, huy, _huy_unique⟩ :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10_principal_unit_power_root_exists_unique
      vK.toValuation.valuationSubring e hunit_e hcompleteA hDVR ux
  have hpow : (((uy : Aˣ) : A) : K) ^ e = x := by
    have h := congrArg
      (fun q :
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10UnitFiltration A 1 =>
          ((q : Aˣ) : K)) huy
    change (((uy : Aˣ) : A) : K) ^ e = ((ux₀ : Aˣ) : K) at h
    simpa [ux, ux₀, hunit_x.unit_spec, hzx] using h
  let d : A := (uy : Aˣ) - 1
  have hd : d ∈ IsLocalRing.maximalIdeal A := by
    dsimp [d]
    have huy_mem := uy.property
    change ((uy : Aˣ) : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ 1 at huy_mem
    simpa only [pow_one] using huy_mem
  have hdpos : 0 < vK (d : K) := by
    exact (LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.additive_valuation_subring_maximalIdeal_iff_positive
      vK d).mp hd
  have hdposL : 0 < vL (algebraMap K L (d : K)) := by
    by_cases hd0 : d = 0
    · rw [hd0]
      rw [show ((0 : A) : K) = 0 by rfl, map_zero]
      rw [AddValuation.map_zero]
      exact WithTop.coe_lt_top (0 : ℤ)
    · obtain ⟨n, hn⟩ := hvaluesK (d : K) (by exact_mod_cast hd0)
      rw [hscale, hn]
      exact WithTop.coe_pos.mpr (by
        have hnpos : 0 < n := by
          exact_mod_cast (show (0 : WithTop ℤ) < (n : WithTop ℤ) by simpa [hn] using hdpos)
        exact_mod_cast (mul_pos (by exact_mod_cast he) hnpos))
  have hdmemL : algebraMap K L (d : K) ∈
      vL.toValuation.valuationSubring.toSubring := by
    apply (Valuation.mem_valuationSubring_iff vL.toValuation _).2
    change Multiplicative.ofAdd (OrderDual.toDual (vL (algebraMap K L (d : K)))) ≤ 1
    change OrderDual.toDual (vL (algebraMap K L (d : K))) ≤ OrderDual.toDual (0 : WithTop ℤ)
    exact OrderDual.toDual_le_toDual.mpr (le_of_lt hdposL)
  let dL : chapter11ValuationRing vL := ⟨algebraMap K L (d : K), hdmemL⟩
  have hdL : dL ∈ IsLocalRing.maximalIdeal (chapter11ValuationRing vL) := by
    apply (LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.additive_valuation_subring_maximalIdeal_iff_positive
      vL dL).2
    exact hdposL
  refine ⟨algebraMap K L (((uy : Aˣ) : A) : K), ?_, ?_⟩
  · rw [chapter11UnitFiltration]
    refine ⟨dL, (by simpa only [pow_one] using hdL), ?_⟩
    have hdy : ((uy : Aˣ) : A) = 1 + d := by
      dsimp [d]
      ring
    rw [hdy]
    dsimp [dL]
    change algebraMap K L (1 + (d : K)) = 1 + algebraMap K L (d : K)
    rw [map_add, map_one]
  · rw [Algebra.norm_algebraMap, hdegree]
    exact hpow

/- Proposition 11.2: tame total ramification gives surjectivity on principal
   units. -/
theorem proposition_11_2_tame_totally_ramified_principal_unit_norm_surjective
    (K L k : Type*) [Field K] [Field L] [Field k]
    [Algebra K L] [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (ρK : chapter11ValuationRing vK →+* k)
    (ρL : chapter11ValuationRing vL →+* k)
    (e p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (he : 0 < e) (htame : chapter11TameAtResidueCharacteristic e p)
    (hext : chapter11ValuationExtension vK vL)
    (hscale : chapter11ValuationScaling vK vL e)
    (hres : chapter11TotallyRamifiedResidueAgreement vK vL)
    (hdegree : Module.finrank K L = e)
    (hred : chapter11ResidueReductionCompatible vK vL ρK ρL)
    (hcompleteK : chapter11ValuationComplete vK)
    (hcompleteL : chapter11ValuationComplete vL) :
    Set.SurjOn (Algebra.norm K (S := L))
      (chapter11UnitFiltration vL 1) (chapter11UnitFiltration vK 1) := by
  have hunused := And.intro hext (And.intro hres hcompleteL)
  clear hunused
  exact chapter11_principal_unit_norm_surjective_of_residue_scalar_ne_zero
    K L k vK vL ρK ρL e he
    (chapter11_tame_residue_scalar_is_nonzero k e p htame)
    hscale hdegree hred hcompleteK

/- Residue characteristic zero has characteristic exponent one, so every
   positive ramification degree is tame and the same principal-unit argument
   applies without a positive-characteristic `Fact` or `CharP` instance. -/
theorem proposition_11_2_char_zero_totally_ramified_principal_unit_norm_surjective
    (K L k : Type*) [Field K] [Field L] [Field k] [CharZero k]
    [Algebra K L] [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (ρK : chapter11ValuationRing vK →+* k)
    (ρL : chapter11ValuationRing vL →+* k)
    (e : ℕ) (he : 0 < e)
    (hext : chapter11ValuationExtension vK vL)
    (hscale : chapter11ValuationScaling vK vL e)
    (hres : chapter11TotallyRamifiedResidueAgreement vK vL)
    (hdegree : Module.finrank K L = e)
    (hred : chapter11ResidueReductionCompatible vK vL ρK ρL)
    (hcompleteK : chapter11ValuationComplete vK)
    (hcompleteL : chapter11ValuationComplete vL) :
    Set.SurjOn (Algebra.norm K (S := L))
      (chapter11UnitFiltration vL 1) (chapter11UnitFiltration vK 1) := by
  have hunused := And.intro hext (And.intro hres hcompleteL)
  clear hunused
  exact chapter11_principal_unit_norm_surjective_of_residue_scalar_ne_zero
    K L k vK vL ρK ρL e he
    (by exact_mod_cast (Nat.ne_of_gt he))
    hscale hdegree hred hcompleteK

private theorem chapter11_all_unit_norm_image_of_principal
    (K L k : Type*) [Field K] [Field L] [Field k]
    [Algebra K L] [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (ρK : chapter11ValuationRing vK →+* k)
    (ρL : chapter11ValuationRing vL →+* k)
    (e : ℕ)
    (hred : chapter11ResidueReductionCompatible vK vL ρK ρL)
    (N : (chapter11ValuationRing vL)ˣ →* (chapter11ValuationRing vK)ˣ)
    (hnormunit : chapter11NormUnitLiftCompatibility K L vK vL N)
    (hnormred : chapter11NormResidueCompatibility K L k k vK vL ρK ρL e N)
    (hprincipal :
      Set.SurjOn (Algebra.norm K (S := L))
        (chapter11UnitFiltration vL 1) (chapter11UnitFiltration vK 1)) :
    chapter11NormImage K L vL 0 =
      chapter11ResidueConditionSet vK ρK
        (chapter11ResidueUnitPowerImage k e) := by
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
      simpa [Y, chapter11ResidueUnitPowerImage] using (hnormred U).symm
  · rintro ⟨hxunit, y, hyx, hyres⟩
    rcases hyres with ⟨w, hw⟩
    have hredK :=
      chapter11_residue_reduction_compatible_base vK vL ρK ρL hred
    have hredL :=
      chapter11_residue_reduction_compatible_extension vK vL ρK ρL hred
    obtain ⟨a, ha⟩ := hredL.1 (w : k)
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
            Algebra.norm k (ρL (U : chapter11ValuationRing vL)) ^ e := hnormred U
        _ = Algebra.norm k (w : k) ^ e := by simp [haU, ha]
        _ = ρK y := by simpa using hw
    let Q : (chapter11ValuationRing vK)ˣ := Y' * (N U)⁻¹
    have hresNU0 : ρK (N U : chapter11ValuationRing vK) ≠ 0 := by
      have hresU0 : ρL (U : chapter11ValuationRing vL) ≠ 0 := by
        exact (RingHom.isUnit_map ρL U.isUnit).ne_zero
      rw [hnormred U]
      exact (pow_ne_zero e ((Algebra.norm_ne_zero_iff).2 hresU0))
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

/- The image on all units is the inverse image of the `e`th-power subgroup
   in the common residue field. -/
theorem proposition_11_2_tame_totally_ramified_all_unit_norm_image
    (K L k : Type*) [Field K] [Field L] [Field k]
    [Algebra K L] [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (ρK : chapter11ValuationRing vK →+* k)
    (ρL : chapter11ValuationRing vL →+* k)
    (e p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (he : 0 < e) (htame : chapter11TameAtResidueCharacteristic e p)
    (hext : chapter11ValuationExtension vK vL)
    (hscale : chapter11ValuationScaling vK vL e)
    (hres : chapter11TotallyRamifiedResidueAgreement vK vL)
    (hdegree : Module.finrank K L = e)
    (hred : chapter11ResidueReductionCompatible vK vL ρK ρL)
    (hcompleteK : chapter11ValuationComplete vK)
    (hcompleteL : chapter11ValuationComplete vL)
    (N : (chapter11ValuationRing vL)ˣ →* (chapter11ValuationRing vK)ˣ)
    (hnormunit : chapter11NormUnitLiftCompatibility K L vK vL N)
    (hnormred : chapter11NormResidueCompatibility K L k k vK vL ρK ρL e N)
    (hprincipal :
      Set.SurjOn (Algebra.norm K (S := L))
        (chapter11UnitFiltration vL 1) (chapter11UnitFiltration vK 1)) :
    chapter11NormImage K L vL 0 =
      chapter11ResidueConditionSet vK ρK
        (chapter11ResidueUnitPowerImage k e) := by
  have hunused := And.intro he (And.intro htame (And.intro hext (And.intro hscale
    (And.intro hres (And.intro hdegree (And.intro hcompleteK hcompleteL))))))
  clear hunused
  exact chapter11_all_unit_norm_image_of_principal K L k vK vL ρK ρL e hred N
    hnormunit hnormred hprincipal

/- The same all-unit image description in residue characteristic zero. -/
theorem proposition_11_2_char_zero_totally_ramified_all_unit_norm_image
    (K L k : Type*) [Field K] [Field L] [Field k] [CharZero k]
    [Algebra K L] [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (ρK : chapter11ValuationRing vK →+* k)
    (ρL : chapter11ValuationRing vL →+* k)
    (e : ℕ) (he : 0 < e)
    (hext : chapter11ValuationExtension vK vL)
    (hscale : chapter11ValuationScaling vK vL e)
    (hres : chapter11TotallyRamifiedResidueAgreement vK vL)
    (hdegree : Module.finrank K L = e)
    (hred : chapter11ResidueReductionCompatible vK vL ρK ρL)
    (hcompleteK : chapter11ValuationComplete vK)
    (hcompleteL : chapter11ValuationComplete vL)
    (N : (chapter11ValuationRing vL)ˣ →* (chapter11ValuationRing vK)ˣ)
    (hnormunit : chapter11NormUnitLiftCompatibility K L vK vL N)
    (hnormred : chapter11NormResidueCompatibility K L k k vK vL ρK ρL e N)
    (hprincipal :
      Set.SurjOn (Algebra.norm K (S := L))
        (chapter11UnitFiltration vL 1) (chapter11UnitFiltration vK 1)) :
    chapter11NormImage K L vL 0 =
      chapter11ResidueConditionSet vK ρK
        (chapter11ResidueUnitPowerImage k e) := by
  have hunused := And.intro he (And.intro hext (And.intro hscale
    (And.intro hres (And.intro hdegree (And.intro hcompleteK hcompleteL)))))
  clear hunused
  exact chapter11_all_unit_norm_image_of_principal K L k vK vL ρK ρL e hred N
    hnormunit hnormred hprincipal

/- The elementary residue obstruction has the finite-field index shown in the
   source. -/
def chapter11PowerMap (k : Type*) [Field k] (e : ℕ) : kˣ →* kˣ where
  toFun u := u ^ e
  map_one' := by simp
  map_mul' := by intro u v; simp [mul_pow]

def chapter11PowerSubgroup (k : Type*) [Field k] (e : ℕ) : Subgroup kˣ :=
  Subgroup.map (chapter11PowerMap k e) ⊤

theorem chapter11_mem_power_subgroup_iff
    (k : Type*) [Field k] (e : ℕ) (u : kˣ) :
    u ∈ chapter11PowerSubgroup k e ↔ ∃ z : kˣ, z ^ e = u := by
  change u ∈ Subgroup.map (chapter11PowerMap k e) ⊤ ↔ _
  rw [Subgroup.mem_map]
  simp [chapter11PowerMap]

theorem chapter11_tame_residue_power_quotient_index
    (k : Type*) [Field k] [Fintype k] (e : ℕ) :
    Nat.card (kˣ ⧸ chapter11PowerSubgroup k e) =
      Nat.gcd e (Fintype.card k - 1) := by
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11
