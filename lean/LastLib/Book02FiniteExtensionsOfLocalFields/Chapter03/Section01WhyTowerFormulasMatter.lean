import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.Section01TheLocalExtensionProblem
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02.Section04TheFundamentalEquality
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section04RamificationIndexAndResidueDegree
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.Section09Towers

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03

noncomputable section

open Ideal
open scoped BigOperators TensorProduct WithZero
open LastLib.Book01ValuationsDVRsAndCompletions.Chapter12

/-! ## 3.1. Why tower formulas matter -/

/-- A tower with the normalized valuations and the two restriction factors. -/
structure Chapter03NormalizedValuedTower
    (K M L : Type*) [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L] [FiniteDimensional K M] [FiniteDimensional M L] where
  vK : AddValuation K (WithTop ℤ)
  vM : AddValuation M (WithTop ℤ)
  vL : AddValuation L (WithTop ℤ)
  eMK : ℕ
  eLM : ℕ
  vK_discrete :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vK
  vM_discrete :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vM
  vL_discrete :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vL
  restrict_M_to_K :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.chapter01ValuationRestrictionScale
      vK vM eMK
  restrict_L_to_M :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.chapter01ValuationRestrictionScale
      vM vL eLM

/-- Book-facing data recording the two local factors and their degree product. -/
structure Chapter03FiniteLocalExtensionData
    (K L Γ : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] where
  e : ℕ
  f : ℕ
  e_eq : chapterRamificationIndex vK.valuationSubring vL.valuationSubring
    (IsLocalRing.maximalIdeal vL.valuationSubring) = e
  f_eq : chapterResidueDegree vK.valuationSubring vL.valuationSubring
    (IsLocalRing.maximalIdeal vL.valuationSubring) = f
  degree_eq : Module.finrank K L = e * f

/-- The field-level form of the fundamental equality. -/
def chapter03FundamentalEquality
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] : Prop :=
  Module.finrank K L =
    chapterRamificationIndex vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) *
      chapterResidueDegree vK.valuationSubring vL.valuationSubring
        (IsLocalRing.maximalIdeal vL.valuationSubring)

theorem chapter03_fundamental_equality_iff_extension_data
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] :
    chapter03FundamentalEquality vK vL ↔
      Nonempty (Chapter03FiniteLocalExtensionData K L Γ vK vL) := by
  constructor
  · intro h
    refine ⟨⟨_, _, ?_, ?_, h⟩⟩
    · rfl
    · rfl
  · rintro ⟨d⟩
    have hdegree := d.degree_eq
    rw [← d.e_eq, ← d.f_eq] at hdegree
    exact hdegree

theorem chapter03_complete_fundamental_equality
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring) :
    chapter03FundamentalEquality vK vL := by
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02.fundamental_equality
    vK vL hcomplete

/-- Ramification indices and residue degrees multiply in a local tower. -/
theorem chapter03_tower_ramification_and_residue_laws
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (p : Ideal R) (q : Ideal S) (r : Ideal T)
    [p.IsPrime] [q.IsPrime] [r.IsPrime]
    [q.LiesOver p] [r.LiesOver q] [Module.Flat S T] :
    r.ramificationIdx R = q.ramificationIdx R * r.ramificationIdx S ∧
      r.inertiaDeg R = q.inertiaDeg R * r.inertiaDeg S := by
  exact ⟨
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11_ramification_indices_multiply_in_towers
      p q r,
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11_inertia_degrees_multiply_in_towers
      p q r⟩

/-- The vector-space degree identity in the same tower. -/
theorem chapter03_tower_degree_formula
    (K M L : Type*) [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L] :
    Module.finrank K L = Module.finrank K M * Module.finrank M L := by
  exact (Module.finrank_mul_finrank K M L).symm

/-- The two normalized restriction factors compose along the tower. -/
theorem chapter03_restriction_factors_compose
    {K M L : Type*} [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L]
    (T : Chapter03NormalizedValuedTower K M L) (x : K) (hx : x ≠ 0) :
    T.vL (algebraMap K L x) = (T.eLM * T.eMK) • T.vK x := by
  have hxm : algebraMap K M x ≠ 0 :=
    (map_ne_zero_iff (algebraMap K M)
      (FaithfulSMul.algebraMap_injective K M)).2 hx
  have hMK :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.chapter01_restriction_scale_apply
      T.vK T.vM T.eMK T.restrict_M_to_K hx
  have hLM :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.chapter01_restriction_scale_apply
      T.vM T.vL T.eLM T.restrict_L_to_M hxm
  rw [IsScalarTower.algebraMap_apply K M L x]
  rw [hLM, hMK]
  simp [smul_smul]

/-- The ideal-power form of the tower formula. -/
def chapter03IdealPowerTowerFormula
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (p : Ideal A) (q : Ideal B) (r : Ideal C)
    (eBC eAB eAC : ℕ) : Prop :=
  Ideal.map (algebraMap A C) p = r ^ eAC ∧
    Ideal.map (algebraMap B C) q = r ^ eBC ∧
    Ideal.map (algebraMap A C) p =
      (Ideal.map (algebraMap B C) q) ^ eAB ∧
    eAC = eBC * eAB

private theorem chapter03_dvr_maximalIdeal_map_eq_pow_ramificationIdx
    (A B : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [Algebra A B]
    [Algebra.IsIntegral A B] [Module.IsTorsionFree A B] [Module.Finite A B] :
    Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
      (IsLocalRing.maximalIdeal B) ^
        (IsLocalRing.maximalIdeal B).ramificationIdx A := by
  classical
  let m : Ideal A := IsLocalRing.maximalIdeal A
  let P : Ideal B := IsLocalRing.maximalIdeal B
  have hm0 : m ≠ (⊥ : Ideal A) := by
    exact IsDiscreteValuationRing.not_a_field A
  have hmap0 : Ideal.map (algebraMap A B) m ≠ (⊥ : Ideal B) :=
    Ideal.map_ne_bot_of_ne_bot hm0
  obtain ⟨n, hPn⟩ :=
    exists_maximalIdeal_pow_eq_of_principal B
      (IsPrincipalIdealRing.principal P)
      (Ideal.map (algebraMap A B) m) hmap0
  have hram : P.ramificationIdx A = n := by
    let _ : IsDiscreteValuationRing (Localization.AtPrime P) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B
        (IsDiscreteValuationRing.not_a_field B) (Localization.AtPrime P)
    rw [Ideal.ramificationIdx_eq m P]
    change (Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸
        Ideal.map (algebraMap A (Localization.AtPrime P)) m)).toNat = n
    have hPn' := congrArg
      (Ideal.map (algebraMap B (Localization.AtPrime P))) hPn
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq A B
      (Localization.AtPrime P), Ideal.map_pow,
      Localization.AtPrime.map_eq_maximalIdeal] at hPn'
    rw [hPn', IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
    rfl
  simpa [m, P, hram] using hPn

theorem chapter03_ideal_power_tower_formula
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing C]
    [Module.Finite A B] [Module.Finite B C]
    [Module.Flat A B] [Module.Flat B C]
    [Module.IsTorsionFree A C] [Module.IsTorsionFree B C]
    [Algebra.IsIntegral A B] [Algebra.IsIntegral B C]
    (p : Ideal A) (q : Ideal B) (r : Ideal C)
    [p.IsPrime] [q.IsPrime] [r.IsPrime]
    [q.LiesOver p] [r.LiesOver q]
    (hp : p = IsLocalRing.maximalIdeal A)
    (hq : q = IsLocalRing.maximalIdeal B)
    (hr : r = IsLocalRing.maximalIdeal C) :
    chapter03IdealPowerTowerFormula p q r
      (r.ramificationIdx B) (q.ramificationIdx A) (r.ramificationIdx A) := by
  let _ : Algebra.IsIntegral A C := Algebra.IsIntegral.trans B
  let _ : Module.Finite A C := Module.Finite.trans B C
  have hpC : Ideal.map (algebraMap A C) p =
      r ^ r.ramificationIdx A := by
    rw [hp, hr]
    exact chapter03_dvr_maximalIdeal_map_eq_pow_ramificationIdx A C
  have hqC : Ideal.map (algebraMap B C) q =
      r ^ r.ramificationIdx B := by
    rw [hq, hr]
    exact chapter03_dvr_maximalIdeal_map_eq_pow_ramificationIdx B C
  have htower : r.ramificationIdx A =
      q.ramificationIdx A * r.ramificationIdx B :=
    Ideal.ramificationIdx_tower q r
  have htower' : r.ramificationIdx A =
      r.ramificationIdx B * q.ramificationIdx A := by
    simpa [Nat.mul_comm] using htower
  refine ⟨hpC, hqC, ?_, htower'⟩
  calc
    Ideal.map (algebraMap A C) p = r ^ r.ramificationIdx A := hpC
    _ = r ^ (q.ramificationIdx A * r.ramificationIdx B) := by rw [htower]
    _ = (r ^ r.ramificationIdx B) ^ q.ramificationIdx A := by
      simpa [Nat.mul_comm] using
        (pow_mul r (r.ramificationIdx B) (q.ramificationIdx A))
    _ = (Ideal.map (algebraMap B C) q) ^ q.ramificationIdx A := by rw [hqC]

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03
