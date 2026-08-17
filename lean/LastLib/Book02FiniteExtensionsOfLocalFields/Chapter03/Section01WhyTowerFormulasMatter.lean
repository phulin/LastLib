import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.Section01TheLocalExtensionProblem
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02.Section04TheFundamentalEquality
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
  sorry

theorem chapter03_complete_fundamental_equality
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL]
    [PerfectField (IsLocalRing.ResidueField vK.valuationSubring)]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring) :
    chapter03FundamentalEquality vK vL := by
  sorry

/-- Ramification indices and residue degrees multiply in a local tower. -/
theorem chapter03_tower_ramification_and_residue_laws
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (p : Ideal R) (q : Ideal S) (r : Ideal T)
    [p.IsPrime] [q.IsPrime] [r.IsPrime]
    [q.LiesOver p] [r.LiesOver q] [Module.Flat S T] :
    r.ramificationIdx R = q.ramificationIdx R * r.ramificationIdx S ∧
      r.inertiaDeg R = q.inertiaDeg R * r.inertiaDeg S := by
  sorry

/-- The vector-space degree identity in the same tower. -/
theorem chapter03_tower_degree_formula
    (K M L : Type*) [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L] :
    Module.finrank K L = Module.finrank K M * Module.finrank M L := by
  sorry

/-- The two normalized restriction factors compose along the tower. -/
theorem chapter03_restriction_factors_compose
    {K M L : Type*} [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L]
    (T : Chapter03NormalizedValuedTower K M L) (x : K) (hx : x ≠ 0) :
    T.vL (algebraMap K L x) = (T.eLM * T.eMK) • T.vK x := by
  sorry

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
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03
