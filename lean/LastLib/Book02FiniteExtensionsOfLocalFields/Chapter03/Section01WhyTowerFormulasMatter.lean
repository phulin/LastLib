import Mathlib
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03

noncomputable section

open Ideal
open scoped BigOperators WithZero
open LastLib.Book01ValuationsDVRsAndCompletions.Chapter12

/-! ## 3.1. Why tower formulas matter -/

/--
The normalized restriction relation used throughout this chapter.

The factor is recorded explicitly because normalized valuations on the two
fields need not restrict literally equally.
-/
abbrev chapter03ValuationRestrictionScale
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (e : ℕ) : Prop :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.chapter01ValuationRestrictionScale
    vK vL e

/-- A normalized-valued field tower, with the two restriction factors visible. -/
structure Chapter03NormalizedValuedTower
    (K M L : Type*) [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L] where
  vK : AddValuation K (WithTop ℤ)
  vM : AddValuation M (WithTop ℤ)
  vL : AddValuation L (WithTop ℤ)
  eMK : ℕ
  eLM : ℕ
  vK_discrete : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vK
  vM_discrete : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vM
  vL_discrete : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vL
  restrict_M_to_K : chapter03ValuationRestrictionScale vK vM eMK
  restrict_L_to_M : chapter03ValuationRestrictionScale vM vL eLM

/-! The following wrappers keep the normalized local invariants attached to
the chosen valuations.  In particular, `e` and `f` are not unconstrained
natural numbers whose product merely happens to be the field degree. -/

def chapter03RamificationIndex
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] : ℕ :=
  chapterRamificationIndex vK.valuationSubring vL.valuationSubring
    (IsLocalRing.maximalIdeal vL.valuationSubring)

def chapter03ResidueDegree
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] : ℕ :=
  chapterResidueDegree vK.valuationSubring vL.valuationSubring
    (IsLocalRing.maximalIdeal vL.valuationSubring)

structure Chapter03FiniteLocalExtensionData
    (K L Γ : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] where
  e : ℕ
  f : ℕ
  e_eq : chapter03RamificationIndex vK vL = e
  f_eq : chapter03ResidueDegree vK vL = f
  degree_eq : Module.finrank K L = e * f

/-- The chapter's field-level form of the fundamental equality. -/
def chapter03FundamentalEquality
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] : Prop :=
  Module.finrank K L = chapter03RamificationIndex vK vL * chapter03ResidueDegree vK vL

-- SOURCE_ISSUE: The source's unqualified complete-discrete fundamental
-- equality is false over general imperfect residue fields because finite
-- defect extensions exist.  The minimally corrected interface assumes a
-- perfect residue field (a defectless hypothesis would also suffice).
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
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02.fundamental_equality
    vK vL hcomplete

/--
The ramification and residue factors multiply in a finite local tower.  This
is stated without a separability hypothesis, using Mathlib's intrinsic ideal
invariants.
-/
theorem chapter03_tower_ramification_and_residue_laws
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (p : Ideal R) (q : Ideal S) (r : Ideal T)
    [p.IsPrime] [q.IsPrime] [r.IsPrime]
    [q.LiesOver p] [r.LiesOver q] [Module.Flat S T] :
    r.ramificationIdx R = q.ramificationIdx R * r.ramificationIdx S ∧
      r.inertiaDeg R = q.inertiaDeg R * r.inertiaDeg S := by
  constructor
  · exact
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11_ramification_indices_multiply_in_towers
        p q r
  · exact
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11_inertia_degrees_multiply_in_towers
        p q r

/-- The vector-space degree identity for the same tower. -/
theorem chapter03_tower_degree_formula
    (K M L : Type*) [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L] :
    Module.finrank K L = Module.finrank K M * Module.finrank M L := by
  simpa using
    (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11_field_degrees_multiply_in_towers
      K M L)

/-- The restriction formula along the two steps of a normalized tower. -/
theorem chapter03_restriction_factors_compose
    {K M L : Type*} [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L]
    (T : Chapter03NormalizedValuedTower K M L) (x : K) (hx : x ≠ 0) :
    T.vL (algebraMap K L x) = (T.eLM * T.eMK) • T.vK x := by
  rcases T.restrict_M_to_K with ⟨_, hMK⟩
  rcases T.restrict_L_to_M with ⟨_, hLM⟩
  have hay : algebraMap K M x ≠ 0 :=
    (algebraMap K M).injective.ne_zero hx
  calc
    T.vL (algebraMap K L x) =
        T.vL (algebraMap M L (algebraMap K M x)) := by
          rw [IsScalarTower.algebraMap_eq K M L x]
    _ = T.eLM • T.vM (algebraMap K M x) := hLM _ hay
    _ = T.eLM • (T.eMK • T.vK x) := by rw [hMK x hx]
    _ = (T.eLM * T.eMK) • T.vK x := by rw [smul_smul]

/--
The ideal-theoretic version of the tower formula.  The equalities are kept as
an explicit proposition so later proof passes can instantiate it with maximal
ideals of discrete valuation rings without losing the normalization powers.
-/
def chapter03IdealPowerTowerFormula
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (p : Ideal A) (q : Ideal B) (r : Ideal C)
    (eBC eAB eAC : ℕ) : Prop :=
  Ideal.map (algebraMap A C) p = r ^ eAC ∧
    Ideal.map (algebraMap B C) q = r ^ eBC ∧
    Ideal.map (algebraMap A C) p = (Ideal.map (algebraMap B C) q) ^ eAB ∧
    eAC = eBC * eAB

/--
The ring-level tower formula for finite extensions of local DVRs.  The
discrete-local hypotheses are intentionally explicit; no separability class
is required.
-/
theorem chapter03_ideal_power_tower_formula
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing C]
    [Module.Finite A B] [Module.Finite B C]
    [Module.Flat B C]
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
