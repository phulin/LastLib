import Mathlib
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter11
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03

noncomputable section

open Ideal
open scoped BigOperators

/-! ## 3.1. Why tower formulas matter -/

/--
The normalized restriction relation used throughout this chapter.

The factor is recorded explicitly because normalized valuations on the two
fields need not restrict literally equally.
-/
def chapter03ValuationRestrictionScale
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (e : ℕ) : Prop :=
  ∀ x : K, vL (algebraMap K L x) = e • vK x

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

/--
The local numerical data attached to a finite extension.  The degree equation
is included as the fundamental equality; the `e` and `f` fields are reserved
for the normalized ramification index and residue degree.
-/
structure Chapter03FiniteLocalExtensionData
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] where
  e : ℕ
  f : ℕ
  degree_eq : Module.finrank K L = e * f

/-- The chapter's field-level form of the fundamental equality. -/
def chapter03FundamentalEquality
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (data : Chapter03FiniteLocalExtensionData K L) : Prop :=
  Module.finrank K L = data.e * data.f

/--
The ramification and residue factors multiply in a finite local tower.  This
is stated without a separability hypothesis, using Mathlib's intrinsic ideal
invariants.
-/
theorem chapter03_tower_ramification_and_residue_laws
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (p : Ideal R) (q : Ideal S) (r : Ideal T)
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
    (T : Chapter03NormalizedValuedTower K M L) (x : K) :
    T.vL (algebraMap K L x) = (T.eLM * T.eMK) • T.vK x := by
  sorry

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
    [Module.Finite A B] [Module.Finite B C]
    [Module.Flat B C]
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
