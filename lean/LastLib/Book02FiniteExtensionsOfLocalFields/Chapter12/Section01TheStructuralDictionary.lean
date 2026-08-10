import Mathlib
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12

noncomputable section

open Ideal IsLocalRing
open scoped BigOperators TensorProduct WithZero

universe u

/-! ## 12.1. The structural dictionary -/

/--
The multiplicative form of the normalized restriction formula.  Mathlib's
`Valuation` is multiplicative, so the additive identity
`v_L|_K = e • v_K` is represented by `v_L(x) = v_K(x)^e`.
-/
def normalizedValuationRestriction
    {K L Γ : Type*} [Field K] [Field L]
    [Algebra K L] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ) (e : ℕ) : Prop :=
  ∀ x : K, vL (algebraMap K L x) = (vK x) ^ e

/-- The ideal-theoretic form of `m_K B = m_L^e`. -/
def maximalIdealExtensionIsPower
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (mA : Ideal A) (mB : Ideal B) (e : ℕ) : Prop :=
  Ideal.map (algebraMap A B) mA = mB ^ e

/--
Residue trace and norm formulas are stated with the residue maps explicit.
This avoids pretending that Mathlib can infer a map between arbitrary
quotients from ideals alone; in the local-field application these maps are
the canonical quotient residue maps.
-/
structure Chapter12ResidueArithmeticShadow
    {A B k l : Type*} [CommRing A] [CommRing B] [Field k] [Field l]
    [Algebra A B] [Algebra k l]
    [Module.Finite A B] [Module.Free A B]
    [Module.Finite k l] [Module.Free k l] where
  e : ℕ
  baseResidue : A →+* k
  extensionResidue : B →+* l
  residueCompatibility : ∀ a : A,
    extensionResidue (algebraMap A B a) = algebraMap k l (baseResidue a)
  trace_shadow : ∀ x : B,
    baseResidue (Algebra.trace A B x) =
      (e : k) * Algebra.trace k l (extensionResidue x)
  norm_shadow : ∀ u : Bˣ,
    baseResidue (Algebra.norm A (u : B)) =
      (Algebra.norm k ((Units.map extensionResidue.toMonoidHom u : lˣ) : l)) ^ e

/--
Book 2, §12.1: in a finite extension of complete discretely valued fields,
the valuation ring upstairs is the integral closure and is finite free.  The
rank is exposed by a basis indexed by the field degree.
-/
theorem complete_extension_has_finite_free_integral_closure
    {K L Γ : Type*} [Field K] [Field L]
    [Algebra K L] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [Module.Finite K L]
    [Algebra vK.valuationSubring L]
    [IsScalarTower vK.valuationSubring K L]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring) :
    (integralClosure vK.valuationSubring L : Set L) =
        (vL.valuationSubring : Set L) ∧
      Module.Finite vK.valuationSubring vL.valuationSubring ∧
      Module.Free vK.valuationSubring vL.valuationSubring ∧
      Nonempty (Module.Basis (Fin (Module.finrank K L))
        vK.valuationSubring vL.valuationSubring) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal vL.valuationSubring)
        vL.valuationSubring ∧
      IsDiscreteValuationRing vL.valuationSubring := by
  sorry

/-- Book 2, §12.1: the normalized valuation restriction carries the factor `e`. -/
theorem normalized_restriction_has_ramification_factor
    {K L Γ : Type*} [Field K] [Field L]
    [Algebra K L] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ) (e : ℕ)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL]
    (he : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
      vK.valuationSubring vL.valuationSubring
        (IsLocalRing.maximalIdeal vL.valuationSubring) = e) :
    normalizedValuationRestriction vK vL e := by
  sorry

/-- Book 2, §12.1: extension of the base maximal ideal. -/
theorem maximal_ideal_extension_is_ramification_power
    {K L Γ : Type*} [Field K] [Field L]
    [Algebra K L] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ) (e : ℕ)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [Module.Finite K L]
    (he : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
      vK.valuationSubring vL.valuationSubring
        (IsLocalRing.maximalIdeal vL.valuationSubring) = e) :
    maximalIdealExtensionIsPower
      (IsLocalRing.maximalIdeal vK.valuationSubring)
      (IsLocalRing.maximalIdeal vL.valuationSubring) e := by
  sorry

-- SOURCE_ISSUE: §§12.1–12.2 state `[L : K] = e f` for every finite extension of a complete discretely valued field without a defectless or perfect-residue hypothesis. Complete discretely valued fields with imperfect residue field can have finite defect extensions, so the equality is false as stated; the minimally corrected interface below assumes the standard defectless degree equality explicitly.
/-- Book 2, §12.1: one valuation/residue block accounts for `e * f` dimensions. -/
theorem complete_extension_degree_is_ramification_times_residue_degree
    {K L Γ : Type*} [Field K] [Field L]
    [Algebra K L] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ) (e f : ℕ)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [Module.Finite K L]
    (he : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
      vK.valuationSubring vL.valuationSubring
        (IsLocalRing.maximalIdeal vL.valuationSubring) = e)
    (hf : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree
      vK.valuationSubring vL.valuationSubring
        (IsLocalRing.maximalIdeal vL.valuationSubring) = f)
    (hdefectless : Module.finrank K L =
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
          vK.valuationSubring vL.valuationSubring
          (IsLocalRing.maximalIdeal vL.valuationSubring) *
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree
          vK.valuationSubring vL.valuationSubring
          (IsLocalRing.maximalIdeal vL.valuationSubring))
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring) :
    Module.finrank K L = e * f := by
  simpa [he, hf] using hdefectless

/-- Book 2, §12.1: both local indices multiply in a tower. -/
theorem ramification_and_residue_degrees_multiply_in_a_tower
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T]
    (p : Ideal R) (q : Ideal S) (r : Ideal T)
    [q.LiesOver p] [r.LiesOver q] [Module.Flat S T] :
    r.ramificationIdx R = q.ramificationIdx R * r.ramificationIdx S ∧
      r.inertiaDeg R = q.inertiaDeg R * r.inertiaDeg S := by
  sorry

/-- Book 2, §12.1: trace and norm transfer through a finite tower. -/
theorem trace_and_norm_transfer_in_a_tower
    {K M L : Type*} [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L]
    [Module.Finite K M] [Module.Finite M L] [Module.Finite K L] (x : L) :
    Algebra.trace K L x = Algebra.trace K M (Algebra.trace M L x) ∧
      Algebra.norm K x = Algebra.norm K (Algebra.norm M x) := by
  sorry

/-- Book 2, §12.1: the valuation of a norm records the residue degree. -/
theorem structural_norm_valuation_formula
    {K L Γ : Type*} [Field K] [Field L]
    [Algebra K L] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ) (f : ℕ)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [Module.Finite K L]
    (hf : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree
      vK.valuationSubring vL.valuationSubring
        (IsLocalRing.maximalIdeal vL.valuationSubring) = f)
    (x : L) :
    vK (Algebra.norm K x) = (vL x) ^ f := by
  sorry

/-- Book 2, §12.1: the residue trace shadow, with no separability assumption. -/
theorem residue_trace_shadow_formula
    {A B k l : Type*} [CommRing A] [CommRing B] [Field k] [Field l]
    [Algebra A B] [Algebra k l]
    [Module.Finite A B] [Module.Free A B]
    [Module.Finite k l] [Module.Free k l]
    (d : Chapter12ResidueArithmeticShadow) (x : B) :
    d.baseResidue (Algebra.trace A B x) =
      (d.e : k) * Algebra.trace k l (d.extensionResidue x) := by
  exact d.trace_shadow x

/-- Book 2, §12.1: the residue norm shadow, with no separability assumption. -/
theorem residue_norm_shadow_formula
    {A B k l : Type*} [CommRing A] [CommRing B] [Field k] [Field l]
    [Algebra A B] [Algebra k l]
    [Module.Finite A B] [Module.Free A B]
    [Module.Finite k l] [Module.Free k l]
    (d : Chapter12ResidueArithmeticShadow) (u : Bˣ) :
    d.baseResidue (Algebra.norm A (u : B)) =
      (Algebra.norm k ((Units.map d.extensionResidue.toMonoidHom u : lˣ) : l)) ^ d.e := by
  exact d.norm_shadow u

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12
