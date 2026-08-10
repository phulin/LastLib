import Mathlib
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter09
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter11
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01

noncomputable section

open scoped TensorProduct WithZero

/-! # Book 2, Chapter 1, Section 1.1

The declarations in this file fix the local-field notation used throughout the
chapter.  Valuation equivalence is kept separate from the normalized additive
valuation scale: the former describes the place and the latter records the
ramification factor.
-/

universe u

/-! ### The four structures attached to one valued field -/

/-- The valuation ring attached to a chosen valuation. -/
abbrev chapter01ValuationRing {K Γ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) : Type _ :=
  v.valuationSubring

/-- The maximal ideal of the chosen valuation ring. -/
abbrev chapter01MaximalIdeal {K Γ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) :
    Ideal (chapter01ValuationRing v) :=
  IsLocalRing.maximalIdeal (chapter01ValuationRing v)

/-- The residue field of the chosen valuation ring. -/
abbrev chapter01ResidueField {K Γ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) : Type _ :=
  IsLocalRing.ResidueField (chapter01ValuationRing v)

/-- Completeness and rank-one discreteness for a normalized multiplicative valuation. -/
def chapter01CompleteDiscreteValuation (K : Type*) [Field K]
    (v : Valuation K ℤᵐ⁰) : Prop :=
  Valuation.IsRankOneDiscrete v ∧
    IsAdicComplete (chapter01MaximalIdeal v) (chapter01ValuationRing v)

/-- A uniformizer in the valuation ring, expressed by its maximal-ideal equation. -/
def chapter01IsUniformizer {K Γ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    (π : chapter01ValuationRing v) : Prop :=
  π ≠ 0 ∧ chapter01MaximalIdeal v = Ideal.span ({π} : Set (chapter01ValuationRing v))

/-- A discrete valuation ring has a generator for its maximal ideal. -/
theorem chapter01_complete_discrete_has_uniformizer
    {K : Type*} [Field K] (v : Valuation K ℤᵐ⁰)
    [Valuation.IsRankOneDiscrete v] :
    ∃ π : chapter01ValuationRing v, chapter01IsUniformizer v π := by
  sorry

/-! ### Normalized additive scales and compatible valuation rings -/

/-- The normalized additive restriction formula with its positive integer factor. -/
def chapter01ValuationRestrictionScale
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (e : ℕ) : Prop :=
  0 < e ∧ ∀ x : K, x ≠ 0 →
    vL (algebraMap K L x) = e • vK x

/-- The multiplicative formulation of “the two valuations extend the same place”. -/
def chapter01SamePlace
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ) : Prop :=
  vK.IsEquiv (vL.comap (algebraMap K L))

/-- For normalized discrete additive valuations, restriction changes only by a scale. -/
theorem chapter01_normalized_restriction_scale_exists
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (hvK : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vK)
    (hvL : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vL)
    (hext : vK.IsEquiv (AddValuation.comap (algebraMap K L) vL)) :
    ∃ e : ℕ, chapter01ValuationRestrictionScale vK vL e := by
  sorry

/-! ### The finite extension is still local -/

/-- In a finite complete extension, the upper valuation ring is complete, finite, and a DVR. -/
theorem chapter01_finite_extension_remains_local
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal vK.valuationSubring)
      vK.valuationSubring) :
    Module.Finite vK.valuationSubring vL.valuationSubring ∧
      Module.Free vK.valuationSubring vL.valuationSubring ∧
      IsAdicComplete (IsLocalRing.maximalIdeal vL.valuationSubring)
        vL.valuationSubring ∧
      IsDiscreteValuationRing vL.valuationSubring := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.finite_complete_extension_valuation_ring vK vL hcomplete

/-- The upper valuation ring is the integral closure of the lower one. -/
theorem chapter01_extension_valuation_ring_is_integral_closure
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal vK.valuationSubring)
      vK.valuationSubring) :
    (vL.valuationSubring : Set L) =
      {x : L | IsIntegral vK.valuationSubring x} := by
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01
