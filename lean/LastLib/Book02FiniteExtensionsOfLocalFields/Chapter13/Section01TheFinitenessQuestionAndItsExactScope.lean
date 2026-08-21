import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter13.Dependencies
import Mathlib.NumberTheory.Padics.PadicNumbers

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter13

noncomputable section

open scoped Topology WithZero

/-! ## 13.1. The finiteness question and its exact scope -/

/-- The source-level hypotheses for Theorem 13.1. -/
def chapter13Theorem13_1Hypotheses
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) : Prop :=
  CharZero K ∧ Valuation.IsRankOneDiscrete vK ∧
    IsAdicComplete (IsLocalRing.maximalIdeal vK.valuationSubring)
      vK.valuationSubring ∧
    Finite (IsLocalRing.ResidueField vK.valuationSubring)

/-- Theorem 13.1: a complete discretely valued field of characteristic zero
with finite residue field has only finitely many bounded-degree extension
classes over the base field. -/
theorem chapter13_theorem_13_1_bounded_degree_finiteness
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) [CharZero K]
    [Valuation.IsRankOneDiscrete vK]
    [Finite (IsLocalRing.ResidueField vK.valuationSubring)]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (N : ℕ) (hN : 1 ≤ N) :
    chapter13BoundedDegreeFiniteness (K := K) N := by
  sorry

/-- The canonical `p`-adic valuation has the hypotheses used by Theorem 13.1.
The proof is kept as a reusable bridge because the compactness theorem is
stated for an arbitrary normalized valuation. -/
theorem chapter13_padic_field_has_complete_discrete_finite_residue_profile
    (p : ℕ) [Fact p.Prime] :
    chapter13CompleteDiscreteValuedField (Padic.mulValuation (p := p)) := by
  sorry

/-- Every finite extension of a `p`-adic field is covered by Theorem 13.1. -/
theorem chapter13_padic_field_bounded_degree_finiteness
    (p : ℕ) [Fact p.Prime] (N : ℕ) (hN : 1 ≤ N) :
    chapter13BoundedDegreeFiniteness (K := ℚ_[p]) N := by
  let hprofile :=
    chapter13_padic_field_has_complete_discrete_finite_residue_profile p
  let : Valuation.IsRankOneDiscrete (Padic.mulValuation (p := p)) := hprofile.1
  let : Finite (IsLocalRing.ResidueField
      (Padic.mulValuation (p := p)).valuationSubring) := hprofile.2.2
  exact chapter13_theorem_13_1_bounded_degree_finiteness
    (vK := Padic.mulValuation (p := p))
    hprofile.2.1 N hN

/-- The source-level hypotheses for the tame bounded-degree theorem. -/
def chapter13Theorem13_2Hypotheses
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) : Prop :=
  Valuation.IsRankOneDiscrete vK ∧
    IsAdicComplete (IsLocalRing.maximalIdeal vK.valuationSubring)
      vK.valuationSubring ∧
    Finite (IsLocalRing.ResidueField vK.valuationSubring)

/-- Theorem 13.2: among finite extensions of a complete discretely valued
field with finite residue field, the tamely ramified classes of bounded degree
form a finite set.  Unramified extensions are included because their
ramification index is one. -/
theorem chapter13_theorem_13_2_bounded_tame_finiteness
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ)
    [Valuation.IsRankOneDiscrete vK]
    [Finite (IsLocalRing.ResidueField vK.valuationSubring)]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (N : ℕ) :
    chapter13TameBoundedDegreeFiniteness vK N := by
  sorry

theorem chapter13_char_zero_finiteness_restricts_to_tame_classes
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) [CharZero K]
    [Valuation.IsRankOneDiscrete vK]
    [Finite (IsLocalRing.ResidueField vK.valuationSubring)]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (N : ℕ) (hN : 1 ≤ N) :
    Set.Finite (chapter13TameBoundedDegreeClasses vK N) := by
  sorry

/-- Embeddings into a chosen overfield are not the same object as
base-field isomorphism classes. -/
def chapter13ExtensionEmbeddings
    (K L Ω : Type*) [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [Algebra L Ω]
    [IsScalarTower K L Ω] : Type _ :=
  L →ₐ[K] Ω

theorem chapter13_one_separable_class_can_have_several_embeddings
    {K L Ω : Type*} [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [Algebra L Ω]
    [IsScalarTower K L Ω] [IsAlgClosed Ω]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hdegree : 2 ≤ Module.finrank K L) :
    ∃ σ τ : chapter13ExtensionEmbeddings K L Ω, σ ≠ τ := by
  sorry

theorem chapter13_unbounded_degrees_are_not_a_bounded_finiteness_claim
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) [CharZero K]
    [Valuation.IsRankOneDiscrete vK]
    [Finite (IsLocalRing.ResidueField vK.valuationSubring)]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring) :
    Set.Infinite (Set.univ : Set (Chapter13FiniteExtensionClass K)) := by
  sorry

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter13
