import LastLib.Book03RamificationTheory.Chapter02.Section01WhyDisplacementIsTheRightMeasurement
import Mathlib.GroupTheory.Commutator.Basic

namespace LastLib.Book03RamificationTheory.Chapter02

noncomputable section

open scoped BigOperators Pointwise commutatorElement

universe u

/-! ## 2.2. Basic group properties -/

/-- The normality part of Proposition 2.1. -/
theorem chapter02_lower_filtration_groups_normal
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) :
    ∀ n : ℕ, (F.group n).Normal := by
  exact F.normal

/-- The descending part of Proposition 2.1. -/
theorem chapter02_lower_filtration_descending
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) (n : ℕ) :
    F.group (n + 1) ≤ F.group n := by
  exact F.descending n

/-- A finite lower filtration is eventually trivial. -/
theorem chapter02_lower_filtration_eventually_trivial
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → F.group n = ⊥ := by
  exact F.eventually_trivial

/-- The canonical valuation lower groups are normal in the decomposition group. -/
theorem chapter02_canonical_lower_group_normal
    (K : Type u) {L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : AddValuation L (WithTop ℤ)) (n : ℕ) :
    (chapter02LowerGroupNat K v n).Normal := by
  sorry

/-- The canonical valuation lower groups form a descending chain. -/
theorem chapter02_canonical_lower_group_succ_le
    (K : Type u) {L : Type u} [Field K] [Field L] [Algebra K L]
    (v : AddValuation L (WithTop ℤ)) (n : ℕ) :
    chapter02LowerGroupNat K v (n + 1) ≤ chapter02LowerGroupNat K v n := by
  sorry

/-- The canonical valuation filtration is eventually trivial. -/
theorem chapter02_canonical_lower_group_eventually_trivial
    (K : Type u) {L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : AddValuation L (WithTop ℤ)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → chapter02LowerGroupNat K v n = ⊥ := by
  sorry

/-- The group-valued form of the commutator estimate. -/
theorem chapter02_commutator_lower_group_le
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    [Valuation.IsRankOneDiscrete vK.toValuation]
    [Valuation.IsRankOneDiscrete vL.toValuation]
    (hext : vK.IsEquiv (vL.comap (algebraMap K L)))
    [Algebra (IsLocalRing.ResidueField vK.toValuation.valuationSubring)
      (IsLocalRing.ResidueField vL.toValuation.valuationSubring)]
    (hseparable : Algebra.IsSeparable
      (IsLocalRing.ResidueField vK.toValuation.valuationSubring)
      (IsLocalRing.ResidueField vL.toValuation.valuationSubring))
    (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) :
    ⁅chapter02LowerGroupNat K vL i, chapter02LowerGroupNat K vL j⁆ ≤
      chapter02LowerGroupNat K vL (i + j) := by
  sorry

/-- Pointwise membership in the commutator estimate. -/
theorem chapter02_commutator_mem_lower_group
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    [Valuation.IsRankOneDiscrete vK.toValuation]
    [Valuation.IsRankOneDiscrete vL.toValuation]
    (hext : vK.IsEquiv (vL.comap (algebraMap K L)))
    [Algebra (IsLocalRing.ResidueField vK.toValuation.valuationSubring)
      (IsLocalRing.ResidueField vL.toValuation.valuationSubring)]
    (hseparable : Algebra.IsSeparable
      (IsLocalRing.ResidueField vK.toValuation.valuationSubring)
      (IsLocalRing.ResidueField vL.toValuation.valuationSubring))
    (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j)
    (σ τ : chapter02DecompositionGroup K vL)
    (hσ : σ ∈ chapter02LowerGroupNat K vL i)
    (hτ : τ ∈ chapter02LowerGroupNat K vL j) :
    ⁅σ, τ⁆ ∈ chapter02LowerGroupNat K vL (i + j) := by
  sorry

/- The source deliberately declines to record a uniform power estimate in
   mixed characteristic: the competing depths depend on `v_L(p)`. -/

end

end LastLib.Book03RamificationTheory.Chapter02
