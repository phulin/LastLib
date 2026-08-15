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
  refine ⟨?_⟩
  intro h hh g
  change ∀ x : v.toValuation.valuationSubring,
    (g * h * g⁻¹) • x - x ∈
      (IsLocalRing.maximalIdeal v.toValuation.valuationSubring) ^ (n + 1)
  intro x
  have hmem := hh (g⁻¹ • x)
  have hmem' := (
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.decomposition_group_preserves_maximal_ideal_powers
      v.toValuation.valuationSubring g (n + 1)
      (h • (g⁻¹ • x) - (g⁻¹ • x))).mp hmem
  have heq : (g * h * g⁻¹) • x - x =
      g • (h • (g⁻¹ • x) - (g⁻¹ • x)) := by
    rw [mul_smul, mul_smul, smul_sub, smul_smul]
    simp
  rw [heq]
  exact hmem'

/-- The canonical valuation lower groups form a descending chain. -/
theorem chapter02_canonical_lower_group_succ_le
    (K : Type u) {L : Type u} [Field K] [Field L] [Algebra K L]
    (v : AddValuation L (WithTop ℤ)) (n : ℕ) :
    chapter02LowerGroupNat K v (n + 1) ≤ chapter02LowerGroupNat K v n := by
  exact
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05RamificationGroup_succ_le
      (A := v.toValuation.valuationSubring) (n + 1)

/-- The canonical valuation filtration is eventually trivial. -/
theorem chapter02_canonical_lower_group_eventually_trivial
    (K : Type u) {L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : AddValuation L (WithTop ℤ))
    [Valuation.IsRankOneDiscrete v.toValuation]
    [Finite (chapter02DecompositionGroup K v)]
    (hnormalized : Function.Surjective v) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → chapter02LowerGroupNat K v n = ⊥ := by
  exact (chapter02CanonicalLowerFiltration K v hnormalized).eventually_trivial

/-- The group-valued form of the commutator estimate. -/
theorem chapter02_commutator_lower_group_le
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    [Valuation.IsRankOneDiscrete vK.toValuation]
    [Valuation.IsRankOneDiscrete vL.toValuation]
    (_hext : vK.IsEquiv (vL.comap (algebraMap K L)))
    [Algebra (IsLocalRing.ResidueField vK.toValuation.valuationSubring)
      (IsLocalRing.ResidueField vL.toValuation.valuationSubring)]
    (_hseparable : Algebra.IsSeparable
      (IsLocalRing.ResidueField vK.toValuation.valuationSubring)
      (IsLocalRing.ResidueField vL.toValuation.valuationSubring))
    (i j : ℕ) (_hi : 1 ≤ i) (_hj : 1 ≤ j) :
    ⁅chapter02LowerGroupNat K vL i, chapter02LowerGroupNat K vL j⁆ ≤
      chapter02LowerGroupNat K vL (i + j) := by
  classical
  let A := vL.toValuation.valuationSubring
  let I : Ideal A := IsLocalRing.maximalIdeal A
  have hcong (r : ℕ) (g : chapter02DecompositionGroup K vL)
      (hg : g ∈ chapter02LowerGroupNat K vL r) (x : A) :
      g • x - x ∈ I ^ (r + 1) := by
    change LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05HigherCongruence
      A (r + 1) g at hg
    exact hg x
  have hpres (g : chapter02DecompositionGroup K vL) (r : ℕ) (x : A)
      (hx : x ∈ I ^ r) : g • x ∈ I ^ r := by
    exact
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.decomposition_group_preserves_maximal_ideal_powers
        A g r x).mp hx
  have hdelta_pow (m : ℕ) (g : chapter02DecompositionGroup K vL)
      (hg : g ∈ chapter02LowerGroupNat K vL m) :
      ∀ r : ℕ, ∀ x : A, x ∈ I ^ r →
        g • x - x ∈ I ^ (m + r) := by
    intro r
    induction r with
    | zero =>
        intro x hx
        have hx' := hcong m g hg x
        simpa using Ideal.pow_le_pow_right (Nat.le_succ m) hx'
    | succ r ih =>
        intro x hx
        rw [I.pow_succ] at hx
        refine Submodule.mul_induction_on hx ?_ ?_
        · intro a ha b hb
          have hga : g • a ∈ I ^ r := by
            exact hpres g r a ha
          have hterm1 :
              g • a * (g • b - b) ∈ I ^ (m + (r + 1)) := by
            rw [show m + (r + 1) = r + (m + 1) by omega,
              Ideal.IsTwoSided.pow_add r (m + 1)]
            exact Ideal.mul_mem_mul hga (hcong m g hg b)
          have hterm2 :
              b * (g • a - a) ∈ I ^ (m + (r + 1)) := by
            rw [show m + (r + 1) = (m + r) + 1 by omega, I.pow_succ]
            exact Ideal.mul_mem_mul_rev (ih a ha) hb
          have heq : g • (a * b) - (a * b) =
              g • a * (g • b - b) + b * (g • a - a) := by
            simp [smul_mul']
            ring
          rw [heq]
          exact (I ^ (m + (r + 1))).add_mem hterm1 hterm2
        · intro x y hx hy
          have heq : g • (x + y) - (x + y) =
              (g • x - x) + (g • y - y) := by
            simp [smul_add]
            ring
          rw [heq]
          exact (I ^ (m + (r + 1))).add_mem hx hy
  refine Subgroup.commutator_le.mpr ?_
  intro σ hσ τ hτ
  change LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05HigherCongruence
    A (i + j + 1) ⁅σ, τ⁆
  intro x
  have hp : σ * τ * σ⁻¹ ∈ chapter02LowerGroupNat K vL j := by
    exact
      (chapter02_canonical_lower_group_normal K vL j).conj_mem τ hτ σ
  have hq : τ * σ⁻¹ * τ⁻¹ ∈ chapter02LowerGroupNat K vL i := by
    exact
      (chapter02_canonical_lower_group_normal K vL i).conj_mem
        σ⁻¹ ((chapter02LowerGroupNat K vL i).inv_mem hσ) τ
  have hσx := hcong i σ hσ x
  have hτx := hcong j τ hτ x
  have hpdeep :=
    hdelta_pow j (σ * τ * σ⁻¹) hp (i + 1) (σ • x - x) hσx
  have hqdeep :=
    hdelta_pow i (τ * σ⁻¹ * τ⁻¹) hq (j + 1) (τ • x - x) hτx
  have hpdeep' :
      (σ * τ * σ⁻¹) • (σ • x - x) - (σ • x - x) ∈ I ^ (i + j + 1) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hpdeep
  have hqdeep' :
      (τ * σ⁻¹ * τ⁻¹) • (τ • x - x) - (τ • x - x) ∈ I ^ (i + j + 1) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hqdeep
  have hqdeep'' :
      σ • ((τ * σ⁻¹ * τ⁻¹) • (τ • x - x) - (τ • x - x)) ∈ I ^ (i + j + 1) :=
    hpres σ (i + j + 1) _ hqdeep'
  have hidentity :
      ⁅σ, τ⁆ • x - x =
        - (σ • ((τ * σ⁻¹ * τ⁻¹) • (τ • x - x) - (τ • x - x))) -
          ((σ * τ * σ⁻¹) • (σ • x - x) - (σ • x - x)) := by
    simp [commutatorElement_def, mul_smul, smul_sub]
    ring
  rw [hidentity]
  exact (I ^ (i + j + 1)).sub_mem ((I ^ (i + j + 1)).neg_mem hqdeep'') hpdeep'

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
  exact
    (chapter02_commutator_lower_group_le K L vK vL hext hseparable i j hi hj)
      (Subgroup.commutator_mem_commutator hσ hτ)

/- The source deliberately declines to record a uniform power estimate in
   mixed characteristic: the competing depths depend on `v_L(p)`. -/

end

end LastLib.Book03RamificationTheory.Chapter02
