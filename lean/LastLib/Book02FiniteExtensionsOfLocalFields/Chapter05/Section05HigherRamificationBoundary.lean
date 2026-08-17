import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.Section03ResidueActionAndInertia

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05

noncomputable section

open scoped BigOperators

/-! ## 5.5. What inertia does not yet measure -/

/-- Congruence of a decomposition-group automorphism modulo the `n`th maximal-ideal power. -/
def chapter05HigherCongruence
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) (n : ℕ)
    (σ : chapter05DecompositionGroup F A) : Prop :=
  ∀ x : A, (σ • x - x) ∈ (IsLocalRing.maximalIdeal A) ^ n

/-- The elementary congruence-defined higher ramification subgroup. -/
def chapter05RamificationGroup
    (F : Type*) {E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) (n : ℕ) :
    Subgroup (chapter05DecompositionGroup F A) := by
  refine
    { carrier := {σ | chapter05HigherCongruence A n σ}
      one_mem' := by
        change chapter05HigherCongruence A n 1
        unfold chapter05HigherCongruence
        intro x
        simp
      mul_mem' := by
        intro σ τ hσ hτ
        change chapter05HigherCongruence A n σ at hσ
        change chapter05HigherCongruence A n τ at hτ
        unfold chapter05HigherCongruence at hσ hτ ⊢
        intro x
        have h₁ := (decomposition_group_preserves_maximal_ideal_powers A σ n)
          (τ • x - x)
        have h₂ := hσ x
        have h₃ := hτ x
        have h₄ : σ • (τ • x - x) ∈ (IsLocalRing.maximalIdeal A) ^ n :=
          h₁.mp h₃
        have hrewrite : σ • τ • x - x =
            σ • (τ • x - x) + (σ • x - x) := by
          rw [smul_sub]
          exact (sub_add_sub_cancel _ _ _).symm
        rw [mul_smul, hrewrite]
        exact (IsLocalRing.maximalIdeal A ^ n).add_mem h₄ h₂
      inv_mem' := by
        intro σ hσ
        change chapter05HigherCongruence A n σ at hσ
        unfold chapter05HigherCongruence at hσ ⊢
        intro x
        have h₁ := (decomposition_group_preserves_maximal_ideal_powers A σ⁻¹ n)
          (σ • x - x)
        have h₂ := h₁.mp (hσ x)
        have h₃ := (IsLocalRing.maximalIdeal A ^ n).neg_mem h₂
        simpa [smul_sub, smul_smul] using h₃ }

/-- The first congruence layer is the inertia subgroup. -/
theorem chapter05FirstRamificationGroup_eq_inertia
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) :
    chapter05RamificationGroup F A 1 = chapter05InertiaGroup F A := by
  ext σ
  constructor
  · intro hσ
    apply (inertia_mem_iff_residue_fixed A σ).mpr
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    have hσ' : chapter05HigherCongruence A 1 σ := hσ
    have hzero : IsLocalRing.residue A (σ • x - x) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr (by simpa [pow_one] using hσ' x)
    rw [← residue_action_commutes_with_reduction A σ x]
    exact sub_eq_zero.mp (by simpa only [map_sub] using hzero)
  · intro hσ
    change chapter05HigherCongruence A 1 σ
    intro x
    have hfixed := (inertia_mem_iff_residue_fixed A σ).mp hσ
      (IsLocalRing.residue A x)
    have hzero : IsLocalRing.residue A (σ • x - x) = 0 := by
      rw [map_sub, residue_action_commutes_with_reduction A σ x, hfixed, sub_self]
    simpa [pow_one] using (IsLocalRing.residue_eq_zero_iff _).mp hzero

/-- Higher congruence conditions refine as the power of the maximal ideal grows. -/
theorem chapter05RamificationGroup_succ_le
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) (n : ℕ) :
    chapter05RamificationGroup F A (n + 1) ≤ chapter05RamificationGroup F A n := by
  intro σ hσ
  change chapter05HigherCongruence A (n + 1) σ at hσ
  change chapter05HigherCongruence A n σ
  intro x
  exact Ideal.pow_le_pow_right (Nat.le_succ n) (hσ x)

/-- The zeroth congruence layer is the whole decomposition group. -/
theorem chapter05ZerothRamificationGroup_eq_top
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) :
    chapter05RamificationGroup F A 0 = ⊤ := by
  apply le_antisymm le_top
  intro σ _
  change chapter05HigherCongruence A 0 σ
  intro x
  simp

/-- Prime-to-residue-characteristic ramification is the tame boundary.

The parameter `p` is the characteristic exponent: it is the residue
characteristic in positive characteristic and `1` in residue characteristic
zero, as in the chapter's convention. -/
def chapter05TameAtResidueCharacteristic (e p : ℕ) : Prop :=
  Nat.Coprime e p

/-- Wild ramification is the positive-characteristic non-prime-to-`p` case. -/
def chapter05WildAtResidueCharacteristic (e p : ℕ) : Prop :=
  p ≠ 1 ∧ ¬Nat.Coprime e p

/-- The tame/wild alternatives are exhaustive. -/
theorem chapter05TameOrWild (e p : ℕ) :
    chapter05TameAtResidueCharacteristic e p ∨
      chapter05WildAtResidueCharacteristic e p := by
  by_cases h : Nat.Coprime e p
  · left
    exact h
  · right
    refine ⟨?_, h⟩
    intro hp
    subst p
    exact h (Nat.coprime_one_right e)

/-- The tame and wild alternatives are disjoint. -/
theorem chapter05TameAndWildDisjoint (e p : ℕ) :
    ¬(chapter05TameAtResidueCharacteristic e p ∧
      chapter05WildAtResidueCharacteristic e p) := by
  rintro ⟨he, _, hnot⟩
  exact hnot he

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05
