import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.Section04FixedFieldsOfInertia

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
          abel
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
  simp only [chapter05RamificationGroup]
  change chapter05HigherCongruence A 1 σ ↔
    σ ∈ chapter05InertiaGroup F A
  unfold chapter05HigherCongruence
  rw [Submodule.pow_one]
  constructor
  · intro h
    rw [inertia_mem_iff_residue_fixed]
    intro y
    rcases IsLocalRing.residue_surjective y with ⟨x, rfl⟩
    rw [← residue_action_commutes_with_reduction]
    apply sub_eq_zero.mp
    exact (IsLocalRing.residue_eq_zero_iff _).mpr (h x)
  · intro hi x
    apply (IsLocalRing.residue_eq_zero_iff _).mp
    rw [map_sub, residue_action_commutes_with_reduction]
    exact sub_eq_zero.mpr
      ((inertia_mem_iff_residue_fixed A σ).mp hi
        (IsLocalRing.residue A x))

/-- Higher congruence conditions refine as the power of the maximal ideal grows. -/
theorem chapter05RamificationGroup_succ_le
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) (n : ℕ) :
    chapter05RamificationGroup F A (n + 1) ≤ chapter05RamificationGroup F A n := by
  intro σ hσ
  simp only [chapter05RamificationGroup] at hσ ⊢
  change chapter05HigherCongruence A (n + 1) σ at hσ
  change chapter05HigherCongruence A n σ
  unfold chapter05HigherCongruence at hσ ⊢
  intro x
  exact Ideal.pow_le_pow_right (Nat.le_succ n) (hσ x)

/-- The zeroth congruence layer is the whole decomposition group. -/
theorem chapter05ZerothRamificationGroup_eq_top
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) :
    chapter05RamificationGroup F A 0 = ⊤ := by
  ext σ
  simp only [chapter05RamificationGroup]
  change chapter05HigherCongruence A 0 σ ↔ True
  unfold chapter05HigherCongruence
  simp

/-- Prime-to-residue-characteristic ramification is the tame boundary. -/
def chapter05TameAtResidueCharacteristic (e p : ℕ) : Prop :=
  p = 0 ∨ Nat.Coprime e p

/-- Wild ramification is the positive-characteristic non-prime-to-`p` case. -/
def chapter05WildAtResidueCharacteristic (e p : ℕ) : Prop :=
  p ≠ 0 ∧ ¬Nat.Coprime e p

/-- The tame/wild alternatives are exhaustive. -/
theorem chapter05TameOrWild (e p : ℕ) :
    chapter05TameAtResidueCharacteristic e p ∨
      chapter05WildAtResidueCharacteristic e p := by
  by_cases hp : p = 0
  · exact Or.inl (Or.inl hp)
  · by_cases hcop : Nat.Coprime e p
    · exact Or.inl (Or.inr hcop)
    · exact Or.inr ⟨hp, hcop⟩

/-- The tame and wild alternatives are disjoint. -/
theorem chapter05TameAndWildDisjoint (e p : ℕ) :
    ¬(chapter05TameAtResidueCharacteristic e p ∧
      chapter05WildAtResidueCharacteristic e p) := by
  rintro ⟨htame, hwild⟩
  rcases htame with hp | hcop
  · exact hwild.1 hp
  · exact hwild.2 hcop

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05
