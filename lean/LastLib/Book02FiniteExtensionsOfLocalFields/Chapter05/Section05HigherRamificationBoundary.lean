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
  sorry

/-- The first congruence layer is the inertia subgroup. -/
theorem chapter05FirstRamificationGroup_eq_inertia
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) :
    chapter05RamificationGroup F A 1 = chapter05InertiaGroup F A := by
  sorry

/-- Higher congruence conditions refine as the power of the maximal ideal grows. -/
theorem chapter05RamificationGroup_succ_le
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) (n : ℕ) :
    chapter05RamificationGroup F A (n + 1) ≤ chapter05RamificationGroup F A n := by
  sorry

/-- The zeroth congruence layer is the whole decomposition group. -/
theorem chapter05ZerothRamificationGroup_eq_top
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) :
    chapter05RamificationGroup F A 0 = ⊤ := by
  sorry

/-- Prime-to-residue-characteristic ramification is the tame boundary. -/
abbrev chapter05TameAtResidueCharacteristic (e p : ℕ) : Prop :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11TameAtResidueCharacteristic e p

/-- Divisibility of the ramification index by the residue characteristic is wild. -/
abbrev chapter05WildAtResidueCharacteristic (e p : ℕ) : Prop :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11WildAtResidueCharacteristic e p

/-- The tame/wild alternatives are exhaustive. -/
theorem chapter05TameOrWild (e p : ℕ) :
    chapter05TameAtResidueCharacteristic e p ∨
      chapter05WildAtResidueCharacteristic e p := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11_branch_data_supports_later_tame_wild_analysis e p

/-- The tame and wild alternatives are disjoint. -/
theorem chapter05TameAndWildDisjoint (e p : ℕ) :
    ¬(chapter05TameAtResidueCharacteristic e p ∧
      chapter05WildAtResidueCharacteristic e p) := by
  intro h
  exact h.2 h.1

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05
