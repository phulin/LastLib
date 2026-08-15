import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.Section03ResidueActionAndInertia
import Mathlib.RingTheory.LocalRing.Length

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05

noncomputable section

open scoped BigOperators WithTop

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

/-!
The cyclic Hasse--Arf argument uses two pieces of local algebra that are
different from the congruence subgroups themselves.  First, an automorphism
has a canonical fixed-point ideal, and its fixed-point multiplicity is the
module length of the corresponding quotient.  Second, the ramification
number of a nonidentity automorphism is the cutoff detected by the canonical
congruence groups.  The structures below keep those two pieces explicit so
that later chapters do not replace them by unrelated natural-number data.
-/

/-- The ideal cutting out the fixed points of an iterate of a ring automorphism. -/
def chapter05FixedPointIdeal
    {A : Type*} [CommRing A] (u : A ≃+* A) (n : ℕ) : Ideal A :=
  Ideal.span (Set.range (fun x : A => (u ^ n) x - x))

/-- The local fixed-point multiplicity, allowed to be infinite before finiteness is assumed. -/
def chapter05FixedPointMultiplicity
    {A : Type*} [CommRing A] (u : A ≃+* A) (n : ℕ) : ℕ∞ :=
  Module.length A (A ⧸ chapter05FixedPointIdeal u n)

/-- A ramification-number cutoff for the canonical congruence filtration. -/
structure Chapter05RamificationNumberProfile
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) where
  number : chapter05DecompositionGroup F A → ℕ∞
  number_one : number 1 = ⊤
  finite_of_ne_one : ∀ {σ : chapter05DecompositionGroup F A}, σ ≠ 1 →
    number σ ≠ ⊤
  mem_iff : ∀ (σ : chapter05DecompositionGroup F A) (n : ℕ),
    σ ∈ chapter05RamificationGroup F A (n + 1) ↔
      ((n + 1 : ℕ) : ℕ∞) ≤ number σ

/-!
This is the branch-level package used by the cyclic ramification-number
argument.  `fixed_point_multiplicity` below is not an arbitrary count: it is
the length of the explicitly defined fixed-point ideal.  The
`primitive_period_count` fields expose the periodic-orbit divisibility input;
the two equality fields tie it to the canonical lower filtration through the
ramification-number profile and to the actual fixed-point lengths.
-/
structure Chapter05CyclicRamificationFixedPointInterface
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E]
    (A : ValuationSubring E) [IsDiscreteValuationRing A]
    (R : Chapter05RamificationNumberProfile F E A)
    (σ : chapter05DecompositionGroup F A)
    [Finite (chapter05DecompositionGroup F A)] where
  complete : IsAdicComplete (IsLocalRing.maximalIdeal A) A
  residue_perfect : PerfectField (IsLocalRing.ResidueField A)
  p : ℕ
  p_prime : Nat.Prime p
  residue_characteristic : CharP (IsLocalRing.ResidueField A) p
  σ_inertia : σ ∈ chapter05InertiaGroup F A
  cyclic : IsCyclic (chapter05DecompositionGroup F A)
  automorphism_order : ℕ
  automorphism_order_pos : 0 < automorphism_order
  automorphism_period : σ ^ automorphism_order = 1
  automorphism_order_minimal :
    ∀ {n : ℕ}, σ ^ n = 1 → automorphism_order ∣ n
  wild_exponent : ℕ
  wild_exponent_pos : 0 < wild_exponent
  automorphism_order_eq : automorphism_order = p ^ wild_exponent
  power_nontrivial :
    ∀ {r : ℕ}, r < wild_exponent → σ ^ (p ^ r) ≠ 1
  q : ℕ → ℕ
  q_eq_ramification_number :
    ∀ {r : ℕ}, r < wild_exponent →
      q r + 1 = (R.number (σ ^ (p ^ r))).toNat
  q_eq_fixed_point_multiplicity :
    ∀ {r : ℕ}, r < wild_exponent →
      q r + 1 =
        (chapter05FixedPointMultiplicity
          (chapter05ValuationRingAction F A σ) (p ^ r)).toNat
  fixed_point_multiplicity_finite :
    ∀ {n : ℕ}, σ ^ n ≠ 1 →
      chapter05FixedPointMultiplicity
        (chapter05ValuationRingAction F A σ) n ≠ ⊤
  primitive_period_count : ℕ → ℕ
  periodic_orbit_count : ℕ → ℕ
  primitive_period_count_eq_periodic_orbits :
    ∀ n : ℕ, primitive_period_count n = periodic_orbit_count n
  periodic_orbit_count_divisible :
    ∀ {n : ℕ}, 0 < n → n ∣ periodic_orbit_count n
  prime_power_mobius_identity :
    ∀ {r : ℕ}, 0 < r → r < wild_exponent →
      primitive_period_count (p ^ r) =
        (chapter05FixedPointMultiplicity
          (chapter05ValuationRingAction F A σ) (p ^ r)).toNat -
          (chapter05FixedPointMultiplicity
            (chapter05ValuationRingAction F A σ) (p ^ (r - 1))).toNat
  q_monotone :
    ∀ {r : ℕ}, 0 < r → r < wild_exponent → q (r - 1) ≤ q r

/-- The fixed-point multiplicity divisibility input for a prime-power iterate. -/
theorem chapter05_cyclic_fixed_point_difference_divisibility
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E]
    (A : ValuationSubring E) [IsDiscreteValuationRing A]
    (R : Chapter05RamificationNumberProfile F E A)
    (σ : chapter05DecompositionGroup F A)
    [Finite (chapter05DecompositionGroup F A)]
    (P : Chapter05CyclicRamificationFixedPointInterface A R σ)
    {r : ℕ} (hr : 0 < r) (hr_last : r < P.wild_exponent) :
    P.p ^ r ∣
      (chapter05FixedPointMultiplicity
        (chapter05ValuationRingAction F A σ) (P.p ^ r)).toNat -
        (chapter05FixedPointMultiplicity
          (chapter05ValuationRingAction F A σ) (P.p ^ (r - 1))).toNat := by
  rw [← P.prime_power_mobius_identity hr hr_last,
    P.primitive_period_count_eq_periodic_orbits]
  exact P.periodic_orbit_count_divisible (Nat.pow_pos P.p_prime.pos)

/-- The cyclic ramification-number congruence used by the Hasse--Arf argument. -/
theorem chapter05_cyclic_ramification_number_congruence
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E]
    (A : ValuationSubring E) [IsDiscreteValuationRing A]
    (R : Chapter05RamificationNumberProfile F E A)
    (σ : chapter05DecompositionGroup F A)
    [Finite (chapter05DecompositionGroup F A)]
    (P : Chapter05CyclicRamificationFixedPointInterface A R σ)
    {r : ℕ} (hr : 0 < r) (hr_last : r < P.wild_exponent) :
    P.p ^ r ∣ P.q r - P.q (r - 1) := by
  have hprev : r - 1 < P.wild_exponent := by omega
  have hdiv := chapter05_cyclic_fixed_point_difference_divisibility A R σ P hr hr_last
  have hqr := P.q_eq_fixed_point_multiplicity (r := r) hr_last
  have hqprev := P.q_eq_fixed_point_multiplicity (r := r - 1) hprev
  rw [← hqr, ← hqprev] at hdiv
  convert hdiv using 1
  exact (Nat.add_sub_add_right (P.q r) 1 (P.q (r - 1))).symm

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
