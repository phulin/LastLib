import LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.Section08TraceAndBoundedness

universe u v

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter11

noncomputable section

open Ideal IsLocalRing
open Polynomial
open scoped BigOperators TensorProduct WithZero Polynomial nonZeroDivisors

/-! # Chapter 11: several places above one place

This file is a statement-only formalization of sections 11.1--11.9 of Book 1.
The declarations are intentionally local to this namespace because the chapters
are generated independently.
-/

/-! # Book 1, Chapter 11, Section 11.9: Towers
-/

/-! ## 11.9. Towers of extensions -/

/-- Ramification indices multiply in a tower, using Mathlib's intrinsic definition. -/
theorem chapter11_ramification_indices_multiply_in_towers
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (p : Ideal R) (q : Ideal S) (r : Ideal T)
    [p.IsPrime] [q.IsPrime] [r.IsPrime]
    [q.LiesOver p] [r.LiesOver q] [Module.Flat S T] :
    r.ramificationIdx R = q.ramificationIdx R * r.ramificationIdx S := by
  exact Ideal.ramificationIdx_tower q r

/-- Inertia degrees multiply in a tower. -/
theorem chapter11_inertia_degrees_multiply_in_towers
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (p : Ideal R) (q : Ideal S) (r : Ideal T)
    [p.IsPrime] [q.IsPrime] [r.IsPrime]
    [q.LiesOver p] [r.LiesOver q] :
    r.inertiaDeg R = q.inertiaDeg R * r.inertiaDeg S := by
  exact Ideal.inertiaDeg_tower q r

/-- The degree of a field tower is multiplicative. -/
theorem chapter11_field_degrees_multiply_in_towers
    (K L M : Type*) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] :
    Module.finrank K M = Module.finrank K L * Module.finrank L M := by
  exact (Module.finrank_mul_finrank K L M).symm

/-- Combining a first-stage local degree formula with field-tower
multiplicativity. -/
theorem chapter11_branch_tree_recovers_tower_degree
    (K L M : Type*) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M]
    {ι : Type*} [Fintype ι] (e₁ f₁ : ι → ℕ)
    (hL : Module.finrank K L = ∑ i, e₁ i * f₁ i) :
    Module.finrank K M =
      (∑ i, e₁ i * f₁ i) * Module.finrank L M := by
  calc
    Module.finrank K M = Module.finrank K L * Module.finrank L M :=
      (Module.finrank_mul_finrank K L M).symm
    _ = (∑ i, e₁ i * f₁ i) * Module.finrank L M := by rw [hL]

/-- A two-level branch-tree degree computation is the product of the two
stage sums. -/
theorem chapter11_two_stage_branch_tree_recovers_tower_degree
    (K L M : Type*) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e₁ f₁ : ι → ℕ) (e₂ f₂ : κ → ℕ)
    (hL : Module.finrank K L = ∑ i, e₁ i * f₁ i)
    (hM : Module.finrank L M = ∑ j, e₂ j * f₂ j) :
    Module.finrank K M =
      (∑ i, e₁ i * f₁ i) * (∑ j, e₂ j * f₂ j) := by
  calc
    Module.finrank K M = Module.finrank K L * Module.finrank L M :=
      (Module.finrank_mul_finrank K L M).symm
    _ = (∑ i, e₁ i * f₁ i) * (∑ j, e₂ j * f₂ j) := by rw [hL, hM]

/-- A specified chain of primes composes to a prime above the bottom prime.
The Henselian/non-Henselian distinction concerns whether such a chain is
canonical; the transitivity assertion itself does not require a Henselian
hypothesis. -/
theorem chapter11_extensions_transmit_liesOver_along_branch_chain
    (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (p : Ideal R) (q : Ideal S) (r : Ideal T) :
    q.LiesOver p ∧ r.LiesOver q → r.LiesOver p := by
  rintro ⟨hqp, hrq⟩
  letI : q.LiesOver p := hqp
  letI : r.LiesOver q := hrq
  exact Ideal.LiesOver.trans r q p

/-- The tame/wild distinction is the later refinement of the e-data. -/
def chapter11TameAtResidueCharacteristic (e p : ℕ) : Prop :=
  p = 0 ∨ Nat.Coprime e p

/-- Ramification is wild when the residue characteristic divides the ramification index. -/
def chapter11WildAtResidueCharacteristic (e p : ℕ) : Prop :=
  p ≠ 0 ∧ p ∣ e

/-- The branch data g, e, and f are the reusable local input for later tame/wild analysis. -/
theorem chapter11_branch_data_supports_later_tame_wild_analysis
    (e p : ℕ) (hp : p = 0 ∨ Nat.Prime p) :
    chapter11TameAtResidueCharacteristic e p ∨
      chapter11WildAtResidueCharacteristic e p := by
  rcases hp with rfl | hp
  · exact Or.inl (Or.inl rfl)
  by_cases hdiv : p ∣ e
  · exact Or.inr ⟨hp.ne_zero, hdiv⟩
  · exact Or.inl (Or.inr (hp.coprime_iff_not_dvd.mpr hdiv).symm)

end
end LastLib.Book01ValuationsDVRsAndCompletions.Chapter11
