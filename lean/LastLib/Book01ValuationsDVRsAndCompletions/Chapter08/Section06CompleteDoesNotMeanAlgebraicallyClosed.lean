import LastLib.Book01ValuationsDVRsAndCompletions.Chapter08.Section03ThePadicIntegersAndNumbers
import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter08

open Polynomial IsLocalRing
open Filter
open scoped Topology

noncomputable section

/-!
# Chapter 8: Inverse limits and digit expansions

This file is deliberately a statement-generation pass. The declarations use Mathlib's
AdicCompletion, ideal quotients, PadicInt, Padic, PowerSeries, and LaurentSeries
where those interfaces match the book. A few predicates package the adic convergence and
digit notation used in the prose.
-/

/-! # Book 1, Chapter 8, Section 8.6: Complete Does Not Mean Algebraically Closed
-/

/-! ### 8.6 Complete does not mean algebraically closed -/

/-- An approximate root modulo I ^ n. -/
def Chapter08ApproximateRoot
    {A : Type*} [CommRing A] (I : Ideal A) (f : A[X]) (a : A) (n : ℕ) : Prop :=
  f.eval a ∈ I ^ n

/-- A unit whose residue is not a square. -/
def Chapter08NonsquareResidueUnit
    (A : Type*) [CommRing A] [IsLocalRing A] (u : A) : Prop :=
  IsUnit u ∧
    ¬ ∃ y : IsLocalRing.ResidueField A,
      y ^ 2 = IsLocalRing.residue A u

/-- A nonsquare residue unit cannot be a square in the local ring. -/
theorem chapter08_nonsquare_residue_unit_not_square
    (A : Type*) [CommRing A] [IsLocalRing A] (u : A)
    (hns : Chapter08NonsquareResidueUnit A u) :
    ¬ ∃ x : A, x ^ 2 = u := by
  classical
  rintro ⟨x, hx⟩
  apply hns.2
  refine ⟨IsLocalRing.residue A x, ?_⟩
  calc
    IsLocalRing.residue A x ^ 2 = IsLocalRing.residue A (x ^ 2) :=
      (map_pow (IsLocalRing.residue A) x 2).symm
    _ = IsLocalRing.residue A u := by rw [hx]

-- The quadratic X^2-u is an explicit algebraic obstruction. -/
theorem chapter08_quadratic_without_root_from_nonsquare_residue
    (A : Type*) [CommRing A] [IsLocalRing A] (u : A)
    (hns : Chapter08NonsquareResidueUnit A u) :
    ¬ ∃ x : A, (Polynomial.X ^ 2 - Polynomial.C u).eval x = 0 := by
  classical
  rintro ⟨x, hx⟩
  apply chapter08_nonsquare_residue_unit_not_square A u hns
  refine ⟨x, ?_⟩
  exact sub_eq_zero.mp (by
    simpa [Polynomial.eval_sub, Polynomial.eval_pow] using hx)

theorem chapter08_complete_padic_field_not_algebraically_closed
    (p : ℕ) [Fact p.Prime] :
      CompleteSpace (Chapter08PadicNumbers p) ∧
      ¬ IsAlgClosed (Chapter08PadicNumbers p) := by
  classical
  refine ⟨inferInstance, ?_⟩
  intro hclosed
  have hdeg : (Polynomial.X ^ 2 - Polynomial.C (p : Chapter08PadicNumbers p)).degree ≠ 0 := by
    rw [Polynomial.degree_X_pow_sub_C (by decide)]
    norm_num
  obtain ⟨z, hz⟩ := @IsAlgClosed.exists_root
    (Chapter08PadicNumbers p) inferInstance hclosed
    (Polynomial.X ^ 2 - Polynomial.C (p : Chapter08PadicNumbers p)) hdeg
  have hz' : z ^ 2 = (p : Chapter08PadicNumbers p) := by
    exact sub_eq_zero.mp (by
      simpa [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow] using hz)
  have hv := congrArg Padic.valuation hz'
  rw [Padic.valuation_pow, Padic.valuation_p] at hv
  omega

/-! Simple roots do lift: this is the Henselian principle deferred to the next chapter. -/
theorem chapter08_simple_root_lifts_in_complete_local_ring
    (A : Type*) [CommRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    ∀ f : A[X],
      ∀ a₀ : IsLocalRing.ResidueField A,
        aeval a₀ f = 0 →
        aeval a₀ f.derivative ≠ 0 →
        ∃ a : A, f.IsRoot a ∧ IsLocalRing.residue A a = a₀ := by
  sorry

theorem chapter08_complete_local_ring_is_henselian
    (A : Type*) [CommRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    HenselianLocalRing A := by
  classical
  refine {
    toIsLocalRing := inferInstance
    is_henselian := ?_ }
  intro f hf a₀ h₁ h₂
  obtain ⟨a, ha, hmem⟩ :=
    (inferInstance : HenselianRing A (IsLocalRing.maximalIdeal A)).is_henselian
      f hf a₀ h₁ (h₂.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))
  exact ⟨a, ha, hmem⟩

end
end LastLib.Book01ValuationsDVRsAndCompletions.Chapter08
