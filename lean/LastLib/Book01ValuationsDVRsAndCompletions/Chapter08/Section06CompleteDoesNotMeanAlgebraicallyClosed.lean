import LastLib.Book01ValuationsDVRsAndCompletions.Chapter08.Section05UnitsAndPrincipalUnits

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter08

open Polynomial IsLocalRing
open Filter
open scoped BigOperators LaurentSeries Topology PowerSeries.WithPiTopology

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
    (_hu : IsUnit u)
    (hns : ¬ ∃ y : IsLocalRing.ResidueField A,
      y ^ 2 = IsLocalRing.residue A u) :
    ¬ ∃ x : A, x ^ 2 = u := by
  classical
  rintro ⟨x, hx⟩
  apply hns
  refine ⟨IsLocalRing.residue A x, ?_⟩
  calc
    IsLocalRing.residue A x ^ 2 = IsLocalRing.residue A (x ^ 2) :=
      (map_pow (IsLocalRing.residue A) x 2).symm
    _ = IsLocalRing.residue A u := by rw [hx]

-- The quadratic X^2-u is an explicit algebraic obstruction. -/
theorem chapter08_quadratic_without_root_from_nonsquare_residue
    (A : Type*) [CommRing A] [IsLocalRing A] (u : A)
    (hu : IsUnit u)
    (hns : ¬ ∃ y : IsLocalRing.ResidueField A,
      y ^ 2 = IsLocalRing.residue A u) :
    ¬ ∃ x : A, (Polynomial.X ^ 2 - Polynomial.C u).eval x = 0 := by
  classical
  rintro ⟨x, hx⟩
  apply chapter08_nonsquare_residue_unit_not_square A u hu hns
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
    ∀ f : A[X], f.Monic →
      ∀ a₀ : IsLocalRing.ResidueField A,
        aeval a₀ f = 0 →
        aeval a₀ f.derivative ≠ 0 →
        ∃ a : A, f.IsRoot a ∧ IsLocalRing.residue A a = a₀ := by
  classical
  have hHenselian : HenselianLocalRing A := {
    toIsLocalRing := inferInstance
    is_henselian := by
      intro g hg b hb hunit
      obtain ⟨c, hc, hcmem⟩ :=
        (inferInstance : HenselianRing A (IsLocalRing.maximalIdeal A)).is_henselian
          g hg b hb (hunit.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))
      exact ⟨c, hc, hcmem⟩ }
  intro f hf a₀ hfa₀ hfderiv
  obtain ⟨a₀', ha₀'⟩ := IsLocalRing.residue_surjective a₀
  have hroot : f.eval a₀' ∈ IsLocalRing.maximalIdeal A := by
    apply (IsLocalRing.residue_eq_zero_iff (f.eval a₀')).1
    have hfa₀' : aeval (IsLocalRing.residue A a₀') f = 0 := by
      simpa [ha₀'] using hfa₀
    simpa [aeval_def, IsLocalRing.ResidueField.algebraMap_eq, eval₂_at_apply] using
      hfa₀'
  have hderiv : IsUnit (f.derivative.eval a₀') := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit (f.derivative.eval a₀')).1
    have hfderiv' : aeval (IsLocalRing.residue A a₀') f.derivative ≠ 0 := by
      simpa [ha₀'] using hfderiv
    simpa [aeval_def, IsLocalRing.ResidueField.algebraMap_eq, eval₂_at_apply] using
      hfderiv'
  obtain ⟨a, ha, hmem⟩ := hHenselian.is_henselian f hf a₀' hroot hderiv
  refine ⟨a, ha, ?_⟩
  rw [← sub_eq_zero]
  calc
    IsLocalRing.residue A a - a₀ =
        IsLocalRing.residue A a - IsLocalRing.residue A a₀' := by rw [ha₀']
    _ = IsLocalRing.residue A (a - a₀') := by rw [map_sub]
    _ = 0 := by
      exact (IsLocalRing.residue_eq_zero_iff (a - a₀')).2 hmem

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
