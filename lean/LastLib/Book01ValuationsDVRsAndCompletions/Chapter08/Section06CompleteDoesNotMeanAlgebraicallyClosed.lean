import LastLib.Book01ValuationsDVRsAndCompletions.Chapter08.Section03ThePadicIntegersAndNumbers
import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter08

open Polynomial IsLocalRing
open Filter
open scoped Ring Topology

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
  classical
  have hensel_of_mem : ∀ (f : A[X]) (a₀ : A),
      f.eval a₀ ∈ IsLocalRing.maximalIdeal A →
      IsUnit (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)
        (f.derivative.eval a₀)) →
      ∃ a : A, f.IsRoot a ∧ a - a₀ ∈ IsLocalRing.maximalIdeal A := by
    intro f a₀ h₁ h₂
    let f' := derivative f
    let c : ℕ → A := fun n =>
      Nat.recOn n a₀ fun _ b => b - f.eval b * (f'.eval b)⁻¹ʳ
    have hc : ∀ n, c (n + 1) = c n - f.eval (c n) *
        (f'.eval (c n))⁻¹ʳ := by
      intro n
      simp only [c]
    have hc_mod : ∀ n, c n ≡ a₀ [SMOD IsLocalRing.maximalIdeal A] := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [hc, sub_eq_add_neg, ← add_zero a₀]
        refine ih.add ?_
        rw [SModEq.zero, Ideal.neg_mem_iff]
        refine (IsLocalRing.maximalIdeal A).mul_mem_right _ ?_
        rw [← SModEq.zero] at h₁ ⊢
        exact (ih.eval f).trans h₁
    have hf'c : ∀ n, IsUnit (f'.eval (c n)) := by
      intro n
      have := isLocalHom_of_le_jacobson_bot
        (IsLocalRing.maximalIdeal A)
        (IsAdicComplete.le_jacobson_bot (IsLocalRing.maximalIdeal A))
      apply IsUnit.of_map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))
      convert! h₂ using 1
      exact SModEq.def.mp ((hc_mod n).eval _)
    have hfcI : ∀ n, f.eval (c n) ∈
        (IsLocalRing.maximalIdeal A) ^ (n + 1) := by
      intro n
      induction n with
      | zero => simpa only [Nat.rec_zero, zero_add, pow_one] using! h₁
      | succ n ih =>
        rw [← taylor_eval_sub (c n), hc, sub_eq_add_neg, sub_eq_add_neg,
          add_neg_cancel_comm]
        rw [eval_eq_sum, sum_over_range' _ _ _
          (lt_add_of_pos_right _ zero_lt_two), ←
          Finset.sum_range_add_sum_Ico _ (Nat.le_add_left _ _)]
        swap
        · intro i
          rw [zero_mul]
        refine Ideal.add_mem _ ?_ ?_
        · rw [← one_add_one_eq_two, Finset.sum_range_succ, Finset.range_one,
            Finset.sum_singleton, taylor_coeff_zero, taylor_coeff_one,
            pow_zero, pow_one, mul_one, mul_neg, mul_left_comm,
            Ring.mul_inverse_cancel _ (hf'c n), mul_one, add_neg_cancel]
          exact Ideal.zero_mem _
        · refine Submodule.sum_mem _ ?_
          simp only [Finset.mem_Ico]
          rintro i ⟨h2i, _⟩
          have aux : n + 2 ≤ i * (n + 1) := by
            trans 2 * (n + 1) <;> nlinarith only [h2i]
          refine Ideal.mul_mem_left _ _
            (Ideal.pow_le_pow_right aux ?_)
          rw [pow_mul']
          exact Ideal.pow_mem_pow
            ((Ideal.neg_mem_iff _).2 <|
              Ideal.mul_mem_right _ _ ih) _
    have aux : ∀ m n, m ≤ n → c m ≡ c n
        [SMOD ((IsLocalRing.maximalIdeal A) ^ m • (⊤ : Ideal A))] := by
      intro m n hmn
      rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      clear hmn
      induction k with
      | zero => rw [add_zero]
      | succ k ih =>
        rw [← add_assoc, hc, ← add_zero (c m), sub_eq_add_neg]
        refine ih.add ?_
        symm
        rw [SModEq.zero, Ideal.neg_mem_iff]
        refine Ideal.mul_mem_right _ _
          (Ideal.pow_le_pow_right ?_ (hfcI _))
        rw [add_assoc]
        exact le_self_add
    obtain ⟨a, ha⟩ := IsPrecomplete.prec' c (aux _ _)
    refine ⟨a, ?_, ?_⟩
    · show f.IsRoot a
      suffices ∀ n, f.eval a ≡ 0
          [SMOD ((IsLocalRing.maximalIdeal A) ^ n • (⊤ : Ideal A))] by
        exact IsHausdorff.haus' _ this
      intro n
      specialize ha n
      rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at ha ⊢
      refine (ha.symm.eval f).trans ?_
      rw [SModEq.zero]
      exact Ideal.pow_le_pow_right le_self_add (hfcI _)
    · show a - a₀ ∈ IsLocalRing.maximalIdeal A
      specialize ha (0 + 1)
      rw [hc, pow_one, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one,
        sub_eq_add_neg] at ha
      rw [← SModEq.sub_mem, ← add_zero a₀]
      refine ha.symm.trans (SModEq.rfl.add ?_)
      rw [SModEq.zero, Ideal.neg_mem_iff]
      exact Ideal.mul_mem_right _ _ h₁
  intro f a₀ h₁ h₂
  obtain ⟨a₀', ha₀'⟩ := IsLocalRing.residue_surjective a₀
  have h₁' : f.eval a₀' ∈ IsLocalRing.maximalIdeal A := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change IsLocalRing.residue A (f.eval a₀') = 0
    have h₁'' := h₁
    rw [← ha₀'] at h₁''
    simpa [aeval_def, ResidueField.algebraMap_eq, eval₂_at_apply] using h₁''
  have h₂' : IsUnit (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)
      (f.derivative.eval a₀')) := by
    have hderiv_res : IsLocalRing.residue A
        (f.derivative.eval a₀') ≠ 0 := by
      have h₂'' := h₂
      rw [← ha₀'] at h₂''
      simpa [aeval_def, ResidueField.algebraMap_eq, eval₂_at_apply] using h₂''
    have hunit : IsUnit (f.derivative.eval a₀') :=
      (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hderiv_res
    exact IsUnit.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) hunit
  obtain ⟨a, ha, hmem⟩ := hensel_of_mem f a₀' h₁' h₂'
  refine ⟨a, ha, ?_⟩
  rw [← ha₀', ← sub_eq_zero, ← map_sub]
  change (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a -
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a₀') = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem

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
