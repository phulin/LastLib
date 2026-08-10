import Mathlib

namespace LastLib.Book01ValuationsDVRsAndCompletions
namespace Chapter09

universe u uK uL uΓ uA uH uC uI

open scoped BigOperators Polynomial WithZeroTopology
open Ideal IsLocalRing Polynomial

noncomputable section

local instance chapter09FactPrime7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
local instance chapter09FactPrime2 : Fact (Nat.Prime 2) := ⟨by norm_num⟩

/-! # Chapter 9: Hensel lifting

This file is a statement-generation pass for Chapter 9 of Book 1.  The
declarations deliberately keep the hypotheses visible: in particular, a
complete DVR means adic completeness, while the valuation form is stated for
an arbitrary additive valuation.
-/

/-! ## Common residue-ring and valuation interfaces -/

/-- The residue ring of a local ring, written as a quotient by its maximal ideal. -/
abbrev ResidueRing (A : Type*) [CommRing A] [IsLocalRing A] :=
  A ⧸ IsLocalRing.maximalIdeal A

/-- The canonical map from a local ring to its residue ring. -/
def residueMap (A : Type*) [CommRing A] [IsLocalRing A] : A →+* ResidueRing A :=
  Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)

/-- The residue class of an element of a local ring. -/
def residueClass {A : Type*} [CommRing A] [IsLocalRing A] (a : A) : ResidueRing A :=
  residueMap A a

/-- Reduction of a polynomial to the residue ring. -/
def residuePolynomial {A : Type*} [CommRing A] [IsLocalRing A] (f : A[X]) :
    Polynomial (ResidueRing A) :=
  f.map (residueMap A)

/-- Congruence modulo an ideal, in a form convenient for chapter statements. -/
def CongruentModIdeal {A : Type*} [Ring A] (I : Ideal A) (a b : A) : Prop :=
  a - b ∈ I

/-- Every coefficient of a polynomial belongs to a specified ideal. -/
def PolynomialCoefficientsInIdeal {A : Type*} [Semiring A] (I : Ideal A) (f : A[X]) : Prop :=
  ∀ n : ℕ, f.coeff n ∈ I

/-- Every coefficient of a polynomial over a field lies in a chosen subring. -/
def PolynomialCoefficientsInSubring {K : Type*} [Field K] (A : Subring K) (f : K[X]) : Prop :=
  ∀ n : ℕ, f.coeff n ∈ A

/-- A subring described as the nonnegative part of an additive valuation. -/
def IsValuationSubring {K Γ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (A : Subring K)
    (v : AddValuation K Γ) : Prop :=
  ∀ x : K, x ∈ A ↔ v x ≥ 0

/-- A complete DVR for this chapter: a DVR complete and separated in the maximal-ideal topology. -/
class CompleteDVR (A : Type*) [CommRing A] [IsDomain A] : Prop
    extends IsDiscreteValuationRing A where
  isAdicComplete' : IsAdicComplete (IsLocalRing.maximalIdeal A) A

/-- The adic-completeness field of `CompleteDVR` is available as an instance. -/
instance CompleteDVR.isAdicComplete (A : Type*) [CommRing A] [IsDomain A]
    [hA : CompleteDVR A] : IsAdicComplete (IsLocalRing.maximalIdeal A) A :=
  hA.isAdicComplete'

/-- A residue root together with the nonvanishing derivative condition. -/
def IsSimpleResidueRoot {A : Type*} [CommRing A] [IsLocalRing A]
    (f : A[X]) (a : ResidueRing A) : Prop :=
  (residuePolynomial f).eval a = 0 ∧
    IsUnit ((residuePolynomial f).derivative.eval a)

/-- In a DVR, an irreducible element is the Mathlib notion of a uniformizer. -/
def IsUniformizer {A : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (π : A) : Prop :=
  Irreducible π

/-- The additive valuation supplied by Mathlib for a DVR. -/
noncomputable def chapterDvrValuation (A : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] : AddValuation A ℕ∞ :=
  IsDiscreteValuationRing.addVal A

/-- In a DVR, uniformizers are precisely generators of the maximal ideal. -/
theorem isUniformizer_iff_maximalIdeal_span {A : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (π : A) :
    IsUniformizer π ↔ IsLocalRing.maximalIdeal A = Ideal.span ({π} : Set A) := by
  simpa [IsUniformizer] using
    (IsDiscreteValuationRing.irreducible_iff_uniformizer (R := A) π)

/-! ## 9.1 Correcting an approximate root -/

/-- The quadratic example `X² - c` used throughout the chapter. -/
def quadraticPolynomial {R : Type*} [CommRing R] (c : R) : R[X] :=
  X ^ 2 - C c

/-- The second-order Taylor identity `f(a+h)=f(a)+h f'(a)+h² g`. -/
theorem taylor_second_order {A : Type*} [CommRing A] (f : A[X]) (a h : A) :
    ∃ g : A,
      f.eval (a + h) = f.eval a + h * f.derivative.eval a + h ^ 2 * g := by
  obtain ⟨g, hg⟩ := f.exists_mul_sq_add_linear_part_eq_eval_add a h
  refine ⟨g, ?_⟩
  rw [← hg]
  ring

/-- Newton's correction, using Mathlib's globally defined ring inverse. -/
noncomputable def newtonCorrection {R : Type*} [CommRing R] (f : R[X]) (a : R) : R :=
  a - f.eval a * Ring.inverse (f.derivative.eval a)

/-- The sequence of Newton iterates. -/
noncomputable def newtonIterate {R : Type*} [CommRing R] (f : R[X]) (a₀ : R) : ℕ → R
  | 0 => a₀
  | n + 1 => newtonCorrection f (newtonIterate f a₀ n)

/-- Over a field, the ring-inverse definition is the usual Newton quotient. -/
theorem newtonCorrection_as_division {K : Type*} [Field K] (f : K[X]) (a : K)
    (h : f.derivative.eval a ≠ 0) :
    newtonCorrection f a = a - f.eval a / f.derivative.eval a := by
  have _h := h
  rw [newtonCorrection, div_eq_mul_inv, Ring.inverse_eq_inv]

/-- Polynomial evaluation preserves congruence modulo an ideal. -/
theorem polynomial_eval_congruent_mod_ideal {A : Type*} [CommRing A]
    (I : Ideal A) (f : A[X]) {a b : A} (hab : CongruentModIdeal I a b) :
    CongruentModIdeal I (f.eval a) (f.eval b) := by
  unfold CongruentModIdeal at hab ⊢
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change Ideal.Quotient.mk I (f.eval a - f.eval b) = 0
  rw [map_sub, ← eval_map_apply, ← eval_map_apply]
  rw [sub_eq_zero]
  rw [(Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := I) a b).mpr hab]

/-- Newton corrections remain in the maximal ideal when the current error does. -/
theorem newton_correction_congruent {A : Type*} [CommRing A] [IsLocalRing A]
    (f : A[X]) (a : A) (hfa : f.eval a ∈ IsLocalRing.maximalIdeal A) :
    CongruentModIdeal (IsLocalRing.maximalIdeal A) (newtonCorrection f a) a := by
  unfold CongruentModIdeal
  rw [show newtonCorrection f a - a =
      -(f.eval a * Ring.inverse (f.derivative.eval a)) by
        unfold newtonCorrection
        ring]
  apply (IsLocalRing.maximalIdeal A).neg_mem
  simpa [mul_comm] using
    (IsLocalRing.maximalIdeal A).mul_mem_left (Ring.inverse (f.derivative.eval a)) hfa

/-- The derivative has the same residue at congruent points. -/
theorem derivative_evaluation_congruent {A : Type*} [CommRing A] [IsLocalRing A]
    (f : A[X]) {a b : A}
    (hab : CongruentModIdeal (IsLocalRing.maximalIdeal A) a b) :
    CongruentModIdeal (IsLocalRing.maximalIdeal A)
      (f.derivative.eval a) (f.derivative.eval b) := by
  exact polynomial_eval_congruent_mod_ideal (IsLocalRing.maximalIdeal A) f.derivative hab

/-- A unit derivative stays a unit throughout the Newton residue class. -/
theorem derivative_unit_on_residue_class {A : Type*} [CommRing A] [IsLocalRing A]
    (f : A[X]) {a a₀ : A}
    (ha : CongruentModIdeal (IsLocalRing.maximalIdeal A) a a₀)
    (ha₀ : IsUnit (f.derivative.eval a₀)) :
    IsUnit (f.derivative.eval a) := by
  rw [← notMem_maximalIdeal]
  intro hmem
  have hcongr := derivative_evaluation_congruent f ha
  have hdiff := (IsLocalRing.maximalIdeal A).sub_mem hmem hcongr
  have hfa0 : f.derivative.eval a₀ ∈ IsLocalRing.maximalIdeal A := by
    simpa [sub_eq_add_neg, add_assoc] using hdiff
  exact (notMem_maximalIdeal.mpr ha₀) hfa0

/-- In a complete DVR, the valuation of a Newton error at least doubles. -/
theorem newton_error_valuation_doubles {A : Type*} [CommRing A] [IsDomain A]
    [CompleteDVR A] (f : A[X]) (a : A)
    (hfa : f.eval a ∈ IsLocalRing.maximalIdeal A)
    (hunit : IsUnit (f.derivative.eval a)) :
    chapterDvrValuation A (f.eval (newtonCorrection f a)) ≥
      chapterDvrValuation A (f.eval a) + chapterDvrValuation A (f.eval a) := by
  have _hfa := hfa
  let v := chapterDvrValuation A
  obtain ⟨g, hg⟩ := taylor_second_order f a (newtonCorrection f a - a)
  have hcancel :
      f.eval a + (newtonCorrection f a - a) * f.derivative.eval a = 0 := by
    rw [show newtonCorrection f a - a =
        -(f.eval a * Ring.inverse (f.derivative.eval a)) by
          unfold newtonCorrection
          ring]
    rw [neg_mul, mul_assoc, Ring.inverse_mul_cancel _ hunit, mul_one]
    ring
  have heq : f.eval (newtonCorrection f a) =
      (newtonCorrection f a - a) ^ 2 * g := by
    calc
      f.eval (newtonCorrection f a) =
          f.eval (a + (newtonCorrection f a - a)) := by
            congr 1
            ring
      _ = f.eval a + (newtonCorrection f a - a) * f.derivative.eval a +
            (newtonCorrection f a - a) ^ 2 * g := hg
      _ = (newtonCorrection f a - a) ^ 2 * g := by
        rw [hcancel, zero_add]
  have hinv : IsUnit (Ring.inverse (f.derivative.eval a)) := hunit.ringInverse
  have hvalinv : v (Ring.inverse (f.derivative.eval a)) = 0 :=
    (IsDiscreteValuationRing.addVal_eq_zero_iff (R := A)).mpr hinv
  have hcorr : v (newtonCorrection f a - a) = v (f.eval a) := by
    rw [show newtonCorrection f a - a =
        -(f.eval a * Ring.inverse (f.derivative.eval a)) by
          unfold newtonCorrection
          ring]
    simp [v.map_neg, v.map_mul, hvalinv]
  rw [heq, v.map_mul, v.map_pow, hcorr]
  have hle : v (f.eval a) + v (f.eval a) ≤
      (v (f.eval a) + v (f.eval a)) + v g :=
    le_add_of_nonneg_right (show (0 : ℕ∞) ≤ v g from zero_le)
  simpa only [two_smul] using hle

/-- The correction has the same DVR valuation as the current error when the derivative is a unit. -/
theorem newton_correction_valuation {A : Type*} [CommRing A] [IsDomain A]
    [CompleteDVR A] (f : A[X]) (a : A)
    (hunit : IsUnit (f.derivative.eval a)) :
    chapterDvrValuation A (newtonCorrection f a - a) =
      chapterDvrValuation A (f.eval a) := by
  let v := chapterDvrValuation A
  have hinv : IsUnit (Ring.inverse (f.derivative.eval a)) := hunit.ringInverse
  have hvalinv : v (Ring.inverse (f.derivative.eval a)) = 0 :=
    (IsDiscreteValuationRing.addVal_eq_zero_iff (R := A)).mpr hinv
  rw [show newtonCorrection f a - a =
      -(f.eval a * Ring.inverse (f.derivative.eval a)) by
        unfold newtonCorrection
        ring]
  rw [v.map_neg, v.map_mul, hvalinv, add_zero]

/-- An adic Cauchy sequence, stated without choosing a separate topology. -/
def AdicCauchySeq {A : Type*} [CommRing A] [IsLocalRing A] (s : ℕ → A) : Prop :=
  ∀ n : ℕ, ∃ N : ℕ, ∀ m k : ℕ, N ≤ m → N ≤ k →
    s m - s k ∈ (IsLocalRing.maximalIdeal A) ^ n

/-- An adic limit of a sequence. -/
def IsAdicLimit {A : Type*} [CommRing A] [IsLocalRing A] (s : ℕ → A) (a : A) : Prop :=
  ∀ n : ℕ, s n - a ∈ (IsLocalRing.maximalIdeal A) ^ n

private theorem newton_iterates_error_and_cauchy
    {A : Type*} [CommRing A] [IsLocalRing A]
    (f : A[X]) (a₀ : A)
    (hfa : f.eval a₀ ∈ IsLocalRing.maximalIdeal A)
    (hunit : IsUnit (f.derivative.eval a₀)) :
    (∀ n : ℕ, f.eval (newtonIterate f a₀ n) ∈
      (IsLocalRing.maximalIdeal A) ^ (n + 1)) ∧
    (∀ m n : ℕ, m ≤ n →
      newtonIterate f a₀ m - newtonIterate f a₀ n ∈
        (IsLocalRing.maximalIdeal A) ^ m) := by
  let I : Ideal A := IsLocalRing.maximalIdeal A
  have hc : ∀ n : ℕ,
      newtonIterate f a₀ (n + 1) =
        newtonIterate f a₀ n -
          f.eval (newtonIterate f a₀ n) *
            Ring.inverse (f.derivative.eval (newtonIterate f a₀ n)) := by
    intro n
    simp [newtonIterate, newtonCorrection]
  have hres : ∀ n : ℕ,
      newtonIterate f a₀ n - a₀ ∈ I := by
    intro n
    induction n with
    | zero => simpa only [newtonIterate, sub_self] using I.zero_mem
    | succ n ih =>
        have hfn : f.eval (newtonIterate f a₀ n) ∈ I := by
          have hcongr := polynomial_eval_congruent_mod_ideal I f ih
          have hcongr' : f.eval (newtonIterate f a₀ n) - f.eval a₀ ∈ I := hcongr
          simpa [sub_eq_add_neg, add_assoc] using I.add_mem hcongr' hfa
        have hprod : f.eval (newtonIterate f a₀ n) *
            Ring.inverse (f.derivative.eval (newtonIterate f a₀ n)) ∈ I :=
          I.mul_mem_right _ hfn
        rw [hc n]
        convert I.sub_mem ih hprod using 1 ; ring
  have hunitn : ∀ n : ℕ,
      IsUnit (f.derivative.eval (newtonIterate f a₀ n)) := by
    intro n
    exact derivative_unit_on_residue_class f (hres n) hunit
  have herror : ∀ n : ℕ,
      f.eval (newtonIterate f a₀ n) ∈ I ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
        change f.eval a₀ ∈ I ^ 1
        simpa only [I, pow_one] using hfa
    | succ n ih =>
        obtain ⟨g, hg⟩ :=
          taylor_second_order f (newtonIterate f a₀ n)
            (newtonIterate f a₀ (n + 1) - newtonIterate f a₀ n)
        have hcancel :
            f.eval (newtonIterate f a₀ n) +
              (newtonIterate f a₀ (n + 1) - newtonIterate f a₀ n) *
                f.derivative.eval (newtonIterate f a₀ n) = 0 := by
          rw [show newtonIterate f a₀ (n + 1) - newtonIterate f a₀ n =
              -(f.eval (newtonIterate f a₀ n) *
                Ring.inverse (f.derivative.eval (newtonIterate f a₀ n))) by
                rw [hc n]
                ring]
          rw [neg_mul, mul_assoc, Ring.inverse_mul_cancel _ (hunitn n), mul_one]
          ring
        have hdelta :
            newtonIterate f a₀ (n + 1) - newtonIterate f a₀ n ∈ I ^ (n + 1) := by
          rw [show newtonIterate f a₀ (n + 1) - newtonIterate f a₀ n =
              -(f.eval (newtonIterate f a₀ n) *
                Ring.inverse (f.derivative.eval (newtonIterate f a₀ n))) by
                rw [hc n]
                ring]
          exact (I ^ (n + 1)).neg_mem
            ((I ^ (n + 1)).mul_mem_right _ ih)
        have hsq :
            (newtonIterate f a₀ (n + 1) - newtonIterate f a₀ n) ^ 2 ∈
              I ^ (2 * (n + 1)) := by
          rw [pow_two]
          have hm := Ideal.mul_mem_mul hdelta hdelta
          simpa [← pow_add, two_mul, Nat.add_comm, Nat.add_left_comm,
            Nat.add_assoc] using hm
        have hsq' :
            (newtonIterate f a₀ (n + 1) - newtonIterate f a₀ n) ^ 2 * g ∈
              I ^ (n + 2) := by
          exact (I ^ (n + 2)).mul_mem_right g
            ((Ideal.pow_le_pow_right (I := I) (by omega)) hsq)
        rw [show newtonIterate f a₀ (n + 1) =
            newtonIterate f a₀ n +
              (newtonIterate f a₀ (n + 1) - newtonIterate f a₀ n) by ring,
          hg, hcancel, zero_add]
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsq'
  have hstep : ∀ n : ℕ,
      newtonIterate f a₀ (n + 1) - newtonIterate f a₀ n ∈ I ^ (n + 1) := by
    intro n
    rw [show newtonIterate f a₀ (n + 1) - newtonIterate f a₀ n =
        -(f.eval (newtonIterate f a₀ n) *
          Ring.inverse (f.derivative.eval (newtonIterate f a₀ n))) by
          rw [hc n]
          ring]
    exact (I ^ (n + 1)).neg_mem
      ((I ^ (n + 1)).mul_mem_right _ (herror n))
  refine ⟨herror, ?_⟩
  intro m n hmn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  induction k with
  | zero => simp
  | succ k ih =>
      have hinc :
          newtonIterate f a₀ (m + k + 1) -
              newtonIterate f a₀ (m + k) ∈ I ^ m := by
        apply Ideal.pow_le_pow_right (by omega)
        simpa [Nat.add_assoc] using hstep (m + k)
      have hsum :
          newtonIterate f a₀ m - newtonIterate f a₀ (m + k + 1) =
            (newtonIterate f a₀ m - newtonIterate f a₀ (m + k)) +
              (newtonIterate f a₀ (m + k) -
                newtonIterate f a₀ (m + k + 1)) := by ring
      have hsum' :
          newtonIterate f a₀ m - newtonIterate f a₀ (m + (k + 1)) =
            (newtonIterate f a₀ m - newtonIterate f a₀ (m + k)) +
              (newtonIterate f a₀ (m + k) -
                newtonIterate f a₀ (m + k + 1)) := by
        rw [Nat.add_assoc]
        exact hsum
      rw [hsum']
      apply I ^ m |>.add_mem (ih (by omega))
      simpa [sub_eq_add_neg] using (I ^ m).neg_mem hinc

/-- Newton iterates form an adic Cauchy sequence under the simple-root hypotheses. -/
theorem newton_iterates_adic_cauchy {A : Type*} [CommRing A] [IsDomain A]
    [CompleteDVR A] (f : A[X]) (a₀ : A)
    (hfa : f.eval a₀ ∈ IsLocalRing.maximalIdeal A)
    (hunit : IsUnit (f.derivative.eval a₀)) :
    AdicCauchySeq (newtonIterate f a₀) := by
  obtain ⟨_, hcauchy⟩ := newton_iterates_error_and_cauchy f a₀ hfa hunit
  intro n
  refine ⟨n, ?_⟩
  intro m k hnm hnk
  have hm := hcauchy n m hnm
  have hk := hcauchy n k hnk
  have hdiff : newtonIterate f a₀ m - newtonIterate f a₀ k =
      (newtonIterate f a₀ m - newtonIterate f a₀ n) +
        (newtonIterate f a₀ n - newtonIterate f a₀ k) := by ring
  rw [hdiff]
  have hmn' : newtonIterate f a₀ m - newtonIterate f a₀ n ∈
      IsLocalRing.maximalIdeal A ^ n := by
    convert (IsLocalRing.maximalIdeal A ^ n).neg_mem hm using 1 ; ring
  exact (IsLocalRing.maximalIdeal A ^ n).add_mem hmn' hk

/-- Completeness supplies an adic limit for the Newton iterates. -/
theorem newton_iterates_have_limit {A : Type*} [CommRing A] [IsDomain A]
    [CompleteDVR A] (f : A[X]) (a₀ : A)
    (hfa : f.eval a₀ ∈ IsLocalRing.maximalIdeal A)
    (hunit : IsUnit (f.derivative.eval a₀)) :
    ∃ a : A, IsAdicLimit (newtonIterate f a₀) a := by
  obtain ⟨_, hcauchy⟩ := newton_iterates_error_and_cauchy f a₀ hfa hunit
  obtain ⟨a, ha⟩ := IsPrecomplete.prec' (I := IsLocalRing.maximalIdeal A)
    (M := A) (newtonIterate f a₀) (by
    intro m n hmn
    rw [SModEq.sub_mem]
    simpa only [← Ideal.one_eq_top, smul_eq_mul, mul_one] using
      hcauchy m n hmn)
  refine ⟨a, ?_⟩
  intro n
  have hn := ha n
  rw [SModEq.sub_mem] at hn
  simpa only [← Ideal.one_eq_top, smul_eq_mul, mul_one] using hn

/-- Simple-root Hensel lifting: the exact assertion of Theorem 9.1. -/
theorem hensel_simple_root {A : Type*} [CommRing A] [IsDomain A]
    [CompleteDVR A] (f : A[X]) (a₀ : A)
    (hfa : f.eval a₀ ∈ IsLocalRing.maximalIdeal A)
    (hunit : IsUnit (f.derivative.eval a₀)) :
    ∃! a : A,
      f.eval a = 0 ∧
        CongruentModIdeal (IsLocalRing.maximalIdeal A) a a₀ := by
  obtain ⟨a, ha⟩ := newton_iterates_have_limit f a₀ hfa hunit
  have hroot : f.eval a = 0 := by
    apply IsHausdorff.haus' (R := A) (I := IsLocalRing.maximalIdeal A) (M := A)
      (f.eval a)
    intro n
    have hn := ha (n + 1)
    have hfn : f.eval (newtonIterate f a₀ (n + 1)) ∈
        (IsLocalRing.maximalIdeal A) ^ (n + 1 + 1) :=
      (newton_iterates_error_and_cauchy f a₀ hfa hunit).1 (n + 1)
    have hev : CongruentModIdeal ((IsLocalRing.maximalIdeal A) ^ (n + 1))
        (f.eval (newtonIterate f a₀ (n + 1))) (f.eval a) :=
      polynomial_eval_congruent_mod_ideal
        ((IsLocalRing.maximalIdeal A) ^ (n + 1)) f hn
    have hfn' : f.eval (newtonIterate f a₀ (n + 1)) ∈
        (IsLocalRing.maximalIdeal A) ^ (n + 1) :=
      Ideal.pow_le_pow_right (by omega) hfn
    have hfa' : f.eval a ∈ (IsLocalRing.maximalIdeal A) ^ (n + 1) := by
      unfold CongruentModIdeal at hev
      have hmem := ((IsLocalRing.maximalIdeal A) ^ (n + 1)).sub_mem hfn' hev
      simpa [sub_sub_cancel] using hmem
    rw [SModEq.sub_mem]
    have hfa'' : f.eval a ∈ IsLocalRing.maximalIdeal A ^ n :=
      Ideal.pow_le_pow_right (by omega) hfa'
    simpa only [sub_zero, ← Ideal.one_eq_top, smul_eq_mul, mul_one] using hfa''
  have hcongr : CongruentModIdeal (IsLocalRing.maximalIdeal A) a a₀ := by
    have hn := ha 1
    have hres1 : newtonIterate f a₀ 1 - a₀ ∈ IsLocalRing.maximalIdeal A := by
      simpa [CongruentModIdeal, newtonIterate] using
        (newton_correction_congruent f a₀ hfa)
    have hn' : newtonIterate f a₀ 1 - a ∈ IsLocalRing.maximalIdeal A := by
      simpa [pow_one] using hn
    have hmem := (IsLocalRing.maximalIdeal A).sub_mem hres1 hn'
    unfold CongruentModIdeal
    convert hmem using 1 ; ring
  refine ⟨a, ⟨hroot, hcongr⟩, ?_⟩
  intro b hb
  have habmem : a - b ∈ IsLocalRing.maximalIdeal A := by
    have h₁ := hcongr
    have h₂ := hb.2
    unfold CongruentModIdeal at h₁ h₂
    have := (IsLocalRing.maximalIdeal A).sub_mem h₁ h₂
    simpa [sub_eq_add_neg, add_assoc] using this
  have habunit : ¬ IsUnit (a - b) := by
    intro hab
    exact (notMem_maximalIdeal.mpr hab) habmem
  have hunit_a : IsUnit (f.derivative.eval a) :=
    derivative_unit_on_residue_class f hcongr hunit
  exact (IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub
    (f := f) (a := a) (b := b) hroot hb.1 habunit hunit_a).symm

/-- Polynomial division in two variables, packaged as a divided-difference statement. -/
def IsDividedDifference {A : Type*} [CommRing A] (f : A[X]) (a b q : A) : Prop :=
  f.eval a - f.eval b = (a - b) * q

/-- Every polynomial admits a divided difference at two points. -/
theorem exists_divided_difference {A : Type*} [CommRing A] (f : A[X]) (a b : A) :
    ∃ q : A, IsDividedDifference f a b q := by
  obtain ⟨q, hq⟩ := Polynomial.sub_dvd_eval_sub a b f
  refine ⟨q, ?_⟩
  exact hq

/-- The divided difference is congruent to the derivative in the common residue class. -/
theorem divided_difference_congruent_derivative {A : Type*} [CommRing A] [IsLocalRing A]
    (f : A[X]) {a b a₀ : A}
    (ha : CongruentModIdeal (IsLocalRing.maximalIdeal A) a a₀)
    (hb : CongruentModIdeal (IsLocalRing.maximalIdeal A) b a₀) :
    ∃ q : A,
      IsDividedDifference f a b q ∧
        CongruentModIdeal (IsLocalRing.maximalIdeal A) q (f.derivative.eval a₀) := by
  let qpoly : A[X] := f /ₘ (X - C b)
  refine ⟨qpoly.eval a, ?_, ?_⟩
  · unfold IsDividedDifference
    have hpoly :=
      X_sub_C_mul_divByMonic_eq_sub_modByMonic f b
    rw [modByMonic_X_sub_C_eq_C_eval] at hpoly
    have heval := congrArg (fun P : A[X] => P.eval a) hpoly
    simpa [qpoly, eval_mul, eval_sub, eval_X, eval_C] using heval.symm
  · have hab : a - b ∈ IsLocalRing.maximalIdeal A := by
      unfold CongruentModIdeal at ha hb
      have h := (IsLocalRing.maximalIdeal A).sub_mem ha hb
      simpa [sub_eq_add_neg, add_assoc] using h
    have hder :=
      divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative f b
    have hder' := congrArg (fun P : A[X] => P.eval a) hder
    have hqdiff : qpoly.eval a - f.derivative.eval a ∈
        IsLocalRing.maximalIdeal A := by
      have hprod := (IsLocalRing.maximalIdeal A).mul_mem_left
        (qpoly.derivative.eval a) hab
      have hneg := (IsLocalRing.maximalIdeal A).neg_mem hprod
      have heq : qpoly.eval a - f.derivative.eval a =
          -((a - b) * qpoly.derivative.eval a) := by
        have hder_eval :
            qpoly.eval a + (a - b) * qpoly.derivative.eval a =
              f.derivative.eval a := by
          simpa [qpoly, eval_add, eval_mul, eval_sub, eval_X, eval_C] using hder'
        rw [← hder_eval]
        simp
      rw [heq]
      simpa [mul_comm] using hneg
    have hdercongr := derivative_evaluation_congruent f ha
    unfold CongruentModIdeal at hdercongr ⊢
    have hadd := (IsLocalRing.maximalIdeal A).add_mem hqdiff hdercongr
    simpa [sub_eq_add_neg, add_assoc] using hadd

/-- Two roots in the simple-root residue class coincide by the divided-difference argument. -/
theorem simple_root_residue_class_unique {A : Type*} [CommRing A] [IsDomain A]
    [CompleteDVR A] (f : A[X]) (a₀ a b : A)
    (ha : f.eval a = 0)
    (hb : f.eval b = 0)
    (ha₀ : IsUnit (f.derivative.eval a₀))
    (hca : CongruentModIdeal (IsLocalRing.maximalIdeal A) a a₀)
    (hcb : CongruentModIdeal (IsLocalRing.maximalIdeal A) b a₀) :
    a = b := by
  obtain ⟨q, hq, hqcongr⟩ := divided_difference_congruent_derivative f hca hcb
  have hqunit : IsUnit q := by
    rw [← notMem_maximalIdeal]
    intro hqmem
    have hqdiff := hqcongr
    unfold CongruentModIdeal at hqdiff
    have hdermem : f.derivative.eval a₀ ∈ IsLocalRing.maximalIdeal A := by
      have := (IsLocalRing.maximalIdeal A).sub_mem hqmem hqdiff
      simpa [sub_eq_add_neg, add_assoc] using this
    exact (notMem_maximalIdeal.mpr ha₀) hdermem
  have habq : (a - b) * q = 0 := by
    unfold IsDividedDifference at hq
    simpa [ha, hb] using hq
  rcases mul_eq_zero.mp habq with hab | hqzero
  · exact sub_eq_zero.mp hab
  · exact (hqunit.ne_zero hqzero).elim

private theorem mem_maximalIdeal_pow_iff_dvrVal_ge
    {A : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (x : A) (r : ℕ) :
    x ∈ (IsLocalRing.maximalIdeal A) ^ r ↔
      (r : ℕ∞) ≤ chapterDvrValuation A x := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← IsDiscreteValuationRing.addVal_le_iff_dvd, hπ.addVal_pow]
  rfl

/-- Once the error has valuation at least `r`, the next Newton error has valuation at least `2r`. -/
theorem newton_precision_doubles {A : Type*} [CommRing A] [IsDomain A]
    [CompleteDVR A] (f : A[X]) (a : A) (r : ℕ)
    (hunit : IsUnit (f.derivative.eval a))
    (hprecision : f.eval a ∈ (IsLocalRing.maximalIdeal A) ^ r) :
    f.eval (newtonCorrection f a) ∈ (IsLocalRing.maximalIdeal A) ^ (2 * r) := by
  by_cases hr : r = 0
  · simp [hr]
  have hfa : f.eval a ∈ IsLocalRing.maximalIdeal A := by
    simpa only [pow_one] using
      (Ideal.pow_le_pow_right (Nat.one_le_iff_ne_zero.mpr hr)) hprecision
  have hdouble := newton_error_valuation_doubles f a hfa hunit
  have hval : (r : ℕ∞) ≤ chapterDvrValuation A (f.eval a) :=
    (mem_maximalIdeal_pow_iff_dvrVal_ge (f.eval a) r).mp hprecision
  have hval' : ((2 * r : ℕ) : ℕ∞) ≤
      chapterDvrValuation A (f.eval a) + chapterDvrValuation A (f.eval a) := by
    simpa [Nat.cast_mul, two_mul] using add_le_add hval hval
  apply (mem_maximalIdeal_pow_iff_dvrVal_ge
    (f.eval (newtonCorrection f a)) (2 * r)).mpr
  exact hval'.trans hdouble

/-- The example `X²-p` has a root at zero modulo `p`. -/
theorem padic_x_sq_sub_p_has_mod_p_root_zero (p : ℕ) [Fact p.Prime] :
    (quadraticPolynomial (p : ZMod p)).eval 0 = 0 := by
  simp [quadraticPolynomial]

/-- The same polynomial has no root in `ℚ_[p]`, because square valuations are even. -/
theorem padic_x_sq_sub_p_has_no_root (p : ℕ) [Fact p.Prime] :
    ¬ ∃ x : ℚ_[p], x ^ 2 = (p : ℚ_[p]) := by
  rintro ⟨x, hx⟩
  have hv := congrArg (Padic.addValuation (p := p)) hx
  rw [pow_two, (Padic.addValuation (p := p)).map_mul] at hv
  have hp0 : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  rw [Padic.addValuation.apply hp0, Padic.valuation_p] at hv
  have hxp : x ≠ 0 := by
    intro hx0
    subst x
    exact hp0 (by simpa using hx.symm)
  rw [Padic.addValuation.apply hxp] at hv
  have hv' : x.valuation + x.valuation = (1 : ℤ) := by
    exact_mod_cast hv
  omega

/-- The additive p-adic valuation of a square is twice the valuation of its base. -/
theorem padic_square_valuation_is_even (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) :
    Padic.addValuation (p := p) (x ^ 2) =
      Padic.addValuation (p := p) x + Padic.addValuation (p := p) x := by
  rw [pow_two]
  exact (Padic.addValuation (p := p)).map_mul x x

/-! ## 9.2 The valuation form -/

/-- The excess of a valuation error beyond twice a fixed derivative value. -/
def valuationExcess {K Γ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (v : AddValuation K Γ)
    (f : K[X]) (s : Γ) (a : K) : Γ :=
  v (f.eval a) - (s + s)

/- The uniformity canonically induced by an additive valuation. -/
noncomputable def Chapter09ValuationUniformSpace
    {K Γ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (v : AddValuation K Γ) : UniformSpace K :=
  (Valued.mk' v.toValuation).toUniformSpace

/- Completeness for the nonarchimedean uniformity attached to `v`. -/
def Chapter09NonarchimedeanComplete
    {K Γ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (v : AddValuation K Γ) : Prop :=
  @CompleteSpace K (Chapter09ValuationUniformSpace v)

/-- A sequence of values tends to infinity in the ordered-value sense. -/
def TendsToTop {Γ : Type*} [Preorder Γ] (s : ℕ → Γ) : Prop :=
  ∀ γ : Γ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → γ ≤ s n

/- Cofinality needed to turn valuation doubling into convergence to the top. -/
def Chapter09DoublingCofinal {Γ : Type*}
    [LinearOrderedAddCommGroupWithTop Γ] (q : Γ) : Prop :=
  ∀ γ : Γ, ∃ n : ℕ, γ ≤ (2 ^ n) • q

/-- The strong triangle inequality for an additive valuation. -/
theorem valuation_strong_triangle {K Γ : Type*} [Ring K]
    [LinearOrderedAddCommMonoidWithTop Γ] (v : AddValuation K Γ) (x y : K) :
    min (v x) (v y) ≤ v (x + y) := by
  exact v.map_add x y

/-- Unequal valuation terms cannot cancel. -/
theorem valuation_unequal_value_rigidity {K Γ : Type*} [Ring K]
    [LinearOrderedAddCommMonoidWithTop Γ] (v : AddValuation K Γ) {x y : K}
    (hxy : v x ≠ v y) :
    v (x + y) = min (v x) (v y) := by
  exact v.map_add_of_distinct_val hxy

/-- The Newton correction and derivative invariants in the proof of Theorem 9.2. -/
theorem valuation_newton_induction {K Γ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (v : AddValuation K Γ)
    (A : Subring K) (hA : IsValuationSubring A v) (f : K[X])
    (hf : PolynomialCoefficientsInSubring A f) (a₀ : K) (ha₀ : a₀ ∈ A)
    (hineq : v (f.eval a₀) > v (f.derivative.eval a₀) + v (f.derivative.eval a₀))
    (hderiv : v (f.derivative.eval a₀) ≠ ⊤) :
    let s := v (f.derivative.eval a₀)
    let q₀ := v (f.eval a₀) - (s + s)
    ∀ n : ℕ,
      v (f.derivative.eval (newtonIterate f a₀ n)) = s ∧
        valuationExcess v f s (newtonIterate f a₀ n) ≥ (2 ^ n) • q₀ ∧
        v (newtonIterate f a₀ (n + 1) - newtonIterate f a₀ n) =
          s + valuationExcess v f s (newtonIterate f a₀ n) := by
  dsimp
  let s : Γ := v (f.derivative.eval a₀)
  let q₀ : Γ := v (f.eval a₀) - (s + s)
  have hs : s ≠ ⊤ := by
    simpa [s] using hderiv
  have hs_nonneg : 0 ≤ s := by
    apply (hA _).mp
    have hfd : PolynomialCoefficientsInSubring A f.derivative := by
      intro n
      rw [coeff_derivative]
      exact A.mul_mem (hf (n + 1)) (by simpa using intCast_mem A (n + 1 : ℤ))
    rw [eval_eq_sum_range]
    apply A.sum_mem
    intro n hn
    exact A.mul_mem (hfd n) (A.pow_mem ha₀ n)
  have hq₀pos : 0 < q₀ := by
    dsimp [q₀, s]
    exact LinearOrderedAddCommGroupWithTop.sub_pos.mpr (Or.inl hineq)
  have hEvalMem : ∀ (p : K[X]), PolynomialCoefficientsInSubring A p →
      ∀ {x : K}, x ∈ A → p.eval x ∈ A := by
    intro p hp x hx
    rw [eval_eq_sum_range]
    apply A.sum_mem
    intro n hn
    exact A.mul_mem (hp n) (A.pow_mem hx n)
  have hDerivativeCoeffs : PolynomialCoefficientsInSubring A f.derivative := by
    intro n
    rw [coeff_derivative]
    exact A.mul_mem (hf (n + 1)) (by simpa using intCast_mem A (n + 1 : ℤ))
  have hDerivativeDerivativeCoeffs :
      PolynomialCoefficientsInSubring A f.derivative.derivative := by
    intro n
    rw [coeff_derivative]
    exact A.mul_mem (hDerivativeCoeffs (n + 1))
      (by simpa using intCast_mem A (n + 1 : ℤ))
  have hTaylorIntegral : ∀ (p : K[X]), PolynomialCoefficientsInSubring A p →
      ∀ (x y : K), x ∈ A → y ∈ A → ∃ g : A,
        p.eval (x + y) = p.eval x + y * p.derivative.eval x + y ^ 2 * (g : K) := by
    intro p hp x y hx hy
    let hpcoeff : (p.coeffs : Set K) ⊆ A := by
      intro c hc
      rcases (Polynomial.mem_coeffs_iff.mp hc) with ⟨n, hn, rfl⟩
      exact hp n
    let pA : A[X] := p.toSubring A hpcoeff
    obtain ⟨g, hg⟩ := taylor_second_order pA ⟨x, hx⟩ ⟨y, hy⟩
    refine ⟨g, ?_⟩
    have hmap := congrArg (fun z : A => (z : K)) hg
    have hpmap : pA.map (Subring.subtype A) = p := by
      exact Polynomial.map_toSubring p A hpcoeff
    have heval (z : A) : ((pA.eval z : A) : K) = p.eval (z : K) := by
      have h := Polynomial.eval_map_apply (p := pA) (Subring.subtype A) z
      rw [hpmap] at h
      exact h.symm
    have hdermap : pA.derivative.map (Subring.subtype A) = p.derivative := by
      rw [← Polynomial.derivative_map, hpmap]
    have hderval (z : A) : ((pA.derivative.eval z : A) : K) = p.derivative.eval (z : K) := by
      have h := Polynomial.eval_map_apply (p := pA.derivative) (Subring.subtype A) z
      rw [hdermap] at h
      exact h.symm
    calc
      p.eval (x + y) = ((pA.eval (⟨x, hx⟩ + ⟨y, hy⟩) : A) : K) := by
        simpa using (heval (⟨x, hx⟩ + ⟨y, hy⟩)).symm
      _ = ((pA.eval ⟨x, hx⟩ + ⟨y, hy⟩ *
          pA.derivative.eval ⟨x, hx⟩ +
          ⟨y, hy⟩ ^ 2 * g : A) : K) := hmap
      _ = p.eval x + y * p.derivative.eval x + y ^ 2 * (g : K) := by
        simp [heval, hderval, Subring.coe_add, Subring.coe_mul]
  have hStep : ∀ n : ℕ,
      newtonIterate f a₀ n ∈ A ∧
        v (f.derivative.eval (newtonIterate f a₀ n)) = s ∧
        valuationExcess v f s (newtonIterate f a₀ n) ≥ (2 ^ n) • q₀ := by
    intro n
    induction n with
    | zero =>
        have hfe : f.eval a₀ ∈ A := hEvalMem f hf ha₀
        have hfde : f.derivative.eval a₀ ∈ A := hEvalMem f.derivative hDerivativeCoeffs ha₀
        refine ⟨ha₀, ?_, ?_⟩
        · rfl
        · simp [newtonIterate, valuationExcess, s, q₀]
    | succ n ih =>
        let an : K := newtonIterate f a₀ n
        let d : K := f.derivative.eval an
        let e : K := f.eval an
        let qn : Γ := valuationExcess v f s an
        have han : an ∈ A := by simpa [an] using ih.1
        have hdn : v d = s := by simpa [d] using ih.2.1
        have hqn : qn ≥ (2 ^ n) • q₀ := by simpa [qn] using ih.2.2
        have hqnpos : 0 < qn := lt_of_lt_of_le
          (nsmul_pos hq₀pos (by positivity : 2 ^ n ≠ 0)) hqn
        have hene : s + s ≤ v e := by
          have hqnonneg : 0 ≤ qn :=
            (le_of_lt (nsmul_pos hq₀pos (by positivity : 2 ^ n ≠ 0))).trans hqn
          have hcancel : s + s + (v e - (s + s)) = v e := by
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
              (LinearOrderedAddCommGroupWithTop.add_neg_cancel_left_of_ne_top
                (show s + s ≠ ⊤ by simp [hs]) (v e))
          rw [show qn = v e - (s + s) by rfl] at hqnonneg
          rw [← hcancel]
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hqnonneg (s + s)
        have hs_le_ve : s ≤ v e := by
          exact (le_add_of_nonneg_right hs_nonneg).trans hene
        have hcorrmem : e * Ring.inverse d ∈ A := by
          apply (hA _).mpr
          rw [Ring.inverse_eq_inv, v.map_mul, AddValuation.map_inv, hdn]
          have h := add_le_add_right hs_le_ve (-s)
          simpa [sub_eq_add_neg, add_comm,
            LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top hs] using h
        have han1 : newtonIterate f a₀ (n + 1) ∈ A := by
          have hrec : newtonIterate f a₀ (n + 1) = an - e * Ring.inverse d := by
            simp [an, d, e, newtonIterate, newtonCorrection]
          rw [hrec]
          exact A.sub_mem han hcorrmem
        have hdelta : newtonIterate f a₀ (n + 1) - an =
            -(e * Ring.inverse d) := by
          have hrec : newtonIterate f a₀ (n + 1) = an - e * Ring.inverse d := by
            simp [an, d, e, newtonIterate, newtonCorrection]
          rw [hrec]
          ring
        obtain ⟨g, hg⟩ := hTaylorIntegral f hf an
          (newtonIterate f a₀ (n + 1) - an) han (by
            rw [hdelta]
            exact A.neg_mem hcorrmem)
        have hdneq : d ≠ 0 := by
          intro hd0
          have : v d = ⊤ := by simp [hd0]
          exact hs ((by simpa [hdn] using this) : s = ⊤)
        have hdu : IsUnit d := isUnit_iff_ne_zero.mpr hdneq
        have hcancel : e + (newtonIterate f a₀ (n + 1) - an) * d = 0 := by
          rw [hdelta, Ring.inverse_eq_inv, neg_mul, mul_assoc,
            inv_mul_cancel₀ hdneq, mul_one]
          ring
        have hdeltaVal0 : v (newtonIterate f a₀ (n + 1) - an) = s + qn := by
          rw [hdelta, Ring.inverse_eq_inv, v.map_neg, v.map_mul,
            AddValuation.map_inv, hdn]
          by_cases hev : v e = ⊤
          · dsimp [qn, valuationExcess]
            have hev' : v (f.eval an) = ⊤ := by simpa [e] using hev
            rw [hev]
            simp [sub_eq_add_neg]
          · dsimp [qn, valuationExcess]
            have hval_formula : v e + -s = s + (v e + -(s + s)) := by
              rw [neg_add_rev]
              calc
                v e + -s = 0 + (v e + -s) := by simp
                _ = (s + -s) + (v e + -s) := by
                  simp [LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top hs]
                _ = s + (v e + (-s + -s)) := by ac_rfl
            simpa [e, an, sub_eq_add_neg] using hval_formula
        have hdn1 : v (f.derivative.eval (newtonIterate f a₀ (n + 1))) = s := by
          obtain ⟨gd, hgd⟩ := hTaylorIntegral f.derivative hDerivativeCoeffs an
            (newtonIterate f a₀ (n + 1) - an) han (by
              rw [hdelta]
              exact A.neg_mem hcorrmem)
          let delta : K := newtonIterate f a₀ (n + 1) - an
          let u : K := f.derivative.derivative.eval an + delta * (gd : K)
          have hdeltaVal : v delta = s + qn := by
            simpa [delta] using hdeltaVal0
          have hdelta_gt : s < v delta := by
            rw [hdeltaVal]
            have := (add_lt_add_iff_right_of_ne_top hs).mpr hqnpos
            simpa using this
          have hgdmem : (f.derivative.derivative.eval an) ∈ A :=
            hEvalMem f.derivative.derivative hDerivativeDerivativeCoeffs han
          have hgm : (gd : K) ∈ A := gd.property
          have hdelta_mem : delta ∈ A := by
            dsimp [delta]
            rw [hdelta]
            exact A.neg_mem hcorrmem
          have huv : 0 ≤ v u := by
            apply (le_trans (le_min (hA _ |>.mp hgdmem)
              (by
                apply (hA _).mp
                exact A.mul_mem hdelta_mem hgm))
              (v.map_add _ _))
          have hduval : s < v (delta * u) := by
            rw [v.map_mul]
            exact lt_of_lt_of_le hdelta_gt (le_add_of_nonneg_right huv)
          have hdercalc : f.derivative.eval (newtonIterate f a₀ (n + 1)) =
              d + delta * u := by
            rw [show newtonIterate f a₀ (n + 1) = an + delta by
              dsimp [delta]
              ring]
            rw [hgd]
            dsimp [u]
            ring
          calc
            v (f.derivative.eval (newtonIterate f a₀ (n + 1))) =
                v (d + delta * u) := congrArg v hdercalc
            _ = min (v d) (v (delta * u)) :=
              v.map_add_of_distinct_val (by
                rw [hdn]
                exact ne_of_lt hduval)
            _ = s := by rw [hdn, min_eq_left (le_of_lt hduval)]
        have hqn1 : valuationExcess v f s
              (newtonIterate f a₀ (n + 1)) ≥ (2 ^ (n + 1)) • q₀ := by
          let en : K := f.eval (newtonIterate f a₀ (n + 1))
          have hneval : en =
              (newtonIterate f a₀ (n + 1) - an) ^ 2 * (g : K) := by
            dsimp [en]
            calc
              f.eval (newtonIterate f a₀ (n + 1)) =
                  f.eval (an + (newtonIterate f a₀ (n + 1) - an)) := by
                    congr 1
                    ring
              _ = f.eval an +
                  (newtonIterate f a₀ (n + 1) - an) * f.derivative.eval an +
                  (newtonIterate f a₀ (n + 1) - an) ^ 2 * (g : K) := hg
              _ = (newtonIterate f a₀ (n + 1) - an) ^ 2 * (g : K) := by
                have hcancel' : f.eval an +
                    (newtonIterate f a₀ (n + 1) - an) * f.derivative.eval an = 0 := by
                  simpa [e, d] using hcancel
                rw [hcancel', zero_add]
          have hvg : 0 ≤ v (g : K) := (hA _).mp g.property
          have hvn : (s + s) + (2 • qn) ≤ v en := by
            rw [hneval, v.map_mul, v.map_pow, hdeltaVal0]
            have hbase : 2 • (s + qn) = (s + s) + (2 • qn) := by
              simp [two_nsmul, add_assoc]
            rw [hbase]
            exact le_add_of_nonneg_right hvg
          have hsub : 2 • qn ≤ v en - (s + s) := by
            have hss : s + s ≠ ⊤ := by simp [hs]
            have hsub' :
                ((s + s) + (2 • qn)) - (s + s) ≤ v en - (s + s) :=
              (LinearOrderedAddCommGroupWithTop.sub_le_sub_iff_left_of_ne_top hss).mpr hvn
            calc
              2 • qn = ((s + s) + (2 • qn)) - (s + s) := by
                rw [sub_eq_add_neg]
                calc
                  2 • qn = 0 + (2 • qn) := by simp
                  _ = ((s + s) + -(s + s)) + (2 • qn) := by
                    rw [LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top hss]
                  _ = (s + s) + (2 • qn) + -(s + s) := by ac_rfl
              _ ≤ v en - (s + s) := hsub'
          have hdouble : (2 ^ n) • q₀ + (2 ^ n) • q₀ ≤ qn + qn :=
            add_le_add hqn hqn
          have hpow : (2 ^ (n + 1)) • q₀ =
              (2 ^ n) • q₀ + (2 ^ n) • q₀ := by
            have htwo : 2 ^ n * 2 = 2 ^ n + 2 ^ n := by omega
            rw [pow_succ, htwo, add_nsmul]
          dsimp [valuationExcess] at hsub ⊢
          rw [hpow]
          exact hdouble.trans (by simpa [two_nsmul] using hsub)
        exact ⟨han1, hdn1, hqn1⟩
  intro n
  have hn := hStep n
  refine ⟨hn.2.1, hn.2.2, ?_⟩
  let an : K := newtonIterate f a₀ n
  let d : K := f.derivative.eval an
  let e : K := f.eval an
  let qn : Γ := valuationExcess v f s an
  have hdelta : newtonIterate f a₀ (n + 1) - an =
      -(e * Ring.inverse d) := by
    simp [an, d, e, newtonIterate, newtonCorrection]
  have hdn : v d = s := by simpa [d] using hn.2.1
  rw [hdelta, Ring.inverse_eq_inv, v.map_neg, v.map_mul, AddValuation.map_inv, hdn]
  by_cases hev : v e = ⊤
  · have hev' : v (f.eval (newtonIterate f a₀ n)) = ⊤ := by simpa [e, an] using hev
    dsimp [qn, valuationExcess, s]
    rw [hev]
    simp [sub_eq_add_neg]
  · dsimp [qn, valuationExcess]
    have hval_formula : v e + -s = s + (v e + -(s + s)) := by
      rw [neg_add_rev]
      calc
        v e + -s = 0 + (v e + -s) := by simp
        _ = (s + -s) + (v e + -s) := by
          simp [LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top hs]
        _ = s + (v e + (-s + -s)) := by ac_rfl
    simpa [e, an, sub_eq_add_neg] using hval_formula

/-- The valuation Newton form of Hensel's lemma, including the integral root condition. -/
private theorem hensel_cauchy_of_top {K Γ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (v : AddValuation K Γ)
    (hcomplete : Chapter09NonarchimedeanComplete v)
    (u : ℕ → K) (q₀ : Γ) (hq₀ : 0 < q₀)
    (htop : ∀ γ : Γ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      γ ≤ v (u (n + 1) - u n)) :
      @CauchySeq K ℕ (Chapter09ValuationUniformSpace v) inferInstance u := by
  have _hcomplete := hcomplete
  let hvalued : Valued K (Multiplicative Γᵒᵈ) := Valued.mk' v.toValuation
  let hfoo (γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass v.toValuation))ˣ) : Γ :=
    OrderDual.ofDual (Multiplicative.toAdd
      (MonoidWithZeroHom.ValueGroup₀.embedding γ.1))
  have hval_lt_iff (x : K)
      (γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass v.toValuation))ˣ) :
      (v.toValuation.restrict x < γ.1) ↔ hfoo γ < v x := by
    rw [Valuation.restrict_lt_iff_lt_embedding]
    change Multiplicative.ofAdd (OrderDual.toDual (v x)) <
      MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ↔ _
    change OrderDual.toDual (v x) < Multiplicative.toAdd
      (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) ↔ _
    change _ ↔ OrderDual.ofDual (Multiplicative.toAdd
      (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)) < v x
    exact OrderDual.toDual_lt
  have hpair : ∀ (b : Γ) {m n : ℕ}, m ≤ n →
      (∀ i : ℕ, m ≤ i → i < n → b ≤ v (u (i + 1) - u i)) →
      b ≤ v (u n - u m) := by
    intro b m n hmn
    induction n, hmn using Nat.le_induction with
    | base =>
        intro hinc
        simp
    | succ n hmn ih =>
        intro hinc
        have hi := hinc n hmn (by omega)
        have ih' := ih (fun i hi' hlt =>
          hinc i hi' (lt_trans hlt (Nat.lt_succ_self n)))
        have hsum : u (n + 1) - u m =
            (u (n + 1) - u n) + (u n - u m) := by ring
        rw [hsum]
        exact (le_min hi ih').trans (valuation_strong_triangle v _ _)
  have htest : ∀ (γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass v.toValuation))ˣ),
      ∃ M ∈ (Filter.map u Filter.atTop),
        ∀ᵉ (x ∈ M) (y ∈ M), v.toValuation.restrict (y - x) < γ.1 := by
    intro γ
    let t : Γ := hfoo γ
    obtain ⟨N, hN⟩ := htop (t + q₀)
    refine ⟨u '' Set.Ici N, ?_, ?_⟩
    · rw [Filter.mem_map']
      exact Filter.mem_of_superset (Filter.eventually_ge_atTop N)
        (fun n hn => ⟨n, hn, rfl⟩)
    · intro x hx y hy
      rcases hx with ⟨m, hm, rfl⟩
      rcases hy with ⟨n, hn, rfl⟩
      have hmn : m ≤ n ∨ n ≤ m := le_total m n
      rcases hmn with hmn | hnm
      · have hinc : ∀ i : ℕ, m ≤ i → i < n →
            t + q₀ ≤ v (u (i + 1) - u i) := by
          intro i hi _
          exact hN i (le_trans hm hi)
        have hdiff := hpair (t + q₀) hmn hinc
        have ht_top : t ≠ ⊤ := by
          intro htop
          change OrderDual.ofDual (Multiplicative.toAdd
            (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)) = (⊤ : Γ) at htop
          have hdual : Multiplicative.toAdd
              (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) = (⊥ : Γᵒᵈ) :=
            (OrderDual.ofDual_eq_top Γ).mp htop
          have heq : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 = 0 := by
            exact congrArg Multiplicative.ofAdd hdual
          have hγzero : (γ.1 : MonoidWithZeroHom.ValueGroup₀ (.ofClass v.toValuation)) = 0 := by
            apply MonoidWithZeroHom.ValueGroup₀.embedding_injective
            exact heq
          exact (Units.ne_zero γ) hγzero
        have ht : t < t + q₀ := by
          simpa using (add_lt_add_iff_right_of_ne_top ht_top).2 hq₀
        apply hval_lt_iff _ γ |>.mpr
        exact lt_of_lt_of_le ht hdiff
      · have hinc : ∀ i : ℕ, n ≤ i → i < m →
            t + q₀ ≤ v (u (i + 1) - u i) := by
          intro i hi _
          exact hN i (le_trans hn hi)
        have hdiff := hpair (t + q₀) hnm hinc
        have ht_top : t ≠ ⊤ := by
          intro htop
          change OrderDual.ofDual (Multiplicative.toAdd
            (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)) = (⊤ : Γ) at htop
          have hdual : Multiplicative.toAdd
              (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) = (⊥ : Γᵒᵈ) :=
            (OrderDual.ofDual_eq_top Γ).mp htop
          have heq : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 = 0 := by
            exact congrArg Multiplicative.ofAdd hdual
          have hγzero : (γ.1 : MonoidWithZeroHom.ValueGroup₀ (.ofClass v.toValuation)) = 0 := by
            apply MonoidWithZeroHom.ValueGroup₀.embedding_injective
            exact heq
          exact (Units.ne_zero γ) hγzero
        have ht : t < t + q₀ := by
          simpa using (add_lt_add_iff_right_of_ne_top ht_top).2 hq₀
        apply hval_lt_iff _ γ |>.mpr
        have hneg : v (u n - u m) = v (u m - u n) := by
          rw [show u n - u m = -(u m - u n) by ring, v.map_neg]
        exact lt_of_lt_of_le ht (hneg ▸ hdiff)
  change Cauchy (Filter.map u Filter.atTop)
  rw [@Valued.cauchy_iff K _ (Multiplicative Γᵒᵈ) _ hvalued]
  refine ⟨inferInstance, ?_⟩
  intro γ
  exact htest γ


set_option maxHeartbeats 2000000 in
private theorem hensel_newton_data {K Γ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (v : AddValuation K Γ)
    (A : Subring K) (hA : IsValuationSubring A v) (f : K[X])
    (hf : PolynomialCoefficientsInSubring A f) (a₀ : K) (ha₀ : a₀ ∈ A)
    (hineq : v (f.eval a₀) > v (f.derivative.eval a₀) + v (f.derivative.eval a₀))
    (hderiv : v (f.derivative.eval a₀) ≠ ⊤)
    (hcomplete : Chapter09NonarchimedeanComplete v)
    (hcofinal : Chapter09DoublingCofinal
      (valuationExcess v f (v (f.derivative.eval a₀)) a₀)) :
    ∃ a : K, a ∈ A ∧ f.eval a = 0 ∧
      v (a - a₀) = v (f.derivative.eval a₀) +
        (v (f.eval a₀) -
          (v (f.derivative.eval a₀) + v (f.derivative.eval a₀))) ∧
      v (f.derivative.eval a) = v (f.derivative.eval a₀) := by
  let hvalued : Valued K (Multiplicative Γᵒᵈ) := Valued.mk' v.toValuation
  let s : Γ := v (f.derivative.eval a₀)
  let q₀ : Γ := v (f.eval a₀) - (s + s)
  have hs : s ≠ ⊤ := by simpa [s] using hderiv
  have hq₀pos : 0 < q₀ := by
    dsimp [q₀, s]
    exact LinearOrderedAddCommGroupWithTop.sub_pos.mpr (Or.inl hineq)
  have hfd : PolynomialCoefficientsInSubring A f.derivative := by
    intro n
    rw [coeff_derivative]
    exact A.mul_mem (hf (n + 1))
      (by simpa using intCast_mem A (n + 1 : ℤ))
  have hs_nonneg : 0 ≤ s := by
    apply (hA _).mp
    rw [eval_eq_sum_range]
    apply A.sum_mem
    intro n hn
    exact A.mul_mem (hfd n) (A.pow_mem ha₀ n)
  have hmem : ∀ n : ℕ, newtonIterate f a₀ n ∈ A := by
    intro n
    induction n with
    | zero => exact ha₀
    | succ n ih =>
        let an : K := newtonIterate f a₀ n
        let d : K := f.derivative.eval an
        let e : K := f.eval an
        let qn : Γ := valuationExcess v f s an
        have hn := valuation_newton_induction v A hA f hf a₀ ha₀ hineq hderiv n
        have hdn : v d = s := by simpa [d] using hn.1
        have hqn : (2 ^ n) • q₀ ≤ qn := by simpa [qn] using hn.2.1
        have hqnonneg : 0 ≤ qn :=
          (nsmul_nonneg hq₀pos.le _).trans hqn
        have hve : s + s ≤ v e := by
          have hsub : 0 ≤ v e - (s + s) := by
            simpa [qn, valuationExcess, e] using hqnonneg
          have hss : s + s ≠ ⊤ := by simp [hs]
          calc
            s + s = (s + s) + 0 := by simp
            _ ≤ (s + s) + (v e - (s + s)) := add_le_add_right hsub _
            _ = v e := by
              rw [sub_eq_add_neg]
              rw [show s + s + (v e + -(s + s)) =
                  (s + s + -(s + s)) + v e by ac_rfl]
              rw [LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top hss,
                zero_add]
        have hse : s ≤ v e :=
          (le_add_of_nonneg_right hs_nonneg).trans hve
        have hcorrmem : e * Ring.inverse d ∈ A := by
          apply (hA _).mpr
          rw [Ring.inverse_eq_inv, v.map_mul, AddValuation.map_inv, hdn]
          have hsub : 0 ≤ v e - s := by
            apply (add_le_add_iff_right_of_ne_top hs).mp
            calc
              s + 0 = s := by simp
              _ ≤ v e := hse
              _ = s + (v e - s) := by
                rw [sub_eq_add_neg]
                symm
                calc
                  s + (v e + -s) = (s + -s) + v e := by ac_rfl
                  _ = v e := by
                    rw [LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top hs,
                      zero_add]
          simpa [sub_eq_add_neg] using hsub
        have hrec : newtonIterate f a₀ (n + 1) =
            an - e * Ring.inverse d := by
          simp [an, d, e, newtonIterate, newtonCorrection]
        rw [hrec]
        exact A.sub_mem ih hcorrmem
  let u : ℕ → K := newtonIterate f a₀
  have htop : ∀ γ : Γ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      γ ≤ v (u (n + 1) - u n) := by
    intro γ
    obtain ⟨N, hN⟩ := hcofinal (γ - s)
    refine ⟨N, fun n hn => ?_⟩
    have hpow : 2 ^ N ≤ 2 ^ n := by
      exact Nat.pow_le_pow_right (by norm_num) hn
    have hsmul : (2 ^ N) • q₀ ≤ (2 ^ n) • q₀ :=
      nsmul_le_nsmul_left hq₀pos.le hpow
    have hγ : γ ≤ s + (2 ^ n) • q₀ := by
      calc
        γ = s + (γ - s) := by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
            (LinearOrderedAddCommGroupWithTop.add_neg_cancel_left_of_ne_top hs γ).symm
        _ ≤ s + (2 ^ N) • q₀ := by
          simpa [valuationExcess, add_comm] using add_le_add_left hN s
        _ ≤ s + (2 ^ n) • q₀ := by
          simpa [add_comm] using add_le_add_left hsmul s
    have hnstep := valuation_newton_induction v A hA f hf a₀ ha₀ hineq hderiv n
    rw [hnstep.2.2]
    apply hγ.trans
    simpa [s, q₀, valuationExcess, add_comm] using add_le_add_left hnstep.2.1 s
  have hCauchy : @CauchySeq K ℕ (Chapter09ValuationUniformSpace v) inferInstance u :=
    hensel_cauchy_of_top v hcomplete u q₀ hq₀pos htop
  obtain ⟨a, ha_lim⟩ := @cauchySeq_tendsto_of_complete K ℕ
    (Chapter09ValuationUniformSpace v) inferInstance hcomplete (u := u) hCauchy
  have hmemA : a ∈ A := by
    apply (hA _).mpr
    by_contra hnot
    have hneg : v a < 0 := lt_of_not_ge hnot
    have haVal : v.toValuation a ≠ 0 := by
      intro hz
      have hz' : v a = ⊤ := by
        change Multiplicative.ofAdd (OrderDual.toDual (v a)) = 0 at hz
        have hzdual : OrderDual.toDual (v a) = (⊥ : Γᵒᵈ) := by
          have hh := congrArg Multiplicative.toAdd hz
          exact hh
        exact (OrderDual.toDual_eq_bot Γ).mp hzdual
      exact (not_lt_of_ge (le_top : (0 : Γ) ≤ ⊤)) (hz' ▸ hneg)
    have hloc := @Valued.locally_const K _ (Multiplicative Γᵒᵈ) _ hvalued a haVal
    have hev : ∀ᶠ n : ℕ in Filter.atTop,
        v.toValuation (u n) = v.toValuation a := ha_lim.eventually hloc
    obtain ⟨N, hN⟩ := (Filter.eventually_atTop.1 hev)
    have hEq := hN N (le_rfl)
    have hEq' : v (u N) = v a := by
      have hh := congrArg (fun z : Multiplicative Γᵒᵈ =>
          OrderDual.ofDual (Multiplicative.toAdd z)) hEq
      simpa [AddValuation.toValuation_apply] using hh
    have hnonneg : 0 ≤ v (u N) := (hA _).mp (hmem N)
    exact (not_lt_of_ge (hEq' ▸ hnonneg)) hneg
  let hfoo (γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass v.toValuation))ˣ) : Γ :=
    OrderDual.ofDual (Multiplicative.toAdd
      (MonoidWithZeroHom.ValueGroup₀.embedding γ.1))
  have hval_lt_iff (x : K)
      (γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass v.toValuation))ˣ) :
      (v.toValuation.restrict x < γ.1) ↔ hfoo γ < v x := by
    rw [Valuation.restrict_lt_iff_lt_embedding]
    change Multiplicative.ofAdd (OrderDual.toDual (v x)) <
      MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ↔ _
    change OrderDual.toDual (v x) < Multiplicative.toAdd
      (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) ↔ _
    change _ ↔ OrderDual.ofDual (Multiplicative.toAdd
      (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)) < v x
    exact OrderDual.toDual_lt
  have hbound : ∀ n : ℕ,
      s + s + (2 ^ n) • q₀ ≤ v (f.eval (u n)) := by
    intro n
    have hn := valuation_newton_induction v A hA f hf a₀ ha₀ hineq hderiv n
    let e : K := f.eval (u n)
    let qn : Γ := valuationExcess v f s (u n)
    have hqn : (2 ^ n) • q₀ ≤ qn := by simpa [qn] using hn.2.1
    have hss : s + s ≠ ⊤ := by simp [hs]
    calc
      s + s + (2 ^ n) • q₀ ≤ s + s + qn := add_le_add_right hqn _
      _ = v e := by
        rw [show qn = v e - (s + s) by rfl, sub_eq_add_neg]
        rw [show s + s + (v e + -(s + s)) =
            (s + s + -(s + s)) + v e by ac_rfl]
        rw [LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top hss,
          zero_add]
  have hEval : Filter.Tendsto (fun n : ℕ => f.eval (u n)) Filter.atTop (nhds (0 : K)) := by
    rw [(@Valued.hasBasis_nhds_zero K _ (Multiplicative Γᵒᵈ) _ hvalued).tendsto_right_iff]
    intro γ _
    let t : Γ := hfoo γ
    have ht_top : t ≠ ⊤ := by
      intro htop
      change OrderDual.ofDual (Multiplicative.toAdd
        (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)) = (⊤ : Γ) at htop
      have hdual : Multiplicative.toAdd
          (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) = (⊥ : Γᵒᵈ) :=
        (OrderDual.ofDual_eq_top Γ).mp htop
      have heq : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 = 0 := by
        exact congrArg Multiplicative.ofAdd hdual
      have hγzero : (γ.1 : MonoidWithZeroHom.ValueGroup₀ (.ofClass v.toValuation)) = 0 := by
        apply MonoidWithZeroHom.ValueGroup₀.embedding_injective
        exact heq
      exact (Units.ne_zero γ) hγzero
    have hss : s + s ≠ ⊤ := by simp [hs]
    let ss : Γ := s + s
    have hss : ss ≠ ⊤ := by simp [ss, hs]
    let r : Γ := t - ss
    have hr_top : r ≠ ⊤ := by
      dsimp [r]
      intro hr
      apply ht_top
      calc
        t = ss + (t - ss) := by
          rw [sub_eq_add_neg]
          symm
          calc
            ss + (t + -ss) = (ss + -ss) + t := by
              calc
                ss + (t + -ss) = (ss + t) + -ss :=
                  (add_assoc ss t (-ss)).symm
                _ = ss + (t + -ss) :=
                  add_assoc ss t (-ss)
                _ = ss + (-ss + t) :=
                  congrArg (fun z : Γ => ss + z) (add_comm t (-ss))
                _ = (ss + -ss) + t :=
                  (add_assoc ss (-ss) t).symm
            _ = t := by
              rw [LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top hss,
                zero_add]
        _ = ⊤ := by rw [hr]; simp
    obtain ⟨N, hN⟩ := hcofinal (r + q₀)
    refine Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    have hpow : 2 ^ N ≤ 2 ^ n := by
      exact Nat.pow_le_pow_right (by norm_num) hn
    have hsmul : (2 ^ N) • q₀ ≤ (2 ^ n) • q₀ :=
      nsmul_le_nsmul_left hq₀pos.le hpow
    have hrpow : r + q₀ ≤ (2 ^ n) • q₀ :=
      hN.trans hsmul
    have hrstrict : r < r + q₀ := by
      simpa only [add_zero] using (add_lt_add_iff_right_of_ne_top hr_top).2 hq₀pos
    have hstrict : t < ss + (2 ^ n) • q₀ := by
      calc
        t = ss + (t - ss) := by
          rw [sub_eq_add_neg]
          symm
          calc
            ss + (t + -ss) = (ss + -ss) + t := by
              calc
                ss + (t + -ss) = (ss + t) + -ss :=
                  (add_assoc ss t (-ss)).symm
                _ = ss + (t + -ss) :=
                  add_assoc ss t (-ss)
                _ = ss + (-ss + t) :=
                  congrArg (fun z : Γ => ss + z) (add_comm t (-ss))
                _ = (ss + -ss) + t :=
                  (add_assoc ss (-ss) t).symm
            _ = t := by
              rw [LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top hss,
                zero_add]
        _ < ss + ((t - ss) + q₀) := by
          exact (add_lt_add_iff_right_of_ne_top hss).2 hrstrict
        _ ≤ ss + (2 ^ n) • q₀ := add_le_add_right hrpow _
    apply hval_lt_iff _ γ |>.mpr
    have hb : ss + (2 ^ n) • q₀ ≤ v (f.eval (u n)) := by
      dsimp [ss]
      exact hbound n
    exact lt_of_lt_of_le hstrict hb
  have hbase : v (u 1 - u 0) = s + q₀ := by
    have hn0 := valuation_newton_induction v A hA f hf a₀ ha₀ hineq hderiv 0
    have hh := hn0.2.2
    dsimp [u, s, q₀, valuationExcess] at hh ⊢
    simpa [newtonIterate] using hh
  have hdisp_seq : ∀ n : ℕ, 1 ≤ n → v (u n - a₀) = s + q₀ := by
    intro n hn
    by_cases hqtop : q₀ = ⊤
    · have hiter : ∀ k : ℕ, u k = a₀ := by
        intro k
        induction k with
        | zero => simp [u, newtonIterate]
        | succ k ih =>
            have hk := valuation_newton_induction v A hA f hf a₀ ha₀ hineq hderiv k
            have hqk : (2 ^ k) • q₀ ≤ valuationExcess v f s (u k) := by
              simpa [u, s] using hk.2.1
            have hqk_top : valuationExcess v f s (u k) = ⊤ := by
              apply top_unique
              have hpowtop : ∀ j : ℕ, (2 ^ j) • (⊤ : Γ) = ⊤ := by
                intro j
                induction j with
                | zero => simp
                | succ j ih =>
                    rw [pow_succ, show 2 ^ j * 2 = 2 ^ j + 2 ^ j by omega,
                      add_nsmul, ih]
                    simp
              calc
                (⊤ : Γ) = (2 ^ k) • q₀ := by rw [hqtop, hpowtop k]
                _ ≤ valuationExcess v f s (u k) := hqk
            have hinc_top : v (u (k + 1) - u k) = ⊤ := by
              have hinc := hk.2.2
              simpa [s, u, hqk_top] using hinc
            have hinc_zero : u (k + 1) - u k = 0 := by
              by_contra hne
              exact (v.ne_top_iff.mpr hne) hinc_top
            have hinc_eq : u (k + 1) = u k := sub_eq_zero.mp hinc_zero
            rw [hinc_eq, ih]
      rw [hiter n, sub_self, hqtop]
      simp
    · induction n, hn using Nat.le_induction with
      | base =>
          simpa [u, newtonIterate] using hbase
      | succ n hn ih =>
          have hnstep := valuation_newton_induction v A hA f hf a₀ ha₀ hineq hderiv n
          have hqn : (2 ^ n) • q₀ ≤ valuationExcess v f s (u n) := by
            simpa [u] using hnstep.2.1
          have hqgt : q₀ < (2 ^ n) • q₀ := by
            have hp : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
            have hcoef : 2 ^ n - 1 ≠ 0 := by omega
            have hpos : 0 < (2 ^ n - 1) • q₀ := nsmul_pos hq₀pos hcoef
            calc
              q₀ = 0 + q₀ := by simp
              _ < (2 ^ n - 1) • q₀ + q₀ := by
                exact (add_lt_add_iff_left_of_ne_top hqtop).2 hpos
              _ = (2 ^ n) • q₀ := by
                rw [← succ_nsmul]
                congr 1 ; omega
          have hincgt : s + q₀ < v (u (n + 1) - u n) := by
            have hsq : s + q₀ < s + valuationExcess v f s (u n) := by
              exact (add_lt_add_iff_right_of_ne_top hs).2 (hqgt.trans_le hqn)
            have hinc_eq : s + valuationExcess v f s (u n) =
                v (u (n + 1) - u n) := by
              simpa [s, u] using hnstep.2.2.symm
            exact hsq.trans_eq hinc_eq
          have hsum : u (n + 1) - a₀ =
              (u (n + 1) - u n) + (u n - a₀) := by ring
          rw [hsum]
          have hne : v (u (n + 1) - u n) ≠ v (u n - a₀) := by
            rw [ih]
            exact ne_of_gt hincgt
          rw [valuation_unequal_value_rigidity v hne, ih,
            min_eq_right (le_of_lt hincgt)]
  have hdisp : v (a - a₀) = s + q₀ := by
    have hsub_lim : Filter.Tendsto (fun n : ℕ => u n - a₀) Filter.atTop
        (nhds (a - a₀)) := by
      exact (continuous_id.sub continuous_const).continuousAt.tendsto.comp ha_lim
    have hval_lim : Filter.Tendsto
        (fun n : ℕ => v.toValuation.restrict (u n - a₀)) Filter.atTop
        (nhds (v.toValuation.restrict (a - a₀))) := by
      have hcont : Continuous
          (v.toValuation.restrict : K →
            MonoidWithZeroHom.ValueGroup₀ (.ofClass v.toValuation)) := by
        exact @Valued.continuous_valuation K _ (Multiplicative Γᵒᵈ) _ hvalued
      apply Filter.Tendsto.congr' (Filter.Eventually.of_forall (fun n => rfl))
      exact (hcont.continuousAt (x := a - a₀)).tendsto.comp hsub_lim
    have hval_event : ∀ᶠ n : ℕ in Filter.atTop,
        v.toValuation.restrict (u n - a₀) =
          v.toValuation.restrict (u 1 - u 0) := by
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      apply MonoidWithZeroHom.ValueGroup₀.embedding_injective
      rw [Valuation.embedding_restrict, Valuation.embedding_restrict]
      have hh := hdisp_seq n hn
      have hh0 := hbase
      have hadd : v (u n - a₀) = v (u 1 - u 0) := hh.trans hh0.symm
      exact congrArg (fun z : Γ => Multiplicative.ofAdd (OrderDual.toDual z)) hadd
    have hval_const : Filter.Tendsto
        (fun n : ℕ => v.toValuation.restrict (u n - a₀)) Filter.atTop
        (nhds (v.toValuation.restrict (u 1 - u 0))) :=
      Filter.Tendsto.congr' (Filter.EventuallyEq.symm hval_event)
        tendsto_const_nhds
    have hval_eq := tendsto_nhds_unique hval_lim hval_const
    have hval_eq' := congrArg MonoidWithZeroHom.ValueGroup₀.embedding hval_eq
    rw [Valuation.embedding_restrict, Valuation.embedding_restrict] at hval_eq'
    have hadd := congrArg (fun z : Multiplicative Γᵒᵈ =>
        OrderDual.ofDual (Multiplicative.toAdd z)) hval_eq'
    have hEqAdd : v (a - a₀) = v (u 1 - u 0) := by
      simpa [AddValuation.toValuation_apply] using hadd
    exact hEqAdd.trans hbase
  have hzero : f.eval a = 0 := by
    have hEval' : Filter.Tendsto (fun n : ℕ => f.eval (u n)) Filter.atTop
        (nhds (f.eval a)) :=
      (Polynomial.continuousAt f (a := a)).tendsto.comp ha_lim
    have heq : (0 : K) = f.eval a := tendsto_nhds_unique hEval hEval'
    exact heq.symm
  have hderivA : v (f.derivative.eval a) = s := by
    have hder_lim : Filter.Tendsto
        (fun n : ℕ => f.derivative.eval (u n)) Filter.atTop
        (nhds (f.derivative.eval a)) :=
      (Polynomial.continuousAt f.derivative (a := a)).tendsto.comp ha_lim
    have hval_lim : Filter.Tendsto
        (fun n : ℕ => v.toValuation.restrict (f.derivative.eval (u n)))
          Filter.atTop
        (nhds (v.toValuation.restrict (f.derivative.eval a))) := by
      have hcont : Continuous
          (v.toValuation.restrict : K →
            MonoidWithZeroHom.ValueGroup₀ (.ofClass v.toValuation)) := by
        exact @Valued.continuous_valuation K _ (Multiplicative Γᵒᵈ) _ hvalued
      apply Filter.Tendsto.congr' (Filter.Eventually.of_forall (fun n => rfl))
      exact (hcont.continuousAt (x := f.derivative.eval a)).tendsto.comp hder_lim
    have hval_event : ∀ᶠ n : ℕ in Filter.atTop,
        v.toValuation.restrict (f.derivative.eval (u n)) =
          v.toValuation.restrict (f.derivative.eval a₀) := by
      filter_upwards [] with n
      apply MonoidWithZeroHom.ValueGroup₀.embedding_injective
      rw [Valuation.embedding_restrict, Valuation.embedding_restrict]
      have hn := valuation_newton_induction v A hA f hf a₀ ha₀ hineq hderiv n
      have hh : v (f.derivative.eval (u n)) =
          v (f.derivative.eval a₀) := by
        simpa [u] using hn.1
      exact congrArg (fun z : Γ => Multiplicative.ofAdd (OrderDual.toDual z)) hh
    have hval_const : Filter.Tendsto
        (fun n : ℕ => v.toValuation.restrict (f.derivative.eval (u n)))
          Filter.atTop
        (nhds (v.toValuation.restrict (f.derivative.eval a₀))) :=
      Filter.Tendsto.congr' (Filter.EventuallyEq.symm hval_event)
        tendsto_const_nhds
    have hval_eq := tendsto_nhds_unique hval_lim hval_const
    have hval_eq' := congrArg MonoidWithZeroHom.ValueGroup₀.embedding hval_eq
    rw [Valuation.embedding_restrict, Valuation.embedding_restrict] at hval_eq'
    have hadd := congrArg (fun z : Multiplicative Γᵒᵈ =>
        OrderDual.ofDual (Multiplicative.toAdd z)) hval_eq'
    have hEqAdd : v (f.derivative.eval a) =
        v (f.derivative.eval a₀) := by
      simpa [AddValuation.toValuation_apply] using hadd
    exact hEqAdd.trans (by rfl)
  exact ⟨a, hmemA, hzero, (by simpa [s, q₀] using hdisp), hderivA⟩



theorem hensel_newton_form_of_doubling_cofinal {K Γ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (v : AddValuation K Γ)
    (A : Subring K) (hA : IsValuationSubring A v) (f : K[X])
    (hf : PolynomialCoefficientsInSubring A f) (a₀ : K) (ha₀ : a₀ ∈ A)
    (hineq : v (f.eval a₀) > v (f.derivative.eval a₀) + v (f.derivative.eval a₀))
    (hderiv : v (f.derivative.eval a₀) ≠ ⊤)
    (hcomplete : Chapter09NonarchimedeanComplete v)
    (hcofinal : Chapter09DoublingCofinal
      (valuationExcess v f (v (f.derivative.eval a₀)) a₀)) :
    ∃! a : K,
      a ∈ A ∧ f.eval a = 0 ∧
      v (a - a₀) > v (f.derivative.eval a₀) ∧
          v (a - a₀) = v (f.eval a₀) - v (f.derivative.eval a₀) := by
  let s : Γ := v (f.derivative.eval a₀)
  let q₀ : Γ := v (f.eval a₀) - (s + s)
  have hs : s ≠ ⊤ := by simpa [s] using hderiv
  have hq₀pos : 0 < q₀ := by
    dsimp [q₀, s]
    exact LinearOrderedAddCommGroupWithTop.sub_pos.mpr (Or.inl hineq)
  obtain ⟨a, haA, hfa, hdisp, hderivA⟩ :=
    hensel_newton_data v A hA f hf a₀ ha₀ hineq hderiv hcomplete hcofinal
  have hdisp' : v (a - a₀) = s + q₀ := by
    simpa [s, q₀] using hdisp
  have hstrict : s < v (a - a₀) := by
    rw [hdisp']
    simpa using (add_lt_add_iff_right_of_ne_top hs).2 hq₀pos
  have hexact : v (a - a₀) = v (f.eval a₀) - s := by
    rw [hdisp']
    have hval_formula : v (f.eval a₀) + -s =
        s + (v (f.eval a₀) + -(s + s)) := by
      rw [neg_add_rev]
      calc
        v (f.eval a₀) + -s = 0 + (v (f.eval a₀) + -s) := by simp
        _ = (s + -s) + (v (f.eval a₀) + -s) := by
          simp [LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top hs]
        _ = s + (v (f.eval a₀) + (-s + -s)) := by ac_rfl
    simpa [s, q₀, sub_eq_add_neg] using hval_formula.symm
  refine ⟨a, ⟨haA, hfa, hstrict, hexact⟩, ?_⟩
  intro b hb
  by_contra hab
  have hne : b - a ≠ 0 := sub_ne_zero.mpr hab
  have hba_val : s < v (b - a) := by
    have h1 : s < v (b - a₀) := hb.2.2.1
    have h2 : s < v (-(a - a₀)) := by
      rw [v.map_neg]
      exact hstrict
    calc
      s < min (v (b - a₀)) (v (-(a - a₀))) := (lt_min_iff).2 ⟨h1, h2⟩
      _ ≤ v ((b - a₀) + (-(a - a₀))) :=
        valuation_strong_triangle v (b - a₀) (-(a - a₀))
      _ = v (b - a) := by congr 1 ; ring
  have hTaylorIntegral : ∀ (p : K[X]), PolynomialCoefficientsInSubring A p →
      ∀ (x y : K), x ∈ A → y ∈ A → ∃ g : A,
        p.eval (x + y) = p.eval x + y * p.derivative.eval x + y ^ 2 * (g : K) := by
    intro p hp x y hx hy
    let hpcoeff : (p.coeffs : Set K) ⊆ A := by
      intro c hc
      rcases (Polynomial.mem_coeffs_iff.mp hc) with ⟨n, hn, rfl⟩
      exact hp n
    let pA : A[X] := p.toSubring A hpcoeff
    obtain ⟨g, hg⟩ := taylor_second_order pA ⟨x, hx⟩ ⟨y, hy⟩
    refine ⟨g, ?_⟩
    have hmap := congrArg (fun z : A => (z : K)) hg
    have hpmap : pA.map (Subring.subtype A) = p := by
      exact Polynomial.map_toSubring p A hpcoeff
    have heval (z : A) : ((pA.eval z : A) : K) = p.eval (z : K) := by
      have h := Polynomial.eval_map_apply (p := pA) (Subring.subtype A) z
      rw [hpmap] at h
      exact h.symm
    have hdermap : pA.derivative.map (Subring.subtype A) = p.derivative := by
      rw [← Polynomial.derivative_map, hpmap]
    have hderval (z : A) : ((pA.derivative.eval z : A) : K) =
        p.derivative.eval (z : K) := by
      have h := Polynomial.eval_map_apply (p := pA.derivative) (Subring.subtype A) z
      rw [hdermap] at h
      exact h.symm
    calc
      p.eval (x + y) = ((pA.eval (⟨x, hx⟩ + ⟨y, hy⟩) : A) : K) := by
        simpa using (heval (⟨x, hx⟩ + ⟨y, hy⟩)).symm
      _ = ((pA.eval ⟨x, hx⟩ + ⟨y, hy⟩ *
          pA.derivative.eval ⟨x, hx⟩ +
          ⟨y, hy⟩ ^ 2 * g : A) : K) := hmap
      _ = p.eval x + y * p.derivative.eval x + y ^ 2 * (g : K) := by
        simp [heval, hderval, Subring.coe_add, Subring.coe_mul]
  have hmem_h : b - a ∈ A := A.sub_mem hb.1 haA
  obtain ⟨g, hg⟩ := hTaylorIntegral f hf a (b - a) haA hmem_h
  have hrootrel : 0 = (b - a) * f.derivative.eval a +
      (b - a) ^ 2 * (g : K) := by
    calc
      0 = f.eval b := hb.2.1.symm
      _ = f.eval (a + (b - a)) := by rw [show a + (b - a) = b by ring]
      _ = f.eval a + (b - a) * f.derivative.eval a +
          (b - a) ^ 2 * (g : K) := hg
      _ = (b - a) * f.derivative.eval a + (b - a) ^ 2 * (g : K) := by
        rw [hfa]
        simp
  have hfactor : (b - a) *
      (f.derivative.eval a + (b - a) * (g : K)) = 0 := by
    calc
      (b - a) * (f.derivative.eval a + (b - a) * (g : K)) =
          (b - a) * f.derivative.eval a + (b - a) ^ 2 * (g : K) := by ring
      _ = 0 := hrootrel.symm
  have hsumzero : f.derivative.eval a + (b - a) * (g : K) = 0 := by
    rcases (mul_eq_zero.mp hfactor) with hzero | hsum
    · exact (hne hzero).elim
    · exact hsum
  have hg_nonneg : 0 ≤ v (g : K) := (hA _).mp g.property
  have hprodgt : s < v ((b - a) * (g : K)) := by
    rw [v.map_mul]
    exact hba_val.trans_le (le_add_of_nonneg_right hg_nonneg)
  have hneval : v (f.derivative.eval a) ≠ v ((b - a) * (g : K)) := by
    rw [hderivA]
    exact ne_of_lt hprodgt
  have hsumval : v (f.derivative.eval a + (b - a) * (g : K)) = s := by
    calc
      v (f.derivative.eval a + (b - a) * (g : K)) =
          min (v (f.derivative.eval a)) (v ((b - a) * (g : K))) :=
        valuation_unequal_value_rigidity v hneval
      _ = s := by rw [hderivA, min_eq_left (le_of_lt hprodgt)]
  have hstop : s = ⊤ := by
    calc
      s = v (f.derivative.eval a + (b - a) * (g : K)) := hsumval.symm
      _ = ⊤ := by rw [hsumzero, v.map_zero]
  exact hs hstop


/-- The valuation form of Hensel's lemma for a complete rank-one valuation. -/
theorem hensel_newton_form {K Γ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (v : AddValuation K Γ)
    [Valuation.RankOne v.toValuation]
    (A : Subring K) (hA : IsValuationSubring A v) (f : K[X])
    (hf : PolynomialCoefficientsInSubring A f) (a₀ : K) (ha₀ : a₀ ∈ A)
    (hineq : v (f.eval a₀) > v (f.derivative.eval a₀) + v (f.derivative.eval a₀))
    (hcomplete : Chapter09NonarchimedeanComplete v) :
    ∃! a : K,
      f.eval a = 0 ∧
        v (a - a₀) > v (f.derivative.eval a₀) ∧
          v (a - a₀) = v (f.eval a₀) - v (f.derivative.eval a₀) := by
  sorry

/-- The exact displacement in the valuation Newton form under explicit cofinality. -/
theorem hensel_newton_exact_displacement_of_doubling_cofinal {K Γ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (v : AddValuation K Γ)
    (A : Subring K) (hA : IsValuationSubring A v) (f : K[X])
    (hf : PolynomialCoefficientsInSubring A f) (a₀ : K) (ha₀ : a₀ ∈ A)
    (hineq : v (f.eval a₀) > v (f.derivative.eval a₀) + v (f.derivative.eval a₀))
    (hderiv : v (f.derivative.eval a₀) ≠ ⊤)
    (hcomplete : Chapter09NonarchimedeanComplete v)
    (hcofinal : Chapter09DoublingCofinal
      (valuationExcess v f (v (f.derivative.eval a₀)) a₀)) :
    ∃ a : K,
      a ∈ A ∧ f.eval a = 0 ∧
        v (a - a₀) = v (f.eval a₀) - v (f.derivative.eval a₀) := by
  obtain ⟨a, ha, _⟩ :=
    hensel_newton_form_of_doubling_cofinal v A hA f hf a₀ ha₀ hineq hderiv hcomplete hcofinal
  exact ⟨a, ha.1, ha.2.1, ha.2.2.2⟩

/-- The exact displacement supplied by the rank-one Newton form. -/
theorem hensel_newton_exact_displacement {K Γ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (v : AddValuation K Γ)
    [Valuation.RankOne v.toValuation]
    (A : Subring K) (hA : IsValuationSubring A v) (f : K[X])
    (hf : PolynomialCoefficientsInSubring A f) (a₀ : K) (ha₀ : a₀ ∈ A)
    (hineq : v (f.eval a₀) > v (f.derivative.eval a₀) + v (f.derivative.eval a₀))
    (hcomplete : Chapter09NonarchimedeanComplete v) :
    ∃ a : K,
      f.eval a = 0 ∧
        v (a - a₀) = v (f.eval a₀) - v (f.derivative.eval a₀) := by
  obtain ⟨a, ha, _⟩ :=
    hensel_newton_form v A hA f hf a₀ ha₀ hineq hcomplete
  exact ⟨a, ha.1, ha.2.2⟩

/-- The Newton corrections tend to the top of the value group. -/
theorem valuation_newton_corrections_tend_to_top_of_doubling_cofinal {K Γ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (v : AddValuation K Γ)
    (A : Subring K) (hA : IsValuationSubring A v) (f : K[X])
    (hf : PolynomialCoefficientsInSubring A f) (a₀ : K) (ha₀ : a₀ ∈ A)
    (hineq : v (f.eval a₀) > v (f.derivative.eval a₀) + v (f.derivative.eval a₀))
    (hderiv : v (f.derivative.eval a₀) ≠ ⊤)
    (hcomplete : Chapter09NonarchimedeanComplete v)
    (hcofinal : Chapter09DoublingCofinal
      (valuationExcess v f (v (f.derivative.eval a₀)) a₀)) :
    TendsToTop (fun n => v (newtonIterate f a₀ (n + 1) - newtonIterate f a₀ n)) := by
  have _hcomplete := hcomplete
  dsimp [TendsToTop]
  let s : Γ := v (f.derivative.eval a₀)
  let q₀ : Γ := v (f.eval a₀) - (s + s)
  have hs : s ≠ ⊤ := by
    simpa [s] using hderiv
  have hq₀ : 0 < q₀ := by
    dsimp [q₀, s]
    exact LinearOrderedAddCommGroupWithTop.sub_pos.mpr (Or.inl hineq)
  intro γ
  obtain ⟨N, hN⟩ := hcofinal (γ - s)
  refine ⟨N, fun n hn => ?_⟩
  have hpow : 2 ^ N ≤ 2 ^ n := by
    exact Nat.pow_le_pow_right (by norm_num) hn
  have hsmul : (2 ^ N) • q₀ ≤ (2 ^ n) • q₀ :=
    nsmul_le_nsmul_left hq₀.le hpow
  have hγ : γ ≤ s + (2 ^ n) • q₀ := by
    calc
      γ = s + (γ - s) := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          (LinearOrderedAddCommGroupWithTop.add_neg_cancel_left_of_ne_top hs γ).symm
      _ ≤ s + (2 ^ N) • q₀ := by
        simpa [valuationExcess, add_comm] using add_le_add_left hN s
      _ ≤ s + (2 ^ n) • q₀ := by
        simpa [add_comm] using add_le_add_left hsmul s
  have hnstep := valuation_newton_induction v A hA f hf a₀ ha₀ hineq hderiv n
  rw [hnstep.2.2]
  apply hγ.trans
  simpa [s, q₀, valuationExcess, add_comm] using add_le_add_left hnstep.2.1 s

/-- The Newton corrections tend to the top in the rank-one case. -/
-- STATEMENT_NEEDS_UPDATE: `Valuation.RankOne v.toValuation` controls only the ordered value-group image of `v`, not the ambient codomain `Γ`; that image can lie in a proper non-cofinal convex subgroup. Moreover, `TendsToTop` quantifies over `⊤`, while a generic Newton correction has finite value, so the displayed sequence need not tend to the top even in the value-group image. The minimal correction is to quantify only over finite values in the value-group image (or to add an appropriate finite-value cofinality hypothesis and exclude `⊤`).
theorem valuation_newton_corrections_tend_to_top {K Γ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (v : AddValuation K Γ)
    [Valuation.RankOne v.toValuation]
    (A : Subring K) (hA : IsValuationSubring A v) (f : K[X])
    (hf : PolynomialCoefficientsInSubring A f) (a₀ : K) (ha₀ : a₀ ∈ A)
    (hineq : v (f.eval a₀) > v (f.derivative.eval a₀) + v (f.derivative.eval a₀))
    (hcomplete : Chapter09NonarchimedeanComplete v) :
    TendsToTop (fun n => v (newtonIterate f a₀ (n + 1) - newtonIterate f a₀ n)) := by
  sorry

/-- The strict Newton inequality is the error being smaller than the square of the derivative. -/
def StrictNewtonCondition {K Γ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (v : AddValuation K Γ)
    (f : K[X]) (a₀ : K) : Prop :=
  v (f.eval a₀) > v (f.derivative.eval a₀) + v (f.derivative.eval a₀)

/-- A residue approximation at which both the polynomial and derivative vanish. -/
def IsMultipleResidueApproximation {A : Type*} [CommRing A] [IsLocalRing A]
    (f : A[X]) (a₀ : A) : Prop :=
  f.eval a₀ ∈ IsLocalRing.maximalIdeal A ∧
    f.derivative.eval a₀ ∈ IsLocalRing.maximalIdeal A

/-- A multiple approximation can split into two distinct exact roots. -/
theorem quadratic_multiple_approximation_can_split {K : Type*} [Field K]
    (c : K) (hc : c ≠ 0) (hcneg : c ≠ -c) :
    quadraticPolynomial (c ^ 2) = (X - C c) * (X + C c) ∧
      (quadraticPolynomial (c ^ 2)).eval c = 0 ∧
      (quadraticPolynomial (c ^ 2)).eval (-c) = 0 ∧ c ≠ -c := by
  have _hc := hc
  refine ⟨?_, ?_, ?_, hcneg⟩
  · simp [quadraticPolynomial]
    ring
  · simp [quadraticPolynomial]
  · simp [quadraticPolynomial]

/-- The strict inequality in Theorem 9.2 cannot be dropped in general. -/
theorem strict_newton_condition_is_essential :
    ¬ StrictNewtonCondition (Padic.addValuation (p := 2))
        (quadraticPolynomial (2 : ℚ_[2])) 0 ∧
      ¬ ∃ x : ℚ_[2], x ^ 2 = (2 : ℚ_[2]) := by
  constructor
  · intro h
    have h' := h
    simp [StrictNewtonCondition, quadraticPolynomial] at h'
  · exact padic_x_sq_sub_p_has_no_root 2

/-! ## 9.3 Lifting factorizations -/

/-- Approximate factorization modulo a power of the maximal ideal. -/
def ApproximateFactorization {A : Type*} [CommRing A] [IsLocalRing A]
    (f g h : A[X]) (n : ℕ) : Prop :=
  PolynomialCoefficientsInIdeal ((IsLocalRing.maximalIdeal A) ^ n) (f - g * h)

/-- The linear correction map `(r,s) ↦ r h + s g`. -/
def factorizationCorrectionMap {R : Type*} [CommRing R]
    (g h : R[X]) (rs : R[X] × R[X]) : R[X] :=
  rs.1 * h + rs.2 * g

/-- The bounded-degree coprime correction property used in Hensel factor lifting. -/
def CoprimeCorrectionProperty {R : Type*} [CommRing R]
    (g h : R[X]) : Prop :=
  ∀ t : R[X], t.degree < (g * h).degree →
    ∃! rs : R[X] × R[X],
      rs.1.degree < g.degree ∧ rs.2.degree < h.degree ∧
        factorizationCorrectionMap g h rs = t

/-- Coprimality gives the unique bounded-degree solution to the linear correction equation. -/
theorem coprime_correction_property {k : Type*} [Field k]
    {g h : k[X]} (hg : g.Monic) (hh : h.Monic) (hcop : IsCoprime g h) :
    CoprimeCorrectionProperty g h := by
  let G : Bool → k[X] := Bool.rec h g
  have hG : ∀ i ∈ (Finset.univ : Finset Bool), (G i).Monic := by
    intro i hi
    cases i <;> simp [G, hg, hh]
  have hGcop : Set.Pairwise (Finset.univ : Finset Bool)
      (fun i j => IsCoprime (G i) (G j)) := by
    simp [G, Set.pairwise_insert, hcop, hcop.symm]
  intro t ht
  obtain ⟨q, r, hr, htq⟩ :=
    eq_quo_mul_prod_add_sum_rem_mul_prod
      (f := t) (s := (Finset.univ : Finset Bool)) hG hGcop
  have huniv : (Finset.univ : Finset Bool) = {false, true} := by decide
  rw [huniv] at htq
  have htq2 : t = q * (g * h) + r true * h + r false * g := by
    simpa [G, Finset.erase_insert_of_ne, Finset.erase_insert_eq_erase,
      add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using htq
  have hrt : (r true * h).degree < (g * h).degree := by
    calc
      (r true * h).degree ≤ (r true).degree + h.degree := degree_mul_le _ _
      _ < g.degree + h.degree := by
        rw [WithBot.add_lt_add_iff_right (degree_ne_bot.mpr hh.ne_zero)]
        simpa [G] using hr true (Finset.mem_univ true)
      _ = (g * h).degree := (degree_mul).symm
  have hrf : (r false * g).degree < (g * h).degree := by
    calc
      (r false * g).degree ≤ (r false).degree + g.degree := degree_mul_le _ _
      _ < h.degree + g.degree := by
        rw [WithBot.add_lt_add_iff_right (degree_ne_bot.mpr hg.ne_zero)]
        simpa [G] using hr false (Finset.mem_univ false)
      _ = (g * h).degree := by rw [degree_mul]; ac_rfl
  have hR : (r true * h + r false * g).degree < (g * h).degree :=
    (degree_add_le _ _).trans_lt (max_lt hrt hrf)
  have hq : q = 0 := by
    by_contra hq0
    have hprod : (g * h).degree ≤ (q * (g * h)).degree := by
      rw [mul_comm q (g * h)]
      exact degree_le_mul_left (g * h) hq0
    have hRlt : (r true * h + r false * g).degree < (q * (g * h)).degree :=
      lt_of_lt_of_le hR hprod
    have htd : t.degree = (q * (g * h)).degree := by
      rw [htq2, add_assoc, degree_add_eq_left_of_degree_lt hRlt]
    exact (not_lt_of_ge hprod) (htd ▸ ht)
  refine ⟨(r true, r false), ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · simpa [G] using hr true (Finset.mem_univ true)
    · simpa [G] using hr false (Finset.mem_univ false)
    · simpa [factorizationCorrectionMap, hq] using htq2.symm
  · rintro ⟨r₁, s₁⟩ ⟨hr₁, hs₁, hcorr₁⟩
    let R : Bool → k[X] := Bool.rec s₁ r₁
    have hRdeg : ∀ i ∈ (Finset.univ : Finset Bool),
        (R i).degree < (G i).degree := by
      intro i hi
      cases i
      · simpa [R, G] using hs₁
      · simpa [R, G] using hr₁
    have hrepr₁ : (0 : k[X]) * (g * h) + r true * h + r false * g = t := by
      simpa [hq] using htq2.symm
    have hrepr₂ : (0 : k[X]) * (g * h) + r₁ * h + s₁ * g = t := by
      simpa [factorizationCorrectionMap] using hcorr₁
    have hEq :
        (0 : k[X]) * (∏ i ∈ (Finset.univ : Finset Bool), G i) +
          ∑ i ∈ (Finset.univ : Finset Bool),
            r i * ∏ j ∈ (Finset.univ : Finset Bool).erase i, G j =
        0 * (∏ i ∈ (Finset.univ : Finset Bool), G i) +
          ∑ i ∈ (Finset.univ : Finset Bool),
            R i * ∏ j ∈ (Finset.univ : Finset Bool).erase i, G j := by
      simpa [huniv, G, R, Finset.erase_insert_of_ne, Finset.erase_insert_eq_erase,
        add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
        hrepr₁.trans hrepr₂.symm
    obtain ⟨_, hreq⟩ : (0 : k[X]) = 0 ∧
        ∀ i ∈ (Finset.univ : Finset Bool), r i = R i :=
      quo_mul_prod_add_sum_rem_mul_prod_unique
        (s := (Finset.univ : Finset Bool)) hG hGcop hr hRdeg hEq
    apply Prod.ext
    · simpa using (hreq true (Finset.mem_univ true)).symm
    · simpa [R] using (hreq false (Finset.mem_univ false)).symm

/-- One coefficientwise Hensel correction step, modulo `π^(n+1)`. -/
theorem hensel_factorization_step {A : Type*} [CommRing A] [IsDomain A]
    [CompleteDVR A] (f g h : A[X]) (g₀ h₀ : Polynomial (ResidueRing A))
    (π : A) (hπ : IsUniformizer π) (n : ℕ)
    (hf : f.Monic) (hg : g.Monic) (hh : h.Monic)
    (hgdeg : 0 < g.natDegree) (hhdeg : 0 < h.natDegree)
    (happrox : ApproximateFactorization f g h n)
    (hredg : residuePolynomial g = g₀) (hredh : residuePolynomial h = h₀)
    (hcop : IsCoprime g₀ h₀)
    (hred : residuePolynomial f = g₀ * h₀)
    (hn : 1 ≤ n) :
    ∃ r s : A[X],
      r.natDegree < g.natDegree ∧ s.natDegree < h.natDegree ∧
        ApproximateFactorization f
          (g + C (π ^ n) * r) (h + C (π ^ n) * s) (n + 1) := by
  let m : Ideal A := IsLocalRing.maximalIdeal A
  let hfield : Field (ResidueRing A) :=
    Ideal.Quotient.field (IsLocalRing.maximalIdeal A)
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hm : m = Ideal.span ({π} : Set A) := by
    exact hπ.maximalIdeal_eq
  have hm_pow (k : ℕ) : m ^ k = Ideal.span ({π ^ k} : Set A) := by
    rw [hm, Ideal.span_singleton_pow]
  have hc_mem : π ^ n ∈ m ^ n := by
    rw [hm_pow]
    exact Ideal.mem_span_singleton.mpr (dvd_refl _)
  have hcoeff_mem : ∀ i : ℕ, (f - g * h).coeff i ∈ m ^ n := by
    intro i
    exact happrox i
  let qcoeff : ℕ → A := fun i =>
    Classical.choose (Ideal.mem_span_singleton.mp (hm_pow n ▸ hcoeff_mem i))
  have hqcoeff : ∀ i : ℕ, (f - g * h).coeff i = π ^ n * qcoeff i := by
    intro i
    have hi := Classical.choose_spec (Ideal.mem_span_singleton.mp
      (hm_pow n ▸ hcoeff_mem i))
    dsimp [qcoeff]
    exact hi
  have hq_support : ∀ i : ℕ, qcoeff i ≠ 0 → i ∈ (f - g * h).support := by
    intro i hi
    apply Polynomial.mem_support_iff.mpr
    intro hzero
    apply hi
    have hmul : π ^ n * qcoeff i = 0 := by simpa [hzero] using hqcoeff i
    exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero n hπ0)
  let q : ℕ →₀ A := Finsupp.onFinset (f - g * h).support qcoeff hq_support
  let t : A[X] := Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff q)
  have htcoeff : ∀ i : ℕ, t.coeff i = qcoeff i := by
    intro i
    change (AddMonoidAlgebra.ofCoeff q).coeff i = qcoeff i
    simp [q, Finsupp.onFinset_apply]
  have hEt : f - g * h = C (π ^ n) * t := by
    ext i
    rw [Polynomial.coeff_C_mul, htcoeff, hqcoeff]
  have hdeg_f : (residuePolynomial f).natDegree = f.natDegree :=
    hf.natDegree_map (residueMap A)
  have hdeg_g : (residuePolynomial g).natDegree = g.natDegree :=
    hg.natDegree_map (residueMap A)
  have hdeg_h : (residuePolynomial h).natDegree = h.natDegree :=
    hh.natDegree_map (residueMap A)
  have hprod_monic : (g * h).Monic := hg.mul hh
  have hdeg_prod : (g₀ * h₀).natDegree = (g * h).natDegree := by
    calc
      (g₀ * h₀).natDegree = (residuePolynomial g * residuePolynomial h).natDegree := by
        rw [hredg, hredh]
      _ = (residuePolynomial (g * h)).natDegree := by
        simp [residuePolynomial, Polynomial.map_mul]
      _ = (g * h).natDegree := hprod_monic.natDegree_map (residueMap A)
  have hdeg_fprod : f.natDegree = (g * h).natDegree := by
    calc
      f.natDegree = (residuePolynomial f).natDegree := hdeg_f.symm
      _ = (g₀ * h₀).natDegree := by rw [hred]
      _ = (g * h).natDegree := hdeg_prod
  have hg₀ : g₀.Monic := by
    rw [← hredg]
    exact hg.map (residueMap A)
  have hh₀ : h₀.Monic := by
    rw [← hredh]
    exact hh.map (residueMap A)
  have hEdeg : (f - g * h).degree < (g * h).degree := by
    apply Polynomial.degree_sub_lt_right
    · calc
        f.degree = (f.natDegree : WithBot ℕ) := Polynomial.degree_eq_natDegree hf.ne_zero
        _ = ((g * h).natDegree : WithBot ℕ) := by rw [hdeg_fprod]
        _ = (g * h).degree := (Polynomial.degree_eq_natDegree hprod_monic.ne_zero).symm
    · exact hprod_monic.ne_zero
    · rw [hf.leadingCoeff, hprod_monic.leadingCoeff]
  have htdeg : t.degree = (f - g * h).degree := by
    rw [hEt, Polynomial.degree_C_mul (pow_ne_zero n hπ0)]
  have htdeg_lt : t.degree < (g₀ * h₀).degree := by
    rw [htdeg]
    calc
      (f - g * h).degree < (g * h).degree := hEdeg
      _ = (g₀ * h₀).degree := by
        rw [Polynomial.degree_eq_natDegree hprod_monic.ne_zero,
          Polynomial.degree_eq_natDegree (hg₀.mul hh₀).ne_zero,
          hdeg_prod]
  let tbar : Polynomial (ResidueRing A) := t.map (residueMap A)
  have hcorrprop : CoprimeCorrectionProperty g₀ h₀ :=
    @coprime_correction_property (ResidueRing A) hfield g₀ h₀ hg₀ hh₀ hcop
  have htbar_deg : tbar.degree < (g₀ * h₀).degree := by
    exact (Polynomial.degree_map_le.trans_lt htdeg_lt)
  obtain ⟨⟨rbar, sbar⟩, hrsdeg, hrsEq⟩ := hcorrprop tbar htbar_deg
  have hrbar_deg : rbar.degree < g₀.degree := hrsdeg.1
  have hsbar_deg : sbar.degree < h₀.degree := hrsdeg.2.1
  obtain ⟨r₀, hr₀⟩ := Polynomial.map_surjective
    (residueMap A)
    (Ideal.Quotient.mk_surjective : Function.Surjective (residueMap A)) rbar
  obtain ⟨r, hrmap, hrd⟩ :=
    Polynomial.exists_natDegree_eq_of_mem_lifts
      ((Polynomial.mem_lifts rbar).mpr ⟨r₀, hr₀⟩)
  obtain ⟨s₀, hs₀⟩ := Polynomial.map_surjective
    (residueMap A)
    (Ideal.Quotient.mk_surjective : Function.Surjective (residueMap A)) sbar
  obtain ⟨s, hsmap, hsd⟩ :=
    Polynomial.exists_natDegree_eq_of_mem_lifts
      ((Polynomial.mem_lifts sbar).mpr ⟨s₀, hs₀⟩)
  have hrdeg : r.natDegree < g.natDegree := by
    by_cases hrbar0 : rbar = 0
    · rw [hrd, hrbar0]
      exact hgdeg
    · calc
        r.natDegree = rbar.natDegree := hrd
        _ < g₀.natDegree := Polynomial.natDegree_lt_natDegree hrbar0 hrbar_deg
        _ = g.natDegree := by rw [← hredg, hdeg_g]
  have hsdeg : s.natDegree < h.natDegree := by
    by_cases hsbar0 : sbar = 0
    · rw [hsd, hsbar0]
      exact hhdeg
    · calc
        s.natDegree = sbar.natDegree := hsd
        _ < h₀.natDegree := Polynomial.natDegree_lt_natDegree hsbar0 hsbar_deg
        _ = h.natDegree := by rw [← hredh, hdeg_h]
  let u : A[X] := t - (r * h + s * g)
  have hu_res : residuePolynomial u = 0 := by
    calc
      residuePolynomial u = tbar - (rbar * h₀ + sbar * g₀) := by
        rw [residuePolynomial]
        simp only [u, tbar, Polynomial.map_sub, Polynomial.map_add,
          Polynomial.map_mul]
        have hredh' : Polynomial.map (residueMap A) h = h₀ := hredh
        have hredg' : Polynomial.map (residueMap A) g = g₀ := hredg
        rw [hrmap, hsmap, hredh', hredg']
      _ = 0 := by
        have hcorrEq : rbar * h₀ + sbar * g₀ = tbar := by
          simpa [factorizationCorrectionMap] using hrsdeg.2.2
        rw [← hcorrEq]
        simp
  have hu_mem : ∀ i : ℕ, u.coeff i ∈ m := by
    intro i
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change residueMap A (u.coeff i) = 0
    have hi := congrArg (fun P : Polynomial (ResidueRing A) => P.coeff i) hu_res
    simpa [residuePolynomial] using hi
  let J : Ideal A := m ^ (n + 1)
  have hfirst : PolynomialCoefficientsInIdeal J (C (π ^ n) * u) := by
    intro i
    rw [Polynomial.coeff_C_mul]
    have hi := Ideal.mul_mem_mul hc_mem (hu_mem i)
    simpa [J, pow_succ] using hi
  have hc2 : (π ^ n) ^ 2 ∈ J := by
    have hcc : (π ^ n) ^ 2 ∈ m ^ (n + n) := by
      have hcc' : (π ^ n) * (π ^ n) ∈ m ^ n * m ^ n :=
        Ideal.mul_mem_mul hc_mem hc_mem
      rw [← pow_add] at hcc'
      simpa [pow_two] using hcc'
    have hle : n + 1 ≤ n + n := by omega
    exact (Ideal.pow_le_pow_right hle) hcc
  have hsecond : PolynomialCoefficientsInIdeal J (C ((π ^ n) ^ 2) * (r * s)) := by
    intro i
    rw [Polynomial.coeff_C_mul]
    exact Ideal.mul_mem_right _ J hc2
  have hexpand : f - (g + C (π ^ n) * r) * (h + C (π ^ n) * s) =
      C (π ^ n) * u - C ((π ^ n) ^ 2) * (r * s) := by
    have hf_eq : f = C (π ^ n) * t + g * h := eq_add_of_sub_eq hEt
    rw [hf_eq]
    dsimp [u]
    simp [pow_two]
    ring
  refine ⟨r, s, hrdeg, hsdeg, ?_⟩
  unfold ApproximateFactorization PolynomialCoefficientsInIdeal
  intro i
  rw [hexpand]
  simpa only [Polynomial.coeff_sub] using J.sub_mem (hfirst i) (hsecond i)

/-- A pair of lifted factors with the prescribed reductions and degrees. -/
def IsFactorizationLift {A : Type*} [CommRing A] [IsLocalRing A]
    (f : A[X]) (g₀ h₀ : Polynomial (ResidueRing A)) (g h : A[X]) : Prop :=
  g.Monic ∧ h.Monic ∧
    g.natDegree = g₀.natDegree ∧ h.natDegree = h₀.natDegree ∧
    residuePolynomial g = g₀ ∧ residuePolynomial h = h₀ ∧ f = g * h

set_option maxHeartbeats 3000000 in
/-- Factorization-form Hensel lifting: the exact assertion of Theorem 9.3. -/
lemma hensel_factorization {A : Type*} [CommRing A] [IsDomain A]
    [CompleteDVR A] (f : A[X]) (g₀ h₀ : Polynomial (ResidueRing A))
    (hf : f.Monic) (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hcop : IsCoprime g₀ h₀)
    (hred : residuePolynomial f = g₀ * h₀) :
    ∃! gh : A[X] × A[X], IsFactorizationLift f g₀ h₀ gh.1 gh.2 := by
  by_cases hg0deg : g₀.natDegree = 0
  · have hg01 : g₀ = 1 := hg₀.natDegree_eq_zero.mp hg0deg
    have hredh : residuePolynomial f = h₀ := by simpa [hg01] using hred
    have hfdeg : f.natDegree = h₀.natDegree := by
      calc
        f.natDegree = (residuePolynomial f).natDegree :=
          (hf.natDegree_map (residueMap A)).symm
        _ = h₀.natDegree := congrArg Polynomial.natDegree hredh
    refine ⟨(1, f), ?_, ?_⟩
    · refine ⟨by simp, hf, by simp [hg01], hfdeg, ?_, hredh, by simp⟩
      simp [residuePolynomial, hg01]
    · intro gh hgh
      rcases hgh with ⟨hg, hh, hgd, hhd, hrg, hrh, hfac⟩
      apply Prod.ext
      · exact hg.natDegree_eq_zero.mp (by simpa [hg01] using hgd)
      · rw [show gh.1 = 1 by exact hg.natDegree_eq_zero.mp (by simpa [hg01] using hgd)] at hfac
        simp [hfac]
  · by_cases hh0deg : h₀.natDegree = 0
    · have hh01 : h₀ = 1 := hh₀.natDegree_eq_zero.mp hh0deg
      have hredg : residuePolynomial f = g₀ := by simpa [hh01] using hred
      have hfdeg : f.natDegree = g₀.natDegree := by
        calc
          f.natDegree = (residuePolynomial f).natDegree :=
            (hf.natDegree_map (residueMap A)).symm
          _ = g₀.natDegree := congrArg Polynomial.natDegree hredg
      refine ⟨(f, 1), ?_, ?_⟩
      · refine ⟨hf, by simp, hfdeg, by simp [hh01], hredg, ?_, by simp⟩
        simp [residuePolynomial, hh01]
      · intro gh hgh
        rcases hgh with ⟨hg, hh, hgd, hhd, hrg, hrh, hfac⟩
        apply Prod.ext
        · rw [show gh.2 = 1 by exact hh.natDegree_eq_zero.mp (by simpa [hh01] using hhd)] at hfac
          simp [hfac]
        · exact hh.natDegree_eq_zero.mp (by simpa [hh01] using hhd)
    · have hg0pos : 0 < g₀.natDegree := Nat.pos_of_ne_zero hg0deg
      have hh0pos : 0 < h₀.natDegree := Nat.pos_of_ne_zero hh0deg
      have hg0_lifts : g₀ ∈ Polynomial.lifts (residueMap A) := by
        rw [Polynomial.lifts_iff_coeff_lifts]
        intro n
        exact Ideal.Quotient.mk_surjective (g₀.coeff n)
      have hh0_lifts : h₀ ∈ Polynomial.lifts (residueMap A) := by
        rw [Polynomial.lifts_iff_coeff_lifts]
        intro n
        exact Ideal.Quotient.mk_surjective (h₀.coeff n)
      obtain ⟨g₁, hmapg₁, hdeg₁, hg₁⟩ :=
        Polynomial.lifts_and_natDegree_eq_and_monic hg0_lifts hg₀
      obtain ⟨h₁, hmaph₁, hdeh₁, hh₁⟩ :=
        Polynomial.lifts_and_natDegree_eq_and_monic hh0_lifts hh₀
      have hredg₁ : residuePolynomial g₁ = g₀ := hmapg₁
      have hredh₁ : residuePolynomial h₁ = h₀ := hmaph₁
      have happrox₁ : ApproximateFactorization f g₁ h₁ 1 := by
        unfold ApproximateFactorization PolynomialCoefficientsInIdeal
        intro n
        rw [pow_one]
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        change residueMap A ((f - g₁ * h₁).coeff n) = 0
        have hzero : residuePolynomial f - residuePolynomial (g₁ * h₁) = 0 := by
          rw [hred, ← hredg₁, ← hredh₁]
          simp [residuePolynomial, Polynomial.map_mul]
        simpa only [residuePolynomial, Polynomial.coeff_sub, Polynomial.coeff_map,
          map_zero, coeff_zero, map_sub] using congrArg (fun p => p.coeff n) hzero
      have hpositive_g : 0 < g₁.natDegree := by simpa [hdeg₁] using hg0pos
      have hpositive_h : 0 < h₁.natDegree := by simpa [hdeh₁] using hh0pos
      have hπ : ∃ π : A, IsUniformizer π := IsDiscreteValuationRing.exists_irreducible A
      obtain ⟨π, hπ⟩ := hπ
      let LiftAt : ℕ → (A[X] × A[X]) → Prop := fun n gh =>
        gh.1.Monic ∧ gh.2.Monic ∧
          gh.1.natDegree = g₀.natDegree ∧ gh.2.natDegree = h₀.natDegree ∧
          residuePolynomial gh.1 = g₀ ∧ residuePolynomial gh.2 = h₀ ∧
          ApproximateFactorization f gh.1 gh.2 (n + 1)
      let Q : ℕ → Type _ := fun n => {gh : A[X] × A[X] // LiftAt n gh}
      have hQ0 : Q 0 := by
        refine ⟨(g₁, h₁), hg₁, hh₁, hdeg₁, hdeh₁, hredg₁, hredh₁, happrox₁⟩
      let factorChoice : ∀ n (qn : Q n), ∃ r s : A[X],
          r.natDegree < qn.1.1.natDegree ∧
            s.natDegree < qn.1.2.natDegree ∧
            ApproximateFactorization f
              (qn.1.1 + C (π ^ (n + 1)) * r)
              (qn.1.2 + C (π ^ (n + 1)) * s) (n + 1 + 1) := by
        intro n qn
        rcases qn.property with ⟨hg, hh, hgd, hhd, hrg, hrh, happrox⟩
        exact hensel_factorization_step f qn.1.1 qn.1.2 g₀ h₀ π hπ
          (n + 1) hf hg hh (by simpa [hgd] using hg0pos)
          (by simpa [hhd] using hh0pos) happrox hrg hrh hcop hred (by omega)
      let StepData : ∀ n, Q n → Type _ := fun n qn =>
        {z : Q (n + 1) × (A[X] × A[X]) //
          z.1.1.1 = qn.1.1 + C (π ^ (n + 1)) * z.2.1 ∧
            z.1.1.2 = qn.1.2 + C (π ^ (n + 1)) * z.2.2}
      let stepData : ∀ n (qn : Q n), StepData n qn := fun n qn => by
        rcases qn.property with ⟨hg, hh, hgd, hhd, hrg, hrh, happrox⟩
        have hex := factorChoice n qn
        let r : A[X] := hex.choose
        let s : A[X] := hex.choose_spec.choose
        have hrs : r.natDegree < qn.1.1.natDegree := hex.choose_spec.choose_spec.1
        have hss : s.natDegree < qn.1.2.natDegree := hex.choose_spec.choose_spec.2.1
        have hnext : ApproximateFactorization f
            (qn.1.1 + C (π ^ (n + 1)) * r)
            (qn.1.2 + C (π ^ (n + 1)) * s) (n + 1 + 1) :=
          hex.choose_spec.choose_spec.2.2
        have htermg : (C (π ^ (n + 1)) * r).natDegree < qn.1.1.natDegree :=
          (natDegree_C_mul_le _ _).trans_lt hrs
        have htermh : (C (π ^ (n + 1)) * s).natDegree < qn.1.2.natDegree :=
          (natDegree_C_mul_le _ _).trans_lt hss
        have hg' : (qn.1.1 + C (π ^ (n + 1)) * r).Monic :=
          hg.add_of_left (degree_lt_degree htermg)
        have hh' : (qn.1.2 + C (π ^ (n + 1)) * s).Monic :=
          hh.add_of_left (degree_lt_degree htermh)
        have hgd' : (qn.1.1 + C (π ^ (n + 1)) * r).natDegree = g₀.natDegree :=
          (natDegree_add_eq_left_of_natDegree_lt htermg).trans hgd
        have hhd' : (qn.1.2 + C (π ^ (n + 1)) * s).natDegree = h₀.natDegree :=
          (natDegree_add_eq_left_of_natDegree_lt htermh).trans hhd
        have hπmem : π ∈ IsLocalRing.maximalIdeal A := by
          rw [hπ.maximalIdeal_eq]
          exact Submodule.mem_span_singleton_self π
        have hπpowmem : π ^ (n + 1) ∈ IsLocalRing.maximalIdeal A := by
          simpa [pow_succ, mul_comm] using
            (IsLocalRing.maximalIdeal A).mul_mem_left (π ^ n) hπmem
        have hπpowzero : residueMap A (π ^ (n + 1)) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr hπpowmem
        have hπzero : residueMap A π = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr hπmem
        have hrg' : residuePolynomial
            (qn.1.1 + C (π ^ (n + 1)) * r) = g₀ := by
          calc
            residuePolynomial (qn.1.1 + C (π ^ (n + 1)) * r) =
                residuePolynomial qn.1.1 + residuePolynomial (C (π ^ (n + 1)) * r) := by
                  simp [residuePolynomial]
            _ = g₀ := by rw [hrg]; simp [residuePolynomial, hπzero]
        have hrh' : residuePolynomial
            (qn.1.2 + C (π ^ (n + 1)) * s) = h₀ := by
          calc
            residuePolynomial (qn.1.2 + C (π ^ (n + 1)) * s) =
                residuePolynomial qn.1.2 + residuePolynomial (C (π ^ (n + 1)) * s) := by
                  simp [residuePolynomial]
            _ = h₀ := by rw [hrh]; simp [residuePolynomial, hπzero]
        refine ⟨(⟨(qn.1.1 + C (π ^ (n + 1)) * r,
          qn.1.2 + C (π ^ (n + 1)) * s),
          ⟨hg', hh', hgd', hhd', hrg', hrh', hnext⟩⟩, (r, s)), ?_⟩
        exact ⟨rfl, rfl⟩
      let q : ∀ n, Q n := fun n => Nat.rec hQ0 (fun n qn => (stepData n qn).1.1) n
      have hqsucc (n : ℕ) : q (n + 1) = (stepData n (q n)).1.1 := by
        simp [q]
      have hqsucc_factor (n : ℕ) :
          ∃ r : A[X], (q (n + 1)).1.1 = (q n).1.1 + C (π ^ (n + 1)) * r := by
        rw [hqsucc]
        exact ⟨(stepData n (q n)).1.2.1, (stepData n (q n)).2.1⟩
      have hπpow_mem (k : ℕ) : π ^ (k + 1) ∈
          (IsLocalRing.maximalIdeal A) ^ (k + 1) := by
        exact Ideal.pow_mem_pow
          (by
            rw [hπ.maximalIdeal_eq]
            exact Submodule.mem_span_singleton_self π) _
      have hcoeff_step (k d : ℕ) :
          (q (k + 1)).1.1.coeff d - (q k).1.1.coeff d ∈
            (IsLocalRing.maximalIdeal A) ^ (k + 1) := by
        obtain ⟨r, hr⟩ := hqsucc_factor k
        rw [hr]
        simp only [Polynomial.coeff_add,
          Polynomial.coeff_C_mul]
        simpa [sub_eq_add_neg, add_assoc] using
          Ideal.mul_mem_right (r.coeff d)
            ((IsLocalRing.maximalIdeal A) ^ (k + 1)) (hπpow_mem k)
      have hcoeff_diff (d m n : ℕ) (hmn : m ≤ n) :
          (q m).1.1.coeff d - (q n).1.1.coeff d ∈
            (IsLocalRing.maximalIdeal A) ^ m := by
        induction n, hmn using Nat.le_induction with
        | base => simp
        | succ n hmn ih =>
            have hs := hcoeff_step n d
            have hle : m ≤ n + 1 := hmn.trans (Nat.le_succ n)
            have hs' : (q (n + 1)).1.1.coeff d - (q n).1.1.coeff d ∈
                (IsLocalRing.maximalIdeal A) ^ m :=
              (Ideal.pow_le_pow_right hle) hs
            have hsneg : (q n).1.1.coeff d - (q (n + 1)).1.1.coeff d ∈
                (IsLocalRing.maximalIdeal A) ^ m := by
              simpa [sub_eq_add_neg] using
                (IsLocalRing.maximalIdeal A ^ m).neg_mem hs'
            convert (IsLocalRing.maximalIdeal A ^ m).add_mem ih hsneg using 1 ;
              ring
      have hgCauchy (d : ℕ) :
          AdicCompletion.IsAdicCauchy (IsLocalRing.maximalIdeal A) A
            (fun n => (q n).1.1.coeff d) := by
        intro m n hmn
        rw [SModEq.sub_mem]
        simpa [smul_eq_mul, Ideal.mul_top] using hcoeff_diff d m n hmn
      have hgLimit (d : ℕ) : ∃ L : A, ∀ n : ℕ,
          (q n).1.1.coeff d - L ∈ (IsLocalRing.maximalIdeal A) ^ n := by
        obtain ⟨L, hL⟩ := IsPrecomplete.prec
          (inferInstance : IsPrecomplete (IsLocalRing.maximalIdeal A) A)
          (hgCauchy d)
        refine ⟨L, ?_⟩
        intro n
        have hn := hL n
        rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hn
        exact hn
      let glim : ℕ → A := fun d => (hgLimit d).choose
      have hglim_spec (d n : ℕ) :
          (q n).1.1.coeff d - glim d ∈ (IsLocalRing.maximalIdeal A) ^ n :=
        (hgLimit d).choose_spec n
      have hcoeff_zero_high (d n : ℕ) (hd : g₀.natDegree < d) :
          (q n).1.1.coeff d = 0 := by
        rcases (q n).property with ⟨hg, hh, hgd, hhd, hrg, hrh, happrox⟩
        apply coeff_eq_zero_of_natDegree_lt
        rw [hgd]
        exact hd
      have hcoeff_lead_one (n : ℕ) :
          (q n).1.1.coeff g₀.natDegree = 1 := by
        rcases (q n).property with ⟨hg, hh, hgd, hhd, hrg, hrh, happrox⟩
        simpa [← hgd] using hg.coeff_natDegree
      have hglim_eq_zero (d : ℕ) (hd : g₀.natDegree < d) : glim d = 0 := by
        apply (IsHausdorff.eq_iff_smodEq (I := IsLocalRing.maximalIdeal A)
          (M := A)).mpr
        intro n
        have hn := hglim_spec d n
        rw [hcoeff_zero_high d n hd] at hn
        rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
        simpa using (IsLocalRing.maximalIdeal A ^ n).neg_mem hn
      have hglim_eq_one : glim g₀.natDegree = 1 := by
        apply (IsHausdorff.eq_iff_smodEq (I := IsLocalRing.maximalIdeal A)
          (M := A)).mpr
        intro n
        have hn := hglim_spec g₀.natDegree n
        rw [hcoeff_lead_one n] at hn
        rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
        simpa using (IsLocalRing.maximalIdeal A ^ n).neg_mem hn
      let g : A[X] := X ^ g₀.natDegree +
        ∑ i ∈ Finset.range g₀.natDegree, C (glim i) * X ^ i
      have hg : g.Monic := by
        dsimp [g]
        apply monic_X_pow_add
        simp_rw [← Fin.sum_univ_eq_sum_range, degree_sum_fin_lt]
      have hgcoeff_low (i : ℕ) (hi : i < g₀.natDegree) :
          g.coeff i = glim i := by
        simp [g, hi, Nat.ne_of_lt hi]
      have hgcoeff_lead : g.coeff g₀.natDegree = 1 := by
        simp [g]
      have hgcoeff_high (i : ℕ) (hi : g₀.natDegree < i) :
          g.coeff i = 0 := by
        simp [g, Nat.ne_of_gt hi, Nat.not_lt_of_ge (Nat.le_of_lt hi)]
      have hqsucc_factor_h (n : ℕ) :
          ∃ s : A[X], (q (n + 1)).1.2 = (q n).1.2 + C (π ^ (n + 1)) * s := by
        rw [hqsucc]
        exact ⟨(stepData n (q n)).1.2.2, (stepData n (q n)).2.2⟩
      have hcoeff_step_h (k d : ℕ) :
          (q (k + 1)).1.2.coeff d - (q k).1.2.coeff d ∈
            (IsLocalRing.maximalIdeal A) ^ (k + 1) := by
        obtain ⟨s, hs⟩ := hqsucc_factor_h k
        rw [hs]
        simp only [Polynomial.coeff_add,
          Polynomial.coeff_C_mul]
        simpa [sub_eq_add_neg, add_assoc] using
          Ideal.mul_mem_right (s.coeff d)
            ((IsLocalRing.maximalIdeal A) ^ (k + 1)) (hπpow_mem k)
      have hcoeff_diff_h (d m n : ℕ) (hmn : m ≤ n) :
          (q m).1.2.coeff d - (q n).1.2.coeff d ∈
            (IsLocalRing.maximalIdeal A) ^ m := by
        induction n, hmn using Nat.le_induction with
        | base => simp
        | succ n hmn ih =>
            have hs := hcoeff_step_h n d
            have hle : m ≤ n + 1 := hmn.trans (Nat.le_succ n)
            have hs' : (q (n + 1)).1.2.coeff d - (q n).1.2.coeff d ∈
                (IsLocalRing.maximalIdeal A) ^ m :=
              (Ideal.pow_le_pow_right hle) hs
            have hsneg : (q n).1.2.coeff d - (q (n + 1)).1.2.coeff d ∈
                (IsLocalRing.maximalIdeal A) ^ m := by
              simpa [sub_eq_add_neg] using
                (IsLocalRing.maximalIdeal A ^ m).neg_mem hs'
            convert (IsLocalRing.maximalIdeal A ^ m).add_mem ih hsneg using 1 ;
              ring
      have hhCauchy (d : ℕ) :
          AdicCompletion.IsAdicCauchy (IsLocalRing.maximalIdeal A) A
            (fun n => (q n).1.2.coeff d) := by
        intro m n hmn
        rw [SModEq.sub_mem]
        simpa [smul_eq_mul, Ideal.mul_top] using hcoeff_diff_h d m n hmn
      have hhLimit (d : ℕ) : ∃ L : A, ∀ n : ℕ,
          (q n).1.2.coeff d - L ∈ (IsLocalRing.maximalIdeal A) ^ n := by
        obtain ⟨L, hL⟩ := IsPrecomplete.prec
          (inferInstance : IsPrecomplete (IsLocalRing.maximalIdeal A) A)
          (hhCauchy d)
        refine ⟨L, ?_⟩
        intro n
        have hn := hL n
        rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hn
        exact hn
      let hlim : ℕ → A := fun d => (hhLimit d).choose
      have hhlim_spec (d n : ℕ) :
          (q n).1.2.coeff d - hlim d ∈ (IsLocalRing.maximalIdeal A) ^ n :=
        (hhLimit d).choose_spec n
      have hcoeff_h_zero_high (d n : ℕ) (hd : h₀.natDegree < d) :
          (q n).1.2.coeff d = 0 := by
        rcases (q n).property with ⟨hg, hh, hgd, hhd, hrg, hrh, happrox⟩
        apply coeff_eq_zero_of_natDegree_lt
        rw [hhd]
        exact hd
      have hcoeff_h_lead_one (n : ℕ) :
          (q n).1.2.coeff h₀.natDegree = 1 := by
        rcases (q n).property with ⟨hg, hh, hgd, hhd, hrg, hrh, happrox⟩
        simpa [← hhd] using hh.coeff_natDegree
      have hhlim_eq_zero (d : ℕ) (hd : h₀.natDegree < d) : hlim d = 0 := by
        apply (IsHausdorff.eq_iff_smodEq (I := IsLocalRing.maximalIdeal A)
          (M := A)).mpr
        intro n
        have hn := hhlim_spec d n
        rw [hcoeff_h_zero_high d n hd] at hn
        rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
        simpa using (IsLocalRing.maximalIdeal A ^ n).neg_mem hn
      have hhlim_eq_one : hlim h₀.natDegree = 1 := by
        apply (IsHausdorff.eq_iff_smodEq (I := IsLocalRing.maximalIdeal A)
          (M := A)).mpr
        intro n
        have hn := hhlim_spec h₀.natDegree n
        rw [hcoeff_h_lead_one n] at hn
        rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
        simpa using (IsLocalRing.maximalIdeal A ^ n).neg_mem hn
      let h : A[X] := X ^ h₀.natDegree +
        ∑ i ∈ Finset.range h₀.natDegree, C (hlim i) * X ^ i
      have hh : h.Monic := by
        dsimp [h]
        apply monic_X_pow_add
        simp_rw [← Fin.sum_univ_eq_sum_range, degree_sum_fin_lt]
      have hhcoeff_low (i : ℕ) (hi : i < h₀.natDegree) :
          h.coeff i = hlim i := by
        simp [h, hi, Nat.ne_of_lt hi]
      have hhcoeff_lead : h.coeff h₀.natDegree = 1 := by
        simp [h]
      have hhcoeff_high (i : ℕ) (hi : h₀.natDegree < i) :
          h.coeff i = 0 := by
        simp [h, Nat.ne_of_gt hi,
          Nat.not_lt_of_ge (Nat.le_of_lt hi)]
      have hgcoeff_eq (i : ℕ) : g.coeff i = glim i := by
        by_cases hi : i < g₀.natDegree
        · exact hgcoeff_low i hi
        by_cases hieq : i = g₀.natDegree
        · subst i
          simpa [hglim_eq_one] using hgcoeff_lead
        have hig : g₀.natDegree < i := lt_of_le_of_ne
          (Nat.le_of_not_gt hi) (Ne.symm hieq)
        rw [hgcoeff_high i hig, hglim_eq_zero i hig]
      have hhcoeff_eq (i : ℕ) : h.coeff i = hlim i := by
        by_cases hi : i < h₀.natDegree
        · exact hhcoeff_low i hi
        by_cases hieq : i = h₀.natDegree
        · subst i
          simpa [hhlim_eq_one] using hhcoeff_lead
        have hig : h₀.natDegree < i := lt_of_le_of_ne
          (Nat.le_of_not_gt hi) (Ne.symm hieq)
        rw [hhcoeff_high i hig, hhlim_eq_zero i hig]
      have hprod_coeff (n d : ℕ) :
          ((q n).1.1 * (q n).1.2).coeff d - (g * h).coeff d ∈
            (IsLocalRing.maximalIdeal A) ^ n := by
        rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
        rw [← Finset.sum_sub_distrib]
        apply (IsLocalRing.maximalIdeal A ^ n).sum_mem
        intro x hx
        have hga : (q n).1.1.coeff x.1 - g.coeff x.1 ∈
            (IsLocalRing.maximalIdeal A) ^ n := by
          rw [hgcoeff_eq x.1]
          exact hglim_spec x.1 n
        have hhb : (q n).1.2.coeff x.2 - h.coeff x.2 ∈
            (IsLocalRing.maximalIdeal A) ^ n := by
          rw [hhcoeff_eq x.2]
          exact hhlim_spec x.2 n
        have hterm :
            (q n).1.1.coeff x.1 * (q n).1.2.coeff x.2 -
                g.coeff x.1 * h.coeff x.2 ∈
              (IsLocalRing.maximalIdeal A) ^ n := by
          rw [show (q n).1.1.coeff x.1 * (q n).1.2.coeff x.2 -
                g.coeff x.1 * h.coeff x.2 =
              ((q n).1.1.coeff x.1 - g.coeff x.1) *
                  (q n).1.2.coeff x.2 +
                g.coeff x.1 *
                  ((q n).1.2.coeff x.2 - h.coeff x.2) by ring]
          have h1 := Ideal.mul_mem_left (IsLocalRing.maximalIdeal A ^ n)
            ((q n).1.2.coeff x.2) hga
          have h2 := Ideal.mul_mem_left (IsLocalRing.maximalIdeal A ^ n)
            (g.coeff x.1) hhb
          exact (IsLocalRing.maximalIdeal A ^ n).add_mem
            (by rw [mul_comm]; exact h1) h2
        exact hterm
      have hfactor_coeff (n d : ℕ) :
          (f - g * h).coeff d ∈ (IsLocalRing.maximalIdeal A) ^ n := by
        rcases (q n).property with ⟨hgq, hhq, hgdq, hhdq, hrgq, hrhq, happrox⟩
        unfold ApproximateFactorization PolynomialCoefficientsInIdeal at happrox
        have ha := happrox d
        have ha' : (f - (q n).1.1 * (q n).1.2).coeff d ∈
            (IsLocalRing.maximalIdeal A) ^ n := by
          exact (Ideal.pow_le_pow_right (Nat.le_succ n)) ha
        have hp := hprod_coeff n d
        have hadd := (IsLocalRing.maximalIdeal A ^ n).add_mem ha' hp
        simpa [sub_eq_add_neg, add_assoc] using hadd
      have hfactor : f = g * h := by
        apply sub_eq_zero.mp
        apply Polynomial.ext
        intro d
        apply (IsHausdorff.haus (I := IsLocalRing.maximalIdeal A) (M := A)
          (inferInstance : IsHausdorff (IsLocalRing.maximalIdeal A) A))
        intro n
        rw [SModEq.sub_mem]
        simpa [smul_eq_mul, Ideal.mul_top] using hfactor_coeff n d
      have hqred_g (i : ℕ) :
          residueMap A ((q 1).1.1.coeff i) = g₀.coeff i := by
        rcases (q 1).property with ⟨hgq, hhq, hgdq, hhdq, hrgq, hrhq, happrox⟩
        have hi := congrArg (fun p : Polynomial (ResidueRing A) => p.coeff i) hrgq
        simpa [residuePolynomial] using hi
      have hqred_h (i : ℕ) :
          residueMap A ((q 1).1.2.coeff i) = h₀.coeff i := by
        rcases (q 1).property with ⟨hgq, hhq, hgdq, hhdq, hrgq, hrhq, happrox⟩
        have hi := congrArg (fun p : Polynomial (ResidueRing A) => p.coeff i) hrhq
        simpa [residuePolynomial] using hi
      have hglim_map (i : ℕ) : residueMap A (glim i) = g₀.coeff i := by
        have hi := hglim_spec i 1
        have hi' : residueMap A ((q 1).1.1.coeff i - glim i) = 0 := by
          apply Ideal.Quotient.eq_zero_iff_mem.mpr
          simpa [pow_one] using hi
        rw [map_sub] at hi'
        exact (sub_eq_zero.mp hi').symm.trans (hqred_g i)
      have hlim_map (i : ℕ) : residueMap A (hlim i) = h₀.coeff i := by
        have hi := hhlim_spec i 1
        have hi' : residueMap A ((q 1).1.2.coeff i - hlim i) = 0 := by
          apply Ideal.Quotient.eq_zero_iff_mem.mpr
          simpa [pow_one] using hi
        rw [map_sub] at hi'
        exact (sub_eq_zero.mp hi').symm.trans (hqred_h i)
      have hdeg_g : g.natDegree = g₀.natDegree := by
        have hsum : (∑ i ∈ Finset.range g₀.natDegree,
            C (glim i) * X ^ i).degree < (g₀.natDegree : WithBot ℕ) := by
          simp_rw [← Fin.sum_univ_eq_sum_range, degree_sum_fin_lt]
        dsimp [g]
        rw [Polynomial.natDegree_add_eq_left_of_degree_lt]
        · simp
        · simpa [degree_X_pow] using hsum
      have hdeg_h : h.natDegree = h₀.natDegree := by
        have hsum : (∑ i ∈ Finset.range h₀.natDegree,
            C (hlim i) * X ^ i).degree < (h₀.natDegree : WithBot ℕ) := by
          simp_rw [← Fin.sum_univ_eq_sum_range, degree_sum_fin_lt]
        dsimp [h]
        rw [Polynomial.natDegree_add_eq_left_of_degree_lt]
        · simp
        · simpa [degree_X_pow] using hsum
      have hredg : residuePolynomial g = g₀ := by
        apply Polynomial.ext
        intro i
        by_cases hi : i < g₀.natDegree
        · have hi' : residueMap A (g.coeff i) = g₀.coeff i := by
            rw [hgcoeff_low i hi, hglim_map i]
          simpa only [residuePolynomial, Polynomial.coeff_map] using hi'
        · by_cases hieq : i = g₀.natDegree
          · subst i
            have hi' : residueMap A (g.coeff g₀.natDegree) =
                g₀.coeff g₀.natDegree := by
              rw [hgcoeff_lead, hg₀.coeff_natDegree]
              simp
            simpa only [residuePolynomial, Polynomial.coeff_map] using hi'
          · have hig : g₀.natDegree < i := lt_of_le_of_ne
              (Nat.le_of_not_gt hi) (Ne.symm hieq)
            have hi' : residueMap A (g.coeff i) = g₀.coeff i := by
              rw [hgcoeff_high i hig]
              have hzero : g₀.coeff i = 0 := coeff_eq_zero_of_natDegree_lt hig
              simp [hzero]
            simpa only [residuePolynomial, Polynomial.coeff_map] using hi'
      have hredh : residuePolynomial h = h₀ := by
        apply Polynomial.ext
        intro i
        by_cases hi : i < h₀.natDegree
        · have hi' : residueMap A (h.coeff i) = h₀.coeff i := by
            rw [hhcoeff_low i hi, hlim_map i]
          simpa only [residuePolynomial, Polynomial.coeff_map] using hi'
        · by_cases hieq : i = h₀.natDegree
          · subst i
            have hi' : residueMap A (h.coeff h₀.natDegree) =
                h₀.coeff h₀.natDegree := by
              rw [hhcoeff_lead, hh₀.coeff_natDegree]
              simp
            simpa only [residuePolynomial, Polynomial.coeff_map] using hi'
          · have hig : h₀.natDegree < i := lt_of_le_of_ne
              (Nat.le_of_not_gt hi) (Ne.symm hieq)
            have hi' : residueMap A (h.coeff i) = h₀.coeff i := by
              rw [hhcoeff_high i hig]
              have hzero : h₀.coeff i = 0 := coeff_eq_zero_of_natDegree_lt hig
              simp [hzero]
            simpa only [residuePolynomial, Polynomial.coeff_map] using hi'
      let m : Ideal A := IsLocalRing.maximalIdeal A
      have hm : m = Ideal.span ({π} : Set A) := by
        exact hπ.maximalIdeal_eq
      have hm_pow (n : ℕ) : m ^ n = Ideal.span ({π ^ n} : Set A) := by
        rw [hm, Ideal.span_singleton_pow]
      have hdivide (p : A[X]) (n : ℕ) (hp : ∀ i : ℕ, p.coeff i ∈ m ^ n) :
          ∃ t : A[X], p = C (π ^ n) * t ∧ t.degree ≤ p.degree := by
        let qcoeff : ℕ → A := fun i =>
          Classical.choose (Ideal.mem_span_singleton.mp (hm_pow n ▸ hp i))
        have hqcoeff : ∀ i : ℕ, p.coeff i = π ^ n * qcoeff i := by
          intro i
          have hi := Classical.choose_spec (Ideal.mem_span_singleton.mp
            (hm_pow n ▸ hp i))
          dsimp [qcoeff]
          exact hi
        have hq_support : ∀ i : ℕ, qcoeff i ≠ 0 → i ∈ p.support := by
          intro i hi
          apply Polynomial.mem_support_iff.mpr
          intro hzero
          apply hi
          have hmul : π ^ n * qcoeff i = 0 := by simpa [hzero] using hqcoeff i
          exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero n hπ.ne_zero)
        let q : ℕ →₀ A := Finsupp.onFinset p.support qcoeff hq_support
        let t : A[X] := Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff q)
        have htcoeff : ∀ i : ℕ, t.coeff i = qcoeff i := by
          intro i
          change (AddMonoidAlgebra.ofCoeff q).coeff i = qcoeff i
          simp [q, Finsupp.onFinset_apply]
        have hpt : p = C (π ^ n) * t := by
          ext i
          rw [Polynomial.coeff_C_mul, htcoeff, hqcoeff]
        refine ⟨t, hpt, ?_⟩
        apply Polynomial.degree_mono
        intro i hi
        apply hq_support i
        rw [← htcoeff i]
        exact Polynomial.mem_support_iff.mp hi
      refine ⟨(g, h), ?_, ?_⟩
      · exact ⟨hg, hh, hdeg_g, hdeg_h, hredg, hredh, hfactor⟩
      · intro gh hgh
        rcases hgh with ⟨hg', hh', hgd', hhd', hredg', hredh', hfac'⟩
        have hprod_eq : gh.1 * gh.2 = g * h := by
          rw [← hfac', hfactor]
        have hbase (i : ℕ) :
            (gh.1 - g).coeff i ∈ m ∧ (gh.2 - h).coeff i ∈ m := by
          constructor
          · change (gh.1 - g).coeff i ∈ IsLocalRing.maximalIdeal A
            have hi0 : residueMap A ((gh.1 - g).coeff i) = 0 := by
              have hi := congrArg (fun P : Polynomial (ResidueRing A) => P.coeff i)
                (hredg'.trans hredg.symm)
              have hi' : residueMap A (gh.1.coeff i) = residueMap A (g.coeff i) := by
                simpa only [residuePolynomial, Polynomial.coeff_map] using hi
              rw [Polynomial.coeff_sub, map_sub]
              exact sub_eq_zero.mpr hi'
            exact Ideal.Quotient.eq_zero_iff_mem.mp hi0
          · change (gh.2 - h).coeff i ∈ IsLocalRing.maximalIdeal A
            have hi0 : residueMap A ((gh.2 - h).coeff i) = 0 := by
              have hi := congrArg (fun P : Polynomial (ResidueRing A) => P.coeff i)
                (hredh'.trans hredh.symm)
              have hi' : residueMap A (gh.2.coeff i) = residueMap A (h.coeff i) := by
                simpa only [residuePolynomial, Polynomial.coeff_map] using hi
              rw [Polynomial.coeff_sub, map_sub]
              exact sub_eq_zero.mpr hi'
            exact Ideal.Quotient.eq_zero_iff_mem.mp hi0
        let hfield : Field (ResidueRing A) :=
          Ideal.Quotient.field (IsLocalRing.maximalIdeal A)
        have hstep_unique (n : ℕ) (hn : 1 ≤ n)
            (hgn : ∀ i : ℕ, (gh.1 - g).coeff i ∈ m ^ n)
            (hhn : ∀ i : ℕ, (gh.2 - h).coeff i ∈ m ^ n) :
            ∀ i : ℕ,
              (gh.1 - g).coeff i ∈ m ^ (n + 1) ∧
                (gh.2 - h).coeff i ∈ m ^ (n + 1) := by
          obtain ⟨rg, hrg_eq, hrgdeg⟩ := hdivide (gh.1 - g) n hgn
          obtain ⟨rh, hrh_eq, hrhdeg⟩ := hdivide (gh.2 - h) n hhn
          have hδgdeg : (gh.1 - g).degree < g.degree := by
            apply Polynomial.degree_sub_lt_right
            · rw [Polynomial.degree_eq_natDegree hg'.ne_zero,
                Polynomial.degree_eq_natDegree hg.ne_zero, hgd', hdeg_g]
            · exact hg.ne_zero
            · rw [hg'.leadingCoeff, hg.leadingCoeff]
          have hδhdeg : (gh.2 - h).degree < h.degree := by
            apply Polynomial.degree_sub_lt_right
            · rw [Polynomial.degree_eq_natDegree hh'.ne_zero,
                Polynomial.degree_eq_natDegree hh.ne_zero, hhd', hdeg_h]
            · exact hh.ne_zero
            · rw [hh'.leadingCoeff, hh.leadingCoeff]
          have hrgdeg' : rg.degree < g.degree := hrgdeg.trans_lt hδgdeg
          have hrhdeg' : rh.degree < h.degree := hrhdeg.trans_lt hδhdeg
          have hrelg : gh.1 = g + C (π ^ n) * rg := by
            simpa [add_comm] using (eq_add_of_sub_eq hrg_eq)
          have hrelh : gh.2 = h + C (π ^ n) * rh := by
            simpa [add_comm] using (eq_add_of_sub_eq hrh_eq)
          have hexpand :
              C (π ^ n) * (rg * h + rh * g) +
                  C ((π ^ n) ^ 2) * (rg * rh) = 0 := by
            calc
              C (π ^ n) * (rg * h + rh * g) +
                    C ((π ^ n) ^ 2) * (rg * rh) =
                  (g + C (π ^ n) * rg) * (h + C (π ^ n) * rh) - g * h := by
                    have hC : C ((π ^ n) ^ 2) =
                        C (π ^ n) * C (π ^ n) := by
                      rw [pow_two]
                      exact Polynomial.C_mul (a := π ^ n) (b := π ^ n)
                    simp only [mul_add, add_mul]
                    rw [hC]
                    ring
              _ = gh.1 * gh.2 - g * h := by rw [hrelg, hrelh]
              _ = 0 := sub_eq_zero.mpr hprod_eq
          have hp_mem : π ^ n ∈ m ^ n := by
            rw [hm_pow n]
            exact Ideal.mem_span_singleton.mpr (dvd_refl _)
          have hp2_mem' : (π ^ n) ^ 2 ∈ m ^ (n + n) := by
            have hmul := Ideal.mul_mem_mul hp_mem hp_mem
            rw [← pow_add] at hmul
            simpa [pow_two] using hmul
          have hp2_mem : (π ^ n) ^ 2 ∈ m ^ (n + 1) := by
            exact (Ideal.pow_le_pow_right (by omega)) hp2_mem'
          have hquad (d : ℕ) :
              (C ((π ^ n) ^ 2) * (rg * rh)).coeff d ∈ m ^ (n + 1) := by
            rw [Polynomial.coeff_C_mul]
            exact Ideal.mul_mem_right _ (m ^ (n + 1)) hp2_mem
          have hcancel_mem (x : A) (hx : π ^ n * x ∈ m ^ (n + 1)) :
              x ∈ m := by
            rw [hm]
            obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp
              (hm_pow (n + 1) ▸ hx)
            apply Ideal.mem_span_singleton.mpr
            refine ⟨c, ?_⟩
            apply (mul_left_cancel₀ (pow_ne_zero n hπ.ne_zero))
            calc
              π ^ n * x = π ^ (n + 1) * c := hc
              _ = π ^ n * (π * c) := by rw [pow_succ]; ring
          have hlin_mem (d : ℕ) :
              (rg * h + rh * g).coeff d ∈ m := by
            have he := congrArg (fun P : A[X] => P.coeff d) hexpand
            rw [Polynomial.coeff_add, Polynomial.coeff_C_mul,
              Polynomial.coeff_C_mul] at he
            apply hcancel_mem
            have hneg := (m ^ (n + 1)).neg_mem (hquad d)
            rw [eq_neg_of_add_eq_zero_left he]
            simpa only [Polynomial.coeff_C_mul] using hneg
          have hlin_res : residuePolynomial (rg * h + rh * g) = 0 := by
            apply Polynomial.ext
            intro d
            have hd : residueMap A ((rg * h + rh * g).coeff d) = 0 :=
              Ideal.Quotient.eq_zero_iff_mem.mpr (hlin_mem d)
            simpa only [residuePolynomial, Polynomial.coeff_map, coeff_zero] using hd
          have hcorrprop : CoprimeCorrectionProperty g₀ h₀ :=
            @coprime_correction_property (ResidueRing A) hfield g₀ h₀ hg₀ hh₀ hcop
          have hrgbar_deg : (residuePolynomial rg).degree < g₀.degree := by
            calc
              (residuePolynomial rg).degree ≤ rg.degree := Polynomial.degree_map_le
              _ < g.degree := hrgdeg'
              _ = g₀.degree := by
                rw [Polynomial.degree_eq_natDegree hg.ne_zero,
                  Polynomial.degree_eq_natDegree hg₀.ne_zero, hdeg_g]
          have hrhbar_deg : (residuePolynomial rh).degree < h₀.degree := by
            calc
              (residuePolynomial rh).degree ≤ rh.degree := Polynomial.degree_map_le
              _ < h.degree := hrhdeg'
              _ = h₀.degree := by
                rw [Polynomial.degree_eq_natDegree hh.ne_zero,
                  Polynomial.degree_eq_natDegree hh₀.ne_zero, hdeg_h]
          have hlin_corr :
              factorizationCorrectionMap g₀ h₀
                (residuePolynomial rg, residuePolynomial rh) = 0 := by
            dsimp [factorizationCorrectionMap]
            rw [← hredh, ← hredg]
            simpa [residuePolynomial, Polynomial.map_add, Polynomial.map_mul] using
              hlin_res
          have hg₀deg : g₀.degree ≠ (⊥ : WithBot ℕ) :=
            Polynomial.degree_ne_bot.mpr hg₀.ne_zero
          have hh₀deg : h₀.degree ≠ (⊥ : WithBot ℕ) :=
            Polynomial.degree_ne_bot.mpr hh₀.ne_zero
          have hzero_deg :
              (0 : Polynomial (ResidueRing A)).degree < (g₀ * h₀).degree := by
            rw [Polynomial.degree_zero, Polynomial.degree_mul]
            exact WithBot.bot_lt_iff_ne_bot.mpr
              (WithBot.add_ne_bot.mpr ⟨hg₀deg, hh₀deg⟩)
          obtain ⟨rs₀, hrs₀, hrsuniq⟩ := hcorrprop 0 hzero_deg
          have hzero_prop :
              (0 : Polynomial (ResidueRing A)).degree < g₀.degree ∧
                (0 : Polynomial (ResidueRing A)).degree < h₀.degree ∧
                factorizationCorrectionMap g₀ h₀ (0, 0) = 0 := by
            refine ⟨WithBot.bot_lt_iff_ne_bot.mpr hg₀deg,
              WithBot.bot_lt_iff_ne_bot.mpr hh₀deg, ?_⟩
            simp [factorizationCorrectionMap]
          have hpair :
              (residuePolynomial rg, residuePolynomial rh) = (0, 0) := by
            exact (hrsuniq _ ⟨hrgbar_deg, hrhbar_deg, hlin_corr⟩).trans
              (hrsuniq _ hzero_prop).symm
          have hrg_res : residuePolynomial rg = 0 := congrArg Prod.fst hpair
          have hrh_res : residuePolynomial rh = 0 := congrArg Prod.snd hpair
          have hrg_mem (d : ℕ) : rg.coeff d ∈ m := by
            change rg.coeff d ∈ IsLocalRing.maximalIdeal A
            have hd := congrArg (fun P : Polynomial (ResidueRing A) => P.coeff d)
              hrg_res
            have hd0 : residueMap A (rg.coeff d) = 0 := by
              simpa only [residuePolynomial, Polynomial.coeff_map, coeff_zero] using hd
            exact Ideal.Quotient.eq_zero_iff_mem.mp hd0
          have hrh_mem (d : ℕ) : rh.coeff d ∈ m := by
            change rh.coeff d ∈ IsLocalRing.maximalIdeal A
            have hd := congrArg (fun P : Polynomial (ResidueRing A) => P.coeff d)
              hrh_res
            have hd0 : residueMap A (rh.coeff d) = 0 := by
              simpa only [residuePolynomial, Polynomial.coeff_map, coeff_zero] using hd
            exact Ideal.Quotient.eq_zero_iff_mem.mp hd0
          intro d
          constructor
          · rw [hrg_eq, Polynomial.coeff_C_mul]
            simpa [pow_succ] using Ideal.mul_mem_mul hp_mem (hrg_mem d)
          · rw [hrh_eq, Polynomial.coeff_C_mul]
            simpa [pow_succ] using Ideal.mul_mem_mul hp_mem (hrh_mem d)
        have hdiff_succ : ∀ k : ℕ, ∀ i : ℕ,
            (gh.1 - g).coeff i ∈ m ^ (k + 1) ∧
              (gh.2 - h).coeff i ∈ m ^ (k + 1) := by
          intro k
          induction k with
          | zero => intro i; simpa [pow_one] using hbase i
          | succ k ih =>
              exact hstep_unique (k + 1) (by omega)
                (fun i => (ih i).1) (fun i => (ih i).2)
        have hdiff_all (n i : ℕ) :
            (gh.1 - g).coeff i ∈ m ^ n ∧
              (gh.2 - h).coeff i ∈ m ^ n := by
          cases n with
          | zero => simp
          | succ k => exact hdiff_succ k i
        have hzero_g : gh.1 - g = 0 := by
          apply Polynomial.ext
          intro i
          apply (IsHausdorff.haus (I := IsLocalRing.maximalIdeal A) (M := A)
            (inferInstance : IsHausdorff (IsLocalRing.maximalIdeal A) A))
          intro n
          rw [SModEq.sub_mem]
          simpa [smul_eq_mul, Ideal.mul_top] using (hdiff_all n i).1
        have hzero_h : gh.2 - h = 0 := by
          apply Polynomial.ext
          intro i
          apply (IsHausdorff.haus (I := IsLocalRing.maximalIdeal A) (M := A)
            (inferInstance : IsHausdorff (IsLocalRing.maximalIdeal A) A))
          intro n
          rw [SModEq.sub_mem]
          simpa [smul_eq_mul, Ideal.mul_top] using (hdiff_all n i).2
        apply Prod.ext
        · exact sub_eq_zero.mp hzero_g
        · exact sub_eq_zero.mp hzero_h

/-- The homogeneous first-precision correction equation proves uniqueness of factor lifts. -/
theorem hensel_factorization_unique_at_first_nonzero_precision
    {A : Type*} [CommRing A] [IsDomain A] [CompleteDVR A]
    {f : A[X]} {g₀ h₀ : Polynomial (ResidueRing A)}
    (hf : f.Monic) (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hcop : IsCoprime g₀ h₀) :
    ∀ gh₁ gh₂ : A[X] × A[X],
      IsFactorizationLift f g₀ h₀ gh₁.1 gh₁.2 →
      IsFactorizationLift f g₀ h₀ gh₂.1 gh₂.2 → gh₁ = gh₂ := by
  intro gh₁ gh₂ h₁ h₂
  rcases h₁ with ⟨hg₁, hh₁, hng₁, hnh₁, hrg₁, hrh₁, hfac₁⟩
  have hred : residuePolynomial f = g₀ * h₀ := by
    calc
      residuePolynomial f = residuePolynomial (gh₁.1 * gh₁.2) := by rw [hfac₁]
      _ = residuePolynomial gh₁.1 * residuePolynomial gh₁.2 := by
        simp [residuePolynomial]
      _ = g₀ * h₀ := by rw [hrg₁, hrh₁]
  obtain ⟨gh, hgh, huniq⟩ :=
    hensel_factorization f g₀ h₀ hf hg₀ hh₀ hcop hred
  have h₁' : IsFactorizationLift f g₀ h₀ gh₁.1 gh₁.2 :=
    ⟨hg₁, hh₁, hng₁, hnh₁, hrg₁, hrh₁, hfac₁⟩
  exact (huniq gh₁ h₁').trans (huniq gh₂ h₂).symm

/-- A simple residue root is a linear factor and therefore lifts uniquely. -/
theorem monic_simple_residue_root_lifts {A : Type*} [CommRing A] [IsDomain A]
    [CompleteDVR A] (f : A[X]) (a₀ : ResidueRing A)
    (hf : f.Monic)
    (hroot : (residuePolynomial f).eval a₀ = 0)
    (hsimple : IsUnit ((residuePolynomial f).derivative.eval a₀)) :
    ∃! a : A, f.eval a = 0 ∧ residueClass a = a₀ := by
  have _hf := hf
  obtain ⟨a₀', ha₀'⟩ := Ideal.Quotient.mk_surjective a₀
  have hfa : f.eval a₀' ∈ IsLocalRing.maximalIdeal A := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change residueMap A (f.eval a₀') = 0
    have hroot' := hroot
    rw [← ha₀'] at hroot'
    change (f.map (residueMap A)).eval (residueMap A a₀') = 0 at hroot'
    rw [Polynomial.eval_map_apply] at hroot'
    exact hroot'
  have hunit : IsUnit (f.derivative.eval a₀') := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    change residueMap A (f.derivative.eval a₀') ≠ 0
    have hsimple' : (residuePolynomial f).derivative.eval a₀ ≠ 0 :=
      hsimple.ne_zero
    rw [← ha₀'] at hsimple'
    change ((f.map (residueMap A)).derivative).eval (residueMap A a₀') ≠ 0 at hsimple'
    rw [Polynomial.derivative_map, Polynomial.eval_map_apply] at hsimple'
    exact hsimple'
  obtain ⟨a, ha, huniq⟩ := hensel_simple_root f a₀' hfa hunit
  refine ⟨a, ?_, ?_⟩
  · refine ⟨ha.1, ?_⟩
    unfold residueClass residueMap
    rw [← ha₀']
    rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact ha.2
  · intro b hb
    have hbc : CongruentModIdeal (IsLocalRing.maximalIdeal A) b a₀' := by
      unfold CongruentModIdeal
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      change residueMap A (b - a₀') = 0
      have hres : residueMap A b = residueMap A a₀' := by
        calc
          residueMap A b = a₀ := by simpa [residueClass, residueMap] using hb.2
          _ = residueMap A a₀' := ha₀'.symm
      rw [map_sub, hres]
      simp
    exact huniq b ⟨hb.1, hbc⟩

/-- Pairwise coprime residue factors lift simultaneously. -/
def PairwiseCoprimeFamily {ι R : Type*} [CommRing R]
    (f : ι → R[X]) : Prop :=
  ∀ ⦃i j : ι⦄, i ≠ j → IsCoprime (f i) (f j)

set_option maxHeartbeats 3000000 in
/-- The simultaneous pairwise-coprime factor lifting consequence. -/
theorem hensel_lift_pairwise_coprime_factors {A : Type*} {ι : Type uI}
    [CommRing A] [IsDomain A]
    [CompleteDVR A] [Fintype ι] (f : A[X])
    (f₀ : ι → Polynomial (ResidueRing A))
    (hf : f.Monic) (hmonic : ∀ i, (f₀ i).Monic)
    (hpair : PairwiseCoprimeFamily f₀)
    (hred : residuePolynomial f = ∏ i, f₀ i) :
    ∃ lifts : ι → A[X],
      (∀ i, (lifts i).Monic ∧ (lifts i).natDegree = (f₀ i).natDegree ∧
        residuePolynomial (lifts i) = f₀ i) ∧
      f = ∏ i, lifts i := by
  classical
  let P : ∀ (ι : Type uI) [Fintype ι], Prop := fun ι _ =>
    ∀ (f : A[X]) (f₀ : ι → Polynomial (ResidueRing A)),
      f.Monic → (∀ i, (f₀ i).Monic) →
      PairwiseCoprimeFamily f₀ → residuePolynomial f = ∏ i, f₀ i →
      ∃ lifts : ι → A[X],
        (∀ i, (lifts i).Monic ∧ (lifts i).natDegree = (f₀ i).natDegree ∧
          residuePolynomial (lifts i) = f₀ i) ∧
        f = ∏ i, lifts i
  have hP : P ι := by
    apply Fintype.induction_empty_option (P := fun ι _ => P ι)
    · intro α β inst e IH
      letI : Fintype α := Fintype.ofEquiv β e.symm
      intro f f₀ hf hmonic hpair hred
      let f₀' : α → Polynomial (ResidueRing A) := fun a => f₀ (e a)
      have hmonic' : ∀ a, (f₀' a).Monic := by
        intro a
        exact hmonic (e a)
      have hpair' : PairwiseCoprimeFamily f₀' := by
        intro a b hab
        apply hpair
        intro heq
        apply hab
        exact e.injective heq
      have hred' : residuePolynomial f = ∏ a, f₀' a := by
        rw [hred]
        exact (e.prod_comp f₀).symm
      obtain ⟨lifts, hlifts, hprod⟩ := IH f f₀' hf hmonic' hpair' hred'
      let lifts' : β → A[X] := fun b => lifts (e.symm b)
      refine ⟨lifts', ?_, ?_⟩
      · intro b
        simpa [lifts', f₀'] using hlifts (e.symm b)
      · calc
          f = ∏ a, lifts a := hprod
          _ = ∏ b, lifts' b := by
            rw [← e.prod_comp lifts']
            simp [lifts']
    · intro f f₀ hf hmonic hpair hred
      have hred1 : residuePolynomial f = 1 := by
        simpa using hred
      have hfd : f.natDegree = 0 := by
        calc
          f.natDegree = (residuePolynomial f).natDegree :=
            (hf.natDegree_map (residueMap A)).symm
          _ = (1 : Polynomial (ResidueRing A)).natDegree :=
            congrArg Polynomial.natDegree hred1
          _ = 0 := by simp
      have hf1 : f = 1 := hf.natDegree_eq_zero.mp hfd
      refine ⟨fun i => PEmpty.elim i, ?_, ?_⟩
      · intro i
        exact PEmpty.elim i
      · simp [hf1]
    · intro α inst IH f f₀ hf hmonic hpair hred
      let g₀ : Polynomial (ResidueRing A) := f₀ none
      let h₀ : Polynomial (ResidueRing A) := ∏ a, f₀ (some a)
      have hg₀ : g₀.Monic := hmonic none
      have hh₀ : h₀.Monic := by
        dsimp [h₀]
        exact monic_prod_of_monic Finset.univ _ (by
          intro a ha
          exact hmonic (some a))
      have hcop : IsCoprime g₀ h₀ := by
        dsimp [g₀, h₀]
        apply IsCoprime.prod_right
        intro a ha
        exact hpair (by simp)
      have hred' : residuePolynomial f = g₀ * h₀ := by
        dsimp [g₀, h₀]
        rw [hred, Fintype.prod_option]
      obtain ⟨gh, hgh, _⟩ :=
        hensel_factorization f g₀ h₀ hf hg₀ hh₀ hcop hred'
      rcases hgh with ⟨hg, hh, hgd, hhd, hrg, hrh, hfac⟩
      have hpair' : PairwiseCoprimeFamily (fun a : α => f₀ (some a)) := by
        intro a b hab
        apply hpair
        intro heq
        apply hab
        exact Option.some.inj heq
      obtain ⟨rest, hrest, hrestprod⟩ :=
        IH gh.2 (fun a : α => f₀ (some a)) hh
          (fun a => hmonic (some a)) hpair' hrh
      let lifts : Option α → A[X] := fun o =>
        match o with
        | none => gh.1
        | some a => rest a
      refine ⟨lifts, ?_, ?_⟩
      · intro o
        cases o with
        | none => simpa [lifts, g₀] using And.intro hg (And.intro hgd hrg)
        | some a => simpa [lifts] using hrest a
      · calc
          f = gh.1 * gh.2 := hfac
          _ = gh.1 * ∏ a, rest a := by rw [hrestprod]
          _ = ∏ o, lifts o := by
            rw [Fintype.prod_option]
  simpa [P] using hP f f₀ hf hmonic hpair hred

/-- Residue-field factorization predicts a corresponding factorization upstairs. -/
theorem residue_factorization_predicts_complete_factorization
    {A : Type*} [CommRing A] [IsDomain A] [CompleteDVR A]
    (f : A[X]) (g₀ h₀ : Polynomial (ResidueRing A))
    (hf : f.Monic) (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hcop : IsCoprime g₀ h₀) (hred : residuePolynomial f = g₀ * h₀) :
    ∃ g h : A[X], IsFactorizationLift f g₀ h₀ g h := by
  obtain ⟨gh, hgh, _⟩ := hensel_factorization f g₀ h₀ hf hg₀ hh₀ hcop hred
  exact ⟨gh.1, gh.2, hgh⟩

/-! ## 9.4 Henselian local rings -/

/-- Chapter-specific name for Mathlib's henselian local-ring class. -/
def IsHenselianLocalRingChapter09 (A : Type*) [CommRing A] : Prop :=
  HenselianLocalRing A

/-- The simple-residue-root lifting property. -/
def SimpleResidueRootLiftingProperty (A : Type*) [CommRing A] [IsLocalRing A] : Prop :=
  ∀ (f : A[X]) (a₀ : ResidueRing A), f.Monic →
    (residuePolynomial f).eval a₀ = 0 →
    IsUnit ((residuePolynomial f).derivative.eval a₀) →
    ∃! a : A, f.eval a = 0 ∧ residueClass a = a₀

/-- The coprime-factorization lifting property. -/
def HenselianFactorizationProperty (A : Type*) [CommRing A] [IsLocalRing A] : Prop :=
  ∀ (f : A[X]) (g₀ h₀ : Polynomial (ResidueRing A)), f.Monic →
    g₀.Monic → h₀.Monic → IsCoprime g₀ h₀ → residuePolynomial f = g₀ * h₀ →
    ∃! gh : A[X] × A[X], IsFactorizationLift f g₀ h₀ gh.1 gh.2

/-- A residue root is the linear factor `X-ā`. -/
theorem simple_residue_root_iff_linear_factor {A : Type*} [CommRing A] [IsLocalRing A]
    (f : A[X]) (a₀ : ResidueRing A) :
    (residuePolynomial f).eval a₀ = 0 ↔
      ∃ q : Polynomial (ResidueRing A),
        residuePolynomial f = (X - C a₀) * q := by
  constructor
  · intro hroot
    have hdvd : X - C a₀ ∣ residuePolynomial f := by
      rw [Polynomial.dvd_iff_isRoot]
      simpa [Polynomial.IsRoot] using hroot
    rcases hdvd with ⟨q, hq⟩
    exact ⟨q, hq⟩
  · rintro ⟨q, hq⟩
    have hdvd : X - C a₀ ∣ residuePolynomial f := ⟨q, hq⟩
    have hroot := (Polynomial.dvd_iff_isRoot.mp hdvd)
    simpa [Polynomial.IsRoot] using hroot

/-- Simple-residue-root lifting implies coprime factorization lifting. -/
theorem henselian_factorization_by_successive_linear_lifts
    {A : Type*} [CommRing A] [IsLocalRing A]
    (hroot : SimpleResidueRootLiftingProperty A) :
    HenselianFactorizationProperty A := by
  sorry

/-- Conversely, a factorization lift applied to `X-ā` gives simple-root lifting. -/
theorem simple_root_lifting_by_linear_factorization
    {A : Type*} [CommRing A] [IsLocalRing A]
    (hfactor : HenselianFactorizationProperty A) :
    SimpleResidueRootLiftingProperty A := by
  intro f a₀ hf hroot hsimple
  let g₀ : Polynomial (ResidueRing A) := X - C a₀
  let h₀ : Polynomial (ResidueRing A) := residuePolynomial f /ₘ g₀
  have hg₀ : g₀.Monic := by
    simpa [g₀] using monic_X_sub_C a₀
  have hred : residuePolynomial f = g₀ * h₀ := by
    simpa [g₀, h₀, modByMonic_X_sub_C_eq_C_eval, hroot] using
      (X_sub_C_mul_divByMonic_eq_sub_modByMonic (residuePolynomial f) a₀).symm
  have hcop : IsCoprime g₀ h₀ := by
    change IsCoprime (X - C a₀) (residuePolynomial f /ₘ (X - C a₀))
    have hsimple_ne : (residuePolynomial f).derivative.eval a₀ ≠ 0 :=
      hsimple.ne_zero
    exact isCoprime_of_is_root_of_eval_derivative_ne_zero
      (K := IsLocalRing.ResidueField A) (residuePolynomial f) a₀ hsimple_ne
  have hprodmonic : (g₀ * h₀).Monic := by
    rw [← hred]
    exact hf.map (residueMap A)
  have hh₀ : h₀.Monic := hg₀.of_mul_monic_left hprodmonic
  obtain ⟨gh, hgh, _⟩ := hfactor f g₀ h₀ hf hg₀ hh₀ hcop hred
  rcases hgh with ⟨hg, hh, hng, hnh, hrg, hrh, hfac⟩
  have hng' : gh.1.natDegree = 1 := by
    simpa [g₀] using hng
  let a : A := -gh.1.coeff 0
  have hpoly : gh.1 = X - C a := by
    rw [hg.eq_X_add_C hng']
    simp [a, sub_neg_eq_add]
  have hfa : f.eval a = 0 := by
    rw [hfac, eval_mul, hpoly]
    simp
  have hresa : residueClass a = a₀ := by
    have hcoeff := congrArg (fun P : Polynomial (ResidueRing A) => P.coeff 0) hrg
    simp [residuePolynomial, g₀] at hcoeff
    change residueMap A (-gh.1.coeff 0) = a₀
    rw [map_neg, hcoeff]
    simp
  obtain ⟨a₀', ha₀'⟩ := Ideal.Quotient.mk_surjective a₀
  have hunit : IsUnit (f.derivative.eval a₀') := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    change residueMap A (f.derivative.eval a₀') ≠ 0
    have hsimple' : (residuePolynomial f).derivative.eval a₀ ≠ 0 :=
      hsimple.ne_zero
    rw [← ha₀'] at hsimple'
    change ((f.map (residueMap A)).derivative).eval (residueMap A a₀') ≠ 0 at hsimple'
    rw [Polynomial.derivative_map, Polynomial.eval_map_apply] at hsimple'
    exact hsimple'
  have hca : CongruentModIdeal (IsLocalRing.maximalIdeal A) a a₀' := by
    unfold CongruentModIdeal
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change residueMap A (a - a₀') = 0
    have hres : residueMap A a = residueMap A a₀' := by
      calc
        residueMap A a = a₀ := by simpa [residueClass, residueMap] using hresa
        _ = residueMap A a₀' := ha₀'.symm
    rw [map_sub, hres]
    simp
  refine ⟨a, ⟨hfa, hresa⟩, ?_⟩
  intro b hb
  have hcb : CongruentModIdeal (IsLocalRing.maximalIdeal A) b a₀' := by
    unfold CongruentModIdeal
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change residueMap A (b - a₀') = 0
    have hres : residueMap A b = residueMap A a₀' := by
      calc
        residueMap A b = a₀ := by simpa [residueClass, residueMap] using hb.2
        _ = residueMap A a₀' := ha₀'.symm
    rw [map_sub, hres]
    simp
  have hunit_a : IsUnit (f.derivative.eval a) :=
    derivative_unit_on_residue_class f hca hunit
  have habmem : a - b ∈ IsLocalRing.maximalIdeal A := by
    unfold CongruentModIdeal at hca hcb
    have h := (IsLocalRing.maximalIdeal A).sub_mem hca hcb
    simpa [sub_eq_add_neg, add_assoc] using h
  have habunit : ¬ IsUnit (a - b) := by
    intro hab
    exact (notMem_maximalIdeal.mpr hab) habmem
  exact (IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub
    (f := f) (a := a) (b := b) hfa hb.1 habunit hunit_a).symm

/-- Mathlib's henselian local-ring property is equivalent to simple-root lifting. -/
theorem henselian_iff_simple_residue_root_lifting {A : Type*} [CommRing A]
    [IsLocalRing A] :
    IsHenselianLocalRingChapter09 A ↔ SimpleResidueRootLiftingProperty A := by
  constructor
  · intro hH
    change HenselianLocalRing A at hH
    intro f a₀ hf hroot hsimple
    obtain ⟨a₀', ha₀'⟩ := Ideal.Quotient.mk_surjective a₀
    have hfa : f.eval a₀' ∈ IsLocalRing.maximalIdeal A := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      change residueMap A (f.eval a₀') = 0
      have hroot' := hroot
      rw [← ha₀'] at hroot'
      change (f.map (residueMap A)).eval (residueMap A a₀') = 0 at hroot'
      rw [Polynomial.eval_map_apply] at hroot'
      exact hroot'
    have hunit : IsUnit (f.derivative.eval a₀') := by
      apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
      change residueMap A (f.derivative.eval a₀') ≠ 0
      have hsimple' : (residuePolynomial f).derivative.eval a₀ ≠ 0 :=
        hsimple.ne_zero
      rw [← ha₀'] at hsimple'
      change ((f.map (residueMap A)).derivative).eval (residueMap A a₀') ≠ 0 at hsimple'
      rw [Polynomial.derivative_map, Polynomial.eval_map_apply] at hsimple'
      exact hsimple'
    obtain ⟨a, ha, hres⟩ := hH.is_henselian f hf a₀' hfa hunit
    have hares : residueClass a = a₀ := by
      unfold residueClass residueMap
      rw [← ha₀']
      rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact hres
    refine ⟨a, ⟨ha, hares⟩, ?_⟩
    intro b hb
    have hbc : CongruentModIdeal (IsLocalRing.maximalIdeal A) b a₀' := by
      unfold CongruentModIdeal
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      change residueMap A (b - a₀') = 0
      have hresb : residueMap A b = residueMap A a₀' := by
        calc
          residueMap A b = a₀ := by simpa [residueClass, residueMap] using hb.2
          _ = residueMap A a₀' := ha₀'.symm
      rw [map_sub, hresb]
      simp
    have hca : CongruentModIdeal (IsLocalRing.maximalIdeal A) a a₀' := hres
    have hunit_a : IsUnit (f.derivative.eval a) :=
      derivative_unit_on_residue_class f hca hunit
    have habmem : a - b ∈ IsLocalRing.maximalIdeal A := by
      unfold CongruentModIdeal at hca hbc
      have h := (IsLocalRing.maximalIdeal A).sub_mem hca hbc
      simpa [sub_eq_add_neg, add_assoc] using h
    have habunit : ¬ IsUnit (a - b) := by
      intro hab
      exact (notMem_maximalIdeal.mpr hab) habmem
    exact (IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub
      (f := f) (a := a) (b := b) ha hb.1 habunit hunit_a).symm
  · intro hroot
    change HenselianLocalRing A
    refine { toIsLocalRing := inferInstance, is_henselian := ?_ }
    intro f hf a₀ hfa hunit
    have hroot' : (residuePolynomial f).eval (residueClass a₀) = 0 := by
      change (f.map (residueMap A)).eval (residueMap A a₀) = 0
      rw [Polynomial.eval_map_apply]
      change (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) (f.eval a₀) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hfa
    have hsimple : IsUnit ((residuePolynomial f).derivative.eval (residueClass a₀)) := by
      simpa only [residueClass, residuePolynomial, Polynomial.derivative_map,
        Polynomial.eval_map_apply] using hunit.map (residueMap A)
    obtain ⟨a, ha, _⟩ := hroot f (residueClass a₀) hf hroot' hsimple
    refine ⟨a, ha.1, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change residueMap A (a - a₀) = 0
    have hres : residueMap A a = residueMap A a₀ := by
      simpa only [residueClass] using ha.2
    rw [map_sub, hres]
    simp

/-- Factorization-form and simple-root henselianity agree for local rings. -/
theorem henselian_iff_factorization_lifting {A : Type*} [CommRing A]
    [IsLocalRing A] :
    IsHenselianLocalRingChapter09 A ↔ HenselianFactorizationProperty A := by
  constructor
  · intro hH
    exact henselian_factorization_by_successive_linear_lifts
      ((henselian_iff_simple_residue_root_lifting (A := A)).mp hH)
  · intro hfactor
    exact (henselian_iff_simple_residue_root_lifting (A := A)).mpr
      (simple_root_lifting_by_linear_factorization hfactor)

/-- Complete and separated maximal-ideal-adic local rings. -/
def IsMaximalIdealAdicallyCompleteSeparated (A : Type*) [CommRing A] [IsLocalRing A] : Prop :=
  IsAdicComplete (IsLocalRing.maximalIdeal A) A

/-- Completeness and separatedness imply henselianity. -/
theorem complete_separated_local_ring_is_henselian {A : Type*} [CommRing A]
    [IsLocalRing A] (hA : IsMaximalIdealAdicallyCompleteSeparated A) :
    IsHenselianLocalRingChapter09 A := by
  unfold IsMaximalIdealAdicallyCompleteSeparated at hA
  have hring : HenselianRing A (IsLocalRing.maximalIdeal A) :=
    @IsAdicComplete.henselianRing A _ (IsLocalRing.maximalIdeal A) hA
  let hH : HenselianLocalRing A :=
    { is_henselian := by
        intro f hf a₀ hfa hunit
        have hmap : IsUnit
            (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)
              (f.derivative.eval a₀)) :=
          IsUnit.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) hunit
        obtain ⟨a, ha, hres⟩ := hring.is_henselian f hf a₀ hfa hmap
        exact ⟨a, ha, hres⟩ }
  exact hH

/-- Complete DVRs are henselian. -/
theorem complete_DVR_is_henselian {A : Type*} [CommRing A] [IsDomain A]
    [CompleteDVR A] : IsHenselianLocalRingChapter09 A := by
  apply complete_separated_local_ring_is_henselian
  unfold IsMaximalIdealAdicallyCompleteSeparated
  infer_instance

/-- The algebraic property of being henselian without the topological completeness property. -/
def IsHenselianButNotComplete (A : Type*) [CommRing A] [IsLocalRing A] : Prop :=
  HenselianLocalRing A ∧ ¬ IsMaximalIdealAdicallyCompleteSeparated A

/-- A henselian DVR need not be complete; this records an actual example interface. -/
structure Chapter09HenselianNoncompleteDVRExample where
  A : Type*
  [commRing : CommRing A]
  [domain : IsDomain A]
  [dvr : IsDiscreteValuationRing A]
  henselian : IsHenselianLocalRingChapter09 A
  not_adically_complete : ¬ IsMaximalIdealAdicallyCompleteSeparated A

theorem henselian_DVR_need_not_be_complete
    : Nonempty Chapter09HenselianNoncompleteDVRExample.{u} := by
  sorry
/-- A minimal local interface for the henselization of a local ring. -/
def IsHenselizationOf {A H : Type*} [CommRing A] [IsLocalRing A]
    [CommRing H] [IsLocalRing H] [Algebra A H] : Prop :=
  HenselianLocalRing H ∧ IsLocalHom (algebraMap A H) ∧
    Function.Injective (algebraMap A H) ∧
    (∀ x : H, IsIntegral A x) ∧
    ∀ (B : Type*) [CommRing B] [IsLocalRing B] [Algebra A B]
      [HenselianLocalRing B],
      ∃! φ : H →+* B, IsLocalHom φ ∧ φ.comp (algebraMap A H) = algebraMap A B
/-- The universal-property part of henselization: maps to henselian local rings are unique. -/
def HasHenselizationUniversalProperty {A H : Type*} [CommRing A] [IsLocalRing A]
    [CommRing H] [IsLocalRing H] [Algebra A H] : Prop :=
  ∀ (B : Type*) [CommRing B] [IsLocalRing B] [Algebra A B]
    [HenselianLocalRing B],
    ∃! φ : H →+* B, IsLocalHom φ ∧ φ.comp (algebraMap A H) = algebraMap A B

/-- An adic completion interface, kept abstract so the chapter remains self-contained. -/
def IsAdicCompletionOf {A C : Type*} [CommRing A] [IsLocalRing A]
    [CommRing C] [Algebra A C] : Prop :=
  IsAdicComplete (IsLocalRing.maximalIdeal A) C ∧
    Function.Injective (algebraMap A C)
    ∧ ∀ (B : Type*) [CommRing B] [IsLocalRing B] [Algebra A B]
      [IsAdicComplete
        ((IsLocalRing.maximalIdeal A).map (algebraMap A B)) B],
      ∃! φ : C →+* B, IsLocalHom φ ∧ φ.comp (algebraMap A C) = algebraMap A B

/-- A strict embedding records that an algebraic henselization can be smaller than its completion. -/
def IsStrictRingEmbedding {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    (φ : R →+* S) : Prop :=
  Function.Injective φ ∧ ¬ Function.Surjective φ

/-- Henselization elements are algebraic over the original local ring. -/
theorem henselization_adds_algebraic_solutions {A H : Type*} [CommRing A] [IsLocalRing A]
    [CommRing H] [IsLocalRing H] [Algebra A H]
    (hH : IsHenselizationOf (A := A) (H := H)) :
    HenselianLocalRing H ∧ ∀ x : H, IsIntegral A x := by
  rcases hH with ⟨hHens, hlocal, hinj, hint, hUniversal⟩
  exact ⟨hHens, hint⟩

/-! ## 9.5 Worked lifts -/

/-- A unit has a square residue in `𝔽_p` when its residue is a square. -/
def PadicUnitResidueSquare (p : ℕ) [Fact p.Prime] (u : ℤ_[p]) : Prop :=
  IsUnit u ∧ ∃ z : ZMod p, z ^ 2 = PadicInt.toZMod u

/-- At odd `p`, the derivative of `X²-u` is a unit at every unit approximation. -/
theorem odd_padic_square_derivative_is_unit (p : ℕ) [Fact p.Prime]
    (hpodd : p ≠ 2) (a₀ : ℤ_[p]) (ha₀ : IsUnit a₀) :
    IsUnit ((2 : ℤ_[p]) * a₀) := by
  have hp2 : p.Coprime 2 := by
    apply (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr
    intro hdiv
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hdiv with h | h
    · exact (Fact.out : Nat.Prime p).ne_one h
    · exact hpodd h
  have htwo : IsUnit (2 : ℤ_[p]) := by
    apply PadicInt.isUnit_iff.mpr
    exact PadicInt.norm_natCast_eq_one_iff.mpr hp2
  exact htwo.mul ha₀

/-- For odd `p`, a p-adic unit is a square exactly when its residue is a square. -/
theorem odd_padic_unit_square_iff_residue_square (p : ℕ) [Fact p.Prime]
    (hpodd : p ≠ 2) (u : ℤ_[p]) (hu : IsUnit u) :
    (∃ a : ℤ_[p], a ^ 2 = u) ↔
      ∃ z : ZMod p, z ^ 2 = PadicInt.toZMod u := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨PadicInt.toZMod a, ?_⟩
    simpa only [map_pow] using congrArg (PadicInt.toZMod (p := p)) ha
  · rintro ⟨z, hz⟩
    obtain ⟨a₀, ha₀⟩ := ZMod.ringHom_surjective PadicInt.toZMod z
    have ha₀unit : IsUnit a₀ := by
      apply IsLocalRing.notMem_maximalIdeal.mp
      intro ha₀m
      have hz0 : z = 0 := by
        rw [← ha₀]
        rw [← RingHom.mem_ker, PadicInt.ker_toZMod]
        exact ha₀m
      have hu0 : PadicInt.toZMod u = 0 := by simpa [hz0] using hz.symm
      have hum : u ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
        rw [← PadicInt.ker_toZMod, RingHom.mem_ker]
        exact hu0
      exact (notMem_maximalIdeal.mpr hu) hum
    have hmem : a₀ ^ 2 - u ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
      rw [← PadicInt.ker_toZMod, RingHom.mem_ker]
      simp [map_sub, map_pow, ha₀, hz]
    have herr : ‖a₀ ^ 2 - u‖ < 1 := by
      rw [PadicInt.maximalIdeal_eq_span_p] at hmem
      rw [Ideal.mem_span_singleton] at hmem
      exact (PadicInt.norm_lt_one_iff_dvd _).mpr hmem
    have hder : IsUnit ((quadraticPolynomial u).derivative.eval a₀) := by
      have heval : (quadraticPolynomial u).derivative.eval a₀ =
          (2 : ℤ_[p]) * a₀ := by
        simp only [quadraticPolynomial, derivative_sub, derivative_X_pow,
          derivative_C, eval_mul, eval_C, eval_X, Nat.cast_ofNat,
          eval_pow, sub_zero]
        norm_num
      rw [heval]
      exact odd_padic_square_derivative_is_unit p hpodd a₀ ha₀unit
    have hnorm : ‖(quadraticPolynomial u).aeval a₀‖ <
        ‖(quadraticPolynomial u).derivative.aeval a₀‖ ^ 2 := by
      have hdernorm : ‖(quadraticPolynomial u).derivative.aeval a₀‖ = 1 := by
        simpa [aeval_def, eval₂_at_apply] using (PadicInt.isUnit_iff.mp hder)
      calc
        ‖(quadraticPolynomial u).aeval a₀‖ = ‖a₀ ^ 2 - u‖ := by
          simp [quadraticPolynomial, aeval_def]
        _ < 1 := herr
        _ = ‖(quadraticPolynomial u).derivative.aeval a₀‖ ^ 2 := by
          rw [hdernorm]
          norm_num
    obtain ⟨a, ha, -, -, -⟩ := hensels_lemma hnorm
    refine ⟨a, ?_⟩
    have ha' : a ^ 2 - u = 0 := by
      simpa [quadraticPolynomial, aeval_def, eval₂_at_apply] using ha
    exact sub_eq_zero.mp ha'

/-- A chosen square residue root has a unique p-adic square-root lift. -/
theorem odd_padic_square_simple_lift (p : ℕ) [Fact p.Prime]
    (hpodd : p ≠ 2) (u a₀ : ℤ_[p]) (hu : IsUnit u)
    (hroot : (PadicInt.toZMod a₀) ^ 2 = PadicInt.toZMod u) :
    ∃! a : ℤ_[p], a ^ 2 = u ∧ PadicInt.toZMod a = PadicInt.toZMod a₀ := by
  have ha₀unit : IsUnit a₀ := by
    apply IsLocalRing.notMem_maximalIdeal.mp
    intro ha₀m
    have hz0 : PadicInt.toZMod a₀ = 0 := by
      rw [← RingHom.mem_ker, PadicInt.ker_toZMod]
      exact ha₀m
    have hum : u ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
      rw [← PadicInt.ker_toZMod, RingHom.mem_ker]
      simpa [hz0] using hroot.symm
    exact (notMem_maximalIdeal.mpr hu) hum
  have hmem : a₀ ^ 2 - u ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker]
    simp [map_sub, map_pow, hroot]
  have herr : ‖a₀ ^ 2 - u‖ < 1 := by
    rw [PadicInt.maximalIdeal_eq_span_p] at hmem
    rw [Ideal.mem_span_singleton] at hmem
    exact (PadicInt.norm_lt_one_iff_dvd _).mpr hmem
  have hder : IsUnit ((quadraticPolynomial u).derivative.eval a₀) := by
    have heval : (quadraticPolynomial u).derivative.eval a₀ =
        (2 : ℤ_[p]) * a₀ := by
      simp only [quadraticPolynomial, derivative_sub, derivative_X_pow,
        derivative_C, eval_mul, eval_C, eval_X, Nat.cast_ofNat,
        eval_pow, sub_zero]
      norm_num
    rw [heval]
    exact odd_padic_square_derivative_is_unit p hpodd a₀ ha₀unit
  have hdernorm : ‖(quadraticPolynomial u).derivative.aeval a₀‖ = 1 := by
    simpa [aeval_def, eval₂_at_apply] using (PadicInt.isUnit_iff.mp hder)
  have hnorm : ‖(quadraticPolynomial u).aeval a₀‖ <
      ‖(quadraticPolynomial u).derivative.aeval a₀‖ ^ 2 := by
    calc
      ‖(quadraticPolynomial u).aeval a₀‖ = ‖a₀ ^ 2 - u‖ := by
        simp [quadraticPolynomial, aeval_def]
      _ < 1 := herr
      _ = ‖(quadraticPolynomial u).derivative.aeval a₀‖ ^ 2 := by
        rw [hdernorm]
        norm_num
  obtain ⟨z, hz, hzclose, hzder, hzuniq⟩ := hensels_lemma hnorm
  have hzroot : z ^ 2 = u := by
    have hz' : z ^ 2 - u = 0 := by
      simpa [quadraticPolynomial, aeval_def, eval₂_at_apply] using hz
    exact sub_eq_zero.mp hz'
  have hzclose' : ‖z - a₀‖ < 1 := by
    have hdernorm' : ‖(quadraticPolynomial u).derivative.eval a₀‖ = 1 :=
      PadicInt.isUnit_iff.mp hder
    simpa [aeval_def, eval₂_at_apply, hdernorm'] using hzclose
  have hzres : PadicInt.toZMod z = PadicInt.toZMod a₀ := by
    have hzm : z - a₀ ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
      rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]
      exact (PadicInt.norm_lt_one_iff_dvd _).mp hzclose'
    have hzero : PadicInt.toZMod (z - a₀) = 0 := by
      rw [← RingHom.mem_ker, PadicInt.ker_toZMod]
      exact hzm
    simpa [map_sub, sub_eq_zero] using hzero
  refine ⟨z, ⟨hzroot, hzres⟩, ?_⟩
  intro b hb
  have hbm : b - a₀ ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker]
    simp [map_sub, hb.2]
  have hbclose : ‖b - a₀‖ < 1 := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hbm
    exact (PadicInt.norm_lt_one_iff_dvd _).2 hbm
  have hbclose' : ‖b - a₀‖ <
      ‖(quadraticPolynomial u).derivative.aeval a₀‖ := by
    calc
      ‖b - a₀‖ < 1 := hbclose
      _ = ‖(quadraticPolynomial u).derivative.aeval a₀‖ := by
        rw [hdernorm]
  have hbeval : (quadraticPolynomial u).aeval b = 0 := by
    have hb' : b ^ 2 - u = 0 := sub_eq_zero.mpr hb.1
    simpa [quadraticPolynomial, aeval_def, eval₂_at_apply] using hb'
  exact hzuniq b hbeval hbclose'

/-- For odd `p`, the two residue roots give the two square roots overall. -/
theorem odd_padic_square_has_two_roots (p : ℕ) [Fact p.Prime]
    (hpodd : p ≠ 2) (u : ℤ_[p]) (hu : IsUnit u)
    (hres : ∃ z : ZMod p, z ^ 2 = PadicInt.toZMod u) :
    ∃ aPlus aMinus : ℤ_[p],
      aPlus ^ 2 = u ∧ aMinus ^ 2 = u ∧ aPlus ≠ aMinus ∧
        ∀ a : ℤ_[p], a ^ 2 = u → a = aPlus ∨ a = aMinus := by
  obtain ⟨z, hz⟩ := hres
  obtain ⟨a₀, ha₀⟩ := ZMod.ringHom_surjective PadicInt.toZMod z
  have hzroot : (PadicInt.toZMod a₀) ^ 2 = PadicInt.toZMod u := by
    simpa [ha₀] using hz
  obtain ⟨aPlus, hPlus, hPlusuniq⟩ :=
    odd_padic_square_simple_lift p hpodd u a₀ hu hzroot
  have hnegroot : (PadicInt.toZMod (-a₀)) ^ 2 = PadicInt.toZMod u := by
    simpa [map_neg, neg_sq] using hzroot
  obtain ⟨aMinus, hMinus, hMinusuniq⟩ :=
    odd_padic_square_simple_lift p hpodd u (-a₀) hu hnegroot
  have hzunit : IsUnit z := by
    apply isUnit_iff_ne_zero.mpr
    intro hz0
    have hu0 : PadicInt.toZMod u = 0 := by simpa [hz0] using hz.symm
    have hum : u ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
      rw [← PadicInt.ker_toZMod, RingHom.mem_ker]
      exact hu0
    exact (notMem_maximalIdeal.mpr hu) hum
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro htwo
    have hpdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp htwo
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hpdiv with h | h
    · exact (Fact.out : Nat.Prime p).ne_one h
    · exact hpodd h
  have hneq : aPlus ≠ aMinus := by
    intro heq
    have hresEq : z = -z := by
      calc
        z = PadicInt.toZMod aPlus := ha₀.symm.trans hPlus.2.symm
        _ = PadicInt.toZMod aMinus := by rw [heq]
        _ = -z := by simpa [ha₀] using hMinus.2
    have hzsum : (2 : ZMod p) * z = 0 := by
      calc
        (2 : ZMod p) * z = z + z := by ring
        _ = (-z) + z := congrArg (fun t : ZMod p => t + z) hresEq
        _ = 0 := neg_add_cancel z
    rcases mul_eq_zero.mp hzsum with h | h
    · exact htwo h
    · exact hzunit.ne_zero h
  refine ⟨aPlus, aMinus, hPlus.1, hMinus.1, hneq, ?_⟩
  intro a ha
  have hprod : (a - aPlus) * (a + aPlus) = 0 := by
    calc
      (a - aPlus) * (a + aPlus) = a ^ 2 - aPlus ^ 2 := by ring
      _ = u - u := by rw [ha, hPlus.1]
      _ = 0 := sub_self u
  rcases mul_eq_zero.mp hprod with hleft | hright
  · exact Or.inl (sub_eq_zero.mp hleft)
  · right
    have hminus_eq : aMinus = -aPlus := by
      exact (hMinusuniq (-aPlus) (by
        constructor
        · simp [hPlus.1]
        · simp [map_neg, hPlus.2])).symm
    rw [hminus_eq]
    exact eq_neg_of_add_eq_zero_left hright

/-- The polynomial and first approximation in the numerical `u=2` example over `ℤ₇`. -/
def padicSevenPolynomial : (ℤ_[7])[X] :=
  quadraticPolynomial (2 : ℤ_[7])

def padicSevenInitialApproximation : ℤ_[7] :=
  3

def padicSevenFirstNewtonApproximation : ℤ_[7] :=
  3 - (7 : ℤ_[7]) * Ring.inverse (6 : ℤ_[7])

/-- The first Newton approximation agrees with `3-7/6`. -/
theorem padicSeven_first_newton_formula :
    padicSevenFirstNewtonApproximation =
      newtonCorrection padicSevenPolynomial padicSevenInitialApproximation := by
  simp [padicSevenFirstNewtonApproximation, padicSevenPolynomial,
    padicSevenInitialApproximation, newtonCorrection, quadraticPolynomial]
  ring_nf

/-- The inverse of six modulo forty-nine is forty-one. -/
theorem inverse_six_mod_49 : (6 : ZMod 49) * 41 = 1 := by
  decide

/-- The first approximation is `10` modulo `49`. -/
theorem padicSeven_first_approximation_mod_49 :
    PadicInt.toZModPow 2 padicSevenFirstNewtonApproximation = (10 : ZMod (7 ^ 2)) := by
  have h6 : IsUnit (6 : ℤ_[7]) := by
    apply PadicInt.isUnit_iff.mpr
    exact PadicInt.norm_natCast_eq_one_iff.mpr (by norm_num)
  have hmapinv :
      PadicInt.toZModPow 2 (Ring.inverse (6 : ℤ_[7])) *
          PadicInt.toZModPow 2 (6 : ℤ_[7]) = 1 := by
    rw [← map_mul, Ring.inverse_mul_cancel _ h6, map_one]
  have h6mod : IsUnit (6 : ZMod (7 ^ 2)) := by
    apply (ZMod.isUnit_iff_coprime 6 (7 ^ 2)).mpr
    norm_num
  have hinvmod :
      PadicInt.toZModPow 2 (Ring.inverse (6 : ℤ_[7])) = (41 : ZMod (7 ^ 2)) := by
    apply h6mod.mul_right_cancel
    calc
      PadicInt.toZModPow 2 (Ring.inverse (6 : ℤ_[7])) * 6 = 1 := by
        have hmap6 : PadicInt.toZModPow 2 (6 : ℤ_[7]) =
            (6 : ZMod (7 ^ 2)) := by
          change PadicInt.toZModPow 2 ((6 : ℕ) : ℤ_[7]) =
            ((6 : ℕ) : ZMod (7 ^ 2))
          exact map_natCast (PadicInt.toZModPow 2) 6
        rw [hmap6] at hmapinv
        exact hmapinv
      _ = (41 : ZMod (7 ^ 2)) * 6 := by
        rw [mul_comm, inverse_six_mod_49]
  unfold padicSevenFirstNewtonApproximation
  rw [map_sub, map_mul, hinvmod]
  change PadicInt.toZModPow 2 (3 : ℤ_[7]) -
      PadicInt.toZModPow 2 (7 : ℤ_[7]) * 41 = (10 : ZMod (7 ^ 2))
  have hmap3 : PadicInt.toZModPow 2 (3 : ℤ_[7]) =
      (3 : ZMod (7 ^ 2)) := by
    change PadicInt.toZModPow 2 ((3 : ℕ) : ℤ_[7]) =
      ((3 : ℕ) : ZMod (7 ^ 2))
    exact map_natCast (PadicInt.toZModPow 2) 3
  have hmap7 : PadicInt.toZModPow 2 (7 : ℤ_[7]) =
      (7 : ZMod (7 ^ 2)) := by
    change PadicInt.toZModPow 2 ((7 : ℕ) : ℤ_[7]) =
      ((7 : ℕ) : ZMod (7 ^ 2))
    exact map_natCast (PadicInt.toZModPow 2) 7
  rw [hmap3, hmap7]
  decide

/-- Indeed `10²=2` modulo `49`. -/
theorem padicSeven_square_mod_49 :
    (10 : ZMod 49) ^ 2 = 2 := by
  decide

/-- The next Newton step has fourth-power precision, reflecting valuation doubling. -/
def padicSevenSecondNewtonApproximation : ℤ_[7] :=
  newtonCorrection padicSevenPolynomial padicSevenFirstNewtonApproximation

def IsRootModuloPower {A : Type*} [CommRing A] (π : A) (f : A[X]) (a : A) (n : ℕ) : Prop :=
  f.eval a ∈ Ideal.span ({π ^ n} : Set A)

/-- The second numerical correction determines the root modulo `7⁴`, not only `7³`. -/
theorem padicSeven_second_newton_precision :
    IsRootModuloPower (7 : ℤ_[7]) padicSevenPolynomial
      padicSevenSecondNewtonApproximation 4 := by
  let hDVR : CompleteDVR ℤ_[7] := {
    toIsDiscreteValuationRing := inferInstance
    isAdicComplete' := inferInstance
  }
  have h6 : IsUnit (6 : ℤ_[7]) := by
    apply PadicInt.isUnit_iff.mpr
    exact PadicInt.norm_natCast_eq_one_iff.mpr (by norm_num)
  have hinv : ‖(Ring.inverse (6 : ℤ_[7]))‖ = 1 := by
    apply PadicInt.isUnit_iff.mp
    exact isUnit_iff_exists_inv.mpr
      ⟨(6 : ℤ_[7]), Ring.inverse_mul_cancel 6 h6⟩
  have hcorr : ‖((7 : ℤ_[7]) * Ring.inverse (6 : ℤ_[7]))‖ < 1 := by
    rw [norm_mul, hinv, mul_one]
    exact PadicInt.norm_natCast_lt_one_iff.mpr (by norm_num)
  have ha₁unit : IsUnit padicSevenFirstNewtonApproximation := by
    apply PadicInt.isUnit_iff.mpr
    have hnorm :
        ‖(padicSevenFirstNewtonApproximation : ℚ_[7])‖ = ‖(3 : ℚ_[7])‖ := by
      apply Padic.norm_eq_of_norm_sub_lt_right
      change ‖((padicSevenFirstNewtonApproximation - 3 : ℤ_[7]) : ℚ_[7])‖ <
        ‖(3 : ℚ_[7])‖
      rw [show padicSevenFirstNewtonApproximation - 3 =
          -((7 : ℤ_[7]) * Ring.inverse (6 : ℤ_[7])) by
        change (3 - (7 : ℤ_[7]) * Ring.inverse (6 : ℤ_[7])) - 3 =
          -((7 : ℤ_[7]) * Ring.inverse (6 : ℤ_[7]))
        ring]
      change ‖-((7 : ℤ_[7]) * Ring.inverse (6 : ℤ_[7]))‖ <
        ‖(3 : ℚ_[7])‖
      rw [norm_neg]
      have h3 : ‖(3 : ℚ_[7])‖ = 1 := by
        exact Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
      exact lt_of_lt_of_le hcorr h3.ge
    change ‖(padicSevenFirstNewtonApproximation : ℚ_[7])‖ = 1
    rw [hnorm]
    have h3 : ‖(3 : ℚ_[7])‖ = 1 := by
      exact Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
    exact h3
  have hderiv : IsUnit
      (padicSevenPolynomial.derivative.eval padicSevenFirstNewtonApproximation) := by
    have heval : padicSevenPolynomial.derivative.eval
        padicSevenFirstNewtonApproximation =
        (2 : ℤ_[7]) * padicSevenFirstNewtonApproximation := by
      simp [padicSevenPolynomial, quadraticPolynomial]
      norm_num
    rw [heval]
    exact odd_padic_square_derivative_is_unit 7 (by norm_num)
      padicSevenFirstNewtonApproximation ha₁unit
  have hroot₂ : padicSevenPolynomial.eval padicSevenFirstNewtonApproximation ∈
      (IsLocalRing.maximalIdeal ℤ_[7]) ^ 2 := by
    have hroot₂' : padicSevenPolynomial.eval padicSevenFirstNewtonApproximation ∈
        Ideal.span ({(7 : ℤ_[7]) ^ 2} : Set ℤ_[7]) := by
      rw [show padicSevenPolynomial.eval padicSevenFirstNewtonApproximation =
          padicSevenFirstNewtonApproximation ^ 2 - (2 : ℤ_[7]) by
        simp [padicSevenPolynomial, quadraticPolynomial]]
      have hmem : padicSevenFirstNewtonApproximation ^ 2 - (2 : ℤ_[7]) ∈
          RingHom.ker (PadicInt.toZModPow 2 : ℤ_[7] →+* ZMod (7 ^ 2)) := by
        rw [RingHom.mem_ker]
        rw [map_sub, map_pow, padicSeven_first_approximation_mod_49,
          padicSeven_square_mod_49]
        rw [show PadicInt.toZModPow 2 (2 : ℤ_[7]) =
            (2 : ZMod (7 ^ 2)) by
          exact map_natCast (PadicInt.toZModPow 2) 2]
        norm_num
      rw [PadicInt.ker_toZModPow] at hmem
      simpa only [Nat.cast_ofNat] using hmem
    simpa [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow] using hroot₂'
  have hroot₄ := @newton_precision_doubles ℤ_[7] _ _ hDVR padicSevenPolynomial
    padicSevenFirstNewtonApproximation 2 hderiv hroot₂
  simpa [IsRootModuloPower, padicSevenSecondNewtonApproximation,
    PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow] using hroot₄

/-- At `p=2`, the derivative of `X²-u` is never a unit at a unit. -/
theorem two_adic_square_derivative_never_unit (a : ℤ_[2]) (ha : IsUnit a) :
    ¬ IsUnit ((2 : ℤ_[2]) * a) := by
  have _ha := ha
  rw [PadicInt.not_isUnit_iff]
  calc
    ‖(2 : ℤ_[2]) * a‖ = ‖(2 : ℤ_[2])‖ * ‖a‖ := norm_mul _ _
    _ ≤ ‖(2 : ℤ_[2])‖ * 1 :=
      mul_le_mul_of_nonneg_left (PadicInt.norm_le_one a) (norm_nonneg _)
    _ = ‖(2 : ℤ_[2])‖ := by simp
    _ < 1 := by
      simpa only [Nat.cast_ofNat] using
        (PadicInt.norm_natCast_lt_one_iff (p := 2) (n := 2)).mpr (dvd_refl 2)

/-- Being congruent to one modulo eight is the strengthened two-adic Newton condition. -/
theorem two_adic_one_mod_eight_gives_newton_condition (u : ℤ_[2])
    (hu : PadicInt.toZModPow 3 u = 1) :
    Padic.addValuation (p := 2) (1 - (u : ℚ_[2])) ≥ (3 : WithTop ℤ) ∧
      Padic.addValuation (p := 2) (2 : ℚ_[2]) = (1 : WithTop ℤ) ∧
      Padic.addValuation (p := 2) (1 - (u : ℚ_[2])) >
      Padic.addValuation (p := 2) (2 : ℚ_[2]) +
          Padic.addValuation (p := 2) (2 : ℚ_[2]) := by
  have hmem : 1 - u ∈ Ideal.span ({(2 : ℤ_[2]) ^ 3} : Set ℤ_[2]) := by
    change 1 - u ∈ Ideal.span ({((2 : ℕ) : ℤ_[2]) ^ 3} : Set ℤ_[2])
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker]
    simp [hu]
  have hv : Padic.addValuation (p := 2) (1 - (u : ℚ_[2])) ≥
      (3 : WithTop ℤ) := by
    have hcoe : ((1 - u : ℤ_[2]) : ℚ_[2]) = 1 - (u : ℚ_[2]) := by
      norm_num
    by_cases hz : 1 - u = 0
    · rw [← hcoe, hz]
      simp
    · rw [← hcoe, Padic.addValuation.apply (PadicInt.coe_ne_zero.mpr hz),
      PadicInt.valuation_coe]
      have hle := (PadicInt.mem_span_pow_iff_le_valuation
        (1 - u) hz 3).mp hmem
      change (3 : WithTop ℤ) ≤ (PadicInt.valuation (1 - u) : WithTop ℤ)
      exact_mod_cast hle
  have htwo : Padic.addValuation (p := 2) (2 : ℚ_[2]) =
      (1 : WithTop ℤ) := by
    rw [Padic.addValuation.apply (by norm_num), Padic.valuation_ofNat]
    norm_num
  refine ⟨hv, htwo, ?_⟩
  rw [htwo]
  calc
    (2 : WithTop ℤ) < 3 := by exact_mod_cast (show (2 : ℤ) < 3 by norm_num)
    _ ≤ Padic.addValuation (p := 2) (1 - (u : ℚ_[2])) := hv

/-- Every `2`-adic integer congruent to one modulo eight is a square. -/
theorem two_adic_unit_square_of_one_mod_eight (u : ℤ_[2])
    (hu : PadicInt.toZModPow 3 u = 1) :
    ∃ a : ℤ_[2], a ^ 2 = u := by
  have hmem : 1 - u ∈ Ideal.span ({(2 : ℤ_[2]) ^ 3} : Set ℤ_[2]) := by
    change 1 - u ∈ Ideal.span ({((2 : ℕ) : ℤ_[2]) ^ 3} : Set ℤ_[2])
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker]
    simp [hu]
  have hnormerr : ‖1 - u‖ ≤ (2 : ℝ) ^ (-3 : ℤ) := by
    exact (PadicInt.norm_le_pow_iff_mem_span_pow (1 - u) 3).mpr hmem
  have hnormtwo : ‖(2 : ℤ_[2])‖ = (2 : ℝ) ^ (-1 : ℤ) := by
    rw [PadicInt.norm_eq_zpow_neg_valuation (by norm_num)]
    have hval : PadicInt.valuation (2 : ℤ_[2]) = 1 := PadicInt.valuation_p
    rw [hval]
    norm_num
  have hnorm : ‖(quadraticPolynomial u).aeval (1 : ℤ_[2])‖ <
      ‖(quadraticPolynomial u).derivative.aeval (1 : ℤ_[2])‖ ^ 2 := by
    calc
      ‖(quadraticPolynomial u).aeval (1 : ℤ_[2])‖ = ‖1 - u‖ := by
        simp [quadraticPolynomial, aeval_def]
      _ ≤ (2 : ℝ) ^ (-3 : ℤ) := hnormerr
      _ < ((2 : ℝ) ^ (-1 : ℤ)) ^ 2 := by norm_num
      _ = ‖(quadraticPolynomial u).derivative.aeval (1 : ℤ_[2])‖ ^ 2 := by
        have hderiv :
            (quadraticPolynomial u).derivative.aeval (1 : ℤ_[2]) =
              (2 : ℤ_[2]) := by
          simp [quadraticPolynomial, aeval_def]
          norm_num
        rw [hderiv, hnormtwo]
  obtain ⟨a, ha, -, -, -⟩ := hensels_lemma hnorm
  refine ⟨a, ?_⟩
  have ha' : a ^ 2 - u = 0 := by
    simpa [quadraticPolynomial, aeval_def, eval₂_at_apply] using ha
  exact sub_eq_zero.mp ha'

/-- The polynomial and first Newton iterate in the `u=17` two-adic example. -/
def padicTwoSeventeenPolynomial : (ℚ_[2])[X] :=
  quadraticPolynomial (17 : ℚ_[2])

def padicTwoSeventeenFirstNewtonApproximation : ℚ_[2] :=
  1 - ((-16 : ℚ_[2]) / (2 : ℚ_[2]))

/-- For `f=X²-17`, the initial error and derivative have values four and one. -/
theorem padicTwoSeventeen_initial_values :
    Padic.addValuation (p := 2) (padicTwoSeventeenPolynomial.eval 1) = (4 : WithTop ℤ) ∧
      Padic.addValuation (p := 2)
          (padicTwoSeventeenPolynomial.derivative.eval 1) = (1 : WithTop ℤ) := by
  constructor
  · norm_num [padicTwoSeventeenPolynomial, quadraticPolynomial,
      Padic.addValuation, AddValuation.of_apply, Padic.addValuationDef,
      Padic.valuation_intCast]
    have hpv : padicValNat 2 16 = 4 := by
      convert padicValNat_base_pow (p := 2) (by norm_num) 4 using 1
    exact_mod_cast hpv
  · norm_num [padicTwoSeventeenPolynomial, quadraticPolynomial,
      Padic.addValuation, AddValuation.of_apply, Padic.addValuationDef,
      Padic.valuation_intCast]

/-- The first Newton iterate is nine, and its new error is sixty-four of value six. -/
theorem padicTwoSeventeen_first_iterate_and_error :
    padicTwoSeventeenFirstNewtonApproximation = 9 ∧
      padicTwoSeventeenPolynomial.eval padicTwoSeventeenFirstNewtonApproximation = 64 ∧
      Padic.addValuation (p := 2)
          (padicTwoSeventeenPolynomial.eval padicTwoSeventeenFirstNewtonApproximation) =
        (6 : WithTop ℤ) := by
  constructor
  · norm_num [padicTwoSeventeenFirstNewtonApproximation, div_eq_mul_inv]
  constructor
  · norm_num [padicTwoSeventeenFirstNewtonApproximation, padicTwoSeventeenPolynomial,
      quadraticPolynomial, div_eq_mul_inv]
  · norm_num [padicTwoSeventeenFirstNewtonApproximation, padicTwoSeventeenPolynomial,
      quadraticPolynomial, div_eq_mul_inv, Padic.addValuation,
      AddValuation.of_apply, Padic.addValuationDef, Padic.valuation_intCast]
    have hpv : padicValNat 2 64 = 6 := by
      convert padicValNat_base_pow (p := 2) (by norm_num) 6 using 1
    exact_mod_cast hpv

/-- The lifted root has displacement of value three from one, matching the first correction. -/
theorem padicTwoSeventeen_lifted_root_displacement
    : ∃ a : ℚ_[2], padicTwoSeventeenPolynomial.eval a = 0 ∧
      Padic.addValuation (p := 2) (a - 1) = (3 : WithTop ℤ) := by
  let F : (ℤ_[2])[X] := quadraticPolynomial (17 : ℤ_[2])
  have hF : F.aeval (1 : ℤ_[2]) = (-16 : ℤ_[2]) := by
    norm_num [F, quadraticPolynomial, Polynomial.aeval_def, eval₂_at_apply]
  have hFd : F.derivative.aeval (1 : ℤ_[2]) = (2 : ℤ_[2]) := by
    norm_num [F, quadraticPolynomial, Polynomial.aeval_def, eval₂_at_apply]
  have hnorm : ‖F.aeval (1 : ℤ_[2])‖ <
      ‖F.derivative.aeval (1 : ℤ_[2])‖ ^ 2 := by
    rw [hF, hFd]
    have h16 : (16 : ℤ_[2]) = (2 : ℤ_[2]) ^ 4 := by norm_num
    rw [norm_neg, h16, norm_pow]
    have hnorm2 : ‖(2 : ℤ_[2])‖ = (2 : ℝ)⁻¹ := PadicInt.norm_p
    rw [hnorm2]
    norm_num
  obtain ⟨z, hz, hzclose, _, _⟩ :=
    hensels_lemma (p := 2) (F := F) (a := (1 : ℤ_[2])) hnorm
  let a : ℚ_[2] := z
  have ha : padicTwoSeventeenPolynomial.eval a = 0 := by
    have hz' := congrArg (fun x : ℤ_[2] => (x : ℚ_[2])) hz
    have hz'' : (z : ℚ_[2]) ^ 2 - ((17 : ℤ_[2]) : ℚ_[2]) = 0 := by
      simpa [F, quadraticPolynomial, Polynomial.aeval_def, eval₂_at_apply] using hz'
    have h17 : ((17 : ℤ_[2]) : ℚ_[2]) = (17 : ℚ_[2]) := by
      exact PadicInt.coe_natCast 17
    rw [h17] at hz''
    simpa [a, padicTwoSeventeenPolynomial, quadraticPolynomial,
      Polynomial.aeval_def, eval₂_at_apply] using hz''
  have hclose : ‖(z - 1 : ℤ_[2])‖ < (2 : ℝ) ^ (-1 : ℤ) := by
    calc
      ‖(z - 1 : ℤ_[2])‖ < ‖F.derivative.aeval (1 : ℤ_[2])‖ := hzclose
      _ = (2 : ℝ) ^ (-1 : ℤ) := by
        rw [hFd]
        have hnorm2 : ‖(2 : ℤ_[2])‖ = (2 : ℝ)⁻¹ := PadicInt.norm_p
        rw [hnorm2]
        norm_num
  have hzsub : z - 1 ≠ 0 := by
    intro hzsub
    have : z = 1 := sub_eq_zero.mp hzsub
    rw [this] at hz
    norm_num [F, quadraticPolynomial, Polynomial.aeval_def, eval₂_at_apply] at hz
  have hnormle : ‖(z - 1 : ℤ_[2])‖ ≤ (2 : ℝ) ^ (-2 : ℤ) := by
    exact (PadicInt.norm_lt_pow_iff_norm_le_pow_sub_one (z - 1) (-1)).mp hclose
  have hzval : (2 : ℕ) ≤ (z - 1).valuation := by
    exact (PadicInt.norm_le_pow_iff_le_valuation (z - 1) hzsub 2).mp hnormle
  have hcast_sub : ((z - 1 : ℤ_[2]) : ℚ_[2]) = a - 1 := by
    simp [a]
  have hval_sub_cast :
      Padic.addValuation (p := 2) (a - 1) =
        (((z - 1).valuation : ℤ) : WithTop ℤ) := by
    rw [← hcast_sub, Padic.addValuation.apply (PadicInt.coe_ne_zero.mpr hzsub),
      PadicInt.valuation_coe]
  have hvalgt : Padic.addValuation (p := 2) (a - 1) > (1 : WithTop ℤ) := by
    rw [hval_sub_cast]
    exact_mod_cast (show (1 : ℕ) < (z - 1).valuation by omega)
  have hfactor : (a - 1) * (a + 1) = (16 : ℚ_[2]) := by
    have ha' : a ^ 2 - (17 : ℚ_[2]) = 0 := by
      simpa [padicTwoSeventeenPolynomial, quadraticPolynomial,
        Polynomial.eval₂_at_apply] using ha
    have ha_sq : a ^ 2 = (17 : ℚ_[2]) := sub_eq_zero.mp ha'
    calc
      (a - 1) * (a + 1) = a ^ 2 - 1 := by ring
      _ = (17 : ℚ_[2]) - 1 := by rw [ha_sq]
      _ = 16 := by norm_num
  have hval_a_sub : Padic.addValuation (p := 2) (a - 1) ≠ ⊤ := by
    rw [hval_sub_cast]
    exact WithTop.coe_ne_top
  have hzadd : z + 1 ≠ 0 := by
    intro hzadd
    have hzneg : z = -1 := eq_neg_of_add_eq_zero_left hzadd
    rw [hzneg] at hz
    norm_num [F, quadraticPolynomial, Polynomial.aeval_def, eval₂_at_apply] at hz
  have hcast_add : ((z + 1 : ℤ_[2]) : ℚ_[2]) = a + 1 := by
    simp [a]
  have hval_add_cast :
      Padic.addValuation (p := 2) (a + 1) =
        (((z + 1).valuation : ℤ) : WithTop ℤ) := by
    rw [← hcast_add, Padic.addValuation.apply (PadicInt.coe_ne_zero.mpr hzadd),
      PadicInt.valuation_coe]
  have hval_a_add : Padic.addValuation (p := 2) (a + 1) ≠ ⊤ := by
    rw [hval_add_cast]
    exact WithTop.coe_ne_top
  have hval_a_add_eq : Padic.addValuation (p := 2) (a + 1) = (1 : WithTop ℤ) := by
    have hneq : Padic.addValuation (p := 2) (a - 1) ≠
        Padic.addValuation (p := 2) 2 := by
      have htwo : Padic.addValuation (p := 2) (2 : ℚ_[2]) = (1 : WithTop ℤ) := by
        have hp : Padic.valuation (2 : ℚ_[2]) = 1 := by
          exact Padic.valuation_p (p := 2)
        rw [Padic.addValuation.apply (by norm_num), hp]
        norm_num
      rw [hval_sub_cast, htwo]
      exact_mod_cast (show (z - 1).valuation ≠ 1 by omega)
    have hadd := (Padic.addValuation (p := 2)).map_add_of_distinct_val hneq
    have htwo : Padic.addValuation (p := 2) (2 : ℚ_[2]) = (1 : WithTop ℤ) := by
      have hp : Padic.valuation (2 : ℚ_[2]) = 1 := by
        exact Padic.valuation_p (p := 2)
      rw [Padic.addValuation.apply (by norm_num), hp]
      norm_num
    calc
      Padic.addValuation (p := 2) (a + 1) =
          Padic.addValuation (p := 2) ((a - 1) + 2) := by
            congr 1 ; ring
      _ = min (Padic.addValuation (p := 2) (a - 1))
          (Padic.addValuation (p := 2) 2) := hadd
      _ = Padic.addValuation (p := 2) 2 :=
        min_eq_right (by rw [htwo]; exact le_of_lt hvalgt)
      _ = (1 : WithTop ℤ) := htwo
  have hsum : Padic.addValuation (p := 2) (a - 1) +
      Padic.addValuation (p := 2) (a + 1) =
        Padic.addValuation (p := 2) (16 : ℚ_[2]) := by
    calc
      Padic.addValuation (p := 2) (a - 1) +
          Padic.addValuation (p := 2) (a + 1) =
          Padic.addValuation (p := 2) ((a - 1) * (a + 1)) := by
            rw [(Padic.addValuation (p := 2)).map_mul]
      _ = Padic.addValuation (p := 2) (16 : ℚ_[2]) :=
        congrArg (Padic.addValuation (p := 2)) hfactor
  have hval16 : Padic.addValuation (p := 2) (16 : ℚ_[2]) = (4 : WithTop ℤ) := by
    norm_num [Padic.addValuation, AddValuation.of_apply, Padic.addValuationDef,
      Padic.valuation_intCast]
    have hpv : padicValNat 2 16 = 4 := by
      convert padicValNat_base_pow (p := 2) (by norm_num) 4 using 1
    exact_mod_cast hpv
  rw [hval16] at hsum
  have hval_a_sub_eq : Padic.addValuation (p := 2) (a - 1) = (3 : WithTop ℤ) := by
    rw [hval_sub_cast, hval_a_add_eq] at hsum
    have hsum_int : ((z - 1).valuation : ℤ) + 1 = 4 := by
      apply WithTop.coe_injective
      simpa using hsum
    have hzval3 : (z - 1).valuation = 3 := by
      exact_mod_cast (by omega : ((z - 1).valuation : ℤ) = 3)
    rw [hval_sub_cast, hzval3]
    norm_num
  exact ⟨a, ha, hval_a_sub_eq⟩

/-- The Artin--Schreier polynomial `X^p-X-a`. -/
def artinSchreierPolynomial {A : Type*} [CommRing A] (p : ℕ) (a : A) : A[X] :=
  X ^ p - X - C a

/-- The Artin--Schreier polynomial is monic for positive residue characteristic. -/
theorem artinSchreierPolynomial_monic {A : Type*} [CommRing A] [Nontrivial A]
    (p : ℕ) (hp : 1 < p) (a : A) :
    (artinSchreierPolynomial p a).Monic := by
  have hdeg : (X + C a : A[X]).degree < p := by
    rw [degree_X_add_C]
    exact_mod_cast hp
  simpa [artinSchreierPolynomial, sub_eq_add_neg, add_assoc, add_left_comm,
    add_comm] using
    (monic_X_pow_sub (p := X + C a) hdeg)

/-- In residue characteristic `p`, the derivative of `X^p-X-a` is a unit. -/
theorem artinSchreier_derivative_is_unit {A : Type*} [CommRing A] [IsLocalRing A]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueRing A) p] (a x : A) :
    IsUnit ((artinSchreierPolynomial p a).derivative.eval x) := by
  have hpmax : (p : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change (p : ResidueRing A) = 0
    exact CharP.cast_eq_zero (ResidueRing A) p
  have hplus :
      (artinSchreierPolynomial p a).derivative.eval x + 1 ∈
        IsLocalRing.maximalIdeal A := by
    have hmul := (IsLocalRing.maximalIdeal A).mul_mem_left
      (x ^ (p - 1)) hpmax
    have hcalc :
        (artinSchreierPolynomial p a).derivative.eval x + 1 =
          (p : A) * x ^ (p - 1) := by
      simp [artinSchreierPolynomial, derivative_sub, derivative_pow]
    rw [hcalc]
    simpa [mul_comm] using hmul
  rw [← notMem_maximalIdeal]
  intro hder
  have hone := (IsLocalRing.maximalIdeal A).sub_mem hplus hder
  simp [sub_eq_add_neg, add_assoc] at hone

/-- Every residue root of `X^p-X-a` lifts uniquely over a complete DVR. -/
theorem artinSchreier_every_residue_root_lifts {A : Type*} [CommRing A] [IsDomain A]
    [CompleteDVR A] (p : ℕ) [Fact p.Prime] [CharP (ResidueRing A) p]
    (a : A) (x₀ : ResidueRing A)
    (hroot : (residuePolynomial (artinSchreierPolynomial p a)).eval x₀ = 0) :
    ∃! x : A,
      (artinSchreierPolynomial p a).eval x = 0 ∧ residueClass x = x₀ := by
  obtain ⟨x₀lift, hx₀lift⟩ := Ideal.Quotient.mk_surjective x₀
  let F := artinSchreierPolynomial p a
  have hfa : F.eval x₀lift ∈ IsLocalRing.maximalIdeal A := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change residueMap A (F.eval x₀lift) = 0
    rw [← hx₀lift] at hroot
    change (residuePolynomial F).eval (residueMap A x₀lift) = 0 at hroot
    simpa only [residuePolynomial, Polynomial.eval_map_apply] using hroot
  have hunit : IsUnit (F.derivative.eval x₀lift) := by
    exact artinSchreier_derivative_is_unit p a x₀lift
  obtain ⟨x, hx, hcx⟩ := hensel_simple_root F x₀lift hfa hunit
  refine ⟨x, ?_, ?_⟩
  · constructor
    · simpa [F] using hx.1
    · unfold residueClass
      rw [← hx₀lift]
      unfold residueMap
      rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact hx.2
  · intro y hy
    have hyF : F.eval y = 0 := by simpa [F] using hy.1
    have hyq : residueMap A y = residueMap A x₀lift := by
      calc
        residueMap A y = x₀ := hy.2
        _ = residueMap A x₀lift := hx₀lift.symm
    have hym : y - x₀lift ∈ IsLocalRing.maximalIdeal A := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      change residueMap A (y - x₀lift) = 0
      rw [map_sub, hyq]
      simp
    exact hcx y ⟨hyF, hym⟩

/-- The Artin--Schreier calculation is the simple-root, unramified-style lifting test. -/
theorem artinSchreier_simple_root_separates_unramified_behavior {A : Type*}
    [CommRing A] [IsLocalRing A] (p : ℕ) [Fact p.Prime]
    [CharP (ResidueRing A) p] (a x : A) :
    IsUnit ((artinSchreierPolynomial p a).derivative.eval x) := by
  exact artinSchreier_derivative_is_unit p a x

/-! ## 9.6 Algebraic consequences -/

/-- A polynomial has a repeated residue root when it and its derivative vanish there. -/
def HasRepeatedResidueRoot {R : Type*} [CommRing R] (f : R[X]) : Prop :=
  ∃ a : R, f.eval a = 0 ∧ f.derivative.eval a = 0

/-- Coefficients of a polynomial are integral over a base ring. -/
def PolynomialCoefficientsIntegralOver {A K : Type*} [CommRing A] [CommRing K]
    [Algebra A K] (f : K[X]) : Prop :=
  ∀ n : ℕ, IsIntegral A (f.coeff n)

/-- A monic factor of a monic polynomial over a fraction field has integral coefficients. -/
theorem monic_factor_coefficients_are_integral {A K : Type*} [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K]
    (f : A[X]) (g h : K[X]) (hf : f.Monic) (hg : g.Monic) (hh : h.Monic)
    (hfac : Polynomial.map (algebraMap A K) f = g * h) :
    PolynomialCoefficientsIntegralOver (A := A) (K := K) g ∧ PolynomialCoefficientsIntegralOver (A := A) (K := K) h := by
  constructor
  · intro n
    apply Polynomial.isIntegral_coeff_of_dvd f g hf hg
    exact ⟨h, hfac⟩
  · intro n
    apply Polynomial.isIntegral_coeff_of_dvd f h hf hh
    refine ⟨g, ?_⟩
    rw [mul_comm]
    exact hfac

/-- Integral closedness descends a monic factorization from the fraction field to the DVR. -/
theorem monic_factorization_descends_to_integrally_closed_domain
    {A K : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (f : A[X]) (g h : K[X]) (hf : f.Monic) (hg : g.Monic) (hh : h.Monic)
    (hfac : Polynomial.map (algebraMap A K) f = g * h) :
    ∃ gA hA : A[X],
      gA.Monic ∧ hA.Monic ∧
        Polynomial.map (algebraMap A K) gA = g ∧
        Polynomial.map (algebraMap A K) hA = h ∧ f = gA * hA := by
  have hgdiv : g ∣ Polynomial.map (algebraMap A K) f := ⟨h, hfac⟩
  have hhdiv : h ∣ Polynomial.map (algebraMap A K) f := by
    refine ⟨g, ?_⟩
    rw [mul_comm]
    exact hfac
  obtain ⟨gA, hgA⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K hf hgdiv
  obtain ⟨hA, hhA⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K hf hhdiv
  have hmapg : Polynomial.map (algebraMap A K) gA = g := by
    simpa [hg.leadingCoeff] using hgA
  have hmaph : Polynomial.map (algebraMap A K) hA = h := by
    simpa [hh.leadingCoeff] using hhA
  have hmonicg : gA.Monic := by
    apply Polynomial.monic_of_injective (IsFractionRing.injective A K)
    simpa [hmapg] using hg
  have hmonich : hA.Monic := by
    apply Polynomial.monic_of_injective (IsFractionRing.injective A K)
    simpa [hmaph] using hh
  refine ⟨gA, hA, hmonicg, hmonich, hmapg, hmaph, ?_⟩
  apply Polynomial.map_injective (algebraMap A K) (IsFractionRing.injective A K)
  simpa [Polynomial.map_mul, hmapg, hmaph] using hfac

/-- A monic polynomial with irreducible reduction is irreducible over the fraction field. -/
theorem irreducible_of_irreducible_residue_reduction
    {A K : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K]
    (f : A[X]) (hf : f.Monic)
    (hred : Irreducible (residuePolynomial f)) :
    Irreducible (Polynomial.map (algebraMap A K) f) := by
  have hfa : Irreducible f := by
    apply Polynomial.Monic.irreducible_of_irreducible_map
      (residueMap A) f hf
    simpa [residuePolynomial] using hred
  exact (hf.irreducible_iff_irreducible_map_fraction_map).mp hfa

/-- The converse fails: an irreducible polynomial can acquire a repeated reduction. -/
theorem padic_x_sq_sub_p_irreducible_but_reduction_repeated (p : ℕ) [Fact p.Prime] :
    Irreducible
        (Polynomial.map (algebraMap (ℤ_[p]) (ℚ_[p]))
          (quadraticPolynomial (p : ℤ_[p]))) ∧
      HasRepeatedResidueRoot (quadraticPolynomial (p : ZMod p)) := by
  constructor
  · apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
      (p := Polynomial.map (algebraMap (ℤ_[p]) (ℚ_[p]))
        (quadraticPolynomial (p : ℤ_[p])))
      (by
        have hnd :
            (Polynomial.map (algebraMap (ℤ_[p]) (ℚ_[p]))
              (quadraticPolynomial (p : ℤ_[p]))).natDegree = 2 := by
          simp only [quadraticPolynomial, Polynomial.map_sub, Polynomial.map_pow,
            Polynomial.map_C, Polynomial.map_X]
          rw [natDegree_sub_C, natDegree_X_pow]
        rw [hnd]
        norm_num)
    intro x hx
    apply padic_x_sq_sub_p_has_no_root p
    refine ⟨x, ?_⟩
    have hx' : x ^ 2 = (p : ℚ_[p]) := by
      apply sub_eq_zero.mp
      simpa [quadraticPolynomial] using hx
    exact hx'
  · refine ⟨0, ?_, ?_⟩
    · simp [quadraticPolynomial]
    · simp [quadraticPolynomial]

/-- Henselianity is the hypothesis needed to lift a coprime residue factorization. -/
theorem henselianity_lifts_coprime_residue_factorization
    {A : Type*} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    (f : A[X]) (g₀ h₀ : Polynomial (ResidueRing A))
    (hf : f.Monic) (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hcop : IsCoprime g₀ h₀) (hred : residuePolynomial f = g₀ * h₀) :
    ∃! gh : A[X] × A[X], IsFactorizationLift f g₀ h₀ gh.1 gh.2 := by
  have hsimple : SimpleResidueRootLiftingProperty A :=
    (henselian_iff_simple_residue_root_lifting (A := A)).mp
      (show IsHenselianLocalRingChapter09 A from by
        change HenselianLocalRing A
        exact inferInstance)
  exact (henselian_factorization_by_successive_linear_lifts hsimple)
    f g₀ h₀ hf hg₀ hh₀ hcop hred

/-- A prime of an extension ring lying above the maximal ideal. -/
def PrimeAboveMaximal {A B : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [Algebra A B] (P : Ideal B) : Prop :=
  P.IsPrime ∧ P.comap (algebraMap A B) = IsLocalRing.maximalIdeal A

/-- A valuation on `L` extends the valuation on `K` up to Mathlib's equivalence relation. -/
def IsValuationExtension {K L ΓK ΓL : Type*} [Field K] [Field L]
    [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL]
    [Algebra K L]
    (vK : Valuation K ΓK) (vL : Valuation L ΓL) : Prop :=
  vK.IsEquiv (vL.comap (algebraMap K L))

/- A valuation extension may require a genuinely larger ordered value group. -/
structure Chapter09ValuationExtension
    {K : Type uK} {L : Type uL} {ΓK : Type uΓ} [Field K] [Field L]
    [LinearOrderedCommGroupWithZero ΓK] [Algebra K L]
    (vK : Valuation K ΓK) where
  ΓL : Type (max (max uK uL) uΓ)
  [valueGroup : LinearOrderedCommGroupWithZero ΓL]
  valuation : Valuation L ΓL
  isExtension : IsValuationExtension vK valuation

def Chapter09ValuationExtensionEquivalent
    {K L ΓK : Type*} [Field K] [Field L]
    [LinearOrderedCommGroupWithZero ΓK] [Algebra K L]
    (vK : Valuation K ΓK)
    (w₁ w₂ : Chapter09ValuationExtension (L := L) vK) : Prop := by
  letI := w₁.valueGroup
  letI := w₂.valueGroup
  exact w₁.valuation.IsEquiv w₂.valuation

def Chapter09ValuationExtensionSetoid
    {K L ΓK : Type*} [Field K] [Field L]
    [LinearOrderedCommGroupWithZero ΓK] [Algebra K L]
    (vK : Valuation K ΓK) : Setoid (Chapter09ValuationExtension (L := L) vK) where
  r := Chapter09ValuationExtensionEquivalent (L := L) vK
  iseqv := by
    constructor
    · intro w
      unfold Chapter09ValuationExtensionEquivalent
      exact fun _ _ => Iff.rfl
    · intro w₁ w₂ h
      unfold Chapter09ValuationExtensionEquivalent at h ⊢
      exact fun x y => Iff.symm (h x y)
    · intro w₁ w₂ w₃ h₁₂ h₂₃
      unfold Chapter09ValuationExtensionEquivalent at h₁₂ h₂₃ ⊢
      exact fun x y => Iff.trans (h₁₂ x y) (h₂₃ x y)

abbrev Chapter09ValuationExtensionClass
    {K L ΓK : Type*} [Field K] [Field L]
    [LinearOrderedCommGroupWithZero ΓK] [Algebra K L]
    (vK : Valuation K ΓK) : Type _ :=
  Quotient (Chapter09ValuationExtensionSetoid (L := L) vK)
/-- The prime/valuation correspondence, expressed as an equivalence of the two parameter spaces. -/
def ExtensionPrimeCorrespondence {A B K L ΓK : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [Algebra A B] [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK] (vK : Valuation K ΓK) : Prop :=
  Nonempty
    ((Chapter09ValuationExtensionClass (L := L) vK ≃
        {P : Ideal B // PrimeAboveMaximal (A := A) (B := B) P}))

/-- There is exactly one extension valuation in the chosen value group. -/
def HasUniqueValuationExtension {K L ΓK : Type*} [Field K] [Field L]
    [LinearOrderedCommGroupWithZero ΓK] [Algebra K L]
    (vK : Valuation K ΓK) : Prop :=
  ∃ w : Chapter09ValuationExtension (L := L) vK,
    ∀ w' : Chapter09ValuationExtension (L := L) vK,
      Chapter09ValuationExtensionEquivalent (L := L) vK w w'

/-- There is exactly one prime of the extension ring above the maximal ideal. -/
def HasUniquePrimeAbove {A B : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [Algebra A B] : Prop :=
  ∃! P : Ideal B, PrimeAboveMaximal (A := A) (B := B) P

/-- A valued field is henselian when its valuation ring is a henselian local ring. -/
def IsHenselianValuedField {K Γ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (vK : Valuation K Γ) : Prop :=
  HenselianLocalRing vK.valuationSubring

/-- For a finite extension, primes above the maximal ideal correspond to valuation extensions.
The base ring is required to be the ring of integers of the chosen valuation. -/
theorem finite_extension_prime_valuation_correspondence
    {A B K L Γ : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]
    [ValuationRing A] [IsIntegrallyClosed A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra A L] [IsScalarTower A K L]
    [CommRing B] [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L]
    [LinearOrderedCommGroupWithZero Γ] (vK : Valuation K Γ)
    (hA : vK.Integers A) :
    ExtensionPrimeCorrespondence (A := A) (B := B) (L := L) vK := by
  sorry

/-- The correspondence transfers uniqueness of a prime to uniqueness of the extension valuation. -/
theorem unique_prime_iff_unique_valuation_extension
    {A B K L Γ : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [Algebra A B] [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ] (vK : Valuation K Γ)
    (hcor : ExtensionPrimeCorrespondence (A := A) (B := B) (L := L) vK) :
    (HasUniquePrimeAbove (A := A) (B := B) ↔
      HasUniqueValuationExtension (L := L) vK) := by
  obtain ⟨e⟩ := hcor
  constructor
  · rintro ⟨P, hP, hPuniq⟩
    let y₀ : {P : Ideal B // PrimeAboveMaximal (A := A) (B := B) P} := ⟨P, hP⟩
    obtain ⟨q₀, hq₀⟩ := e.surjective y₀
    obtain ⟨w₀, hw₀⟩ := Quotient.exists_rep q₀
    have hy₀ : e (Quotient.mk (Chapter09ValuationExtensionSetoid (L := L) vK) w₀) = y₀ := by
      exact (congrArg e hw₀).trans hq₀
    refine ⟨w₀, ?_⟩
    intro w
    have hy :
        e (Quotient.mk (Chapter09ValuationExtensionSetoid (L := L) vK) w) =
          e (Quotient.mk (Chapter09ValuationExtensionSetoid (L := L) vK) w₀) := by
      apply Subtype.ext
      exact (hPuniq _ (e (Quotient.mk (Chapter09ValuationExtensionSetoid (L := L) vK) w)).property).trans
        (hPuniq _ (e (Quotient.mk (Chapter09ValuationExtensionSetoid (L := L) vK) w₀)).property).symm
    have hq :
        Quotient.mk (Chapter09ValuationExtensionSetoid (L := L) vK) w =
          Quotient.mk (Chapter09ValuationExtensionSetoid (L := L) vK) w₀ := e.injective hy
    have hrel : Chapter09ValuationExtensionEquivalent (L := L) vK w₀ w := by
      exact (Chapter09ValuationExtensionSetoid (L := L) vK).iseqv.symm
        (Quotient.exact hq)
    exact hrel
  · rintro ⟨w₀, hw₀⟩
    let y₀ := e (Quotient.mk (Chapter09ValuationExtensionSetoid (L := L) vK) w₀)
    refine ⟨y₀.1, y₀.2, ?_⟩
    intro P hP
    let y : {P : Ideal B // PrimeAboveMaximal (A := A) (B := B) P} := ⟨P, hP⟩
    obtain ⟨q, hq⟩ := e.surjective y
    obtain ⟨w, hw⟩ := Quotient.exists_rep q
    have hrel := hw₀ w
    have hqeq :
        Quotient.mk (Chapter09ValuationExtensionSetoid (L := L) vK) w₀ =
          Quotient.mk (Chapter09ValuationExtensionSetoid (L := L) vK) w := by
      exact Quotient.sound hrel
    have hy :
        y₀ = e (Quotient.mk (Chapter09ValuationExtensionSetoid (L := L) vK) w) :=
      congrArg e hqeq
    have hwy :
        e (Quotient.mk (Chapter09ValuationExtensionSetoid (L := L) vK) w) = y :=
      (congrArg e hw).trans hq
    have hyy : y₀ = y := hy.trans hwy
    exact congrArg Subtype.val hyy.symm

/-- A henselian valued field has one prime above the maximal ideal in every finite extension.
The base ring is required to be the ring of integers of the chosen valuation. -/
theorem henselian_valued_field_has_unique_prime_and_extension
    {A B K L Γ : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]
    [ValuationRing A] [IsIntegrallyClosed A]
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra A K] [IsFractionRing A K]
    [CommRing B] [Algebra A B] [Algebra B L]
    [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [IsIntegralClosure B A L]
    [LinearOrderedCommGroupWithZero Γ] (vK : Valuation K Γ)
    (hA : vK.Integers A)
    (hH : IsHenselianValuedField vK) :
    HasUniquePrimeAbove (A := A) (B := B) ∧ HasUniqueValuationExtension (L := L) vK := by
  sorry

/-- The finite integral extension has a finite nonempty set of primes above the maximal ideal. -/
theorem finite_extension_primes_above_are_finite
    {A B : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]
    [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B]
    [IsIntegralClosure B A B] [FaithfulSMul A B] :
    Set.Finite {P : Ideal B | PrimeAboveMaximal (A := A) (B := B) P} ∧
      Nonempty {P : Ideal B // PrimeAboveMaximal (A := A) (B := B) P} := by
  let m : Ideal A := IsLocalRing.maximalIdeal A
  have heq : {P : Ideal B | PrimeAboveMaximal (A := A) (B := B) P} =
      m.primesOver B := by
    ext P
    constructor
    · rintro ⟨hprime, hcomap⟩
      exact ⟨hprime, ⟨hcomap.symm⟩⟩
    · rintro ⟨hprime, hover⟩
      exact ⟨hprime, hover.over.symm⟩
  constructor
  · rw [heq]
    exact Algebra.QuasiFinite.finite_primesOver m
  · obtain ⟨P, hPmax, hPover⟩ :=
      exists_maximal_ideal_liesOver_of_isIntegral (S := B) m
    refine ⟨⟨P, ?_⟩⟩
    exact ⟨hPmax.isPrime, hPover.over.symm⟩

/-- A complete rank-one valued field has a henselian valuation ring. -/
theorem complete_valued_field_is_henselian
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ)
    [Valuation.RankOne vK]
    (hcomplete : @CompleteSpace K (Valued.mk' vK).toUniformSpace) :
    IsHenselianValuedField vK := by
  change HenselianLocalRing vK.valuationSubring
  let v : AddValuation K (Additive Γ)ᵒᵈ := Valuation.toAddValuation vK
  have hv_equiv : vK.IsEquiv v.toValuation := by
    rw [Valuation.isEquiv_iff_val_le_one]
    intro x
    rfl
  let hrank : Valuation.RankOne v.toValuation :=
    { hom' := (Valuation.RankOne.hom vK).comp
        hv_equiv.orderMonoidIso.symm.toMonoidWithZeroHom
      strictMono' := (Valuation.RankOne.strictMono vK).comp
        hv_equiv.orderMonoidIso.symm.strictMono
      exists_val_nontrivial := by
        obtain ⟨r, hr0, hr1⟩ := Valuation.RankOne.nontrivial vK
        refine ⟨r, ?_, ?_⟩
        · intro hr
          exact hr0 ((hv_equiv.eq_zero).mpr hr)
        · intro hr
          exact hr1 ((hv_equiv.eq_one_iff_eq_one).mpr hr) }
  have hA : IsValuationSubring vK.valuationSubring.toSubring v := by
    intro x
    change x ∈ vK.valuationSubring ↔ v x ≥ 0
    rw [Valuation.mem_valuationSubring_iff]
    rfl
  have hcomplete' : Chapter09NonarchimedeanComplete v := by
    have hforward : @UniformContinuous K K
        (Valued.mk' vK).toUniformSpace (Valued.mk' v.toValuation).toUniformSpace
        (id : K → K) := hv_equiv.symm.uniformContinuous
    have hback : @UniformContinuous K K
        (Valued.mk' v.toValuation).toUniformSpace (Valued.mk' vK).toUniformSpace
        (id : K → K) := hv_equiv.uniformContinuous
    have hind : @IsUniformInducing K K
        (Valued.mk' vK).toUniformSpace (Valued.mk' v.toValuation).toUniformSpace
        (id : K → K) :=
      @IsUniformInducing.of_comp K K K
        (Valued.mk' vK).toUniformSpace
        (Valued.mk' v.toValuation).toUniformSpace
        (Valued.mk' vK).toUniformSpace
        (id : K → K) (id : K → K) hforward hback
        (@IsUniformInducing.id K (Valued.mk' vK).toUniformSpace)
    have hc : @CompleteSpace K (Valued.mk' v.toValuation).toUniformSpace :=
      (@IsUniformInducing.completeSpace_congr K K
        (Valued.mk' vK).toUniformSpace (Valued.mk' v.toValuation).toUniformSpace
        (id : K → K) hind (Function.surjective_id)).mp hcomplete
    exact hc
  refine { is_henselian := ?_ }
  intro f hf a₀ hfa hunit
  let fK : K[X] := f.map (Subring.subtype vK.valuationSubring.toSubring)
  have hfK : fK.Monic := by
    exact hf.map (Subring.subtype vK.valuationSubring.toSubring)
  have hfcoeff : PolynomialCoefficientsInSubring
      vK.valuationSubring.toSubring fK := by
    intro n
    change (f.map (Subring.subtype vK.valuationSubring.toSubring)).coeff n ∈
      vK.valuationSubring.toSubring
    rw [Polynomial.coeff_map]
    exact (f.coeff n).property
  have hfa_eval : fK.eval (a₀ : K) = ((f.eval a₀ : vK.valuationSubring) : K) := by
    change (f.map (Subring.subtype vK.valuationSubring.toSubring)).eval
        ((Subring.subtype vK.valuationSubring.toSubring) a₀) =
      (Subring.subtype vK.valuationSubring.toSubring) (f.eval a₀)
    exact Polynomial.eval_map_apply
      (Subring.subtype vK.valuationSubring.toSubring) a₀
  have hderiv_eval : fK.derivative.eval (a₀ : K) =
      ((f.derivative.eval a₀ : vK.valuationSubring) : K) := by
    rw [show fK.derivative =
        f.derivative.map (Subring.subtype vK.valuationSubring.toSubring) by
      simp [fK]]
    change (f.derivative.map (Subring.subtype vK.valuationSubring.toSubring)).eval
        ((Subring.subtype vK.valuationSubring.toSubring) a₀) =
      (Subring.subtype vK.valuationSubring.toSubring) (f.derivative.eval a₀)
    exact Polynomial.eval_map_apply
      (Subring.subtype vK.valuationSubring.toSubring) a₀
  have hfa_val : v (fK.eval (a₀ : K)) > 0 := by
    have hlt : vK ((f.eval a₀ : vK.valuationSubring) : K) < 1 :=
      (Valuation.mem_maximalIdeal_iff (v := vK)).mp hfa
    rw [hfa_eval]
    change 0 < OrderDual.toDual
      (Additive.ofMul (vK ((f.eval a₀ : vK.valuationSubring) : K)))
    exact hlt
  have hderiv_val : v ((f.derivative.eval a₀ : vK.valuationSubring) : K) = 0 := by
    obtain ⟨u, hu⟩ := isUnit_iff_exists_inv.mp hunit
    have hmul : ((f.derivative.eval a₀ : vK.valuationSubring) : K) * (u : K) = 1 := by
      exact congrArg (fun z : vK.valuationSubring => (z : K)) hu
    have hnonneg : 0 ≤ v ((f.derivative.eval a₀ : vK.valuationSubring) : K) :=
      (hA _).mp (f.derivative.eval a₀).property
    have hunonneg : 0 ≤ v (u : K) := (hA _).mp u.property
    have hsum : v ((f.derivative.eval a₀ : vK.valuationSubring) : K) + v (u : K) = 0 := by
      rw [← v.map_mul, hmul, v.map_one]
    apply le_antisymm
    · calc
        v ((f.derivative.eval a₀ : vK.valuationSubring) : K) =
            v ((f.derivative.eval a₀ : vK.valuationSubring) : K) + 0 := by simp
        _ ≤ v ((f.derivative.eval a₀ : vK.valuationSubring) : K) + v (u : K) :=
          add_le_add (le_refl _) hunonneg
        _ = 0 := hsum
    · exact hnonneg
  have hineq : v (fK.eval (a₀ : K)) >
      v (fK.derivative.eval (a₀ : K)) + v (fK.derivative.eval (a₀ : K)) := by
    have hderivK_val : v (fK.derivative.eval (a₀ : K)) = 0 := by
      rw [hderiv_eval, hderiv_val]
    rw [hfa_eval, hderivK_val]
    have hfa_val' := hfa_val
    rw [hfa_eval] at hfa_val'
    simpa only [add_zero] using hfa_val'
  obtain ⟨a, ha, _⟩ := @hensel_newton_form K (Additive Γ)ᵒᵈ _ _ v hrank
    vK.valuationSubring.toSubring hA fK hfcoeff (a₀ : K) a₀.property hineq hcomplete'
  have hroot := ha.1
  have hstrict := ha.2.1
  have hderivK_val : v (fK.derivative.eval (a₀ : K)) = 0 := by
    rw [hderiv_eval, hderiv_val]
  have ha_val : v a ≥ 0 := by
    have hdiff : v (a - (a₀ : K)) ≥ 0 :=
      le_of_lt (by simpa [hderivK_val] using hstrict)
    have hsum := valuation_strong_triangle v (a - (a₀ : K)) (a₀ : K)
    have hmin : 0 ≤ min (v (a - (a₀ : K))) (v (a₀ : K)) :=
      le_min hdiff ((hA _).mp a₀.property)
    exact hmin.trans (by simpa [sub_add_cancel] using hsum)
  let a' : vK.valuationSubring := ⟨a, (hA _).mpr ha_val⟩
  refine ⟨a', ?_, ?_⟩
  · apply Subtype.ext
    change ((f.eval a' : vK.valuationSubring) : K) = 0
    have heval : fK.eval (a : K) =
        ((f.eval a' : vK.valuationSubring) : K) := by
      change (f.map (Subring.subtype vK.valuationSubring.toSubring)).eval
          ((Subring.subtype vK.valuationSubring.toSubring) a') =
        (Subring.subtype vK.valuationSubring.toSubring) (f.eval a')
      exact Polynomial.eval_map_apply
        (Subring.subtype vK.valuationSubring.toSubring) a'
    rw [← heval]
    exact hroot
  · rw [Valuation.mem_maximalIdeal_iff]
    have hdiff : v (a - (a₀ : K)) > 0 := by
      simpa [hderivK_val] using hstrict
    have hdiffK : vK (a - (a₀ : K)) < 1 := by
      change 0 < OrderDual.toDual (Additive.ofMul (vK (a - (a₀ : K)))) at hdiff
      exact hdiff
    simpa [a'] using hdiffK

end
end Chapter09
end LastLib.Book01ValuationsDVRsAndCompletions
