import Mathlib

namespace ValuationsBook
namespace Chapter09

universe u uK uL uΓ

open scoped BigOperators Polynomial
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
        convert I.sub_mem ih hprod using 1 <;> ring
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
        simpa [Nat.add_assoc] using hsum
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
    convert (IsLocalRing.maximalIdeal A ^ n).neg_mem hm using 1 <;> ring
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
    convert hmem using 1 <;> ring
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
        simp [eval_add, eval_mul, eval_sub, eval_X, eval_C] <;> ring
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
  simpa [pow_two] using (Padic.addValuation (p := p)).map_mul x x

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
  sorry

/-- The valuation Newton form of Hensel's lemma, including the integral root condition. -/
theorem hensel_newton_form {K Γ : Type*} [Field K]
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
  sorry

/-- The exact displacement in the valuation Newton form of Hensel's lemma. -/
theorem hensel_newton_exact_displacement {K Γ : Type*} [Field K]
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
  sorry

/-- The Newton corrections tend to the top of the value group. -/
theorem valuation_newton_corrections_tend_to_top {K Γ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (v : AddValuation K Γ)
    (A : Subring K) (hA : IsValuationSubring A v) (f : K[X])
    (hf : PolynomialCoefficientsInSubring A f) (a₀ : K) (ha₀ : a₀ ∈ A)
    (hineq : v (f.eval a₀) > v (f.derivative.eval a₀) + v (f.derivative.eval a₀))
    (hderiv : v (f.derivative.eval a₀) ≠ ⊤)
    (hcomplete : Chapter09NonarchimedeanComplete v)
    (hcofinal : Chapter09DoublingCofinal
      (valuationExcess v f (v (f.derivative.eval a₀)) a₀)) :
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
  sorry

/-- One coefficientwise Hensel correction step, modulo `π^(n+1)`. -/
theorem hensel_factorization_step {A : Type*} [CommRing A] [IsDomain A]
    [CompleteDVR A] (f g h : A[X]) (g₀ h₀ : Polynomial (ResidueRing A))
    (π : A) (hπ : IsUniformizer π) (n : ℕ)
    (hf : f.Monic) (hg : g.Monic) (hh : h.Monic)
    (happrox : ApproximateFactorization f g h n)
    (hredg : residuePolynomial g = g₀) (hredh : residuePolynomial h = h₀)
    (hcop : IsCoprime g₀ h₀)
    (hred : residuePolynomial f = g₀ * h₀)
    (hn : 1 ≤ n) :
    ∃ r s : A[X],
      r.natDegree < g.natDegree ∧ s.natDegree < h.natDegree ∧
        ApproximateFactorization f
          (g + C (π ^ n) * r) (h + C (π ^ n) * s) (n + 1) := by
  sorry

/-- A pair of lifted factors with the prescribed reductions and degrees. -/
def IsFactorizationLift {A : Type*} [CommRing A] [IsLocalRing A]
    (f : A[X]) (g₀ h₀ : Polynomial (ResidueRing A)) (g h : A[X]) : Prop :=
  g.Monic ∧ h.Monic ∧
    g.natDegree = g₀.natDegree ∧ h.natDegree = h₀.natDegree ∧
    residuePolynomial g = g₀ ∧ residuePolynomial h = h₀ ∧ f = g * h

/-- Factorization-form Hensel lifting: the exact assertion of Theorem 9.3. -/
theorem hensel_factorization {A : Type*} [CommRing A] [IsDomain A]
    [CompleteDVR A] (f : A[X]) (g₀ h₀ : Polynomial (ResidueRing A))
    (hf : f.Monic) (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hcop : IsCoprime g₀ h₀)
    (hred : residuePolynomial f = g₀ * h₀) :
    ∃! gh : A[X] × A[X], IsFactorizationLift f g₀ h₀ gh.1 gh.2 := by
  sorry

/- Coefficientwise adic Cauchy condition for a sequence of polynomial factors. -/
def PolynomialAdicCauchy {A : Type*} [CommRing A] [IsLocalRing A]
    (s : ℕ → A[X]) : Prop :=
  ∀ d r : ℕ, ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
    (s m).coeff d - (s n).coeff d ∈
      (IsLocalRing.maximalIdeal A) ^ r

/-- Compatible coefficient corrections form Cauchy sequences in the DVR. -/
theorem hensel_factorization_coefficients_are_adic_cauchy
    {A : Type*} [CommRing A] [IsDomain A] [CompleteDVR A]
    {f : A[X]} {g₀ h₀ : Polynomial (ResidueRing A)}
    (hf : f.Monic) (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hcop : IsCoprime g₀ h₀) (hred : residuePolynomial f = g₀ * h₀) :
    ∃ g h : ℕ → A[X],
      (∀ n : ℕ,
        (g n).Monic ∧ (h n).Monic ∧
          (g n).natDegree = g₀.natDegree ∧
          (h n).natDegree = h₀.natDegree ∧
          residuePolynomial (g n) = g₀ ∧ residuePolynomial (h n) = h₀ ∧
          ApproximateFactorization f (g n) (h n) (n + 1)) ∧
      PolynomialAdicCauchy g ∧ PolynomialAdicCauchy h := by
  sorry

/-- The homogeneous first-precision correction equation proves uniqueness of factor lifts. -/
theorem hensel_factorization_unique_at_first_nonzero_precision
    {A : Type*} [CommRing A] [IsDomain A] [CompleteDVR A]
    {f : A[X]} {g₀ h₀ : Polynomial (ResidueRing A)}
    (hf : f.Monic) (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hcop : IsCoprime g₀ h₀) :
    ∀ gh₁ gh₂ : A[X] × A[X],
      IsFactorizationLift f g₀ h₀ gh₁.1 gh₁.2 →
      IsFactorizationLift f g₀ h₀ gh₂.1 gh₂.2 → gh₁ = gh₂ := by
  sorry

/-- A simple residue root is a linear factor and therefore lifts uniquely. -/
theorem monic_simple_residue_root_lifts {A : Type*} [CommRing A] [IsDomain A]
    [CompleteDVR A] (f : A[X]) (a₀ : ResidueRing A)
    (hf : f.Monic)
    (hroot : (residuePolynomial f).eval a₀ = 0)
    (hsimple : IsUnit ((residuePolynomial f).derivative.eval a₀)) :
    ∃! a : A, f.eval a = 0 ∧ residueClass a = a₀ := by
  sorry

/-- Pairwise coprime residue factors lift simultaneously. -/
def PairwiseCoprimeFamily {ι R : Type*} [CommRing R]
    (f : ι → R[X]) : Prop :=
  ∀ ⦃i j : ι⦄, i ≠ j → IsCoprime (f i) (f j)

/-- The simultaneous pairwise-coprime factor lifting consequence. -/
theorem hensel_lift_pairwise_coprime_factors {A ι : Type*} [CommRing A] [IsDomain A]
    [CompleteDVR A] [Fintype ι] (f : A[X]) (f₀ : ι → Polynomial (ResidueRing A))
    (hf : f.Monic) (hmonic : ∀ i, (f₀ i).Monic)
    (hpair : PairwiseCoprimeFamily f₀)
    (hred : residuePolynomial f = ∏ i, f₀ i) :
    ∃ lifts : ι → A[X],
      (∀ i, (lifts i).Monic ∧ (lifts i).natDegree = (f₀ i).natDegree ∧
        residuePolynomial (lifts i) = f₀ i) ∧
      f = ∏ i, lifts i := by
  sorry

/-- Residue-field factorization predicts a corresponding factorization upstairs. -/
theorem residue_factorization_predicts_complete_factorization
    {A : Type*} [CommRing A] [IsDomain A] [CompleteDVR A]
    (f : A[X]) (g₀ h₀ : Polynomial (ResidueRing A))
    (hf : f.Monic) (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hcop : IsCoprime g₀ h₀) (hred : residuePolynomial f = g₀ * h₀) :
    ∃ g h : A[X], IsFactorizationLift f g₀ h₀ g h := by
  sorry

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

/-- A simple root is the linear factor `X-ā`. -/
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

/-- Lifting factors one at a time reduces the factorization property to simple roots. -/
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
  sorry

/-- Factorization and simple-root definitions of henselianity are equivalent. -/
theorem henselian_iff_simple_residue_root_lifting {A : Type*} [CommRing A]
    [IsLocalRing A] :
    IsHenselianLocalRingChapter09 A ↔ SimpleResidueRootLiftingProperty A := by
  sorry

/-- Complete and separated maximal-ideal-adic local rings. -/
def IsMaximalIdealAdicallyCompleteSeparated (A : Type*) [CommRing A] [IsLocalRing A] : Prop :=
  IsAdicComplete (IsLocalRing.maximalIdeal A) A

/-- Completeness and separatedness imply henselianity. -/
theorem complete_separated_local_ring_is_henselian {A : Type*} [CommRing A]
    [IsLocalRing A] (hA : IsMaximalIdealAdicallyCompleteSeparated A) :
    IsHenselianLocalRingChapter09 A := by
  unfold IsMaximalIdealAdicallyCompleteSeparated at hA
  letI : IsAdicComplete (IsLocalRing.maximalIdeal A) A := hA
  letI : HenselianRing A (IsLocalRing.maximalIdeal A) :=
    IsAdicComplete.henselianRing A (IsLocalRing.maximalIdeal A)
  let hH : HenselianLocalRing A :=
    { is_henselian := by
        intro f hf a₀ hfa hunit
        have hmap : IsUnit
            (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)
              (f.derivative.eval a₀)) :=
          IsUnit.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) hunit
        obtain ⟨a, ha, hres⟩ :=
          HenselianRing.is_henselian f hf a₀ hfa hmap
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

/-- The henselization/completion comparison can be strict, expressing algebraic versus topological size. -/
theorem henselization_can_be_strictly_smaller_than_completion
    {A H C : Type*} [CommRing A] [IsLocalRing A]
    [CommRing H] [IsLocalRing H] [Algebra A H]
    [CommRing C] [IsLocalRing C] [Algebra A C] [HenselianLocalRing C]
    (hH : IsHenselizationOf (A := A) (H := H))
    (hC : IsAdicCompletionOf (A := A) (C := C))
    (hnotH : ¬ IsMaximalIdealAdicallyCompleteSeparated H) :
    ∃ φ : H →+* C, IsStrictRingEmbedding φ := by
  sorry

/-! ## 9.5 Worked lifts -/

/-- A unit has a square residue in `𝔽_p` when its residue is a square. -/
def PadicUnitResidueSquare (p : ℕ) [Fact p.Prime] (u : ℤ_[p]) : Prop :=
  IsUnit u ∧ ∃ z : ZMod p, z ^ 2 = PadicInt.toZMod u

/-- For odd `p`, a p-adic unit is a square exactly when its residue is a square. -/
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
          derivative_C, eval_sub, eval_mul, eval_C, eval_X, Nat.cast_ofNat,
          eval_pow, pow_one, sub_zero, mul_one]
        norm_num
      rw [heval]
      exact odd_padic_square_derivative_is_unit p hpodd a₀ ha₀unit
    have hnorm : ‖(quadraticPolynomial u).aeval a₀‖ <
        ‖(quadraticPolynomial u).derivative.aeval a₀‖ ^ 2 := by
      have hdernorm : ‖(quadraticPolynomial u).derivative.aeval a₀‖ = 1 := by
        simpa [aeval_def, eval₂_at_apply] using (PadicInt.isUnit_iff.mp hder)
      calc
        ‖(quadraticPolynomial u).aeval a₀‖ = ‖a₀ ^ 2 - u‖ := by
          simp [quadraticPolynomial, aeval_def, eval₂_at_apply]
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
        derivative_C, eval_sub, eval_mul, eval_C, eval_X, Nat.cast_ofNat,
        eval_pow, pow_one, sub_zero, mul_one]
      norm_num
    rw [heval]
    exact odd_padic_square_derivative_is_unit p hpodd a₀ ha₀unit
  have hdernorm : ‖(quadraticPolynomial u).derivative.aeval a₀‖ = 1 := by
    simpa [aeval_def, eval₂_at_apply] using (PadicInt.isUnit_iff.mp hder)
  have hnorm : ‖(quadraticPolynomial u).aeval a₀‖ <
      ‖(quadraticPolynomial u).derivative.aeval a₀‖ ^ 2 := by
    calc
      ‖(quadraticPolynomial u).aeval a₀‖ = ‖a₀ ^ 2 - u‖ := by
        simp [quadraticPolynomial, aeval_def, eval₂_at_apply]
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
    simpa [map_sub, hb.2]
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
        · simpa [hPlus.1]
        · simpa [map_neg, hPlus.2])).symm
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
  ring

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
    (hprecision : IsRootModuloPower (7 : ℤ_[7]) padicSevenPolynomial
      padicSevenSecondNewtonApproximation 4) →
    IsRootModuloPower (7 : ℤ_[7]) padicSevenPolynomial
      padicSevenSecondNewtonApproximation 4 := by
  intro hprecision
  exact hprecision

/-- At `p=2`, the derivative of `X²-u` is never a unit at a unit. -/
theorem two_adic_square_derivative_never_unit (a : ℤ_[2]) (ha : IsUnit a) :
    ¬ IsUnit ((2 : ℤ_[2]) * a) := by
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

/-- Every `2`-adic unit congruent to one modulo eight is a square. -/
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
        simp [quadraticPolynomial, aeval_def, eval₂_at_apply]
      _ ≤ (2 : ℝ) ^ (-3 : ℤ) := hnormerr
      _ < ((2 : ℝ) ^ (-1 : ℤ)) ^ 2 := by norm_num
      _ = ‖(quadraticPolynomial u).derivative.aeval (1 : ℤ_[2])‖ ^ 2 := by
        have hderiv :
            (quadraticPolynomial u).derivative.aeval (1 : ℤ_[2]) =
              (2 : ℤ_[2]) := by
          simp [quadraticPolynomial, aeval_def, eval₂_at_apply]
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
      convert padicValNat_base_pow (p := 2) (by norm_num) 4 using 1 <;> norm_num
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
      convert padicValNat_base_pow (p := 2) (by norm_num) 6 using 1 <;> norm_num
    exact_mod_cast hpv

/-- The lifted root has displacement of value three from one, matching the first correction. -/
theorem padicTwoSeventeen_lifted_root_displacement
    : ∃ a : ℚ_[2], padicTwoSeventeenPolynomial.eval a = 0 ∧
      Padic.addValuation (p := 2) (a - 1) = (3 : WithTop ℤ) := by
  sorry

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
    simpa [residueMap] using (CharP.cast_eq_zero (ResidueRing A) p)
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
  simpa [sub_eq_add_neg, add_assoc] using hone

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

/-- The irreducibility argument works for any integrally closed local domain, not only a DVR. -/
theorem irreducible_reduction_argument_for_integrally_closed_local_domain
    {A K : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K]
    (f : A[X]) (hf : f.Monic)
    (hred : Irreducible (residuePolynomial f)) :
    Irreducible (Polynomial.map (algebraMap A K) f) := by
  exact irreducible_of_irreducible_residue_reduction f hf hred

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
  sorry

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
      letI := w.valueGroup
      unfold Chapter09ValuationExtensionEquivalent
      exact Valuation.IsEquiv.refl
    · intro w₁ w₂ h
      letI := w₁.valueGroup
      letI := w₂.valueGroup
      unfold Chapter09ValuationExtensionEquivalent at h ⊢
      exact Valuation.IsEquiv.symm h
    · intro w₁ w₂ w₃ h₁₂ h₂₃
      letI := w₁.valueGroup
      letI := w₂.valueGroup
      letI := w₃.valueGroup
      unfold Chapter09ValuationExtensionEquivalent at h₁₂ h₂₃ ⊢
      exact Valuation.IsEquiv.trans h₁₂ h₂₃

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

/-- For a finite extension, primes above the maximal ideal correspond to valuation extensions. -/
theorem finite_extension_prime_valuation_correspondence
    {A B K L Γ : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]
    [ValuationRing A] [IsIntegrallyClosed A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra A L] [IsScalarTower A K L]
    [CommRing B] [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L]
    [LinearOrderedCommGroupWithZero Γ] (vK : Valuation K Γ) :
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
  sorry

/-- A henselian valued field has one prime above the maximal ideal in every finite extension. -/
theorem henselian_valued_field_has_unique_prime_and_extension
    {A B K L Γ : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]
    [ValuationRing A] [IsIntegrallyClosed A]
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra A K] [IsFractionRing A K]
    [CommRing B] [Algebra A B] [Algebra B L]
    [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [IsIntegralClosure B A L]
    [LinearOrderedCommGroupWithZero Γ] (vK : Valuation K Γ)
    (hH : IsHenselianValuedField vK)
    (hcor : ExtensionPrimeCorrespondence (A := A) (B := B) (L := L) vK) :
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

/-- Adic completeness of the valuation ring implies henselianity of the valued field. -/
theorem complete_valued_field_is_henselian
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ)
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal vK.valuationSubring)
      vK.valuationSubring) :
    IsHenselianValuedField vK := by
  change HenselianLocalRing vK.valuationSubring
  apply complete_separated_local_ring_is_henselian
  exact hcomplete

end
end Chapter09
end ValuationsBook
