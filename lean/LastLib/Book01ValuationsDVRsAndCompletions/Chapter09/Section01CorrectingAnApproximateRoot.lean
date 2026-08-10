import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.Topology.Algebra.WithZeroTopology
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

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

/-! # Book 1, Chapter 9, Section 9.1: Correcting an Approximate Root
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

end
end Chapter09
end LastLib.Book01ValuationsDVRsAndCompletions
