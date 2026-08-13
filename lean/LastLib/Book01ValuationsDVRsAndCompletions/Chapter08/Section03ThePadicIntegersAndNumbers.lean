import LastLib.Book01ValuationsDVRsAndCompletions.Chapter08.Section01CompatibleFiniteApproximations
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Topology.MetricSpace.Perfect
import Mathlib.Topology.Algebra.Ring.Compact
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter08

open Polynomial IsLocalRing
open Filter
open scoped BigOperators Topology

noncomputable section

/-!
# Chapter 8: Inverse limits and digit expansions

This file is deliberately a statement-generation pass. The declarations use Mathlib's
AdicCompletion, ideal quotients, PadicInt, Padic, PowerSeries, and LaurentSeries
where those interfaces match the book. A few predicates package the adic convergence and
digit notation used in the prose.
-/

/-! # Book 1, Chapter 8, Section 8.3: The p-adic Integers and Numbers
-/

/-! ### 8.3 The p-adic integers and numbers -/

/-- Mathlib's p-adic integers and p-adic numbers, named as in the book. -/
abbrev Chapter08PadicIntegers (p : ℕ) [Fact p.Prime] := PadicInt p
abbrev Chapter08PadicNumbers (p : ℕ) [Fact p.Prime] := Padic p

/-- The inverse-limit presentation of Z_p used in this chapter. -/
abbrev Chapter08PadicIntegerInverseLimit (p : ℕ) [Fact p.Prime] :=
  Chapter08CompatibleFamily ℤ (Ideal.span {(p : ℤ)})

abbrev Chapter08Zp (p : ℕ) [Fact p.Prime] := Chapter08PadicIntegerInverseLimit p
abbrev Chapter08Qp (p : ℕ) [Fact p.Prime] := Chapter08PadicNumbers p

/-- The p-adic numbers are the fraction field of the p-adic integers. -/
theorem chapter08_padic_numbers_are_the_fraction_field_of_integers
    (p : ℕ) [Fact p.Prime] :
    IsFractionRing (Chapter08PadicIntegers p) (Chapter08PadicNumbers p) := by
  infer_instance

-- The inverse-limit ring is canonically the usual Mathlib p-adic integer ring. -/
theorem chapter08_padic_integer_inverse_limit
    (p : ℕ) [Fact p.Prime] :
    Nonempty (Chapter08PadicIntegers p ≃+* Chapter08Zp p) := by
  classical
  let I : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hpow : ∀ n : ℕ, I ^ n = Ideal.span {((p ^ n : ℕ) : ℤ)} := by
    intro n
    simp [I, Ideal.span_singleton_pow, Nat.cast_pow]
  let q (n : ℕ) : (ℤ ⧸ I ^ n) ≃+* ZMod (p ^ n) :=
    (Ideal.quotientEquivAlgOfEq ℤ (hpow n)).toRingEquiv.trans
      (Int.quotientSpanNatEquivZMod (p ^ n))
  have q_mk (n : ℕ) (z : ℤ) :
      q n (Ideal.Quotient.mk (I ^ n) z) = (z : ZMod (p ^ n)) := by
    simp [q]
  have hfactor_q : ∀ {m n : ℕ} (hmn : m ≤ n) (z : ℤ ⧸ I ^ n),
      (ZMod.cast (q n z) : ZMod (p ^ m)) =
        q m (Ideal.Quotient.factorPow I hmn z) := by
    intro m n hmn z
    refine Submodule.Quotient.induction_on (I ^ n) z ?_
    intro z
    simpa [q, Ideal.Quotient.factorPow] using
      (ZMod.cast_intCast (pow_dvd_pow p hmn) z)
  have hcoord : ∀ {m n : ℕ} (hmn : m ≤ n) (z : Chapter08Zp p),
      Ideal.Quotient.factorPow I (Nat.succ_le_succ hmn) (z.1 n) = z.1 m := by
    intro m n hmn z
    have hlong :=
      Ideal.Quotient.eq_factor_of_eq_factor_succ
        (I := fun i : ℕ => I ^ (i + 1))
        (fun i j hij => Ideal.pow_le_pow_right (Nat.succ_le_succ hij))
        (fun i => z.1 i)
        (fun i => by
          simp)
        hmn
    simpa [Ideal.Quotient.factorPow] using hlong.symm
  let coord (n : ℕ) : Chapter08Zp p →+* ℤ ⧸ I ^ (n + 1) :=
    { toFun := fun z => z.1 n
      map_one' := rfl
      map_mul' := by intro x y; rfl
      map_zero' := rfl
      map_add' := by intro x y; rfl }
  let f0 : Chapter08Zp p →+* ZMod (p ^ 0) :=
    { toFun := fun _ => 0
      map_one' := by
        let : Subsingleton (ZMod (p ^ 0)) :=
          ZMod.subsingleton_iff.2 (pow_zero p)
        exact Subsingleton.elim _ _
      map_mul' := by
        let : Subsingleton (ZMod (p ^ 0)) :=
          ZMod.subsingleton_iff.2 (pow_zero p)
        intros
        exact Subsingleton.elim _ _
      map_zero' := rfl
      map_add' := by
        let : Subsingleton (ZMod (p ^ 0)) :=
          ZMod.subsingleton_iff.2 (pow_zero p)
        intros
        exact Subsingleton.elim _ _ }
  let f : ∀ n : ℕ, Chapter08Zp p →+* ZMod (p ^ n) :=
    fun n => Nat.casesOn n f0 (fun k => (q (k + 1)).toRingHom.comp (coord k))
  have hfcompat : ∀ (m n : ℕ) (hmn : m ≤ n),
      (ZMod.castHom (pow_dvd_pow p hmn) (ZMod (p ^ m))).comp (f n) = f m := by
    intro m n hmn
    cases m with
    | zero =>
        apply RingHom.ext
        intro z
        let : Subsingleton (ZMod (p ^ 0)) :=
          ZMod.subsingleton_iff.2 (pow_zero p)
        exact Subsingleton.elim _ _
    | succ m =>
        cases n with
        | zero => omega
        | succ n =>
            apply RingHom.ext
            intro z
            change (ZMod.cast (q (n + 1) (z.1 n)) : ZMod (p ^ (m + 1))) =
              q (m + 1) (z.1 m)
            rw [hfactor_q (m := m + 1) (n := n + 1)
              hmn (z.1 n), hcoord (Nat.le_of_succ_le_succ hmn) z]
  let fromFamily : Chapter08Zp p →+* Chapter08PadicIntegers p :=
    PadicInt.lift (f_compat := hfcompat)
  let toFamilyFun : Chapter08PadicIntegers p → Chapter08Zp p := fun x =>
    ⟨fun n => (q (n + 1)).symm (PadicInt.toZModPow (n + 1) x), by
      intro n
      apply (q (n + 1)).injective
      rw [RingEquiv.apply_symm_apply]
      rw [← hfactor_q (m := n + 1) (n := n + 2)
        (Nat.le_succ (n + 1)) ((q (n + 2)).symm (PadicInt.toZModPow (n + 2) x))]
      simp only [RingEquiv.apply_symm_apply]
      exact PadicInt.cast_toZModPow (n + 1) (n + 2) (Nat.le_succ (n + 1)) x⟩
  let toFamily : Chapter08PadicIntegers p →+* Chapter08Zp p :=
    { toFun := toFamilyFun
      map_one' := by
        apply Subtype.ext
        funext n
        simp [toFamilyFun]
      map_mul' := by
        intro x y
        apply Subtype.ext
        funext n
        simp [toFamilyFun]
      map_zero' := by
        apply Subtype.ext
        funext n
        simp [toFamilyFun]
      map_add' := by
        intro x y
        apply Subtype.ext
        funext n
        simp [toFamilyFun] }
  have hfrom : ∀ x : Chapter08PadicIntegers p, fromFamily (toFamily x) = x := by
    intro x
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    cases n with
    | zero =>
        let : Subsingleton (ZMod (p ^ 0)) :=
          ZMod.subsingleton_iff.2 (pow_zero p)
        exact Subsingleton.elim _ _
    | succ n =>
        have hspec := RingHom.congr_fun
          (PadicInt.lift_spec (f := f) hfcompat (n + 1)) (toFamily x)
        simpa [fromFamily, toFamily, toFamilyFun, f, coord] using hspec
  have hto : ∀ z : Chapter08Zp p, toFamily (fromFamily z) = z := by
    intro z
    apply Subtype.ext
    funext n
    apply (q (n + 1)).injective
    have hspec := RingHom.congr_fun
      (PadicInt.lift_spec (f := f) hfcompat (n + 1)) z
    simpa [toFamily, toFamilyFun, f, coord, fromFamily] using hspec
  let e : Chapter08PadicIntegers p ≃+* Chapter08Zp p :=
    RingEquiv.ofBijective toFamily
      ⟨by
        intro x y hxy
        have h := congrArg fromFamily hxy
        rw [hfrom x, hfrom y] at h
        exact h
       , by
        intro z
        exact ⟨fromFamily z, hto z⟩⟩
  exact ⟨e⟩

-- Z_p is a complete DVR with uniformizer p and residue field F_p. -/
theorem chapter08_padic_integers_are_a_complete_dvr
    (p : ℕ) [Fact p.Prime] :
    IsDiscreteValuationRing (Chapter08PadicIntegers p) ∧
      CompleteSpace (Chapter08PadicIntegers p) ∧
      Irreducible (p : Chapter08PadicIntegers p) ∧
      Nonempty (IsLocalRing.ResidueField (Chapter08PadicIntegers p) ≃+* ZMod p) := by
  exact ⟨inferInstance, inferInstance, PadicInt.irreducible_p, ⟨PadicInt.residueField⟩⟩

/-- The digit alphabet for p-adic integers. -/
abbrev Chapter08PadicDigitSequences (p : ℕ) :=
  {a : ℕ → ℕ // ∀ i : ℕ, a i < p}

/-- The finite partial sum of a p-adic digit sequence. -/
def Chapter08PadicPartialSum (p : ℕ) [Fact p.Prime]
    (a : ℕ → ℕ) (n : ℕ) : Chapter08PadicIntegers p :=
  ∑ i ∈ Finset.range n,
    (a i : Chapter08PadicIntegers p) * (p : Chapter08PadicIntegers p) ^ i

/-- A convergent p-adic digit expansion with digits 0 ≤ a_i < p. -/
def Chapter08PadicExpansion (p : ℕ) [Fact p.Prime]
    (x : Chapter08PadicIntegers p) (a : ℕ → ℕ) : Prop :=
  (∀ i : ℕ, a i < p) ∧ Tendsto (Chapter08PadicPartialSum p a) atTop (𝓝 x)

/-! Every p-adic integer has a unique base-p expansion. -/
theorem chapter08_padic_digit_expansion_unique
    (p : ℕ) [Fact p.Prime] (x : Chapter08PadicIntegers p) :
    ∃! a : ℕ → ℕ, Chapter08PadicExpansion p x a := by
  classical
  let b : ℕ → ℕ := fun n => x.appr n
  let a : ℕ → ℕ := fun n =>
    (b (n + 1) - b n) / p ^ n
  have hp : 0 < p := (Fact.out : Nat.Prime p).pos
  have hmono : ∀ n : ℕ, b n ≤ b (n + 1) := by
    intro n
    simpa [b, Nat.succ_eq_add_one] using
      (PadicInt.appr_mono x (Nat.le_succ n))
  have hdvd : ∀ n : ℕ, p ^ n ∣ b (n + 1) - b n := by
    intro n
    simpa [b, Nat.succ_eq_add_one] using
      (PadicInt.dvd_appr_sub_appr x n (n + 1) (Nat.le_succ n))
  have ha_lt : ∀ n : ℕ, a n < p := by
    intro n
    apply (Nat.mul_lt_mul_right (Nat.pow_pos hp)).mp
    calc
      a n * p ^ n = b (n + 1) - b n := Nat.div_mul_cancel (hdvd n)
      _ < p ^ (n + 1) :=
        lt_of_le_of_lt (Nat.sub_le _ _)
          (by simpa [b] using PadicInt.appr_lt x (n + 1))
      _ = p * p ^ n := by rw [pow_succ, Nat.mul_comm]
  have hsum : ∀ n : ℕ,
      (∑ i ∈ Finset.range n, a i * p ^ i) = b n := by
    intro n
    induction n with
    | zero => simp [b, PadicInt.appr]
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        rw [Nat.div_mul_cancel (hdvd n)]
        have hmn := hmono n
        omega
  let hlim : Tendsto (fun n : ℕ => (b n : Chapter08PadicIntegers p)) atTop (𝓝 x) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    obtain ⟨N, hN⟩ := PadicInt.exists_pow_neg_lt p hε
    refine ⟨N, fun n hn => ?_⟩
    have hle : ‖x - (b n : Chapter08PadicIntegers p)‖ ≤
        (p : ℝ) ^ (-(n : ℤ)) := by
      apply (PadicInt.norm_le_pow_iff_mem_span_pow _ _).2
      simpa [b] using PadicInt.appr_spec n x
    have hpow : (p : ℝ) ^ (-(n : ℤ)) ≤ (p : ℝ) ^ (-(N : ℤ)) := by
      apply zpow_le_zpow_right₀
        (by exact_mod_cast (Fact.out : Nat.Prime p).one_lt.le)
      exact neg_le_neg (by exact_mod_cast hn)
    rw [dist_eq_norm, norm_sub_rev]
    exact hle.trans_lt (hpow.trans_lt hN)
  have hpartial_diff : ∀ (d : ℕ → ℕ) {k m : ℕ}, k ≤ m →
      Chapter08PadicPartialSum p d m - Chapter08PadicPartialSum p d k ∈
        Ideal.span {((p : Chapter08PadicIntegers p) ^ k)} := by
    intro d k m hkm
    rw [Chapter08PadicPartialSum, Chapter08PadicPartialSum]
    rw [Finset.sum_range_sub_sum_range hkm]
    apply (Ideal.span {((p : Chapter08PadicIntegers p) ^ k)}).sum_mem
    intro i hi
    rw [Finset.mem_filter] at hi
    apply Ideal.mem_span_singleton'.2
    refine ⟨(d i : Chapter08PadicIntegers p) *
        (p : Chapter08PadicIntegers p) ^ (i - k), ?_⟩
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hi.2]
  have hsum_lt : ∀ (d : ℕ → ℕ), (∀ i, d i < p) → ∀ n,
      (∑ i ∈ Finset.range n, d i * p ^ i) < p ^ n := by
    intro d hd n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ]
        have hsum' :
            (∑ i ∈ Finset.range n, d i * p ^ i) + d n * p ^ n <
              p ^ n + d n * p ^ n := by omega
        have hmul_le : p ^ n + d n * p ^ n ≤ p * p ^ n := by
          calc
            p ^ n + d n * p ^ n = (d n + 1) * p ^ n := by ring
            _ ≤ p * p ^ n := by
              exact Nat.mul_le_mul_right _ (Nat.succ_le_of_lt (hd n))
        simpa [pow_succ, Nat.mul_comm] using hsum'.trans_le hmul_le
  have hfinite_eq : ∀ (d : ℕ → ℕ), Chapter08PadicExpansion p x d → ∀ n,
      (∑ i ∈ Finset.range n, d i * p ^ i) = b n := by
    intro d hd n
    have hclosed : IsClosed
        (Ideal.span {((p : Chapter08PadicIntegers p) ^ n)} :
          Set (Chapter08PadicIntegers p)) :=
      (Ideal.isCompact_of_fg (IsNoetherian.noetherian _)).isClosed
    have hxd : x - Chapter08PadicPartialSum p d n ∈
        Ideal.span {((p : Chapter08PadicIntegers p) ^ n)} := by
      apply hclosed.mem_of_tendsto
        ((hd.2.sub tendsto_const_nhds))
      refine eventually_atTop.2 ⟨n, fun m hmn => ?_⟩
      exact hpartial_diff d hmn
    have hxb : x - (b n : Chapter08PadicIntegers p) ∈
        Ideal.span {((p : Chapter08PadicIntegers p) ^ n)} := by
      simpa [b] using PadicInt.appr_spec n x
    have hdiff : Chapter08PadicPartialSum p d n - (b n : Chapter08PadicIntegers p) ∈
        Ideal.span {((p : Chapter08PadicIntegers p) ^ n)} := by
      have h := (Ideal.span {((p : Chapter08PadicIntegers p) ^ n)}).sub_mem hxb hxd
      convert h using 1; ring
    have hker : Chapter08PadicPartialSum p d n - (b n : Chapter08PadicIntegers p) ∈
        RingHom.ker (PadicInt.toZModPow n) := by
      rw [PadicInt.ker_toZModPow]
      exact hdiff
    have hto := (RingHom.mem_ker).1 hker
    have hmodZ :
        ((↑(∑ i ∈ Finset.range n, d i * p ^ i) : ZMod (p ^ n))) =
          (b n : ZMod (p ^ n)) := by
      have hto' :
          (∑ i ∈ Finset.range n, (d i : ZMod (p ^ n)) *
              (p : ZMod (p ^ n)) ^ i) - (b n : ZMod (p ^ n)) = 0 := by
        simpa [Chapter08PadicPartialSum, map_sub, map_sum, map_mul, map_pow] using hto
      have htoeq :
          (∑ i ∈ Finset.range n, (d i : ZMod (p ^ n)) *
              (p : ZMod (p ^ n)) ^ i) = (b n : ZMod (p ^ n)) :=
        sub_eq_zero.mp hto'
      simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow] using htoeq
    have hmod :
        (∑ i ∈ Finset.range n, d i * p ^ i) ≡ b n [MOD p ^ n] :=
      (ZMod.natCast_eq_natCast_iff _ _ _).1 hmodZ
    rw [Nat.ModEq] at hmod
    rw [Nat.mod_eq_of_lt (hsum_lt d hd.1 n),
      Nat.mod_eq_of_lt (by simpa [b] using PadicInt.appr_lt x n)] at hmod
    exact hmod
  refine ⟨a, ?_, ?_⟩
  · refine ⟨ha_lt, ?_⟩
    have hseq : Chapter08PadicPartialSum p a =
        (fun n => (b n : Chapter08PadicIntegers p)) := by
      funext n
      dsimp [Chapter08PadicPartialSum]
      norm_cast
      exact hsum n
    rw [hseq]
    exact hlim
  · intro d hd
    have hsumd := hfinite_eq d hd
    have hdigits : ∀ n : ℕ, d n = a n := by
      intro n
      have hdnext := hsumd (n + 1)
      have hdnow := hsumd n
      have hanext := hsum (n + 1)
      have hanow := hsum n
      rw [Finset.sum_range_succ] at hdnext hanext
      rw [hdnow] at hdnext
      rw [hanow] at hanext
      have hmul : d n * p ^ n = a n * p ^ n :=
        Nat.add_left_cancel (hdnext.trans hanext.symm)
      exact Nat.eq_of_mul_eq_mul_right (Nat.pow_pos hp) hmul
    funext n
    exact hdigits n

/-- The partial sum with all digits equal to p - 1. -/
def Chapter08PadicNegOnePartialSum (p n : ℕ) [Fact p.Prime] :
    Chapter08PadicIntegers p :=
  ∑ i ∈ Finset.range n,
    ((p - 1 : ℕ) : Chapter08PadicIntegers p) * (p : Chapter08PadicIntegers p) ^ i

/-! The displayed expansion -1 = (p-1) + (p-1)p + .... -/
theorem chapter08_padic_negative_one_partial_sum
    (p n : ℕ) [Fact p.Prime] :
    Chapter08PadicNegOnePartialSum p n =
      (p : Chapter08PadicIntegers p) ^ n - 1 := by
  classical
  have hp : 1 ≤ p := (Fact.out : Nat.Prime p).one_lt.le
  induction n with
  | zero => simp [Chapter08PadicNegOnePartialSum]
  | succ n ih =>
    have hstep : Chapter08PadicNegOnePartialSum p (n + 1) =
        Chapter08PadicNegOnePartialSum p n +
          ((p - 1 : ℕ) : Chapter08PadicIntegers p) *
            (p : Chapter08PadicIntegers p) ^ n := by
      simp [Chapter08PadicNegOnePartialSum, Finset.sum_range_succ]
    rw [hstep]
    rw [ih, pow_succ, Nat.cast_sub hp]
    ring

theorem chapter08_padic_negative_one_difference
    (p n : ℕ) [Fact p.Prime] :
    Chapter08PadicNegOnePartialSum p n - (-1) =
      (p : Chapter08PadicIntegers p) ^ n := by
  classical
  rw [chapter08_padic_negative_one_partial_sum]
  ring

theorem chapter08_padic_powers_tend_to_zero
    (p : ℕ) [Fact p.Prime] :
    Tendsto (fun n : ℕ => (p : Chapter08PadicIntegers p) ^ n) atTop (𝓝 0) := by
  classical
  apply tendsto_pow_atTop_nhds_zero_of_norm_lt_one
  rw [PadicInt.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : Nat.Prime p).one_lt)

theorem chapter08_padic_negative_one_expansion
    (p : ℕ) [Fact p.Prime] :
    Tendsto (fun n => Chapter08PadicNegOnePartialSum p n) atTop (𝓝 (-1)) := by
  classical
  have h := chapter08_padic_powers_tend_to_zero p
  simpa [chapter08_padic_negative_one_partial_sum p] using
    (h.sub tendsto_const_nhds)

/-- A single digit carry moves a unit from the zeroth digit to a higher power of p. -/
theorem chapter08_padic_single_digit_carry
    (p : ℕ) [Fact p.Prime] :
    ((p - 1 : ℕ) : Chapter08PadicIntegers p) + 1 =
      (p : Chapter08PadicIntegers p) := by
  classical
  have hp : 1 ≤ p := (Fact.out : Nat.Prime p).one_lt.le
  rw [Nat.cast_sub hp]
  ring

theorem chapter08_higher_powers_are_smaller_p_adically
    (p n : ℕ) [Fact p.Prime] :
    ‖(p : Chapter08PadicIntegers p) ^ (n + 1)‖ <
      ‖(p : Chapter08PadicIntegers p) ^ n‖ := by
  classical
  rw [PadicInt.norm_p_pow, PadicInt.norm_p_pow]
  have hp : (1 : ℝ) < p := by
    exact_mod_cast (Fact.out : Nat.Prime p).one_lt
  exact zpow_lt_zpow_right₀ hp (by omega)

/-- A Laurent expansion in Q_p starts at an arbitrary integral exponent. -/
def Chapter08PadicFieldPartialSum (p : ℕ) [Fact p.Prime]
    (N : ℤ) (a : ℕ → ℕ) (n : ℕ) : Chapter08PadicNumbers p :=
  ∑ i ∈ Finset.range n,
    (a i : Chapter08PadicNumbers p) *
      (p : Chapter08PadicNumbers p) ^ (N + (i : ℤ))

def Chapter08PadicLaurentExpansion (p : ℕ) [Fact p.Prime]
    (x : Chapter08PadicNumbers p) (N : ℤ) (a : ℕ → ℕ) : Prop :=
  (∀ i : ℕ, a i < p) ∧
    Tendsto (Chapter08PadicFieldPartialSum p N a) atTop (𝓝 x)

/-- Every p-adic number admits a Laurent expansion with base-p digits. -/
theorem chapter08_every_padic_number_has_laurent_digit_expansion
    (p : ℕ) [Fact p.Prime] (x : Chapter08PadicNumbers p) :
    ∃ N : ℤ, ∃ a : ℕ → ℕ,
      Chapter08PadicLaurentExpansion p x N a := by
  classical
  by_cases hx : x = 0
  · refine ⟨0, fun _ => 0, ?_⟩
    constructor
    · intro i
      exact (Fact.out : Nat.Prime p).pos
    · have hzero : Chapter08PadicFieldPartialSum p 0 (fun _ => 0) =
          (fun _ => (0 : Chapter08PadicNumbers p)) := by
        funext n
        simp [Chapter08PadicFieldPartialSum]
      rw [hzero]
      simp [hx]
  · have hp0 : (p : Chapter08PadicNumbers p) ≠ 0 := by
      exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
    have hval :
        (x * (p : Chapter08PadicNumbers p) ^ (-x.valuation)).valuation = 0 := by
      rw [Padic.valuation_mul hx (zpow_ne_zero _ hp0),
        Padic.valuation_zpow, Padic.valuation_p]
      ring
    have hy_norm :
        ‖x * (p : Chapter08PadicNumbers p) ^ (-x.valuation)‖ ≤ 1 := by
      apply (Padic.norm_le_one_iff_val_nonneg _).2
      rw [hval]
    let y : Chapter08PadicIntegers p :=
      ⟨x * (p : Chapter08PadicNumbers p) ^ (-x.valuation), hy_norm⟩
    obtain ⟨a, ha, _⟩ := chapter08_padic_digit_expansion_unique p y
    have hxy :
        (y : Chapter08PadicNumbers p) * (p : Chapter08PadicNumbers p) ^ x.valuation = x := by
      change (x * (p : Chapter08PadicNumbers p) ^ (-x.valuation)) *
          (p : Chapter08PadicNumbers p) ^ x.valuation = x
      rw [mul_assoc, ← zpow_add₀ hp0, neg_add_cancel, zpow_zero, mul_one]
    have hpartial (n : ℕ) :
        Chapter08PadicFieldPartialSum p x.valuation a n =
          algebraMap (Chapter08PadicIntegers p) (Chapter08PadicNumbers p)
              (Chapter08PadicPartialSum p a n) *
            (p : Chapter08PadicNumbers p) ^ x.valuation := by
      simp only [Chapter08PadicFieldPartialSum, Chapter08PadicPartialSum,
        map_sum, map_mul, map_pow, PadicInt.algebraMap_apply]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [zpow_add₀ hp0]
      simp only [PadicInt.coe_natCast]
      rw [zpow_natCast]
      ring
    have hcont : Continuous (fun z : Chapter08PadicIntegers p =>
        (z : Chapter08PadicNumbers p) *
          (p : Chapter08PadicNumbers p) ^ x.valuation) := by
      fun_prop
    have hlim := (hcont.tendsto y).comp ha.2
    rw [hxy] at hlim
    refine ⟨x.valuation, a, ?_⟩
    change (∀ i : ℕ, a i < p) ∧
      Tendsto (Chapter08PadicFieldPartialSum p x.valuation a) atTop (𝓝 x)
    refine ⟨ha.1, ?_⟩
    have hseq :
        Chapter08PadicFieldPartialSum p x.valuation a =
          (fun n => algebraMap (Chapter08PadicIntegers p) (Chapter08PadicNumbers p)
              (Chapter08PadicPartialSum p a n) *
            (p : Chapter08PadicNumbers p) ^ x.valuation) := by
      funext n
      exact hpartial n
    rw [hseq]
    exact hlim

/-- The first exponent with a nonzero digit, or top for the zero series. -/
def Chapter08FirstNonzeroExponent (N : ℤ) (a : ℕ → ℕ) : WithTop ℤ := by
  classical
  exact if h : ∃ i : ℕ, a i ≠ 0 then
    (N + (Nat.find h : ℤ) : WithTop ℤ)
  else ⊤

private theorem chapter08_padic_leading_term_valuation
    (p : ℕ) [Fact p.Prime] (x : Chapter08PadicNumbers p)
    (N : ℤ) (a : ℕ → ℕ)
    (ha : Chapter08PadicLaurentExpansion p x N a)
    (hnonzero : ∃ i : ℕ, a i ≠ 0) :
    Padic.addValuation
        ((a (Nat.find hnonzero) : Chapter08PadicNumbers p) *
          (p : Chapter08PadicNumbers p) ^ (N + (Nat.find hnonzero : ℤ))) =
      Chapter08FirstNonzeroExponent N a := by
  classical
  let j := Nat.find hnonzero
  have hj : a j ≠ 0 := Nat.find_spec hnonzero
  have hjp : a j < p := ha.1 j
  have hpndvd : ¬p ∣ a j := Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hj) hjp
  have hval : Padic.valuation (a j : Chapter08PadicNumbers p) = 0 := by
    rw [Padic.valuation_natCast, padicValNat.eq_zero_of_not_dvd hpndvd]
    simp
  have hterm :
      (a j : Chapter08PadicNumbers p) *
          (p : Chapter08PadicNumbers p) ^ (N + (j : ℤ)) ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast hj)
      (zpow_ne_zero _ (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero))
  rw [Padic.addValuation.apply hterm,
    Padic.valuation_mul (by exact_mod_cast hj)
      (zpow_ne_zero _ (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)),
    hval, Padic.valuation_zpow, Padic.valuation_p, zero_add,
    Chapter08FirstNonzeroExponent]
  simp [j, hnonzero]

theorem chapter08_padic_valuation_is_first_nonzero_digit
    (p : ℕ) [Fact p.Prime] (x : Chapter08PadicNumbers p)
    (N : ℤ) (a : ℕ → ℕ)
    (ha : Chapter08PadicLaurentExpansion p x N a)
    (hnonzero : ∃ i : ℕ, a i ≠ 0) :
    Padic.addValuation x = Chapter08FirstNonzeroExponent N a := by
  classical
  let j := Nat.find hnonzero
  have hj : a j ≠ 0 := Nat.find_spec hnonzero
  have hzero_before : ∀ i : ℕ, i < j → a i = 0 := by
    intro i hi
    by_contra hne
    exact (Nat.find_min hnonzero hi) hne
  let term : ℕ → Chapter08PadicNumbers p := fun i =>
    (a i : Chapter08PadicNumbers p) *
      (p : Chapter08PadicNumbers p) ^ (N + (i : ℤ))
  let lead := term j
  have hlead_ne : lead ≠ 0 := by
    dsimp [lead, term]
    exact mul_ne_zero (by exact_mod_cast hj)
      (zpow_ne_zero _ (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero))
  have hcop : p.Coprime (a j) := by
    apply (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr
    exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hj) (ha.1 j)
  have hcoef_lead : ‖(a j : Chapter08PadicNumbers p)‖ = 1 :=
    (Padic.norm_natCast_eq_one_iff).2 hcop
  have hlead_norm : ‖lead‖ =
      ‖(p : Chapter08PadicNumbers p) ^ (N + (j : ℤ))‖ := by
    dsimp [lead, term]
    rw [norm_mul, hcoef_lead, one_mul]
  let bound : ℝ := ‖(p : Chapter08PadicNumbers p) ^ (N + (j : ℤ) + 1)‖
  have hterm : ∀ r : ℕ, ‖term (j + 1 + r)‖ ≤ bound := by
    intro r
    have hcoef : ‖(a (j + 1 + r) : Chapter08PadicNumbers p)‖ ≤ 1 := by
      simpa using (Padic.norm_int_le_one (p := p) (a (j + 1 + r) : ℤ))
    have hexp : -(N + ((j + 1 + r : ℕ) : ℤ)) ≤ -(N + (j : ℤ) + 1) := by
      push_cast
      omega
    have hpow :
        ‖(p : Chapter08PadicNumbers p) ^ (N + ((j + 1 + r : ℕ) : ℤ))‖ ≤
          bound := by
      dsimp [bound]
      rw [Padic.norm_p_zpow, Padic.norm_p_zpow]
      apply zpow_le_zpow_right₀
        (by exact_mod_cast (Fact.out : Nat.Prime p).one_lt.le)
      exact hexp
    calc
      ‖term (j + 1 + r)‖ =
          ‖(a (j + 1 + r) : Chapter08PadicNumbers p)‖ *
            ‖(p : Chapter08PadicNumbers p) ^
              (N + ((j + 1 + r : ℕ) : ℤ))‖ := by
        simp [term, norm_mul]
      _ ≤ 1 * ‖(p : Chapter08PadicNumbers p) ^
            (N + ((j + 1 + r : ℕ) : ℤ))‖ :=
        mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
      _ = ‖(p : Chapter08PadicNumbers p) ^
            (N + ((j + 1 + r : ℕ) : ℤ))‖ := by simp
      _ ≤ bound := hpow
  have hsum_bound : ∀ r : ℕ,
      ‖∑ i ∈ Finset.range r, term (j + 1 + i)‖ ≤ bound := by
    intro r
    induction r with
    | zero =>
        simpa [bound] using
          (norm_nonneg ((p : Chapter08PadicNumbers p) ^ (N + (j : ℤ) + 1)))
    | succ r ihr =>
        rw [Finset.sum_range_succ]
        exact (Padic.nonarchimedean _ _).trans (max_le ihr (hterm r))
  have hbefore : ∑ i ∈ Finset.range j, term i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [term, hzero_before i (Finset.mem_range.mp hi)]
  have hfirst : ∑ i ∈ Finset.range (j + 1), term i = lead := by
    rw [Finset.sum_range_succ, hbefore]
    simp [lead]
  have hbound_lt : bound < ‖lead‖ := by
    rw [hlead_norm]
    dsimp [bound]
    rw [Padic.norm_p_zpow, Padic.norm_p_zpow]
    apply zpow_lt_zpow_right₀ (by exact_mod_cast (Fact.out : Nat.Prime p).one_lt)
    omega
  have hpartial_bound {m : ℕ} (hm : j + 1 ≤ m) :
      ‖Chapter08PadicFieldPartialSum p N a m - lead‖ ≤ bound := by
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hm
    calc
      ‖Chapter08PadicFieldPartialSum p N a ((j + 1) + r) - lead‖ =
          ‖∑ i ∈ Finset.range r, term (j + 1 + i)‖ := by
        dsimp [Chapter08PadicFieldPartialSum]
        rw [Finset.sum_range_add, hfirst]
        congr 1
        ring
      _ ≤ bound := hsum_bound r
  have hlead_pos : 0 < ‖lead‖ := norm_pos_iff.mpr hlead_ne
  obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.1 ha.2) ‖lead‖ hlead_pos
  let m := max M (j + 1)
  have hmM : M ≤ m := le_max_left _ _
  have hmj : j + 1 ≤ m := le_max_right _ _
  have hnear : ‖x - Chapter08PadicFieldPartialSum p N a m‖ < ‖lead‖ := by
    simpa [dist_eq_norm, norm_sub_rev] using hM m hmM
  have htail : ‖Chapter08PadicFieldPartialSum p N a m - lead‖ < ‖lead‖ :=
    (hpartial_bound hmj).trans_lt hbound_lt
  have hxl : ‖x - lead‖ < ‖lead‖ := by
    calc
      ‖x - lead‖ =
          ‖(x - Chapter08PadicFieldPartialSum p N a m) +
            (Chapter08PadicFieldPartialSum p N a m - lead)‖ := by
        congr 1
        ring
      _ ≤ max ‖x - Chapter08PadicFieldPartialSum p N a m‖
          ‖Chapter08PadicFieldPartialSum p N a m - lead‖ :=
        Padic.nonarchimedean _ _
      _ < ‖lead‖ := max_lt hnear htail
  have hnorm : ‖x‖ = ‖lead‖ := Padic.norm_eq_of_norm_sub_lt_right hxl
  have hxne : x ≠ 0 := by
    intro hx
    rw [hx, norm_zero] at hnorm
    exact (ne_of_gt hlead_pos) hnorm.symm
  have hpoweq : (p : ℝ) ^ (-x.valuation) =
      (p : ℝ) ^ (-lead.valuation) := by
    simpa [Padic.norm_eq_zpow_neg_valuation hxne,
      Padic.norm_eq_zpow_neg_valuation hlead_ne] using hnorm
  have hval : x.valuation = lead.valuation := by
    have hneg :=
      (zpow_right_strictMono₀
        (by exact_mod_cast (Fact.out : Nat.Prime p).one_lt)).injective hpoweq
    exact neg_injective hneg
  calc
    Padic.addValuation x = (x.valuation : WithTop ℤ) :=
      Padic.addValuation.apply hxne
    _ = (lead.valuation : WithTop ℤ) := by rw [hval]
    _ = Padic.addValuation lead := (Padic.addValuation.apply hlead_ne).symm
    _ = Chapter08FirstNonzeroExponent N a := by
      simpa [lead, term, j] using
        (chapter08_padic_leading_term_valuation p x N a ha hnonzero)

theorem chapter08_rationals_are_dense_in_Qp
    (p : ℕ) [Fact p.Prime] :
    DenseRange (fun q : ℚ => (q : Chapter08PadicNumbers p)) := by
  exact Padic.denseRange_ratCast p

theorem chapter08_Qp_has_countable_dense_subfield
    (p : ℕ) [Fact p.Prime] :
    DenseRange (fun q : ℚ => (q : Chapter08PadicNumbers p)) ∧ Countable ℚ := by
  exact ⟨chapter08_rationals_are_dense_in_Qp p, inferInstance⟩

theorem chapter08_Zp_is_uncountable
    (p : ℕ) [Fact p.Prime] : ¬ Countable (Chapter08PadicIntegers p) := by
  classical
  let boolEquiv : Set ℕ ≃ (ℕ → Bool) :=
    { toFun := fun s n => if n ∈ s then true else false
      invFun := fun f => {n | f n = true}
      left_inv := by
        intro s
        ext n
        by_cases hn : n ∈ s <;> simp [hn]
      right_inv := by
        intro f
        funext n
        cases h : f n <;> simp [h] }
  have huncBool : Uncountable (ℕ → Bool) := by
    have hcard : Cardinal.aleph0 < Cardinal.mk (ℕ → Bool) := by
      rw [← Cardinal.mk_congr boolEquiv, Cardinal.mk_set_nat]
      exact Cardinal.aleph0_lt_continuum
    constructor
    intro hcount
    exact (not_lt_of_ge (Cardinal.mk_le_aleph0_iff.mpr hcount)) hcard
  have hperfect : Perfect (Set.univ : Set (Chapter08PadicIntegers p)) := by
    refine ⟨isClosed_univ, (preperfect_iff_nhds).2 ?_⟩
    intro z hz U hU
    rcases Metric.mem_nhds_iff.1 hU with ⟨ε, hε, hεU⟩
    obtain ⟨N, hN⟩ := PadicInt.exists_pow_neg_lt p hε
    let y := z + (p : Chapter08PadicIntegers p) ^ N
    refine ⟨y, ⟨hεU ?_, Set.mem_univ _⟩, ?_⟩
    · rw [Metric.mem_ball]
      simpa [y, dist_eq_norm, PadicInt.norm_p_pow, sub_eq_add_neg,
        add_comm, add_left_comm, add_assoc] using hN
    · intro hy
      have hpzero : (p : Chapter08PadicIntegers p) ^ N = 0 := by
        have hy' : z + (p : Chapter08PadicIntegers p) ^ N = z := by
          simpa [y] using hy
        exact add_left_cancel (a := z) (by simpa using hy')
      exact (pow_ne_zero N (by exact_mod_cast
        (Fact.out : Nat.Prime p).ne_zero)) hpzero
  let : Uncountable (ℕ → Bool) := huncBool
  obtain ⟨f, hf_range, hf_cont, hf_inj⟩ :=
    Perfect.exists_nat_bool_injection hperfect ⟨0, Set.mem_univ 0⟩
  exact hf_inj.uncountable.not_countable

theorem chapter08_completion_adds_p_adic_elements
    (p : ℕ) [Fact p.Prime] :
    ¬ Function.Surjective (fun q : ℚ => (q : Chapter08PadicNumbers p)) := by
  classical
  have hZ : Uncountable (Chapter08PadicIntegers p) :=
    ⟨chapter08_Zp_is_uncountable p⟩
  let : Uncountable (Chapter08PadicIntegers p) := hZ
  let : Uncountable (Chapter08PadicNumbers p) :=
    (IsFractionRing.injective (Chapter08PadicIntegers p)
      (Chapter08PadicNumbers p)).uncountable
  exact not_surjective_countable_uncountable _

theorem chapter08_Zp_is_compact
    (p : ℕ) [Fact p.Prime] : CompactSpace (Chapter08PadicIntegers p) := by
  infer_instance

end
end LastLib.Book01ValuationsDVRsAndCompletions.Chapter08
