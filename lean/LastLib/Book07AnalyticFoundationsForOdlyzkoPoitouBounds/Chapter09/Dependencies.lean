import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Order.LiminfLimsup

import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06.Dependencies
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08.Section02TheTriangularAutocorrelation

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter09

open Filter MeasureTheory
open scoped BigOperators

noncomputable section

/-!
Shared interfaces for Chapter 9.

The preceding Book 07 chapters are otherwise developed in parallel.  The
focused Chapter 6 dependency is imported only for the completed-zeta zero
predicate; the declarations below remain the minimal book-facing surface
needed by this chapter and are thin over canonical number-field objects.
-/

abbrev chapter09Degree (K : Type*) [Field K] [NumberField K] : ℕ :=
  Module.finrank ℚ K

abbrev chapter09RealPlaceCount (K : Type*) [Field K] [NumberField K] : ℕ :=
  NumberField.InfinitePlace.nrRealPlaces K

abbrev chapter09ComplexPlaceCount (K : Type*) [Field K] [NumberField K] : ℕ :=
  NumberField.InfinitePlace.nrComplexPlaces K

def chapter09AbsoluteDiscriminant (K : Type*) [Field K] [NumberField K] : ℝ :=
  |(NumberField.discr K : ℝ)|

def chapter09RootDiscriminant (K : Type*) [Field K] [NumberField K] : ℝ :=
  Real.rpow (chapter09AbsoluteDiscriminant K)
    (1 / (chapter09Degree K : ℝ))

abbrev chapter09EulerMascheroni : ℝ := Real.eulerMascheroniConstant

/- Exact rational endpoints for the numerical constants displayed in Chapter 9.
   The proof-carrying interface below is deliberately earlier than the Chapter
   10 certificate machinery. A later certificate chapter can provide a value
   without making this chapter depend on that later chapter. -/
def chapter09GammaLower : ℚ := 577215664901532 / 10 ^ 15

def chapter09GammaUpper : ℚ := 577215664901533 / 10 ^ 15

def chapter09UnconditionalEndpointZero : ℝ :=
  4 * Real.pi * Real.exp chapter09EulerMascheroni

def chapter09UnconditionalEndpointOne : ℝ :=
  4 * Real.pi * Real.exp (1 + chapter09EulerMascheroni)

def chapter09GRHEndpointZero : ℝ :=
  8 * Real.pi * Real.exp chapter09EulerMascheroni

def chapter09GRHEndpointOne : ℝ :=
  8 * Real.pi * Real.exp (chapter09EulerMascheroni + Real.pi / 2)

def chapter09UnconditionalEndpointZeroLower : ℚ := 223816160954 / 10 ^ 10

def chapter09UnconditionalEndpointZeroUpper : ℚ := 223816160955 / 10 ^ 10

def chapter09UnconditionalEndpointOneLower : ℚ := 608395403238 / 10 ^ 10

def chapter09UnconditionalEndpointOneUpper : ℚ := 608395403239 / 10 ^ 10

def chapter09GRHEndpointZeroLower : ℚ := 447632321909 / 10 ^ 10

def chapter09GRHEndpointZeroUpper : ℚ := 447632321910 / 10 ^ 10

def chapter09GRHEndpointOneLower : ℚ := 2153325159534 / 10 ^ 10

def chapter09GRHEndpointOneUpper : ℚ := 2153325159535 / 10 ^ 10

structure Chapter09NumericalEnclosureInterface : Prop where
  gamma_directed_bounds :
    (chapter09GammaLower : ℝ) < chapter09EulerMascheroni ∧
      chapter09EulerMascheroni < (chapter09GammaUpper : ℝ)
  unconditional_endpoint_zero_directed_bounds :
    (chapter09UnconditionalEndpointZeroLower : ℝ) <
        chapter09UnconditionalEndpointZero ∧
      chapter09UnconditionalEndpointZero <
        (chapter09UnconditionalEndpointZeroUpper : ℝ)
  unconditional_endpoint_one_directed_bounds :
    (chapter09UnconditionalEndpointOneLower : ℝ) <
        chapter09UnconditionalEndpointOne ∧
      chapter09UnconditionalEndpointOne <
        (chapter09UnconditionalEndpointOneUpper : ℝ)
  grh_endpoint_zero_directed_bounds :
    (chapter09GRHEndpointZeroLower : ℝ) < chapter09GRHEndpointZero ∧
      chapter09GRHEndpointZero < (chapter09GRHEndpointZeroUpper : ℝ)
  grh_endpoint_one_directed_bounds :
    (chapter09GRHEndpointOneLower : ℝ) < chapter09GRHEndpointOne ∧
      chapter09GRHEndpointOne < (chapter09GRHEndpointOneUpper : ℝ)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem chapter09NumericalEnclosure :
    Chapter09NumericalEnclosureInterface := by
  have hpiL : (3141592653589793 / 10 ^ 15 : ℝ) < Real.pi := by
    exact lt_trans (by norm_num) Real.pi_gt_d20
  have hpiU : Real.pi < (3141592653589794 / 10 ^ 15 : ℝ) := by
    exact lt_trans Real.pi_lt_d20 (by norm_num)
  have hloglo (n : ℕ) (hn : 2 ≤ n) :
      (1 / (n : ℝ) - 1 / (2 * (n : ℝ) ^ 2) + 1 / (3 * (n : ℝ) ^ 3) -
          1 / (4 * (n : ℝ) ^ 4) + 1 / (5 * (n : ℝ) ^ 5)) -
          (1 / (n : ℝ) ^ 6) / (1 - 1 / (n : ℝ)) ≤
        Real.log (1 + 1 / (n : ℝ)) := by
    have hlog :
        |(∑ i ∈ Finset.range 5, (-(1 / (n : ℝ))) ^ (i + 1) / (i + 1 : ℝ))
            + Real.log (1 - (-(1 / (n : ℝ))))| ≤
          |-(1 / (n : ℝ))| ^ (5 + 1) / (1 - |-(1 / (n : ℝ))|) := by
      apply Real.abs_log_sub_add_sum_range_le
      rw [abs_neg, abs_of_pos (by positivity)]
      apply (div_lt_one₀ (by positivity)).2
      exact_mod_cast hn
    norm_num [Finset.sum_range_succ, abs_of_pos, abs_of_nonneg] at hlog
    have hh := (abs_le.mp hlog).1
    ring_nf at hh
    ring_nf
    linarith [hh]
  have hloghi (n : ℕ) (hn : 2 ≤ n) :
      Real.log (1 + 1 / (n : ℝ)) ≤
        (1 / (n : ℝ) - 1 / (2 * (n : ℝ) ^ 2) + 1 / (3 * (n : ℝ) ^ 3) -
          1 / (4 * (n : ℝ) ^ 4) + 1 / (5 * (n : ℝ) ^ 5)) +
          (1 / (n : ℝ) ^ 6) / (1 - 1 / (n : ℝ)) := by
    have hlog :
        |(∑ i ∈ Finset.range 5, (-(1 / (n : ℝ))) ^ (i + 1) / (i + 1 : ℝ))
            + Real.log (1 - (-(1 / (n : ℝ))))| ≤
          |-(1 / (n : ℝ))| ^ (5 + 1) / (1 - |-(1 / (n : ℝ))|) := by
      apply Real.abs_log_sub_add_sum_range_le
      rw [abs_neg, abs_of_pos (by positivity)]
      apply (div_lt_one₀ (by positivity)).2
      exact_mod_cast hn
    norm_num [Finset.sum_range_succ, abs_of_pos, abs_of_nonneg] at hlog
    have hh := (abs_le.mp hlog).2
    ring_nf at hh
    ring_nf
    linarith [hh]
  have hstepA (n : ℕ) (hn : 0 < n) :
      ((harmonic n : ℝ) - Real.log (n : ℝ)) -
          ((harmonic (n + 1) : ℝ) - Real.log (n + 1)) =
        Real.log (1 + 1 / (n : ℝ)) - 1 / (n + 1 : ℝ) := by
    have hlog :
        Real.log (n + 1 : ℝ) - Real.log (n : ℝ) =
          Real.log (1 + 1 / (n : ℝ)) := by
      rw [← Real.log_div (by positivity) (by positivity)]
      congr 1
      field_simp
    calc
      ((harmonic n : ℝ) - Real.log (n : ℝ)) -
          ((harmonic (n + 1) : ℝ) - Real.log (n + 1)) =
          Real.log (n + 1 : ℝ) - Real.log (n : ℝ) - 1 / (n + 1 : ℝ) := by
            rw [harmonic_succ]
            norm_num
            ring
      _ = Real.log (1 + 1 / (n : ℝ)) - 1 / (n + 1 : ℝ) := by
        rw [hlog]
  have hrat (n : ℕ) (hn : 10000 ≤ n) :
      (1 / (2 * (n : ℝ)) - 1 / (12 * (n : ℝ) ^ 2)) -
          (1 / (2 * ((n : ℝ) + 1)) - 1 / (12 * ((n : ℝ) + 1) ^ 2)) +
          1 / (n + 1 : ℝ) <
        (1 / (n : ℝ) - 1 / (2 * (n : ℝ) ^ 2) + 1 / (3 * (n : ℝ) ^ 3) -
            1 / (4 * (n : ℝ) ^ 4) + 1 / (5 * (n : ℝ) ^ 5)) -
          (1 / (n : ℝ) ^ 6) / (1 - 1 / (n : ℝ)) := by
    have hn0 : 0 < (n : ℝ) := by
      exact_mod_cast (show 0 < n by omega)
    have hnminus : 0 < (n : ℝ) - 1 := by
      have h : (1 : ℝ) < n := by
        exact_mod_cast (show 1 < n by omega)
      linarith
    have hden :
        (1 / (n : ℝ) ^ 6) / (1 - 1 / (n : ℝ)) =
          1 / ((n : ℝ) ^ 5 * ((n : ℝ) - 1)) := by
      field_simp
    have hn100 : (100 : ℝ) < n := by
      exact_mod_cast (show 100 < n by omega)
    have hprod : 0 < (n : ℝ) ^ 2 * ((n : ℝ) - 100) := by
      exact mul_pos (sq_pos_of_pos hn0) (sub_pos.mpr hn100)
    have hsq100 : (100 : ℝ) ^ 2 < (n : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((n : ℝ) - 100)]
    have hsmall :
        0 < 147 * (n : ℝ) ^ 2 - 117 * (n : ℝ) - 72 := by
      nlinarith [hsq100, hn100]
    have hnum :
        0 < 2 * (n : ℝ) ^ 3 - 53 * (n : ℝ) ^ 2 - 117 * (n : ℝ) - 72 := by
      nlinarith [hprod, hsmall]
    have hD :
        0 < 60 * (n : ℝ) ^ 5 * ((n : ℝ) - 1) * ((n : ℝ) + 1) ^ 2 := by
      positivity
    have hident :
        ((1 / (n : ℝ) - 1 / (2 * (n : ℝ) ^ 2) + 1 / (3 * (n : ℝ) ^ 3) -
              1 / (4 * (n : ℝ) ^ 4) + 1 / (5 * (n : ℝ) ^ 5)) -
            1 / ((n : ℝ) ^ 5 * ((n : ℝ) - 1)) -
          ((1 / (2 * (n : ℝ)) - 1 / (12 * (n : ℝ) ^ 2)) -
              (1 / (2 * ((n : ℝ) + 1)) -
                1 / (12 * ((n : ℝ) + 1) ^ 2)) +
              1 / (n + 1 : ℝ))) *
            (60 * (n : ℝ) ^ 5 * ((n : ℝ) - 1) * ((n : ℝ) + 1) ^ 2) =
          2 * (n : ℝ) ^ 3 - 53 * (n : ℝ) ^ 2 - 117 * (n : ℝ) - 72 := by
      field_simp
      ring
    have hmul :
        0 <
          ((1 / (n : ℝ) - 1 / (2 * (n : ℝ) ^ 2) + 1 / (3 * (n : ℝ) ^ 3) -
                1 / (4 * (n : ℝ) ^ 4) + 1 / (5 * (n : ℝ) ^ 5)) -
              1 / ((n : ℝ) ^ 5 * ((n : ℝ) - 1)) -
            ((1 / (2 * (n : ℝ)) - 1 / (12 * (n : ℝ) ^ 2)) -
                (1 / (2 * ((n : ℝ) + 1)) -
                  1 / (12 * ((n : ℝ) + 1) ^ 2)) +
                1 / (n + 1 : ℝ))) *
              (60 * (n : ℝ) ^ 5 * ((n : ℝ) - 1) * ((n : ℝ) + 1) ^ 2) := by
      rw [hident]
      exact hnum
    have hdiff :
        0 <
          (1 / (n : ℝ) - 1 / (2 * (n : ℝ) ^ 2) + 1 / (3 * (n : ℝ) ^ 3) -
              1 / (4 * (n : ℝ) ^ 4) + 1 / (5 * (n : ℝ) ^ 5)) -
            1 / ((n : ℝ) ^ 5 * ((n : ℝ) - 1)) -
          ((1 / (2 * (n : ℝ)) - 1 / (12 * (n : ℝ) ^ 2)) -
              (1 / (2 * ((n : ℝ) + 1)) -
                1 / (12 * ((n : ℝ) + 1) ^ 2)) +
              1 / (n + 1 : ℝ)) := by
      exact lt_of_mul_lt_mul_right (by simpa using hmul) (le_of_lt hD)
    rw [hden]
    linarith [hdiff]
  have hratU (n : ℕ) (hn : 10000 ≤ n) :
      (1 / (n : ℝ) - 1 / (2 * (n : ℝ) ^ 2) + 1 / (3 * (n : ℝ) ^ 3) -
          1 / (4 * (n : ℝ) ^ 4) + 1 / (5 * (n : ℝ) ^ 5)) +
          (1 / (n : ℝ) ^ 6) / (1 - 1 / (n : ℝ)) <
        ((1 / (2 * (n : ℝ)) - 1 / (12 * (n : ℝ) ^ 2)) +
            1 / (n : ℝ) ^ 4) -
          (1 / (2 * ((n : ℝ) + 1)) - 1 / (12 * ((n : ℝ) + 1) ^ 2) +
            1 / ((n : ℝ) + 1) ^ 4) +
          1 / (n + 1 : ℝ) := by
    have hn0 : 0 < (n : ℝ) := by
      exact_mod_cast (show 0 < n by omega)
    have hnminus : 0 < (n : ℝ) - 1 := by
      have h : (1 : ℝ) < n := by
        exact_mod_cast (show 1 < n by omega)
      linarith
    have hden :
        (1 / (n : ℝ) ^ 6) / (1 - 1 / (n : ℝ)) =
          1 / ((n : ℝ) ^ 5 * ((n : ℝ) - 1)) := by
      field_simp
    rw [hden]
    field_simp
    ring_nf
    have hn100 : (100 : ℝ) < n := by
      exact_mod_cast (show 100 < n by omega)
    have hprod : 0 < (n : ℝ) ^ 2 * ((n : ℝ) - 100) := by
      exact mul_pos (sq_pos_of_pos hn0) (sub_pos.mpr hn100)
    nlinarith
  have hstepL (n : ℕ) (hn : 10000 ≤ n) :
      (1 / (2 * (n : ℝ)) - 1 / (12 * (n : ℝ) ^ 2)) -
          (1 / (2 * ((n : ℝ) + 1)) - 1 / (12 * ((n : ℝ) + 1) ^ 2)) <
        ((harmonic n : ℝ) - Real.log (n : ℝ)) -
          ((harmonic (n + 1) : ℝ) - Real.log (n + 1)) := by
    rw [hstepA n (by omega)]
    linarith [hloglo n (by omega), hrat n hn]
  have hstepU (n : ℕ) (hn : 10000 ≤ n) :
      ((harmonic n : ℝ) - Real.log (n : ℝ)) -
          ((harmonic (n + 1) : ℝ) - Real.log (n + 1)) <
        ((1 / (2 * (n : ℝ)) - 1 / (12 * (n : ℝ) ^ 2)) +
            1 / (n : ℝ) ^ 4) -
          ((1 / (2 * ((n : ℝ) + 1)) - 1 / (12 * ((n : ℝ) + 1) ^ 2)) +
            1 / ((n : ℝ) + 1) ^ 4) := by
    rw [hstepA n (by omega)]
    linarith [hloghi n (by omega), hratU n hn]
  have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hqL :
      Tendsto
        (fun n : ℕ => 1 / (2 * (n : ℝ)) - 1 / (12 * (n : ℝ) ^ 2))
        atTop (nhds 0) := by
    have hsq := hinv.pow 2
    have hfirst :
        Tendsto (fun n : ℕ => (1 / 2 : ℝ) * (1 / (n : ℝ)))
          atTop (nhds 0) := by
      simpa using
        (tendsto_const_nhds.mul hinv :
          Tendsto (fun n : ℕ => (1 / 2 : ℝ) * (1 / (n : ℝ)))
            atTop (nhds ((1 / 2 : ℝ) * 0)))
    have hsecond :
        Tendsto (fun n : ℕ => (1 / 12 : ℝ) * (1 / (n : ℝ)) ^ 2)
          atTop (nhds 0) := by
      simpa using
        (tendsto_const_nhds.mul hsq :
          Tendsto (fun n : ℕ => (1 / 12 : ℝ) * (1 / (n : ℝ)) ^ 2)
            atTop (nhds ((1 / 12 : ℝ) * (0 ^ 2))))
    have hsub := hfirst.sub hsecond
    convert hsub using 1
    · funext n
      ring
    · norm_num
  have hqU :
      Tendsto
        (fun n : ℕ =>
          (1 / (2 * (n : ℝ)) - 1 / (12 * (n : ℝ) ^ 2)) + 1 / (n : ℝ) ^ 4)
        atTop (nhds 0) := by
    have hpow4 := hinv.pow 4
    convert hqL.add hpow4 using 1 <;>
      try simp [div_eq_mul_inv, mul_comm, mul_left_comm, pow_succ]
  let F : ℕ → ℝ := fun n =>
    (harmonic n : ℝ) - Real.log (n : ℝ) -
      (1 / (2 * (n : ℝ)) - 1 / (12 * (n : ℝ) ^ 2))
  let G : ℕ → ℝ := fun n =>
    (harmonic n : ℝ) - Real.log (n : ℝ) -
      ((1 / (2 * (n : ℝ)) - 1 / (12 * (n : ℝ) ^ 2)) + 1 / (n : ℝ) ^ 4)
  have hlimF : Tendsto F atTop (nhds chapter09EulerMascheroni) := by
    simpa [F, chapter09EulerMascheroni] using
      Real.tendsto_harmonic_sub_log.sub hqL
  have hlimG : Tendsto G atTop (nhds chapter09EulerMascheroni) := by
    simpa [G, chapter09EulerMascheroni] using
      Real.tendsto_harmonic_sub_log.sub hqU
  have hFstep (n : ℕ) (hn : 10000 ≤ n) : F (n + 1) < F n := by
    dsimp [F]
    have hs := hstepL n hn
    norm_num [Nat.cast_add, Nat.cast_one] at hs ⊢
    linarith [hs]
  have hGstep (n : ℕ) (hn : 10000 ≤ n) : G n < G (n + 1) := by
    dsimp [G]
    have hs := hstepU n hn
    norm_num [Nat.cast_add, Nat.cast_one] at hs ⊢
    linarith [hs]
  have hFbound (m : ℕ) (hm : 10001 ≤ m) : F m ≤ F 10001 := by
    induction m, hm using Nat.le_induction with
    | base => exact le_rfl
    | @succ m hm ih =>
      exact (hFstep m (by omega)).le.trans ih
  have hGbound (m : ℕ) (hm : 10001 ≤ m) : G 10001 ≤ G m := by
    induction m, hm using Nat.le_induction with
    | base => exact le_rfl
    | @succ m hm ih =>
      exact ih.trans (hGstep m (by omega)).le
  have hgamma_le_F10001 :
      chapter09EulerMascheroni ≤ F 10001 := by
    apply le_of_tendsto hlimF
    exact eventually_atTop.2 ⟨10001, fun m hm => hFbound m hm⟩
  have hG10001_le_gamma :
      G 10001 ≤ chapter09EulerMascheroni := by
    apply ge_of_tendsto hlimG
    exact eventually_atTop.2 ⟨10001, fun m hm => hGbound m hm⟩
  have hgamma_upper_at_N :
      chapter09EulerMascheroni < F 10000 := by
    have hs := hFstep 10000 (by norm_num)
    exact lt_of_le_of_lt hgamma_le_F10001 hs
  have hgamma_lower_at_N :
      G 10000 < chapter09EulerMascheroni := by
    have hs := hGstep 10000 (by norm_num)
    exact lt_of_lt_of_le hs hG10001_le_gamma
  have hlog2 :=
    Real.sum_range_sub_log_div_le (x := (1 / 3 : ℝ)) (by norm_num) 20
  norm_num at hlog2
  have hlog54 :=
    Real.sum_range_sub_log_div_le (x := (1 / 9 : ℝ)) (by norm_num) 10
  norm_num at hlog54
  have hlogN : Real.log (10000 : ℝ) =
      12 * Real.log 2 + 4 * Real.log (5 / 4 : ℝ) := by
    calc
      Real.log (10000 : ℝ) =
          Real.log ((2 : ℝ) ^ 12 * (5 / 4 : ℝ) ^ 4) := by norm_num
      _ = Real.log ((2 : ℝ) ^ 12) + Real.log ((5 / 4 : ℝ) ^ 4) := by
        rw [Real.log_mul] <;> norm_num
      _ = 12 * Real.log 2 + 4 * Real.log (5 / 4 : ℝ) := by
        rw [Real.log_pow, Real.log_pow]
        norm_num
  have h2u := (abs_le.mp hlog2).2
  have h54u := (abs_le.mp hlog54).2
  have hgammaLowerNumeric :
      (chapter09GammaLower : ℝ) <
        (harmonic 10000 : ℝ) - Real.log 10000 -
          ((1 / (2 * 10000) - 1 / (12 * 10000 ^ 2)) + 1 / (10000 : ℝ) ^ 4) := by
    rw [hlogN]
    set_option maxRecDepth 1000000 in
      norm_num [harmonic, Finset.sum_range_succ, chapter09GammaLower] at ⊢
    nlinarith [h2u, h54u]
  have h2l := (abs_le.mp hlog2).1
  have h54l := (abs_le.mp hlog54).1
  have hgammaUpperNumeric :
      (harmonic 10000 : ℝ) - Real.log 10000 -
          (1 / (2 * 10000) - 1 / (12 * 10000 ^ 2)) <
        (chapter09GammaUpper : ℝ) := by
    rw [hlogN]
    have hsplit (k : ℕ) :
        harmonic (k + 1000) =
          harmonic k +
            (∑ i ∈ Finset.range 1000, ((↑(k + i + 1) : ℚ))⁻¹) := by
      rw [harmonic, harmonic, Finset.sum_range_add]
    have h0 :
        harmonic 1000 =
          harmonic 0 +
            (∑ i ∈ Finset.range 1000, ((↑(0 + i + 1) : ℚ))⁻¹) := by
      exact hsplit 0
    have h1 :
        harmonic 2000 =
          harmonic 1000 +
            (∑ i ∈ Finset.range 1000, ((↑(1000 + i + 1) : ℚ))⁻¹) := by
      exact hsplit 1000
    have h2 :
        harmonic 3000 =
          harmonic 2000 +
            (∑ i ∈ Finset.range 1000, ((↑(2000 + i + 1) : ℚ))⁻¹) := by
      exact hsplit 2000
    have h3 :
        harmonic 4000 =
          harmonic 3000 +
            (∑ i ∈ Finset.range 1000, ((↑(3000 + i + 1) : ℚ))⁻¹) := by
      exact hsplit 3000
    have h4 :
        harmonic 5000 =
          harmonic 4000 +
            (∑ i ∈ Finset.range 1000, ((↑(4000 + i + 1) : ℚ))⁻¹) := by
      exact hsplit 4000
    have h5 :
        harmonic 6000 =
          harmonic 5000 +
            (∑ i ∈ Finset.range 1000, ((↑(5000 + i + 1) : ℚ))⁻¹) := by
      exact hsplit 5000
    have h6 :
        harmonic 7000 =
          harmonic 6000 +
            (∑ i ∈ Finset.range 1000, ((↑(6000 + i + 1) : ℚ))⁻¹) := by
      exact hsplit 6000
    have h7 :
        harmonic 8000 =
          harmonic 7000 +
            (∑ i ∈ Finset.range 1000, ((↑(7000 + i + 1) : ℚ))⁻¹) := by
      exact hsplit 7000
    have h8 :
        harmonic 9000 =
          harmonic 8000 +
            (∑ i ∈ Finset.range 1000, ((↑(8000 + i + 1) : ℚ))⁻¹) := by
      exact hsplit 8000
    have h9 :
        harmonic 10000 =
          harmonic 9000 +
            (∑ i ∈ Finset.range 1000, ((↑(9000 + i + 1) : ℚ))⁻¹) := by
      exact hsplit 9000
    have hsum :
        harmonic 10000 =
          (∑ i ∈ Finset.range 1000, ((↑(0 + i + 1) : ℚ))⁻¹) +
          (∑ i ∈ Finset.range 1000, ((↑(1000 + i + 1) : ℚ))⁻¹) +
          (∑ i ∈ Finset.range 1000, ((↑(2000 + i + 1) : ℚ))⁻¹) +
          (∑ i ∈ Finset.range 1000, ((↑(3000 + i + 1) : ℚ))⁻¹) +
          (∑ i ∈ Finset.range 1000, ((↑(4000 + i + 1) : ℚ))⁻¹) +
          (∑ i ∈ Finset.range 1000, ((↑(5000 + i + 1) : ℚ))⁻¹) +
          (∑ i ∈ Finset.range 1000, ((↑(6000 + i + 1) : ℚ))⁻¹) +
          (∑ i ∈ Finset.range 1000, ((↑(7000 + i + 1) : ℚ))⁻¹) +
          (∑ i ∈ Finset.range 1000, ((↑(8000 + i + 1) : ℚ))⁻¹) +
          (∑ i ∈ Finset.range 1000, ((↑(9000 + i + 1) : ℚ))⁻¹) := by
      have hz : harmonic 0 = 0 := by
        simp [harmonic]
      rw [h9, h8, h7, h6, h5, h4, h3, h2, h1, h0, hz, zero_add]
    have hblock0 :
        (∑ i ∈ Finset.range 1000, ((↑(0 + i + 1) : ℚ))⁻¹) <
          7485470860550344913 / 10 ^ 18 := by
      set_option maxRecDepth 1000000 in
        set_option maxHeartbeats 10000000 in
          norm_num [Finset.sum_range_succ]
    have hblock1 :
        (∑ i ∈ Finset.range 1000, ((↑(1000 + i + 1) : ℚ))⁻¹) <
          692897243059937497 / 10 ^ 18 := by
      set_option maxRecDepth 1000000 in
        set_option maxHeartbeats 10000000 in
          norm_num [Finset.sum_range_succ]
    have hblock2 :
        (∑ i ∈ Finset.range 1000, ((↑(2000 + i + 1) : ℚ))⁻¹) <
          405381786348904705 / 10 ^ 18 := by
      set_option maxRecDepth 1000000 in
        set_option maxHeartbeats 10000000 in
          norm_num [Finset.sum_range_succ]
    have hblock3 :
        (∑ i ∈ Finset.range 1000, ((↑(3000 + i + 1) : ℚ))⁻¹) <
          287640409836040117 / 10 ^ 18 := by
      set_option maxRecDepth 1000000 in
        set_option maxHeartbeats 10000000 in
          norm_num [Finset.sum_range_succ]
    have hblock4 :
        (∑ i ∈ Finset.range 1000, ((↑(4000 + i + 1) : ℚ))⁻¹) <
          223118553189209737 / 10 ^ 18 := by
      have hs4 :
          (∑ i ∈ Finset.range 1000, ((↑(4000 + i + 1) : ℚ))⁻¹) =
            (∑ i ∈ Finset.range 500, ((↑(4000 + i + 1) : ℚ))⁻¹) +
              (∑ i ∈ Finset.range 500,
                ((↑(4000 + (500 + i) + 1) : ℚ))⁻¹) := by
        rw [show (1000 : ℕ) = 500 + 500 by norm_num, Finset.sum_range_add]
      rw [hs4]
      set_option maxRecDepth 1000000 in
        set_option maxHeartbeats 10000000 in
          norm_num [Finset.sum_range_succ]
    have hblock5 :
        (∑ i ∈ Finset.range 1000, ((↑(5000 + i + 1) : ℚ))⁻¹) <
          182304891145806472 / 10 ^ 18 := by
      set_option maxRecDepth 1000000 in
        set_option maxHeartbeats 10000000 in
          norm_num [Finset.sum_range_succ]
    have hblock6 :
        (∑ i ∈ Finset.range 1000, ((↑(6000 + i + 1) : ℚ))⁻¹) <
          154138775679488083 / 10 ^ 18 := by
      set_option maxRecDepth 1000000 in
        set_option maxHeartbeats 10000000 in
          norm_num [Finset.sum_range_succ]
    have hblock7 :
        (∑ i ∈ Finset.range 1000, ((↑(7000 + i + 1) : ℚ))⁻¹) <
          133522464451690990 / 10 ^ 18 := by
      set_option maxRecDepth 1000000 in
        set_option maxHeartbeats 10000000 in
          norm_num [Finset.sum_range_succ]
    have hblock8 :
        (∑ i ∈ Finset.range 1000, ((↑(8000 + i + 1) : ℚ))⁻¹) <
          117776091485215759 / 10 ^ 18 := by
      set_option maxRecDepth 1000000 in
        set_option maxHeartbeats 10000000 in
          norm_num [Finset.sum_range_succ]
    have hblock9 :
        (∑ i ∈ Finset.range 1000, ((↑(9000 + i + 1) : ℚ))⁻¹) <
          105354960297743997 / 10 ^ 18 := by
      set_option maxRecDepth 1000000 in
        set_option maxHeartbeats 10000000 in
          norm_num [Finset.sum_range_succ]
    have hH : harmonic 10000 < 978760603604438227 / 10 ^ 17 := by
      rw [hsum]
      linarith [hblock0, hblock1, hblock2, hblock3, hblock4, hblock5, hblock6,
        hblock7, hblock8, hblock9]
    have hHreal :
        (harmonic 10000 : ℝ) < (978760603604438227 / 10 ^ 17 : ℝ) := by
      have hHreal' :
          (harmonic 10000 : ℝ) <
            ((978760603604438227 / 10 ^ 17 : ℚ) : ℝ) := by
        exact_mod_cast hH
      convert hHreal' using 1 <;> norm_num
    norm_num [chapter09GammaUpper] at ⊢
    set_option maxHeartbeats 10000000 in
      nlinarith [h2l, h54l]
  have hgammaLower :
      (chapter09GammaLower : ℝ) < chapter09EulerMascheroni := by
    apply lt_trans hgammaLowerNumeric
    convert hgamma_lower_at_N using 1 <;> norm_num [G] <;> rfl
  have hgammaUpper :
      chapter09EulerMascheroni < (chapter09GammaUpper : ℝ) := by
    apply lt_trans (by
      convert hgamma_upper_at_N using 1)
    exact hgammaUpperNumeric
  have hgammaLowerVal :
      (577215664901532 / 10 ^ 15 : ℝ) < chapter09EulerMascheroni := by
    simpa [chapter09GammaLower] using hgammaLower
  have hgammaUpperVal :
      chapter09EulerMascheroni < (577215664901533 / 10 ^ 15 : ℝ) := by
    simpa [chapter09GammaUpper] using hgammaUpper
  have hgammaPos : 0 < chapter09EulerMascheroni := by
    exact lt_trans (by norm_num) hgammaLowerVal
  have hgammaBelowOne : chapter09EulerMascheroni < 1 := by
    exact lt_trans hgammaUpperVal (by norm_num)
  have hexpg :
      |Real.exp chapter09EulerMascheroni -
          ∑ m ∈ Finset.range 16,
            chapter09EulerMascheroni ^ m / m.factorial| ≤
        |chapter09EulerMascheroni| ^ 16 *
          ((17 : ℝ) / (Nat.factorial 16 * 16)) := by
    apply Real.exp_bound
    · rw [abs_of_pos]
      · linarith [hgammaBelowOne]
      · exact hgammaPos
    · norm_num
  have hgl :
      (178107241799019 / 10 ^ 14 : ℝ) <
        Real.exp chapter09EulerMascheroni := by
    have hPlo :
        ∑ m ∈ Finset.range 16,
            (577215664901532 / 10 ^ 15 : ℝ) ^ m / m.factorial ≤
          ∑ m ∈ Finset.range 16,
            chapter09EulerMascheroni ^ m / m.factorial := by
      gcongr
    have hE :
        |chapter09EulerMascheroni| ^ 16 *
            ((17 : ℝ) / (Nat.factorial 16 * 16)) ≤
          (577215664901533 / 10 ^ 15 : ℝ) ^ 16 *
            ((17 : ℝ) / (Nat.factorial 16 * 16)) := by
      rw [abs_of_pos]
      · gcongr
      · exact hgammaPos
    have hh := (abs_le.mp hexpg).1
    set_option maxRecDepth 1000000 in
      norm_num [Finset.sum_range_succ] at hh hPlo hE ⊢
    nlinarith [hh, hPlo, hE]
  have hgu :
      Real.exp chapter09EulerMascheroni <
        (178107241799021 / 10 ^ 14 : ℝ) := by
    have hPhi :
        ∑ m ∈ Finset.range 16,
            chapter09EulerMascheroni ^ m / m.factorial ≤
          ∑ m ∈ Finset.range 16,
            (577215664901533 / 10 ^ 15 : ℝ) ^ m / m.factorial := by
      gcongr
    have hE :
        |chapter09EulerMascheroni| ^ 16 *
            ((17 : ℝ) / (Nat.factorial 16 * 16)) ≤
          (577215664901533 / 10 ^ 15 : ℝ) ^ 16 *
            ((17 : ℝ) / (Nat.factorial 16 * 16)) := by
      rw [abs_of_pos]
      · gcongr
      · exact hgammaPos
    have hh := (abs_le.mp hexpg).2
    set_option maxRecDepth 1000000 in
      norm_num [Finset.sum_range_succ] at hh hPhi hE ⊢
    nlinarith [hh, hPhi, hE]
  have h1L : (271828182845904 / 10 ^ 14 : ℝ) < Real.exp 1 := by
    have hh := (abs_le.mp Real.exp_one_near_20).1
    norm_num at hh ⊢
    linarith
  have h1U : Real.exp 1 < (271828182845906 / 10 ^ 14 : ℝ) := by
    have hh := (abs_le.mp Real.exp_one_near_20).2
    norm_num at hh ⊢
    linarith
  have hdL : (570796326794896 / 10 ^ 15 : ℝ) < Real.pi / 2 - 1 := by
    linarith [hpiL]
  have hdU : Real.pi / 2 - 1 < (570796326794898 / 10 ^ 15 : ℝ) := by
    linarith [hpiU]
  have hexpd :
      |Real.exp (Real.pi / 2 - 1) -
          ∑ m ∈ Finset.range 16, (Real.pi / 2 - 1) ^ m / m.factorial| ≤
        |Real.pi / 2 - 1| ^ 16 *
          ((17 : ℝ) / (Nat.factorial 16 * 16)) := by
    apply Real.exp_bound
    · rw [abs_of_pos]
      · linarith [hpiL]
      · linarith [hpiL]
    · norm_num
  have hexpdlo :
      (17696757306773 / 10 ^ 13 : ℝ) <
        Real.exp (Real.pi / 2 - 1) := by
    have hPdlo :
        ∑ m ∈ Finset.range 16,
            (570796326794896 / 10 ^ 15 : ℝ) ^ m / m.factorial ≤
          ∑ m ∈ Finset.range 16,
            (Real.pi / 2 - 1) ^ m / m.factorial := by
      gcongr <;> linarith [hdL]
    have hE :
        |Real.pi / 2 - 1| ^ 16 * ((17 : ℝ) / (Nat.factorial 16 * 16)) ≤
          (570796326794898 / 10 ^ 15 : ℝ) ^ 16 *
            ((17 : ℝ) / (Nat.factorial 16 * 16)) := by
      rw [abs_of_pos]
      · gcongr <;> linarith [hdU]
      · linarith [hpiL]
    have hh := (abs_le.mp hexpd).1
    set_option maxRecDepth 1000000 in
      norm_num [Finset.sum_range_succ] at hh hPdlo hE ⊢
    nlinarith [hh, hPdlo, hE]
  have hexpdhi :
      Real.exp (Real.pi / 2 - 1) <
        (17696757306774 / 10 ^ 13 : ℝ) := by
    have hPdhi :
        ∑ m ∈ Finset.range 16,
            (Real.pi / 2 - 1) ^ m / m.factorial ≤
          ∑ m ∈ Finset.range 16,
            (570796326794898 / 10 ^ 15 : ℝ) ^ m / m.factorial := by
      gcongr <;> linarith [hdU]
    have hE :
        |Real.pi / 2 - 1| ^ 16 * ((17 : ℝ) / (Nat.factorial 16 * 16)) ≤
          (570796326794898 / 10 ^ 15 : ℝ) ^ 16 *
            ((17 : ℝ) / (Nat.factorial 16 * 16)) := by
      rw [abs_of_pos]
      · gcongr <;> linarith [hdU]
      · linarith [hpiL]
    have hh := (abs_le.mp hexpd).2
    set_option maxRecDepth 1000000 in
      norm_num [Finset.sum_range_succ] at hh hPdhi hE ⊢
    nlinarith [hh, hPdhi, hE]
  have hzL :
      (chapter09UnconditionalEndpointZeroLower : ℝ) <
        chapter09UnconditionalEndpointZero := by
    dsimp [chapter09UnconditionalEndpointZero]
    calc
      (chapter09UnconditionalEndpointZeroLower : ℝ) <
          4 * (3141592653589793 / 10 ^ 15 : ℝ) *
            (178107241799019 / 10 ^ 14 : ℝ) := by
              norm_num [chapter09UnconditionalEndpointZeroLower]
      _ < 4 * Real.pi * Real.exp chapter09EulerMascheroni := by
              gcongr
  have hzU :
      chapter09UnconditionalEndpointZero <
        (chapter09UnconditionalEndpointZeroUpper : ℝ) := by
    dsimp [chapter09UnconditionalEndpointZero]
    calc
      4 * Real.pi * Real.exp chapter09EulerMascheroni <
          4 * (3141592653589794 / 10 ^ 15 : ℝ) *
            (178107241799021 / 10 ^ 14 : ℝ) := by
              gcongr
      _ < (chapter09UnconditionalEndpointZeroUpper : ℝ) := by
              norm_num [chapter09UnconditionalEndpointZeroUpper]
  have hfactorOne :
      Real.exp (1 + chapter09EulerMascheroni) =
        Real.exp 1 * Real.exp chapter09EulerMascheroni := by
    rw [Real.exp_add]
  have honeL :
      (chapter09UnconditionalEndpointOneLower : ℝ) <
        chapter09UnconditionalEndpointOne := by
    dsimp [chapter09UnconditionalEndpointOne]
    rw [hfactorOne]
    calc
      (chapter09UnconditionalEndpointOneLower : ℝ) <
          4 * (3141592653589793 / 10 ^ 15 : ℝ) *
            ((271828182845904 / 10 ^ 14 : ℝ) *
              (178107241799019 / 10 ^ 14 : ℝ)) := by
              norm_num [chapter09UnconditionalEndpointOneLower]
      _ < 4 * Real.pi *
          (Real.exp 1 * Real.exp chapter09EulerMascheroni) := by
              gcongr
  have honeU :
      chapter09UnconditionalEndpointOne <
        (chapter09UnconditionalEndpointOneUpper : ℝ) := by
    dsimp [chapter09UnconditionalEndpointOne]
    rw [hfactorOne]
    calc
      4 * Real.pi * (Real.exp 1 * Real.exp chapter09EulerMascheroni) <
          4 * (3141592653589794 / 10 ^ 15 : ℝ) *
            ((271828182845906 / 10 ^ 14 : ℝ) *
              (178107241799021 / 10 ^ 14 : ℝ)) := by
              gcongr
      _ < (chapter09UnconditionalEndpointOneUpper : ℝ) := by
              norm_num [chapter09UnconditionalEndpointOneUpper]
  have hgrhzL :
      (chapter09GRHEndpointZeroLower : ℝ) < chapter09GRHEndpointZero := by
    dsimp [chapter09GRHEndpointZero]
    calc
      (chapter09GRHEndpointZeroLower : ℝ) <
          8 * (3141592653589793 / 10 ^ 15 : ℝ) *
            (178107241799019 / 10 ^ 14 : ℝ) := by
              norm_num [chapter09GRHEndpointZeroLower]
      _ < 8 * Real.pi * Real.exp chapter09EulerMascheroni := by
              gcongr
  have hgrhzU :
      chapter09GRHEndpointZero <
        (chapter09GRHEndpointZeroUpper : ℝ) := by
    dsimp [chapter09GRHEndpointZero]
    calc
      8 * Real.pi * Real.exp chapter09EulerMascheroni <
          8 * (3141592653589794 / 10 ^ 15 : ℝ) *
            (178107241799021 / 10 ^ 14 : ℝ) := by
              gcongr
      _ < (chapter09GRHEndpointZeroUpper : ℝ) := by
              norm_num [chapter09GRHEndpointZeroUpper]
  have hfactorGrh :
      Real.exp (chapter09EulerMascheroni + Real.pi / 2) =
        Real.exp 1 *
          (Real.exp chapter09EulerMascheroni *
            Real.exp (Real.pi / 2 - 1)) := by
    calc
      Real.exp (chapter09EulerMascheroni + Real.pi / 2) =
          Real.exp (1 + (chapter09EulerMascheroni + (Real.pi / 2 - 1))) := by
            congr 1; ring
      _ = Real.exp 1 *
          (Real.exp chapter09EulerMascheroni *
            Real.exp (Real.pi / 2 - 1)) := by
            rw [Real.exp_add, Real.exp_add]
  have hgrhprodL :
      (271828182845904 / 10 ^ 14 : ℝ) *
          ((178107241799019 / 10 ^ 14 : ℝ) *
            (17696757306773 / 10 ^ 13 : ℝ)) <
        Real.exp 1 *
          (Real.exp chapter09EulerMascheroni *
            Real.exp (Real.pi / 2 - 1)) := by
    gcongr
  have hgrhprodU :
      Real.exp 1 *
          (Real.exp chapter09EulerMascheroni *
            Real.exp (Real.pi / 2 - 1)) <
        (271828182845906 / 10 ^ 14 : ℝ) *
          ((178107241799021 / 10 ^ 14 : ℝ) *
            (17696757306774 / 10 ^ 13 : ℝ)) := by
    gcongr
  have hgrhoneL :
      (chapter09GRHEndpointOneLower : ℝ) < chapter09GRHEndpointOne := by
    dsimp [chapter09GRHEndpointOne]
    rw [hfactorGrh]
    calc
      (chapter09GRHEndpointOneLower : ℝ) <
          8 * (3141592653589793 / 10 ^ 15 : ℝ) *
            ((271828182845904 / 10 ^ 14 : ℝ) *
              ((178107241799019 / 10 ^ 14 : ℝ) *
                (17696757306773 / 10 ^ 13 : ℝ))) := by
              norm_num [chapter09GRHEndpointOneLower]
      _ < 8 * Real.pi *
          (Real.exp 1 *
            (Real.exp chapter09EulerMascheroni *
              Real.exp (Real.pi / 2 - 1))) := by
              gcongr
  have hgrhoneU :
      chapter09GRHEndpointOne <
        (chapter09GRHEndpointOneUpper : ℝ) := by
    dsimp [chapter09GRHEndpointOne]
    rw [hfactorGrh]
    calc
      8 * Real.pi *
          (Real.exp 1 *
            (Real.exp chapter09EulerMascheroni *
              Real.exp (Real.pi / 2 - 1))) <
          8 * (3141592653589794 / 10 ^ 15 : ℝ) *
            ((271828182845906 / 10 ^ 14 : ℝ) *
              ((178107241799021 / 10 ^ 14 : ℝ) *
                (17696757306774 / 10 ^ 13 : ℝ))) := by
              gcongr
      _ < (chapter09GRHEndpointOneUpper : ℝ) := by
              norm_num [chapter09GRHEndpointOneUpper]
  exact
    { gamma_directed_bounds := ⟨hgammaLower, hgammaUpper⟩
      unconditional_endpoint_zero_directed_bounds := ⟨hzL, hzU⟩
      unconditional_endpoint_one_directed_bounds := ⟨honeL, honeU⟩
      grh_endpoint_zero_directed_bounds := ⟨hgrhzL, hgrhzU⟩
      grh_endpoint_one_directed_bounds := ⟨hgrhoneL, hgrhoneU⟩ }

theorem chapter09_gamma_directed_bounds :
    (chapter09GammaLower : ℝ) < chapter09EulerMascheroni ∧
      chapter09EulerMascheroni < (chapter09GammaUpper : ℝ) := by
  exact Chapter09NumericalEnclosureInterface.gamma_directed_bounds
    chapter09NumericalEnclosure

theorem chapter09_unconditional_endpoint_zero_directed_bounds :
    (chapter09UnconditionalEndpointZeroLower : ℝ) <
        chapter09UnconditionalEndpointZero ∧
      chapter09UnconditionalEndpointZero <
        (chapter09UnconditionalEndpointZeroUpper : ℝ) := by
  exact Chapter09NumericalEnclosureInterface.unconditional_endpoint_zero_directed_bounds
    chapter09NumericalEnclosure

theorem chapter09_unconditional_endpoint_one_directed_bounds :
    (chapter09UnconditionalEndpointOneLower : ℝ) <
        chapter09UnconditionalEndpointOne ∧
      chapter09UnconditionalEndpointOne <
        (chapter09UnconditionalEndpointOneUpper : ℝ) := by
  exact Chapter09NumericalEnclosureInterface.unconditional_endpoint_one_directed_bounds
    chapter09NumericalEnclosure

theorem chapter09_grh_endpoint_zero_directed_bounds :
    (chapter09GRHEndpointZeroLower : ℝ) < chapter09GRHEndpointZero ∧
      chapter09GRHEndpointZero < (chapter09GRHEndpointZeroUpper : ℝ) := by
  exact Chapter09NumericalEnclosureInterface.grh_endpoint_zero_directed_bounds
    chapter09NumericalEnclosure

theorem chapter09_grh_endpoint_one_directed_bounds :
    (chapter09GRHEndpointOneLower : ℝ) < chapter09GRHEndpointOne ∧
      chapter09GRHEndpointOne < (chapter09GRHEndpointOneUpper : ℝ) := by
  exact Chapter09NumericalEnclosureInterface.grh_endpoint_one_directed_bounds
    chapter09NumericalEnclosure

def chapter09RealProportion (K : Type*) [Field K] [NumberField K] : ℝ :=
  (chapter09RealPlaceCount K : ℝ) / (chapter09Degree K : ℝ)

theorem chapter09_signature_formula
    (K : Type*) [Field K] [NumberField K] :
    chapter09RealPlaceCount K + 2 * chapter09ComplexPlaceCount K =
      chapter09Degree K := by
  simpa [chapter09RealPlaceCount, chapter09ComplexPlaceCount, chapter09Degree] using
    (NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K)

theorem chapter09_degree_pos
    (K : Type*) [Field K] [NumberField K] :
    0 < chapter09Degree K := by
  exact Module.finrank_pos

theorem chapter09_absolute_discriminant_pos
    (K : Type*) [Field K] [NumberField K] :
    0 < chapter09AbsoluteDiscriminant K := by
  rw [chapter09AbsoluteDiscriminant, abs_pos]
  exact_mod_cast NumberField.discr_ne_zero K

theorem chapter09_root_discriminant_pos
    (K : Type*) [Field K] [NumberField K] :
    0 < chapter09RootDiscriminant K := by
  rw [chapter09RootDiscriminant]
  exact Real.rpow_pos_of_pos (chapter09_absolute_discriminant_pos K) _

theorem chapter09_root_discriminant_eq_canonical
    (K : Type*) [Field K] [NumberField K] :
    chapter09RootDiscriminant K = NumberField.rootDiscr K := by
  rw [chapter09RootDiscriminant, NumberField.rootDiscr_def]
  simp [chapter09AbsoluteDiscriminant, chapter09Degree, Int.cast_abs]

theorem chapter09_real_proportion_mem_Icc
    (K : Type*) [Field K] [NumberField K] :
    chapter09RealProportion K ∈ Set.Icc (0 : ℝ) 1 := by
  have hdeg : 0 < chapter09Degree K := Module.finrank_pos
  have hreal : chapter09RealPlaceCount K ≤ chapter09Degree K := by
    have hsig := chapter09_signature_formula K
    omega
  constructor
  · unfold chapter09RealProportion
    positivity
  · unfold chapter09RealProportion
    have hdegR : 0 < (chapter09Degree K : ℝ) := by exact_mod_cast hdeg
    exact (div_le_one hdegR).2 (by exact_mod_cast hreal)

/- The nontrivial-zero support is tied to the completed-zeta function used by
   the preceding analytic package.  This keeps possible boundary zeros in the
   support; the source's unconditional strip-positivity argument explicitly
   includes those endpoints.  Multiplicities and the functional-equation
   package remain upstream data; this interface only supplies support. -/
def chapter09NontrivialCompletedDedekindZetaZero
    (K : Type*) [Field K] [NumberField K] (ρ : ℂ) : Prop :=
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06.chapter06Xi K ρ = 0

class Chapter09ZetaZeroInterface
    (K : Type*) [Field K] [NumberField K] where
  nontrivialZeros : Set ℂ
  nontrivialZeros_spec :
    ∀ ρ, ρ ∈ nontrivialZeros ↔
      chapter09NontrivialCompletedDedekindZetaZero K ρ

theorem chapter09_zeta_zero_interface_eq_canonical_zero_support
    (K : Type*) [Field K] [NumberField K]
    [Chapter09ZetaZeroInterface K] :
    Chapter09ZetaZeroInterface.nontrivialZeros (K := K) =
      LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06.chapter06CanonicalZeroSupport K := by
  ext ρ
  rw [Chapter09ZetaZeroInterface.nontrivialZeros_spec]
  rfl

def chapter09GRHOnZeros (zeros : Set ℂ) : Prop :=
  ∀ ρ ∈ zeros, ρ.re = 1 / 2

def chapter09GRH
    (K : Type*) [Field K] [NumberField K]
    [Chapter09ZetaZeroInterface K] : Prop :=
  chapter09GRHOnZeros
    (Chapter09ZetaZeroInterface.nontrivialZeros (K := K))

abbrev Chapter09TestFunction := ℝ → ℝ

def chapter09TriangularAutocorrelation (T : ℝ) : Chapter09TestFunction :=
  fun x => max (1 - |x| / T) 0

def chapter09UnconditionalTestFunction (T : ℝ) : Chapter09TestFunction :=
  fun x => chapter09TriangularAutocorrelation T x / Real.cosh (x / 2)

def chapter09GRHTestFunction (T : ℝ) : Chapter09TestFunction :=
  chapter09TriangularAutocorrelation T

def chapter09A (F : Chapter09TestFunction) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), F x * Real.cosh (x / 2)

def chapter09B (F : Chapter09TestFunction) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), (1 - F x) / (2 * Real.sinh (x / 2))

def chapter09C (F : Chapter09TestFunction) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), (1 - F x) / (2 * Real.cosh (x / 2))

def chapter09BT (T : ℝ) : ℝ :=
  chapter09B (chapter09UnconditionalTestFunction T)

def chapter09CT (T : ℝ) : ℝ :=
  chapter09C (chapter09UnconditionalTestFunction T)

def chapter09GRHBT (T : ℝ) : ℝ :=
  chapter09B (chapter09GRHTestFunction T)

def chapter09GRHCT (T : ℝ) : ℝ :=
  chapter09C (chapter09GRHTestFunction T)

def chapter09UnconditionalPoleIntegral (T : ℝ) : ℝ :=
  chapter09A (chapter09UnconditionalTestFunction T)

def chapter09GRHPoleIntegral (T : ℝ) : ℝ :=
  chapter09A (chapter09GRHTestFunction T)

theorem chapter09_triangular_at_zero (T : ℝ) :
    chapter09TriangularAutocorrelation T 0 = 1 := by
  simp [chapter09TriangularAutocorrelation]

theorem chapter09_unconditional_test_function_at_zero (T : ℝ) :
    chapter09UnconditionalTestFunction T 0 = 1 := by
  simp [chapter09UnconditionalTestFunction, chapter09_triangular_at_zero]

theorem chapter09_grh_test_function_at_zero (T : ℝ) :
    chapter09GRHTestFunction T 0 = 1 := by
  exact chapter09_triangular_at_zero T

theorem chapter09_unconditional_pole_integral
    {T : ℝ} (hT : 0 < T) :
    chapter09UnconditionalPoleIntegral T = T / 2 := by
  simpa [chapter09UnconditionalPoleIntegral, chapter09A,
    chapter09UnconditionalTestFunction, chapter09TriangularAutocorrelation,
    Chapter08.chapter08A, Chapter08.chapter08FUnconditionalTriangle,
    Chapter08.chapter08TriangularAutocorrelation] using
    (Chapter08.chapter08_unconditional_triangle_A hT)

theorem chapter09_grh_pole_integral
    {T : ℝ} (hT : 0 < T) :
    chapter09GRHPoleIntegral T = 4 / T * (Real.cosh (T / 2) - 1) := by
  simpa [chapter09GRHPoleIntegral, chapter09A,
    chapter09GRHTestFunction, chapter09TriangularAutocorrelation,
    Chapter08.chapter08A, Chapter08.chapter08FGRHTriangle,
    Chapter08.chapter08TriangularAutocorrelation] using
    (Chapter08.chapter08_grh_triangle_A hT)

def chapter09UnconditionalExponent
    (K : Type*) [Field K] [NumberField K] (T : ℝ) : ℝ :=
  chapter09EulerMascheroni + Real.log (8 * Real.pi) +
      chapter09RealProportion K * (Real.pi / 2) -
    2 * T / (chapter09Degree K : ℝ) - chapter09BT T -
      chapter09RealProportion K * chapter09CT T

def chapter09GRHExponent
    (K : Type*) [Field K] [NumberField K] (T : ℝ) : ℝ :=
  chapter09EulerMascheroni + Real.log (8 * Real.pi) +
      chapter09RealProportion K * (Real.pi / 2) -
    4 * chapter09GRHPoleIntegral T / (chapter09Degree K : ℝ) -
      chapter09GRHBT T - chapter09RealProportion K * chapter09GRHCT T

/- A wrapper for varying number fields.  The zero set is carried as a field of
the model because the canonical completed-zeta object is supplied upstream. -/
structure Chapter09NumberFieldModel where
  K : Type*
  [field : Field K]
  [numberField : NumberField K]
  nontrivialZeros : Set ℂ
  nontrivialZeros_spec :
    ∀ ρ, ρ ∈ nontrivialZeros ↔
      chapter09NontrivialCompletedDedekindZetaZero K ρ

namespace Chapter09NumberFieldModel

def degree (M : Chapter09NumberFieldModel) : ℕ := by
  letI := M.field
  letI := M.numberField
  exact chapter09Degree M.K

def realProportion (M : Chapter09NumberFieldModel) : ℝ := by
  letI := M.field
  letI := M.numberField
  exact chapter09RealProportion M.K

def rootDiscriminant (M : Chapter09NumberFieldModel) : ℝ := by
  letI := M.field
  letI := M.numberField
  exact chapter09RootDiscriminant M.K

def satisfiesGRH (M : Chapter09NumberFieldModel) : Prop :=
  chapter09GRHOnZeros M.nontrivialZeros

/- A model carries its zero set as data, whereas the fieldwise GRH theorem
   consumes the chapter's zero-interface typeclass.  This constructor is the
   non-circular bridge needed when applying that theorem to a model member. -/
@[instance_reducible]
def zetaZeroInterface (M : Chapter09NumberFieldModel) :
    @Chapter09ZetaZeroInterface M.K M.field M.numberField := by
  letI := M.field
  letI := M.numberField
  exact
    { nontrivialZeros := M.nontrivialZeros
      nontrivialZeros_spec := M.nontrivialZeros_spec }

theorem degree_pos (M : Chapter09NumberFieldModel) : 0 < M.degree := by
  exact @chapter09_degree_pos M.K M.field M.numberField

theorem real_proportion_mem_Icc (M : Chapter09NumberFieldModel) :
    M.realProportion ∈ Set.Icc (0 : ℝ) 1 := by
  exact @chapter09_real_proportion_mem_Icc M.K M.field M.numberField

theorem root_discriminant_pos (M : Chapter09NumberFieldModel) :
    0 < M.rootDiscriminant := by
  exact @chapter09_root_discriminant_pos M.K M.field M.numberField

end Chapter09NumberFieldModel

structure Chapter09NumberFieldSequence where
  field : ℕ → Chapter09NumberFieldModel

def chapter09SequenceDegree (S : Chapter09NumberFieldSequence) : ℕ → ℕ :=
  fun j => (S.field j).degree

def chapter09SequenceRealProportion
    (S : Chapter09NumberFieldSequence) : ℕ → ℝ :=
  fun j => (S.field j).realProportion

def chapter09SequenceRootDiscriminant
    (S : Chapter09NumberFieldSequence) : ℕ → ℝ :=
  fun j => (S.field j).rootDiscriminant

def chapter09SequenceGRH (S : Chapter09NumberFieldSequence) (j : ℕ) : Prop :=
  chapter09GRHOnZeros (S.field j).nontrivialZeros

theorem chapter09_sequence_degree_pos
    (S : Chapter09NumberFieldSequence) (j : ℕ) :
    0 < chapter09SequenceDegree S j := by
  exact Chapter09NumberFieldModel.degree_pos (S.field j)

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter09
