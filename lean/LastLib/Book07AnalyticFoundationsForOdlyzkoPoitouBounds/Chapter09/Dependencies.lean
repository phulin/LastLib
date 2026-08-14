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

private theorem strictMul {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) (hc : 0 < c) (hb : 0 < b) :
    a * c < b * d :=
  lt_trans (mul_lt_mul_of_pos_right hab hc) (mul_lt_mul_of_pos_left hcd hb)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
private theorem gammaDirectedBounds :
    (chapter09GammaLower : ℝ) < chapter09EulerMascheroni ∧
      chapter09EulerMascheroni < (chapter09GammaUpper : ℝ) := by
  have hloglo (n : ℕ) (hn : 2 ≤ n) :
      (∑ i ∈ Finset.range 11,
          (-(1 / (n : ℝ))) ^ (i + 1) / (i + 1 : ℝ)) * (-1) -
          2 / (n : ℝ) ^ 12 ≤
        Real.log (1 + 1 / (n : ℝ)) := by
    have hlog :
        |(∑ i ∈ Finset.range 11, (-(1 / (n : ℝ))) ^ (i + 1) / (i + 1 : ℝ))
            + Real.log (1 - (-(1 / (n : ℝ))))| ≤
          |-(1 / (n : ℝ))| ^ (11 + 1) / (1 - |-(1 / (n : ℝ))|) := by
      apply Real.abs_log_sub_add_sum_range_le
      rw [abs_neg, abs_of_pos (by positivity)]
      apply (div_lt_one₀ (by positivity)).2
      exact_mod_cast hn
    norm_num [Finset.sum_range_succ, abs_of_pos, abs_of_nonneg] at hlog ⊢
    have hh := (abs_le.mp hlog).1
    have hx : 1 / (n : ℝ) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num)
      exact_mod_cast hn
    have hd : 0 < 1 - 1 / (n : ℝ) := by linarith
    have hi : 1 / (1 - 1 / (n : ℝ)) ≤ (2 : ℝ) := by
      apply (div_le_iff₀ hd).2
      linarith
    have hr :
        (1 / (n : ℝ) ^ 12) / (1 - 1 / (n : ℝ)) ≤
          2 / (n : ℝ) ^ 12 := by
      calc
        (1 / (n : ℝ) ^ 12) / (1 - 1 / (n : ℝ)) =
            (1 / (n : ℝ) ^ 12) * (1 / (1 - 1 / (n : ℝ))) := by ring
        _ ≤ (1 / (n : ℝ) ^ 12) * 2 :=
          mul_le_mul_of_nonneg_left hi (by positivity)
        _ = 2 / (n : ℝ) ^ 12 := by ring
    ring_nf at hr hh ⊢
    linarith
  have hloghi (n : ℕ) (hn : 2 ≤ n) :
      Real.log (1 + 1 / (n : ℝ)) ≤
        (∑ i ∈ Finset.range 11,
          (-(1 / (n : ℝ))) ^ (i + 1) / (i + 1 : ℝ)) * (-1) +
          2 / (n : ℝ) ^ 12 := by
    have hlog :
        |(∑ i ∈ Finset.range 11, (-(1 / (n : ℝ))) ^ (i + 1) / (i + 1 : ℝ))
            + Real.log (1 - (-(1 / (n : ℝ))))| ≤
          |-(1 / (n : ℝ))| ^ (11 + 1) / (1 - |-(1 / (n : ℝ))|) := by
      apply Real.abs_log_sub_add_sum_range_le
      rw [abs_neg, abs_of_pos (by positivity)]
      apply (div_lt_one₀ (by positivity)).2
      exact_mod_cast hn
    norm_num [Finset.sum_range_succ, abs_of_pos, abs_of_nonneg] at hlog ⊢
    have hh := (abs_le.mp hlog).2
    have hx : 1 / (n : ℝ) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num)
      exact_mod_cast hn
    have hd : 0 < 1 - 1 / (n : ℝ) := by linarith
    have hi : 1 / (1 - 1 / (n : ℝ)) ≤ (2 : ℝ) := by
      apply (div_le_iff₀ hd).2
      linarith
    have hr :
        (1 / (n : ℝ) ^ 12) / (1 - 1 / (n : ℝ)) ≤
          2 / (n : ℝ) ^ 12 := by
      calc
        (1 / (n : ℝ) ^ 12) / (1 - 1 / (n : ℝ)) =
            (1 / (n : ℝ) ^ 12) * (1 / (1 - 1 / (n : ℝ))) := by ring
        _ ≤ (1 / (n : ℝ) ^ 12) * 2 :=
          mul_le_mul_of_nonneg_left hi (by positivity)
        _ = 2 / (n : ℝ) ^ 12 := by ring
    ring_nf at hr hh ⊢
    linarith
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
  let qL : ℝ → ℝ := fun x =>
    1 / (2 * x) - 1 / (12 * x ^ 2) + 1 / (120 * x ^ 4) - 1 / (252 * x ^ 6)
  let qU : ℝ → ℝ := fun x => qL x + 1 / (240 * x ^ 8)
  have hratFastL (n : ℕ) (hn : 100 ≤ n) :
      qL n - qL (n + 1) + 1 / (n + 1 : ℝ) <
        (∑ i ∈ Finset.range 11,
          (-(1 / (n : ℝ))) ^ (i + 1) / (i + 1 : ℝ)) * (-1) -
          2 / (n : ℝ) ^ 12 := by
    have hn0 : (0 : ℝ) < n := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 100) hn)
    let x : ℝ := (n : ℝ) - 100
    have hnR : (100 : ℝ) ≤ n := by exact_mod_cast hn
    have hx : 0 ≤ x := by dsimp [x]; linarith
    have hnrep : (n : ℝ) = x + 100 := by dsimp [x]; ring
    rw [hnrep]
    simp only [qL]
    norm_num [Finset.sum_range_succ]
    field_simp [ne_of_gt hn0]
    ring_nf
    apply sub_pos.mp
    ring_nf
    positivity
  have hratFastU (n : ℕ) (hn : 100 ≤ n) :
      (∑ i ∈ Finset.range 11,
          (-(1 / (n : ℝ))) ^ (i + 1) / (i + 1 : ℝ)) * (-1) +
          2 / (n : ℝ) ^ 12 <
        qU n - qU (n + 1) + 1 / (n + 1 : ℝ) := by
    have hn0 : (0 : ℝ) < n := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 100) hn)
    let x : ℝ := (n : ℝ) - 100
    have hnR : (100 : ℝ) ≤ n := by exact_mod_cast hn
    have hx : 0 ≤ x := by dsimp [x]; linarith
    have hnrep : (n : ℝ) = x + 100 := by dsimp [x]; ring
    rw [hnrep]
    simp only [qU, qL]
    norm_num [Finset.sum_range_succ]
    field_simp [ne_of_gt hn0]
    ring_nf
    apply sub_pos.mp
    ring_nf
    positivity
  have hstepL (n : ℕ) (hn : 100 ≤ n) :
      qL n - qL (n + 1) <
        ((harmonic n : ℝ) - Real.log (n : ℝ)) -
          ((harmonic (n + 1) : ℝ) - Real.log (n + 1)) := by
    rw [hstepA n (by omega)]
    linarith [hloglo n (by omega), hratFastL n hn]
  have hstepU (n : ℕ) (hn : 100 ≤ n) :
      ((harmonic n : ℝ) - Real.log (n : ℝ)) -
          ((harmonic (n + 1) : ℝ) - Real.log (n + 1)) <
        qU n - qU (n + 1) := by
    rw [hstepA n (by omega)]
    linarith [hloghi n (by omega), hratFastU n hn]
  have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hqL :
      Tendsto (fun n : ℕ => qL n) atTop (nhds 0) := by
    have hterm (c : ℝ) (k : ℕ) (hk : 0 < k) :
        Tendsto (fun n : ℕ => c * (1 / (n : ℝ)) ^ k) atTop (nhds 0) := by
      simpa [zero_pow (Nat.ne_of_gt hk)] using
        (tendsto_const_nhds.mul (hinv.pow k) :
          Tendsto (fun n : ℕ => c * (1 / (n : ℝ)) ^ k)
            atTop (nhds (c * 0 ^ k)))
    have h := (((hterm (1 / 2) 1 (by norm_num)).sub
      (hterm (1 / 12) 2 (by norm_num))).add
      (hterm (1 / 120) 4 (by norm_num))).sub
      (hterm (1 / 252) 6 (by norm_num))
    convert h using 1
    · funext n
      dsimp [qL]
      ring
    · norm_num
  have hqU :
      Tendsto (fun n : ℕ => qU n) atTop (nhds 0) := by
    have hterm :
        Tendsto (fun n : ℕ => (1 / 240 : ℝ) * (1 / (n : ℝ)) ^ 8)
          atTop (nhds 0) := by
      simpa using
        (tendsto_const_nhds.mul (hinv.pow 8) :
          Tendsto (fun n : ℕ => (1 / 240 : ℝ) * (1 / (n : ℝ)) ^ 8)
            atTop (nhds ((1 / 240 : ℝ) * 0 ^ 8)))
    convert hqL.add hterm using 1
    · funext n
      dsimp [qU]
      ring
    · norm_num
  let F : ℕ → ℝ := fun n =>
    (harmonic n : ℝ) - Real.log (n : ℝ) - qL n
  let G : ℕ → ℝ := fun n =>
    (harmonic n : ℝ) - Real.log (n : ℝ) - qU n
  have hlimF : Tendsto F atTop (nhds chapter09EulerMascheroni) := by
    simpa [F, chapter09EulerMascheroni] using
      Real.tendsto_harmonic_sub_log.sub hqL
  have hlimG : Tendsto G atTop (nhds chapter09EulerMascheroni) := by
    simpa [G, chapter09EulerMascheroni] using
      Real.tendsto_harmonic_sub_log.sub hqU
  have hFstep (n : ℕ) (hn : 100 ≤ n) : F (n + 1) < F n := by
    dsimp [F]
    have hs := hstepL n hn
    norm_num [Nat.cast_add, Nat.cast_one] at hs ⊢
    linarith [hs]
  have hGstep (n : ℕ) (hn : 100 ≤ n) : G n < G (n + 1) := by
    dsimp [G]
    have hs := hstepU n hn
    norm_num [Nat.cast_add, Nat.cast_one] at hs ⊢
    linarith [hs]
  have hFbound (m : ℕ) (hm : 129 ≤ m) : F m ≤ F 129 := by
    induction m, hm using Nat.le_induction with
    | base => exact le_rfl
    | @succ m hm ih =>
      exact (hFstep m (by omega)).le.trans ih
  have hGbound (m : ℕ) (hm : 129 ≤ m) : G 129 ≤ G m := by
    induction m, hm using Nat.le_induction with
    | base => exact le_rfl
    | @succ m hm ih =>
      exact ih.trans (hGstep m (by omega)).le
  have hgamma_le_F129 :
      chapter09EulerMascheroni ≤ F 129 := by
    apply le_of_tendsto hlimF
    exact eventually_atTop.2 ⟨129, fun m hm => hFbound m hm⟩
  have hG129_le_gamma :
      G 129 ≤ chapter09EulerMascheroni := by
    apply ge_of_tendsto hlimG
    exact eventually_atTop.2 ⟨129, fun m hm => hGbound m hm⟩
  have hgamma_upper_at_N :
      chapter09EulerMascheroni < F 128 := by
    have hs := hFstep 128 (by norm_num)
    exact lt_of_le_of_lt hgamma_le_F129 hs
  have hgamma_lower_at_N :
      G 128 < chapter09EulerMascheroni := by
    have hs := hGstep 128 (by norm_num)
    exact lt_of_lt_of_le hs hG129_le_gamma
  have hlog2 :=
    Real.sum_range_sub_log_div_le (x := (1 / 3 : ℝ)) (by norm_num) 20
  norm_num at hlog2
  have hlogN : Real.log (128 : ℝ) = 7 * Real.log 2 := by
    calc
      Real.log (128 : ℝ) = Real.log ((2 : ℝ) ^ 7) := by norm_num
      _ = 7 * Real.log 2 := by rw [Real.log_pow]; norm_num
  have h2u := (abs_le.mp hlog2).2
  have hgammaLowerNumeric :
      (chapter09GammaLower : ℝ) <
        (harmonic 128 : ℝ) - Real.log 128 - qU 128 := by
    rw [hlogN]
    set_option maxRecDepth 1000000 in
      norm_num [harmonic, Finset.sum_range_succ, chapter09GammaLower, qU, qL] at ⊢
    nlinarith [h2u]
  have h2l := (abs_le.mp hlog2).1
  have hgammaUpperNumeric :
      (harmonic 128 : ℝ) - Real.log 128 - qL 128 <
        (chapter09GammaUpper : ℝ) := by
    rw [hlogN]
    set_option maxRecDepth 1000000 in
      norm_num [harmonic, Finset.sum_range_succ, chapter09GammaUpper, qL] at ⊢
    nlinarith [h2l]
  have hgammaLower :
      (chapter09GammaLower : ℝ) < chapter09EulerMascheroni := by
    apply lt_trans hgammaLowerNumeric
    convert hgamma_lower_at_N using 1
    all_goals norm_num [G]
    all_goals rfl
  have hgammaUpper :
      chapter09EulerMascheroni < (chapter09GammaUpper : ℝ) := by
    apply lt_trans (by
      convert hgamma_upper_at_N using 1)
    exact hgammaUpperNumeric
  exact ⟨hgammaLower, hgammaUpper⟩

private def expPartialQ (x : ℚ) : ℚ :=
  ∑ m ∈ Finset.range 16, x ^ m / m.factorial

private def expUpperQ (x : ℚ) : ℚ :=
  expPartialQ x + x ^ 16 * 17 / (Nat.factorial 16 * 16 : ℚ)

private structure RationalCertificates : Prop where
  endpointZeroLower :
    chapter09UnconditionalEndpointZeroLower <
      4 * (3141592653589793 / 10 ^ 15 : ℚ) *
        (178107241799019 / 10 ^ 14 : ℚ)
  endpointZeroUpper :
    4 * (3141592653589794 / 10 ^ 15 : ℚ) *
        (178107241799021 / 10 ^ 14 : ℚ) <
      chapter09UnconditionalEndpointZeroUpper
  endpointOneLower :
    chapter09UnconditionalEndpointOneLower <
      4 * (3141592653589793 / 10 ^ 15 : ℚ) *
        ((271828182845904 / 10 ^ 14 : ℚ) *
          (178107241799019 / 10 ^ 14 : ℚ))
  endpointOneUpper :
    4 * (3141592653589794 / 10 ^ 15 : ℚ) *
        ((271828182845906 / 10 ^ 14 : ℚ) *
          (178107241799021 / 10 ^ 14 : ℚ)) <
      chapter09UnconditionalEndpointOneUpper
  grhEndpointZeroLower :
    chapter09GRHEndpointZeroLower <
      8 * (3141592653589793 / 10 ^ 15 : ℚ) *
        (178107241799019 / 10 ^ 14 : ℚ)
  grhEndpointZeroUpper :
    8 * (3141592653589794 / 10 ^ 15 : ℚ) *
        (178107241799021 / 10 ^ 14 : ℚ) <
      chapter09GRHEndpointZeroUpper
  grhEndpointOneLower :
    chapter09GRHEndpointOneLower <
      8 * (3141592653589793 / 10 ^ 15 : ℚ) *
        ((271828182845904 / 10 ^ 14 : ℚ) *
          ((178107241799019 / 10 ^ 14 : ℚ) *
            (17696757306773 / 10 ^ 13 : ℚ)))
  grhEndpointOneUpper :
    8 * (3141592653589794 / 10 ^ 15 : ℚ) *
        ((271828182845906 / 10 ^ 14 : ℚ) *
          ((178107241799021 / 10 ^ 14 : ℚ) *
            (17696757306774 / 10 ^ 13 : ℚ))) <
      chapter09GRHEndpointOneUpper
  expGammaLower :
    (178107241799019 / 10 ^ 14 : ℚ) < expPartialQ chapter09GammaLower
  expGammaUpper :
    expUpperQ chapter09GammaUpper < (178107241799021 / 10 ^ 14 : ℚ)
  expDeltaLower :
    (17696757306773 / 10 ^ 13 : ℚ) <
      expPartialQ (570796326794896 / 10 ^ 15 : ℚ)
  expDeltaUpper :
    expUpperQ (570796326794898 / 10 ^ 15 : ℚ) <
      (17696757306774 / 10 ^ 13 : ℚ)

private theorem rationalCertificates : RationalCertificates := by
  constructor <;> native_decide

private theorem expBetweenOfRatBounds {x : ℝ} {l u L U : ℚ}
    (hl : (l : ℝ) < x) (hu : x < (u : ℝ))
    (hl0 : 0 ≤ l) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hL : L < expPartialQ l) (hU : expUpperQ u < U) :
    (L : ℝ) < Real.exp x ∧ Real.exp x < (U : ℝ) := by
  have hsumL :
      (L : ℝ) < ∑ m ∈ Finset.range 16, (l : ℝ) ^ m / m.factorial := by
    exact_mod_cast hL
  have hsumU :
      (∑ m ∈ Finset.range 16, (u : ℝ) ^ m / m.factorial) +
          (u : ℝ) ^ 16 * 17 / (Nat.factorial 16 * 16 : ℝ) < (U : ℝ) := by
    have hU' : ((expUpperQ u : ℚ) : ℝ) < (U : ℝ) := by
      exact_mod_cast hU
    simpa [expUpperQ, expPartialQ] using hU'
  have hexpU :
      Real.exp (u : ℝ) ≤
        (∑ m ∈ Finset.range 16, (u : ℝ) ^ m / m.factorial) +
          (u : ℝ) ^ 16 * 17 / (Nat.factorial 16 * 16 : ℝ) := by
    convert Real.exp_bound' (x := (u : ℝ))
      (by exact_mod_cast hu0) (by exact_mod_cast hu1)
      (by norm_num : 0 < 16) using 1
    all_goals norm_num
  constructor
  · exact hsumL.trans_le
      ((Real.sum_le_exp_of_nonneg (by exact_mod_cast hl0) 16).trans
        (Real.exp_lt_exp.mpr hl).le)
  · exact (Real.exp_lt_exp.mpr hu).trans_le (hexpU.trans hsumU.le)


private theorem piDirectedBounds :
    (3141592653589793 / 10 ^ 15 : ℝ) < Real.pi ∧
      Real.pi < (3141592653589794 / 10 ^ 15 : ℝ) := by
  constructor
  · exact lt_trans (by norm_num) Real.pi_gt_d20
  · exact lt_trans Real.pi_lt_d20 (by norm_num)

private theorem expGammaDirectedBounds :
    (178107241799019 / 10 ^ 14 : ℝ) <
        Real.exp chapter09EulerMascheroni ∧
      Real.exp chapter09EulerMascheroni <
        (178107241799021 / 10 ^ 14 : ℝ) := by
  obtain ⟨hL, hU⟩ := gammaDirectedBounds
  convert expBetweenOfRatBounds hL hU (by native_decide) (by native_decide)
    (by native_decide) rationalCertificates.expGammaLower
      rationalCertificates.expGammaUpper using 1 <;> norm_num

private theorem expDeltaDirectedBounds :
    (17696757306773 / 10 ^ 13 : ℝ) < Real.exp (Real.pi / 2 - 1) ∧
      Real.exp (Real.pi / 2 - 1) < (17696757306774 / 10 ^ 13 : ℝ) := by
  obtain ⟨hpiL, hpiU⟩ := piDirectedBounds
  have hdL : (570796326794896 / 10 ^ 15 : ℝ) < Real.pi / 2 - 1 := by
    linarith
  have hdU : Real.pi / 2 - 1 < (570796326794898 / 10 ^ 15 : ℝ) := by
    linarith
  have hdL' : ((570796326794896 / 10 ^ 15 : ℚ) : ℝ) < Real.pi / 2 - 1 := by
    convert hdL using 1
    all_goals norm_num
  have hdU' : Real.pi / 2 - 1 < ((570796326794898 / 10 ^ 15 : ℚ) : ℝ) := by
    convert hdU using 1
    all_goals norm_num
  convert expBetweenOfRatBounds
    (l := (570796326794896 / 10 ^ 15 : ℚ))
    (u := (570796326794898 / 10 ^ 15 : ℚ)) hdL' hdU'
    (by native_decide) (by native_decide) (by native_decide)
    rationalCertificates.expDeltaLower rationalCertificates.expDeltaUpper using 1 <;> norm_num

private theorem expOneDirectedBounds :
    (271828182845904 / 10 ^ 14 : ℝ) < Real.exp 1 ∧
      Real.exp 1 < (271828182845906 / 10 ^ 14 : ℝ) := by
  have hL := (abs_le.mp Real.exp_one_near_20).1
  have hU := (abs_le.mp Real.exp_one_near_20).2
  constructor <;> norm_num at hL hU ⊢ <;> linarith

private theorem strictScaledMul (k : ℝ) {a b c d : ℝ}
    (hk : 0 < k) (hab : a < b) (hcd : c < d) (hc : 0 < c) (hb : 0 < b) :
    k * a * c < k * b * d := by
  simpa only [mul_assoc] using
    mul_lt_mul_of_pos_left (strictMul hab hcd hc hb) hk

set_option maxRecDepth 1000000 in
theorem chapter09NumericalEnclosure :
    Chapter09NumericalEnclosureInterface := by
  obtain ⟨hgammaL, hgammaU⟩ := gammaDirectedBounds
  obtain ⟨hpiL, hpiU⟩ := piDirectedBounds
  obtain ⟨hgl, hgu⟩ := expGammaDirectedBounds
  obtain ⟨h1L, h1U⟩ := expOneDirectedBounds
  obtain ⟨hdL, hdU⟩ := expDeltaDirectedBounds
  have hzL :
      (chapter09UnconditionalEndpointZeroLower : ℝ) <
        chapter09UnconditionalEndpointZero := by
    dsimp [chapter09UnconditionalEndpointZero]
    exact ((by
      simpa [chapter09UnconditionalEndpointZeroLower] using
        (Rat.cast_lt (K := ℝ)).2 rationalCertificates.endpointZeroLower) :
          (chapter09UnconditionalEndpointZeroLower : ℝ) <
            4 * (3141592653589793 / 10 ^ 15 : ℝ) *
              (178107241799019 / 10 ^ 14 : ℝ)).trans
      (strictScaledMul 4 (by norm_num) hpiL hgl (by norm_num) Real.pi_pos)
  have hzU :
      chapter09UnconditionalEndpointZero <
        (chapter09UnconditionalEndpointZeroUpper : ℝ) := by
    dsimp [chapter09UnconditionalEndpointZero]
    exact (strictScaledMul 4 (by norm_num) hpiU hgu (by positivity) (by norm_num)).trans
      ((by
        simpa [chapter09UnconditionalEndpointZeroUpper] using
          (Rat.cast_lt (K := ℝ)).2 rationalCertificates.endpointZeroUpper) :
            4 * (3141592653589794 / 10 ^ 15 : ℝ) *
                (178107241799021 / 10 ^ 14 : ℝ) <
              (chapter09UnconditionalEndpointZeroUpper : ℝ))
  have honeProdL :
      (271828182845904 / 10 ^ 14 : ℝ) *
          (178107241799019 / 10 ^ 14 : ℝ) <
        Real.exp 1 * Real.exp chapter09EulerMascheroni :=
    strictMul h1L hgl (by norm_num) (Real.exp_pos 1)
  have honeProdU :
      Real.exp 1 * Real.exp chapter09EulerMascheroni <
        (271828182845906 / 10 ^ 14 : ℝ) *
          (178107241799021 / 10 ^ 14 : ℝ) :=
    strictMul h1U hgu (Real.exp_pos _) (by norm_num)
  have honeL :
      (chapter09UnconditionalEndpointOneLower : ℝ) <
        chapter09UnconditionalEndpointOne := by
    rw [chapter09UnconditionalEndpointOne, Real.exp_add]
    exact ((by
      simpa [chapter09UnconditionalEndpointOneLower] using
        (Rat.cast_lt (K := ℝ)).2 rationalCertificates.endpointOneLower) :
          (chapter09UnconditionalEndpointOneLower : ℝ) <
            4 * (3141592653589793 / 10 ^ 15 : ℝ) *
              ((271828182845904 / 10 ^ 14 : ℝ) *
                (178107241799019 / 10 ^ 14 : ℝ))).trans
      (strictScaledMul 4 (by norm_num) hpiL honeProdL (by norm_num) Real.pi_pos)
  have honeU :
      chapter09UnconditionalEndpointOne <
        (chapter09UnconditionalEndpointOneUpper : ℝ) := by
    rw [chapter09UnconditionalEndpointOne, Real.exp_add]
    exact (strictScaledMul 4 (by norm_num) hpiU honeProdU (by positivity) (by norm_num)).trans
      ((by
        simpa [chapter09UnconditionalEndpointOneUpper] using
          (Rat.cast_lt (K := ℝ)).2 rationalCertificates.endpointOneUpper) :
            4 * (3141592653589794 / 10 ^ 15 : ℝ) *
                ((271828182845906 / 10 ^ 14 : ℝ) *
                  (178107241799021 / 10 ^ 14 : ℝ)) <
              (chapter09UnconditionalEndpointOneUpper : ℝ))
  have hgrhzL :
      (chapter09GRHEndpointZeroLower : ℝ) < chapter09GRHEndpointZero := by
    dsimp [chapter09GRHEndpointZero]
    exact ((by
      simpa [chapter09GRHEndpointZeroLower] using
        (Rat.cast_lt (K := ℝ)).2 rationalCertificates.grhEndpointZeroLower) :
          (chapter09GRHEndpointZeroLower : ℝ) <
            8 * (3141592653589793 / 10 ^ 15 : ℝ) *
              (178107241799019 / 10 ^ 14 : ℝ)).trans
      (strictScaledMul 8 (by norm_num) hpiL hgl (by norm_num) Real.pi_pos)
  have hgrhzU :
      chapter09GRHEndpointZero < (chapter09GRHEndpointZeroUpper : ℝ) := by
    dsimp [chapter09GRHEndpointZero]
    exact (strictScaledMul 8 (by norm_num) hpiU hgu (by positivity) (by norm_num)).trans
      ((by
        simpa [chapter09GRHEndpointZeroUpper] using
          (Rat.cast_lt (K := ℝ)).2 rationalCertificates.grhEndpointZeroUpper) :
            8 * (3141592653589794 / 10 ^ 15 : ℝ) *
                (178107241799021 / 10 ^ 14 : ℝ) <
              (chapter09GRHEndpointZeroUpper : ℝ))
  have hinnerL :
      (178107241799019 / 10 ^ 14 : ℝ) *
          (17696757306773 / 10 ^ 13 : ℝ) <
        Real.exp chapter09EulerMascheroni * Real.exp (Real.pi / 2 - 1) :=
    strictMul hgl hdL (by norm_num) (Real.exp_pos _)
  have hinnerU :
      Real.exp chapter09EulerMascheroni * Real.exp (Real.pi / 2 - 1) <
        (178107241799021 / 10 ^ 14 : ℝ) *
          (17696757306774 / 10 ^ 13 : ℝ) :=
    strictMul hgu hdU (Real.exp_pos _) (by norm_num)
  have hgrhProdL :
      (271828182845904 / 10 ^ 14 : ℝ) *
          ((178107241799019 / 10 ^ 14 : ℝ) *
            (17696757306773 / 10 ^ 13 : ℝ)) <
        Real.exp 1 *
          (Real.exp chapter09EulerMascheroni * Real.exp (Real.pi / 2 - 1)) :=
    strictMul h1L hinnerL (by positivity) (Real.exp_pos _)
  have hgrhProdU :
      Real.exp 1 *
          (Real.exp chapter09EulerMascheroni * Real.exp (Real.pi / 2 - 1)) <
        (271828182845906 / 10 ^ 14 : ℝ) *
          ((178107241799021 / 10 ^ 14 : ℝ) *
            (17696757306774 / 10 ^ 13 : ℝ)) :=
    strictMul h1U hinnerU (by positivity) (by norm_num)
  have hfactorGrh :
      Real.exp (chapter09EulerMascheroni + Real.pi / 2) =
        Real.exp 1 *
          (Real.exp chapter09EulerMascheroni * Real.exp (Real.pi / 2 - 1)) := by
    rw [show chapter09EulerMascheroni + Real.pi / 2 =
      1 + (chapter09EulerMascheroni + (Real.pi / 2 - 1)) by ring,
      Real.exp_add, Real.exp_add]
  have hgrhoneL :
      (chapter09GRHEndpointOneLower : ℝ) < chapter09GRHEndpointOne := by
    rw [chapter09GRHEndpointOne, hfactorGrh]
    exact ((by
      simpa [chapter09GRHEndpointOneLower] using
        (Rat.cast_lt (K := ℝ)).2 rationalCertificates.grhEndpointOneLower) :
          (chapter09GRHEndpointOneLower : ℝ) <
            8 * (3141592653589793 / 10 ^ 15 : ℝ) *
              ((271828182845904 / 10 ^ 14 : ℝ) *
                ((178107241799019 / 10 ^ 14 : ℝ) *
                  (17696757306773 / 10 ^ 13 : ℝ)))).trans
      (strictScaledMul 8 (by norm_num) hpiL hgrhProdL (by positivity) Real.pi_pos)
  have hgrhoneU :
      chapter09GRHEndpointOne < (chapter09GRHEndpointOneUpper : ℝ) := by
    rw [chapter09GRHEndpointOne, hfactorGrh]
    exact (strictScaledMul 8 (by norm_num) hpiU hgrhProdU (by positivity) (by norm_num)).trans
      ((by
        simpa [chapter09GRHEndpointOneUpper] using
          (Rat.cast_lt (K := ℝ)).2 rationalCertificates.grhEndpointOneUpper) :
            8 * (3141592653589794 / 10 ^ 15 : ℝ) *
                ((271828182845906 / 10 ^ 14 : ℝ) *
                  ((178107241799021 / 10 ^ 14 : ℝ) *
                    (17696757306774 / 10 ^ 13 : ℝ))) <
              (chapter09GRHEndpointOneUpper : ℝ))
  exact
    { gamma_directed_bounds := ⟨hgammaL, hgammaU⟩
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
