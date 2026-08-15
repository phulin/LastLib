import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter10.Section01RationalEnclosuresForElementaryConstants
import Mathlib.Analysis.Calculus.Taylor

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter10

open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08
open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter09
open MeasureTheory Set
open Filter
open scoped BigOperators Topology

noncomputable section

/-! ## 10.2. Finite formulas for `B_T` and `C_T` -/

def chapter10AT (T : ℝ) : ℝ :=
  T / 2

def chapter10BT (T : ℝ) : ℝ :=
  chapter08BT T

def chapter10CT (T : ℝ) : ℝ :=
  chapter08CT T

def chapter10Coth (x : ℝ) : ℝ :=
  Real.cosh x / Real.sinh x

def chapter10BSeriesTerm (T : ℝ) (k : ℕ) : ℝ :=
  chapter08BSeriesTerm T k

def chapter10BSeriesTail (T : ℝ) (m : ℕ) : ℝ :=
  chapter08BSeriesTail T m

theorem chapter10_AT_eq_half (T : ℝ) : chapter10AT T = T / 2 :=
  rfl

theorem chapter10_AT_eq_chapter09_unconditional_pole_integral
    {T : ℝ} (hT : 0 < T) :
    chapter10AT T = chapter09UnconditionalPoleIntegral T := by
  simpa [chapter10AT] using (chapter09_unconditional_pole_integral hT).symm

/- The GRH triangle has a different pole integral; retain it explicitly so the
   two alternatives in (8.4) are both available from the certified-numerics
   chapter. -/
def chapter10GRHAT (T : ℝ) : ℝ :=
  chapter09GRHPoleIntegral T

theorem chapter10_GRHAT_eq_chapter09_grh_pole_integral (T : ℝ) :
    chapter10GRHAT T = chapter09GRHPoleIntegral T :=
  rfl

theorem chapter10_GRHAT_formula
    {T : ℝ} (hT : 0 < T) :
    chapter10GRHAT T = 4 / T * (Real.cosh (T / 2) - 1) := by
  simpa [chapter10GRHAT] using chapter09_grh_pole_integral hT

theorem chapter10_coth_eq_chapter08_coth (x : ℝ) :
    chapter10Coth x = chapter08Coth x :=
  rfl

theorem chapter10_BT_eq_chapter09_BT (T : ℝ) :
    chapter10BT T = chapter09BT T := by
  rfl

theorem chapter10_CT_eq_chapter09_CT (T : ℝ) :
    chapter10CT T = chapter09CT T := by
  rfl

theorem chapter10_log_coth_rewrite
    {T : ℝ} (hT : 0 < T) :
    Real.log (chapter10Coth (T / 2)) =
      Real.log (1 + Real.exp (-T)) - Real.log (1 - Real.exp (-T)) := by
  have hexp : Real.exp (-(T / 2)) = Real.exp (T / 2) * Real.exp (-T) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hminus : 0 < 1 - Real.exp (-T) := by
    apply sub_pos.mpr
    rw [Real.exp_lt_one_iff]
    linarith
  have hratio : chapter10Coth (T / 2) =
      (1 + Real.exp (-T)) / (1 - Real.exp (-T)) := by
    unfold chapter10Coth
    rw [Real.cosh_eq, Real.sinh_eq, hexp]
    field_simp [Real.exp_ne_zero, ne_of_gt hminus]
  have hplus : 1 + Real.exp (-T) ≠ 0 := by positivity
  rw [hratio, Real.log_div hplus (ne_of_gt hminus)]

theorem chapter10_log_cosh_half_rewrite
    {T : ℝ} (hT : 0 < T) :
    Real.log (Real.cosh (T / 2)) =
      T / 2 - Real.log 2 + Real.log (1 + Real.exp (-T)) := by
  have hexp : Real.exp (-(T / 2)) = Real.exp (T / 2) * Real.exp (-T) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hfac : Real.cosh (T / 2) =
      (Real.exp (T / 2) / 2) * (1 + Real.exp (-T)) := by
    rw [Real.cosh_eq, hexp]
    ring
  have hminus : 0 < 1 - Real.exp (-T) := by
    apply sub_pos.mpr
    rw [Real.exp_lt_one_iff]
    linarith
  have hfirst : Real.exp (T / 2) / 2 ≠ 0 := by positivity
  have hplus : 1 + Real.exp (-T) ≠ 0 := by
    nlinarith [Real.exp_nonneg (-T)]
  rw [hfac, Real.log_mul hfirst hplus,
    Real.log_div (Real.exp_ne_zero _) (by norm_num), Real.log_exp]

theorem chapter10_B_finite_formula
    {T : ℝ} (hT : 0 < T) :
    chapter10BT T =
      Real.log 2 + Real.pi ^ 2 / (4 * T) +
        Real.log (chapter10Coth (T / 2)) -
        (2 / T) * (∑' k : ℕ, chapter10BSeriesTerm T k) := by
  simpa [chapter10BT, chapter10Coth, chapter08Coth, chapter10BSeriesTerm] using
    (chapter08_B_exact_formula hT)

theorem chapter10_C_finite_formula
    {T : ℝ} (hT : 0 < T) :
    chapter10CT T =
      Real.pi / 2 - (2 / T) * Real.log (Real.cosh (T / 2)) := by
  simpa [chapter10CT] using chapter08_C_exact_formula hT

theorem chapter10_B_series_tail_bound
    {T : ℝ} (hT : 0 < T) (m : ℕ) :
    0 ≤ chapter10BSeriesTail T m ∧
      chapter10BSeriesTail T m ≤
        (1 + T) * Real.exp (-((2 * m + 3 : ℕ) : ℝ) * T) /
          (1 - Real.exp (-2 * T)) := by
  refine ⟨?_, ?_⟩
  · simpa [chapter10BSeriesTail, chapter10BSeriesTerm] using
      (chapter08_B_series_tail_nonnegative hT m)
  · simpa [chapter10BSeriesTail, chapter10BSeriesTerm] using
      (chapter08_B_series_tail_bound hT m)

def chapter10AlternatingExpPartialSum (r : ℝ) (M : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (M + 1), (-r) ^ j / (Nat.factorial j : ℝ)

def chapter10AlternatingExpRemainder (r : ℝ) (M : ℕ) : ℝ :=
  Real.exp (-r) - chapter10AlternatingExpPartialSum r M

theorem chapter10_alternating_exp_series_identity (r : ℝ) (M : ℕ) :
    Real.exp (-r) =
      chapter10AlternatingExpPartialSum r M +
        chapter10AlternatingExpRemainder r M := by
  simp [chapter10AlternatingExpRemainder]

theorem chapter10_alternating_exp_remainder_bound
    {r : ℝ} (hr : 0 ≤ r) {M : ℕ} (hM : r < (M + 2 : ℕ)) :
    0 ≤ (-1 : ℝ) ^ (M + 1) * chapter10AlternatingExpRemainder r M ∧
      (-1 : ℝ) ^ (M + 1) * chapter10AlternatingExpRemainder r M ≤
        r ^ (M + 1) / (Nat.factorial (M + 1) : ℝ) := by
  let k : ℕ := M + 1
  let g : ℕ → ℝ := fun n =>
    r ^ (n + k) / (Nat.factorial (n + k) : ℝ)
  have hk : r < ((k + 1 : ℕ) : ℝ) := by
    simpa [k, Nat.cast_add, Nat.add_assoc] using hM
  have hanti : Antitone g := by
    refine antitone_nat_of_succ_le ?_
    intro n
    have hnk : k + 1 ≤ n + k + 1 := by omega
    have hden : r ≤ ((n + k + 1 : ℕ) : ℝ) := by
      exact le_trans (le_of_lt hk) (by exact_mod_cast hnk)
    have hratio : r / ((n + k + 1 : ℕ) : ℝ) ≤ 1 :=
      (div_le_one (by positivity)).2 hden
    have hform : g (n + 1) = g n *
        (r / ((n + k + 1 : ℕ) : ℝ)) := by
      dsimp [g]
      rw [show n + 1 + k = (n + k) + 1 by omega,
        pow_succ, Nat.factorial_succ]
      field_simp [Nat.factorial_ne_zero]
      push_cast
      ring
    rw [hform]
    calc
      g n * (r / ((n + k + 1 : ℕ) : ℝ)) ≤ g n * 1 :=
        mul_le_mul_of_nonneg_left hratio (by
          dsimp [g]
          positivity)
      _ = g n := by ring
  let a : ℕ → ℝ := fun n =>
    (-r) ^ n / (Nat.factorial n : ℝ)
  have hexp : HasSum a (Real.exp (-r)) := by
    rw [Real.exp_eq_exp_ℝ]
    simpa [a] using (NormedSpace.expSeries_div_hasSum_exp (-r))
  have htail : HasSum
      (fun i : ℕ => (-r) ^ (i + k) / (Nat.factorial (i + k) : ℝ))
      (chapter10AlternatingExpRemainder r M) := by
    simpa [a, k, chapter10AlternatingExpRemainder,
      chapter10AlternatingExpPartialSum] using
      ((hasSum_nat_add_iff' k).2 hexp)
  have hfun : ∀ i : ℕ,
      (-1 : ℝ) ^ k *
          ((-r) ^ (i + k) / (Nat.factorial (i + k) : ℝ)) =
        (-1 : ℝ) ^ i * g i := by
    intro i
    have hsq : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
      rw [← pow_add, show k + k = 2 * k by omega, pow_mul]
      norm_num
    have hsign : (-1 : ℝ) ^ k * (-1 : ℝ) ^ (i + k) = (-1 : ℝ) ^ i := by
      have hpow : (-1 : ℝ) ^ (i + k) = (-1 : ℝ) ^ i * (-1 : ℝ) ^ k :=
        pow_add (-1 : ℝ) i k
      rw [hpow]
      calc
        (-1 : ℝ) ^ k * ((-1 : ℝ) ^ i * (-1 : ℝ) ^ k) =
            (-1 : ℝ) ^ i * ((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) := by ring
        _ = (-1 : ℝ) ^ i := by rw [hsq, mul_one]
    calc
      (-1 : ℝ) ^ k *
          ((-r) ^ (i + k) / (Nat.factorial (i + k) : ℝ)) =
          ((-1 : ℝ) ^ k * (-1 : ℝ) ^ (i + k)) *
            (r ^ (i + k) / (Nat.factorial (i + k) : ℝ)) := by
        rw [show -r = (-1 : ℝ) * r by ring, mul_pow]
        ring
      _ = (-1 : ℝ) ^ i *
          (r ^ (i + k) / (Nat.factorial (i + k) : ℝ)) := by rw [hsign]
      _ = (-1 : ℝ) ^ i * g i := by rfl
  have htail_signed : HasSum (fun i : ℕ => (-1 : ℝ) ^ i * g i)
      ((-1 : ℝ) ^ k * chapter10AlternatingExpRemainder r M) := by
    simpa only [hfun] using htail.mul_left ((-1 : ℝ) ^ k)
  have hlim : Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * g i) atTop
      (𝓝 ((-1 : ℝ) ^ k * chapter10AlternatingExpRemainder r M)) :=
    htail_signed.tendsto_sum_nat
  have hupper := hanti.tendsto_le_alternating_series hlim 0
  have hlower := hanti.alternating_series_le_tendsto hlim 1
  have hupper' :
      (-1 : ℝ) ^ k * chapter10AlternatingExpRemainder r M ≤ g 0 := by
    simpa using hupper
  have hlower' : g 0 - g 1 ≤
      (-1 : ℝ) ^ k * chapter10AlternatingExpRemainder r M := by
    simpa [Finset.sum_range_succ] using hlower
  have hnonneg : 0 ≤ g 0 - g 1 :=
    sub_nonneg.mpr (hanti (Nat.zero_le 1))
  constructor
  · linarith
  · simpa [g, k] using hupper'

theorem chapter10_alternating_exp_remainder_strict
    {r : ℝ} (hr : 0 < r) {M : ℕ} (hM : r < (M + 2 : ℕ)) :
    0 < (-1 : ℝ) ^ (M + 1) * chapter10AlternatingExpRemainder r M ∧
      (-1 : ℝ) ^ (M + 1) * chapter10AlternatingExpRemainder r M <
        r ^ (M + 1) / (Nat.factorial (M + 1) : ℝ) := by
  let k : ℕ := M + 1
  let g : ℕ → ℝ := fun n =>
    r ^ (n + k) / (Nat.factorial (n + k) : ℝ)
  have hk : r < ((k + 1 : ℕ) : ℝ) := by
    simpa [k, Nat.cast_add, Nat.add_assoc] using hM
  have hform : ∀ n : ℕ, g (n + 1) = g n *
      (r / ((n + k + 1 : ℕ) : ℝ)) := by
    intro n
    dsimp [g]
    rw [show n + 1 + k = (n + k) + 1 by omega,
      pow_succ, Nat.factorial_succ]
    field_simp [Nat.factorial_ne_zero]
    push_cast
    ring
  have hanti : Antitone g := by
    refine antitone_nat_of_succ_le ?_
    intro n
    have hnk : k + 1 ≤ n + k + 1 := by omega
    have hden : r ≤ ((n + k + 1 : ℕ) : ℝ) := by
      exact le_trans (le_of_lt hk) (by exact_mod_cast hnk)
    have hratio : r / ((n + k + 1 : ℕ) : ℝ) ≤ 1 :=
      (div_le_one (by positivity)).2 hden
    rw [hform n]
    exact (mul_le_mul_of_nonneg_left hratio (by
      dsimp [g]
      positivity)).trans_eq (by ring)
  have hstrict : ∀ n : ℕ, g (n + 1) < g n := by
    intro n
    have hnk : k + 1 ≤ n + k + 1 := by omega
    have hden : r < ((n + k + 1 : ℕ) : ℝ) := by
      exact lt_of_lt_of_le hk (by exact_mod_cast hnk)
    have hratio : r / ((n + k + 1 : ℕ) : ℝ) < 1 :=
      (div_lt_one (by positivity)).2 hden
    rw [hform n]
    exact (mul_lt_mul_of_pos_left hratio (by
      dsimp [g]
      positivity)).trans_eq (by ring)
  let a : ℕ → ℝ := fun n =>
    (-r) ^ n / (Nat.factorial n : ℝ)
  have hexp : HasSum a (Real.exp (-r)) := by
    rw [Real.exp_eq_exp_ℝ]
    simpa [a] using (NormedSpace.expSeries_div_hasSum_exp (-r))
  have htail : HasSum
      (fun i : ℕ => (-r) ^ (i + k) / (Nat.factorial (i + k) : ℝ))
      (chapter10AlternatingExpRemainder r M) := by
    simpa [a, k, chapter10AlternatingExpRemainder,
      chapter10AlternatingExpPartialSum] using
      ((hasSum_nat_add_iff' k).2 hexp)
  have hfun : ∀ i : ℕ,
      (-1 : ℝ) ^ k *
          ((-r) ^ (i + k) / (Nat.factorial (i + k) : ℝ)) =
        (-1 : ℝ) ^ i * g i := by
    intro i
    have hsq : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
      rw [← pow_add, show k + k = 2 * k by omega, pow_mul]
      norm_num
    have hpow : (-1 : ℝ) ^ (i + k) = (-1 : ℝ) ^ i * (-1 : ℝ) ^ k :=
      pow_add (-1 : ℝ) i k
    have hsign : (-1 : ℝ) ^ k * (-1 : ℝ) ^ (i + k) = (-1 : ℝ) ^ i := by
      rw [hpow]
      calc
        (-1 : ℝ) ^ k * ((-1 : ℝ) ^ i * (-1 : ℝ) ^ k) =
            (-1 : ℝ) ^ i * ((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) := by ring
        _ = (-1 : ℝ) ^ i := by rw [hsq, mul_one]
    calc
      (-1 : ℝ) ^ k *
          ((-r) ^ (i + k) / (Nat.factorial (i + k) : ℝ)) =
          ((-1 : ℝ) ^ k * (-1 : ℝ) ^ (i + k)) *
            (r ^ (i + k) / (Nat.factorial (i + k) : ℝ)) := by
        rw [show -r = (-1 : ℝ) * r by ring, mul_pow]
        ring
      _ = (-1 : ℝ) ^ i *
          (r ^ (i + k) / (Nat.factorial (i + k) : ℝ)) := by rw [hsign]
      _ = (-1 : ℝ) ^ i * g i := by rfl
  have htail_signed : HasSum (fun i : ℕ => (-1 : ℝ) ^ i * g i)
      ((-1 : ℝ) ^ k * chapter10AlternatingExpRemainder r M) := by
    simpa only [hfun] using htail.mul_left ((-1 : ℝ) ^ k)
  have hlim : Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * g i) atTop
      (𝓝 ((-1 : ℝ) ^ k * chapter10AlternatingExpRemainder r M)) :=
    htail_signed.tendsto_sum_nat
  have hupper := hanti.tendsto_le_alternating_series hlim 1
  have hlower := hanti.alternating_series_le_tendsto hlim 1
  have hupper' :
      (-1 : ℝ) ^ k * chapter10AlternatingExpRemainder r M ≤
        g 0 - g 1 + g 2 := by
    have h' : (-1 : ℝ) ^ k * chapter10AlternatingExpRemainder r M ≤
        g 0 + -g 1 + g 2 := by
      simpa [Finset.sum_range_succ] using hupper
    linarith
  have hlower' : g 0 - g 1 ≤
      (-1 : ℝ) ^ k * chapter10AlternatingExpRemainder r M := by
    simpa [Finset.sum_range_succ] using hlower
  have hpos : 0 <
      (-1 : ℝ) ^ k * chapter10AlternatingExpRemainder r M := by
    have h01 : g 1 < g 0 := by simpa using hstrict 0
    linarith
  have hlt :
      (-1 : ℝ) ^ k * chapter10AlternatingExpRemainder r M < g 0 := by
    have h12 : g 2 < g 1 := by simpa using hstrict 1
    linarith
  constructor
  · simpa [k] using hpos
  · simpa [g, k] using hlt

theorem chapter10_alternating_exp_partial_sum_gap (x : ℝ) :
    chapter10AlternatingExpPartialSum x 32 -
        chapter10AlternatingExpPartialSum x 33 =
      x ^ 33 / (Nat.factorial 33 : ℝ) := by
  unfold chapter10AlternatingExpPartialSum
  change
    (∑ j ∈ Finset.range 33, (-x) ^ j / (Nat.factorial j : ℝ)) -
        (∑ j ∈ Finset.range (33 + 1), (-x) ^ j / (Nat.factorial j : ℝ)) =
      x ^ 33 / (Nat.factorial 33 : ℝ)
  have hsecond :
      (∑ j ∈ Finset.range (33 + 1), (-x) ^ j / (Nat.factorial j : ℝ)) =
        (∑ j ∈ Finset.range 33, (-x) ^ j / (Nat.factorial j : ℝ)) +
          (-x) ^ 33 / (Nat.factorial 33 : ℝ) := by
    rw [Finset.sum_range_succ]
  rw [hsecond]
  have hneg : (-x : ℝ) ^ 33 = -x ^ 33 := by
    rw [show (33 : ℕ) = 2 * 16 + 1 by norm_num, pow_add, pow_mul]
    ring
  rw [hneg]
  ring

theorem chapter10_exp_33_32_bounds {x : ℝ} (hx : 0 < x) :
    chapter10AlternatingExpPartialSum x 33 < Real.exp (-x) ∧
      Real.exp (-x) < chapter10AlternatingExpPartialSum x 32 := by
  let f : ℝ → ℝ := fun y => Real.exp (-y)
  have hcont : ContDiff ℝ ⊤ f := by
    simpa [f, Function.comp_def] using
      (Real.contDiff_exp.comp contDiff_id.neg)
  have hne : (0 : ℝ) ≠ x := ne_of_lt hx
  have hu : UniqueDiffOn ℝ (uIcc (0 : ℝ) x) := uniqueDiffOn_uIcc hne
  have hderiv : ∀ n : ℕ, ∀ y : ℝ,
      iteratedDeriv n f y = (-1 : ℝ) ^ n * Real.exp (-y) := by
    intro n y
    simpa [f] using congrFun (iteratedDeriv_exp_const_mul n (-1)) y
  have hderivWithin : ∀ n : ℕ,
      iteratedDerivWithin n f (uIcc (0 : ℝ) x) 0 =
        (-1 : ℝ) ^ n * Real.exp (-0) := by
    intro n
    rw [iteratedDerivWithin_eq_iteratedDeriv hu
      (hcont.contDiffAt.of_le (by simp)) left_mem_uIcc]
    exact hderiv n 0
  have htaylor : ∀ n : ℕ, ∃ y ∈ uIoo (0 : ℝ) x,
      Real.exp (-x) - chapter10AlternatingExpPartialSum x n =
        (-1 : ℝ) ^ (n + 1) * Real.exp (-y) * x ^ (n + 1) /
          (Nat.factorial (n + 1) : ℝ) := by
    intro n
    obtain ⟨y, hy, hrem⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (f := f) (x₀ := (0 : ℝ))
        (x := x) (n := n) hne (hcont.contDiffOn.of_le (by simp))
    have heval : taylorWithinEval f n (uIcc (0 : ℝ) x) 0 x =
        chapter10AlternatingExpPartialSum x n := by
      rw [taylor_within_apply]
      unfold chapter10AlternatingExpPartialSum
      apply Finset.sum_congr rfl
      intro j hj
      rw [iteratedDerivWithin_eq_iteratedDeriv hu
        (hcont.contDiffAt.of_le (by simp)) left_mem_uIcc]
      rw [hderiv j 0]
      simp only [sub_zero, neg_zero, smul_eq_mul]
      rw [Real.exp_zero, mul_one]
      rw [show (-x : ℝ) ^ j = (-1 : ℝ) ^ j * x ^ j by
        rw [show -x = (-1 : ℝ) * x by ring, mul_pow]]
      ring
    rw [heval, hderiv (n + 1) y] at hrem
    refine ⟨y, hy, ?_⟩
    simpa [f, sub_zero] using hrem
  obtain ⟨y₃₃, hy₃₃, h₃₃⟩ := htaylor 33
  obtain ⟨y₃₂, hy₃₂, h₃₂⟩ := htaylor 32
  have hpos₃₃ : 0 < Real.exp (-y₃₃) * x ^ (33 + 1) /
      (Nat.factorial (33 + 1) : ℝ) := by positivity
  have hpos₃₂ : 0 < Real.exp (-y₃₂) * x ^ (32 + 1) /
      (Nat.factorial (32 + 1) : ℝ) := by positivity
  norm_num at h₃₃ h₃₂
  constructor <;> linarith

structure Chapter10RationalInterval where
  lower : ℚ
  upper : ℚ

def Chapter10RationalInterval.Valid (I : Chapter10RationalInterval) : Prop :=
  I.lower ≤ I.upper

def Chapter10RationalInterval.Contains
    (I : Chapter10RationalInterval) (x : ℝ) : Prop :=
  (I.lower : ℝ) ≤ x ∧ x ≤ (I.upper : ℝ)

theorem chapter10_rational_interval_contains_iff
    (I : Chapter10RationalInterval) (x : ℝ) :
    I.Contains x ↔ x ∈ Set.Icc (I.lower : ℝ) (I.upper : ℝ) := by
  rfl

def chapter10GammaInterval : Chapter10RationalInterval :=
  { lower := chapter10GammaLower
    upper := chapter10GammaUpper }

def chapter10PiInterval : Chapter10RationalInterval :=
  { lower := chapter10PiLower
    upper := chapter10PiUpper }

theorem chapter10_gamma_interval_contains :
    chapter10GammaInterval.Contains Real.eulerMascheroniConstant := by
  change (chapter10GammaLower : ℝ) ≤ Real.eulerMascheroniConstant ∧
    Real.eulerMascheroniConstant ≤ (chapter10GammaUpper : ℝ)
  have h := chapter10_gamma_directed_bounds
  exact ⟨le_of_lt h.1, le_of_lt h.2⟩

theorem chapter10_gamma_interval_valid : chapter10GammaInterval.Valid := by
  norm_num [Chapter10RationalInterval.Valid, chapter10GammaInterval,
    chapter10GammaLower, chapter10GammaUpper]

theorem chapter10_pi_interval_contains :
    chapter10PiInterval.Contains Real.pi := by
  change (chapter10PiLower : ℝ) ≤ Real.pi ∧ Real.pi ≤ (chapter10PiUpper : ℝ)
  have h := chapter10_pi_directed_bounds
  exact ⟨le_of_lt h.1, le_of_lt h.2⟩

theorem chapter10_pi_interval_valid : chapter10PiInterval.Valid := by
  norm_num [Chapter10RationalInterval.Valid, chapter10PiInterval,
    chapter10PiLower, chapter10PiUpper]

def chapter10SquareInterval (I : Chapter10RationalInterval) :
    Chapter10RationalInterval :=
  { lower := I.lower ^ 2
    upper := I.upper ^ 2 }

theorem chapter10_square_interval_contains
    {I : Chapter10RationalInterval} (hvalid : I.Valid)
    (hlower : 0 ≤ I.lower) {x : ℝ} (hx : I.Contains x) :
    (chapter10SquareInterval I).Contains (x ^ 2) := by
  have hvalidR : (I.lower : ℝ) ≤ (I.upper : ℝ) := by
    exact_mod_cast hvalid
  have hlowerR : (0 : ℝ) ≤ (I.lower : ℝ) := by
    exact_mod_cast hlower
  have hxlo : (I.lower : ℝ) ≤ x := hx.1
  have hxhi : x ≤ (I.upper : ℝ) := hx.2
  have hupperR : (0 : ℝ) ≤ (I.upper : ℝ) :=
    le_trans hlowerR hvalidR
  have hleft : 0 ≤ (x - (I.lower : ℝ)) * (x + (I.lower : ℝ)) :=
    mul_nonneg (sub_nonneg.mpr hxlo) (by linarith)
  have hright : 0 ≤ ((I.upper : ℝ) - x) * ((I.upper : ℝ) + x) :=
    mul_nonneg (sub_nonneg.mpr hxhi) (by linarith)
  change ((I.lower ^ 2 : ℚ) : ℝ) ≤ x ^ 2 ∧
    x ^ 2 ≤ ((I.upper ^ 2 : ℚ) : ℝ)
  constructor
  · convert (show (I.lower : ℝ) ^ 2 ≤ x ^ 2 by nlinarith [hleft]) using 1;
      norm_cast
  · convert (show x ^ 2 ≤ (I.upper : ℝ) ^ 2 by nlinarith [hright]) using 1;
      norm_cast

theorem chapter10_exp_negative_is_square_of_half (T : ℝ) :
    Real.exp (-T) = (Real.exp (-(T / 2))) ^ 2 := by
  rw [show -T = -(T / 2) + -(T / 2) by ring, Real.exp_add]
  ring

theorem chapter10_exp_negative_square_interval
    {T a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hlo : a ≤ Real.exp (-(T / 2)))
    (hhi : Real.exp (-(T / 2)) ≤ b) :
    a ^ 2 ≤ Real.exp (-T) ∧ Real.exp (-T) ≤ b ^ 2 := by
  rw [chapter10_exp_negative_is_square_of_half]
  have hy : 0 ≤ Real.exp (-(T / 2)) := Real.exp_nonneg _
  have hleft : 0 ≤
      (Real.exp (-(T / 2)) - a) * (Real.exp (-(T / 2)) + a) :=
    mul_nonneg (sub_nonneg.mpr hlo) (by positivity)
  have hb : 0 ≤ b := le_trans ha hab
  have hright : 0 ≤
      (b - Real.exp (-(T / 2))) * (b + Real.exp (-(T / 2))) :=
    mul_nonneg (sub_nonneg.mpr hhi) (by linarith)
  constructor <;> nlinarith [hleft, hright]

private theorem chapter10_nonneg_pow_mono {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (k : ℕ) : a ^ k ≤ b ^ k := by
  gcongr

private theorem chapter10_log_strict_mono {a b : ℝ} (ha : 0 < a)
    (hab : a < b) : Real.log a < Real.log b := by
  exact Real.strictMonoOn_log ha (lt_trans ha hab) hab

private theorem chapter10_log_two_box :
    (6931471805 / 10 ^ 10 : ℝ) < Real.log 2 ∧
      Real.log 2 < (6931471806 / 10 ^ 10 : ℝ) := by
  have h := chapter10_log_two_series_remainder_bound 10
  have hid := chapter10_log_two_series_identity 10
  have hr := (abs_le.mp h)
  rw [hid]
  norm_num [chapter10LogPartialSum, Finset.sum_range_succ] at hr ⊢
  constructor <;> linarith [hr.1, hr.2]

private theorem chapter10_log_ratio_lower_of_partial {q c : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hc : c < chapter10LogPartialSum q 3 -
      2 * |q| ^ (2 * 3 + 3) /
        (((2 * 3 + 3 : ℕ) : ℝ) * (1 - q ^ 2))) :
    c < Real.log ((1 + q) / (1 - q)) := by
  have hqabs : |q| < 1 := by simpa [abs_of_nonneg hq0] using hq1
  have h := chapter10_log_series_remainder_bound hqabs 3
  have hid := chapter10_log_series_identity q 3
  have hr := (abs_le.mp h)
  rw [hid]
  linarith [hr.1]

private theorem chapter10_log_ratio_upper_of_partial {q c : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hc : chapter10LogPartialSum q 3 +
      2 * |q| ^ (2 * 3 + 3) /
        (((2 * 3 + 3 : ℕ) : ℝ) * (1 - q ^ 2)) < c) :
    Real.log ((1 + q) / (1 - q)) < c := by
  have hqabs : |q| < 1 := by simpa [abs_of_nonneg hq0] using hq1
  have h := chapter10_log_series_remainder_bound hqabs 3
  have hid := chapter10_log_series_identity q 3
  have hr := (abs_le.mp h)
  rw [hid]
  linarith [hr.2]

private theorem chapter10_log_one_add_lower_of_partial {q c : ℝ}
    (hq0 : 0 ≤ q)
    (hc : c < chapter10LogPartialSum (q / (2 + q)) 3 -
      2 * |q / (2 + q)| ^ (2 * 3 + 3) /
        (((2 * 3 + 3 : ℕ) : ℝ) * (1 - (q / (2 + q)) ^ 2))) :
    c < Real.log (1 + q) := by
  have hu0 : 0 ≤ q / (2 + q) := by positivity
  have hu1 : q / (2 + q) < 1 := by
    apply (div_lt_one₀ (by linarith)).2
    linarith
  have huabs : |q / (2 + q)| < 1 := by
    simpa [abs_of_nonneg hu0] using hu1
  have h := chapter10_log_series_remainder_bound huabs 3
  have hid := chapter10_log_series_identity (q / (2 + q)) 3
  have harg :
      (1 + q / (2 + q)) / (1 - q / (2 + q)) = 1 + q := by
    field_simp
    ring
  rw [harg] at hid
  have hr := (abs_le.mp h)
  rw [hid]
  linarith [hr.1]

private theorem chapter10_log_one_add_upper_of_partial {q c : ℝ}
    (hq0 : 0 ≤ q)
    (hc : chapter10LogPartialSum (q / (2 + q)) 3 +
      2 * |q / (2 + q)| ^ (2 * 3 + 3) /
        (((2 * 3 + 3 : ℕ) : ℝ) * (1 - (q / (2 + q)) ^ 2)) < c) :
    Real.log (1 + q) < c := by
  have hu0 : 0 ≤ q / (2 + q) := by positivity
  have hu1 : q / (2 + q) < 1 := by
    apply (div_lt_one₀ (by linarith)).2
    linarith
  have huabs : |q / (2 + q)| < 1 := by
    simpa [abs_of_nonneg hu0] using hu1
  have h := chapter10_log_series_remainder_bound huabs 3
  have hid := chapter10_log_series_identity (q / (2 + q)) 3
  have harg :
      (1 + q / (2 + q)) / (1 - q / (2 + q)) = 1 + q := by
    field_simp
    ring
  rw [harg] at hid
  have hr := (abs_le.mp h)
  rw [hid]
  linarith [hr.2]

private theorem chapter10_log_coth_transfer
    {T qlo qhi cL cU : ℝ} (hT : 0 < T)
    (hqlo0 : 0 ≤ qlo) (hqlo : qlo < Real.exp (-T))
    (hqhi : Real.exp (-T) < qhi) (hqhi1 : qhi < 1)
    (hlo : cL < Real.log ((1 + qlo) / (1 - qlo)))
    (hhi : Real.log ((1 + qhi) / (1 - qhi)) < cU) :
    cL < Real.log (chapter10Coth (T / 2)) ∧
      Real.log (chapter10Coth (T / 2)) < cU := by
  have hq0 : 0 < Real.exp (-T) := Real.exp_pos _
  have hq1 : Real.exp (-T) < 1 := lt_trans hqhi hqhi1
  have hqlo1 : qlo < 1 := lt_trans hqlo (lt_trans hqhi hqhi1)
  have hdenlo : 0 < 1 - qlo := by linarith
  have hden : 0 < 1 - Real.exp (-T) := by linarith
  have hratioLo :
      (1 + qlo) / (1 - qlo) <
        (1 + Real.exp (-T)) / (1 - Real.exp (-T)) := by
    apply (div_lt_div_iff₀ (by linarith) (by linarith)).2
    nlinarith [hqlo]
  have hratioHi :
      (1 + Real.exp (-T)) / (1 - Real.exp (-T)) <
        (1 + qhi) / (1 - qhi) := by
    apply (div_lt_div_iff₀ (by linarith) (by linarith)).2
    nlinarith [hqhi]
  have hlogLo := chapter10_log_strict_mono
    (div_pos (by linarith) hdenlo) hratioLo
  have hlogHi := chapter10_log_strict_mono
    (div_pos (by positivity) hden) hratioHi
  have hrewrite :
      Real.log (chapter10Coth (T / 2)) =
        Real.log ((1 + Real.exp (-T)) / (1 - Real.exp (-T))) := by
    calc
      Real.log (chapter10Coth (T / 2)) =
          Real.log (1 + Real.exp (-T)) - Real.log (1 - Real.exp (-T)) :=
        chapter10_log_coth_rewrite hT
      _ = Real.log ((1 + Real.exp (-T)) / (1 - Real.exp (-T))) := by
        rw [Real.log_div (by positivity) (ne_of_gt hden)]
  rw [hrewrite]
  exact ⟨lt_trans hlo hlogLo, lt_trans hlogHi hhi⟩

private theorem chapter10_log_one_add_transfer
    {q qlo qhi cL cU : ℝ} (hqlo0 : 0 ≤ qlo)
    (hqlo : qlo < q) (hqhi : q < qhi)
    (hlo : cL < Real.log (1 + qlo))
    (hhi : Real.log (1 + qhi) < cU) :
    cL < Real.log (1 + q) ∧ Real.log (1 + q) < cU := by
  have hq0 : 0 < q := lt_of_le_of_lt hqlo0 hqlo
  have hlogLo := chapter10_log_strict_mono
    (a := 1 + qlo) (b := 1 + q) (by positivity) (by linarith)
  have hlogHi := chapter10_log_strict_mono
    (a := 1 + q) (b := 1 + qhi) (by positivity) (by linarith)
  exact ⟨lt_trans hlo hlogLo, lt_trans hlogHi hhi⟩

private theorem chapter10_exp_boxes :
    (333732 / 10 ^ 7 : ℝ) < Real.exp (-(17 / 5 : ℝ)) ∧
      Real.exp (-(17 / 5 : ℝ)) < (333733 / 10 ^ 7 : ℝ) ∧
    (111089 / 10 ^ 7 : ℝ) < Real.exp (-(9 / 2 : ℝ)) ∧
      Real.exp (-(9 / 2 : ℝ)) < (111090 / 10 ^ 7 : ℝ) ∧
    (24787 / 10 ^ 7 : ℝ) < Real.exp (-6) ∧
      Real.exp (-6) < (24788 / 10 ^ 7 : ℝ) := by
  have h17 := chapter10_alternating_exp_remainder_bound
    (r := (17 / 5 : ℝ)) (by norm_num) (M := 20) (by norm_num)
  have h17id := chapter10_alternating_exp_series_identity (17 / 5 : ℝ) 20
  have h17sign : (-1 : ℝ) ^ (20 + 1) = -1 := by norm_num
  rw [h17sign] at h17
  have h17lo :
      chapter10AlternatingExpPartialSum (17 / 5 : ℝ) 20 -
          (17 / 5 : ℝ) ^ (20 + 1) / (Nat.factorial (20 + 1) : ℝ) ≤
        Real.exp (-(17 / 5 : ℝ)) := by
    rw [h17id]
    linarith [h17.2]
  have h17hi : Real.exp (-(17 / 5 : ℝ)) ≤
      chapter10AlternatingExpPartialSum (17 / 5 : ℝ) 20 := by
    rw [h17id]
    linarith [h17.1]
  have h9 := chapter10_alternating_exp_remainder_bound
    (r := (9 / 2 : ℝ)) (by norm_num) (M := 30) (by norm_num)
  have h9id := chapter10_alternating_exp_series_identity (9 / 2 : ℝ) 30
  have h9sign : (-1 : ℝ) ^ (30 + 1) = -1 := by norm_num
  rw [h9sign] at h9
  have h9lo :
      chapter10AlternatingExpPartialSum (9 / 2 : ℝ) 30 -
          (9 / 2 : ℝ) ^ (30 + 1) / (Nat.factorial (30 + 1) : ℝ) ≤
        Real.exp (-(9 / 2 : ℝ)) := by
    rw [h9id]
    linarith [h9.2]
  have h9hi : Real.exp (-(9 / 2 : ℝ)) ≤
      chapter10AlternatingExpPartialSum (9 / 2 : ℝ) 30 := by
    rw [h9id]
    linarith [h9.1]
  have h6 := chapter10_alternating_exp_remainder_bound
    (r := (6 : ℝ)) (by norm_num) (M := 40) (by norm_num)
  have h6id := chapter10_alternating_exp_series_identity (6 : ℝ) 40
  have h6sign : (-1 : ℝ) ^ (40 + 1) = -1 := by norm_num
  rw [h6sign] at h6
  have h6lo :
      chapter10AlternatingExpPartialSum 6 40 -
          (6 : ℝ) ^ (40 + 1) / (Nat.factorial (40 + 1) : ℝ) ≤
        Real.exp (-6) := by
    rw [h6id]
    linarith [h6.2]
  have h6hi : Real.exp (-6) ≤
      chapter10AlternatingExpPartialSum 6 40 := by
    rw [h6id]
    linarith [h6.1]
  constructor
  · calc
      (333732 / 10 ^ 7 : ℝ) <
          chapter10AlternatingExpPartialSum (17 / 5 : ℝ) 20 -
            (17 / 5 : ℝ) ^ (20 + 1) /
              (Nat.factorial (20 + 1) : ℝ) := by
            norm_num [chapter10AlternatingExpPartialSum, Finset.sum_range_succ]
      _ ≤ Real.exp (-(17 / 5 : ℝ)) := h17lo
  · constructor
    · calc
        Real.exp (-(17 / 5 : ℝ)) ≤
            chapter10AlternatingExpPartialSum (17 / 5 : ℝ) 20 := h17hi
        _ < (333733 / 10 ^ 7 : ℝ) := by
          norm_num [chapter10AlternatingExpPartialSum, Finset.sum_range_succ]
    · constructor
      · calc
          (111089 / 10 ^ 7 : ℝ) <
              chapter10AlternatingExpPartialSum (9 / 2 : ℝ) 30 -
                (9 / 2 : ℝ) ^ (30 + 1) /
                  (Nat.factorial (30 + 1) : ℝ) := by
                norm_num [chapter10AlternatingExpPartialSum, Finset.sum_range_succ]
          _ ≤ Real.exp (-(9 / 2 : ℝ)) := h9lo
      · constructor
        · calc
            Real.exp (-(9 / 2 : ℝ)) ≤
                chapter10AlternatingExpPartialSum (9 / 2 : ℝ) 30 := h9hi
            _ < (111090 / 10 ^ 7 : ℝ) := by
              norm_num [chapter10AlternatingExpPartialSum, Finset.sum_range_succ]
        · constructor
          · calc
              (24787 / 10 ^ 7 : ℝ) <
                  chapter10AlternatingExpPartialSum 6 40 -
                    (6 : ℝ) ^ (40 + 1) /
                      (Nat.factorial (40 + 1) : ℝ) := by
                    norm_num [chapter10AlternatingExpPartialSum, Finset.sum_range_succ]
              _ ≤ Real.exp (-6) := h6lo
          · calc
              Real.exp (-6) ≤ chapter10AlternatingExpPartialSum 6 40 := h6hi
              _ < (24788 / 10 ^ 7 : ℝ) := by
                norm_num [chapter10AlternatingExpPartialSum, Finset.sum_range_succ]

private theorem chapter10_archimedean_log_boxes :
    ((667711 / 10 ^ 7 : ℝ) <
        Real.log (chapter10Coth ((17 / 5 : ℝ) / 2)) ∧
      Real.log (chapter10Coth ((17 / 5 : ℝ) / 2)) < (667715 / 10 ^ 7 : ℝ)) ∧
    ((328284 / 10 ^ 7 : ℝ) < Real.log (1 + Real.exp (-(17 / 5 : ℝ))) ∧
      Real.log (1 + Real.exp (-(17 / 5 : ℝ))) < (328286 / 10 ^ 7 : ℝ)) ∧
    ((222187 / 10 ^ 7 : ℝ) <
        Real.log (chapter10Coth ((9 / 2 : ℝ) / 2)) ∧
      Real.log (chapter10Coth ((9 / 2 : ℝ) / 2)) < (222190 / 10 ^ 7 : ℝ)) ∧
    ((110476 / 10 ^ 7 : ℝ) < Real.log (1 + Real.exp (-(9 / 2 : ℝ))) ∧
      Real.log (1 + Real.exp (-(9 / 2 : ℝ))) < (110479 / 10 ^ 7 : ℝ)) ∧
    ((49574 / 10 ^ 7 : ℝ) < Real.log (chapter10Coth ((6 : ℝ) / 2)) ∧
      Real.log (chapter10Coth ((6 : ℝ) / 2)) < (49577 / 10 ^ 7 : ℝ)) ∧
    ((24756 / 10 ^ 7 : ℝ) < Real.log (1 + Real.exp (-6)) ∧
      Real.log (1 + Real.exp (-6)) < (24758 / 10 ^ 7 : ℝ)) := by
  rcases chapter10_exp_boxes with
    ⟨h17lo, h17hi, h9lo, h9hi, h6lo, h6hi⟩
  have h17cl : (667711 / 10 ^ 7 : ℝ) <
      Real.log ((1 + 333732 / 10 ^ 7) / (1 - 333732 / 10 ^ 7)) := by
    apply chapter10_log_ratio_lower_of_partial (by norm_num) (by norm_num)
    norm_num [chapter10LogPartialSum, Finset.sum_range_succ]
  have h17cu : Real.log ((1 + 333733 / 10 ^ 7) / (1 - 333733 / 10 ^ 7)) <
      (667715 / 10 ^ 7 : ℝ) := by
    apply chapter10_log_ratio_upper_of_partial (by norm_num) (by norm_num)
    norm_num [chapter10LogPartialSum, Finset.sum_range_succ]
  have h17c := chapter10_log_coth_transfer
    (T := (17 / 5 : ℝ)) (qlo := 333732 / 10 ^ 7) (qhi := 333733 / 10 ^ 7)
    (cL := 667711 / 10 ^ 7) (cU := 667715 / 10 ^ 7)
    (by norm_num) (by norm_num) h17lo h17hi (by norm_num) h17cl h17cu
  have h17pl : (328284 / 10 ^ 7 : ℝ) <
      Real.log (1 + 333732 / 10 ^ 7) := by
    apply chapter10_log_one_add_lower_of_partial (by norm_num)
    norm_num [chapter10LogPartialSum, Finset.sum_range_succ]
  have h17pu : Real.log (1 + 333733 / 10 ^ 7) <
      (328286 / 10 ^ 7 : ℝ) := by
    apply chapter10_log_one_add_upper_of_partial (by norm_num)
    norm_num [chapter10LogPartialSum, Finset.sum_range_succ]
  have h17p := chapter10_log_one_add_transfer
    (q := Real.exp (-(17 / 5 : ℝ))) (qlo := 333732 / 10 ^ 7)
    (qhi := 333733 / 10 ^ 7) (cL := 328284 / 10 ^ 7)
    (cU := 328286 / 10 ^ 7) (by norm_num) h17lo h17hi h17pl h17pu
  have h9cl : (222187 / 10 ^ 7 : ℝ) <
      Real.log ((1 + 111089 / 10 ^ 7) / (1 - 111089 / 10 ^ 7)) := by
    apply chapter10_log_ratio_lower_of_partial (by norm_num) (by norm_num)
    norm_num [chapter10LogPartialSum, Finset.sum_range_succ]
  have h9cu : Real.log ((1 + 111090 / 10 ^ 7) / (1 - 111090 / 10 ^ 7)) <
      (222190 / 10 ^ 7 : ℝ) := by
    apply chapter10_log_ratio_upper_of_partial (by norm_num) (by norm_num)
    norm_num [chapter10LogPartialSum, Finset.sum_range_succ]
  have h9c := chapter10_log_coth_transfer
    (T := (9 / 2 : ℝ)) (qlo := 111089 / 10 ^ 7) (qhi := 111090 / 10 ^ 7)
    (cL := 222187 / 10 ^ 7) (cU := 222190 / 10 ^ 7)
    (by norm_num) (by norm_num) h9lo h9hi (by norm_num) h9cl h9cu
  have h9pl : (110476 / 10 ^ 7 : ℝ) <
      Real.log (1 + 111089 / 10 ^ 7) := by
    apply chapter10_log_one_add_lower_of_partial (by norm_num)
    norm_num [chapter10LogPartialSum, Finset.sum_range_succ]
  have h9pu : Real.log (1 + 111090 / 10 ^ 7) <
      (110479 / 10 ^ 7 : ℝ) := by
    apply chapter10_log_one_add_upper_of_partial (by norm_num)
    norm_num [chapter10LogPartialSum, Finset.sum_range_succ]
  have h9p := chapter10_log_one_add_transfer
    (q := Real.exp (-(9 / 2 : ℝ))) (qlo := 111089 / 10 ^ 7)
    (qhi := 111090 / 10 ^ 7) (cL := 110476 / 10 ^ 7)
    (cU := 110479 / 10 ^ 7) (by norm_num) h9lo h9hi h9pl h9pu
  have h6cl : (49574 / 10 ^ 7 : ℝ) <
      Real.log ((1 + 24787 / 10 ^ 7) / (1 - 24787 / 10 ^ 7)) := by
    apply chapter10_log_ratio_lower_of_partial (by norm_num) (by norm_num)
    norm_num [chapter10LogPartialSum, Finset.sum_range_succ]
  have h6cu : Real.log ((1 + 24788 / 10 ^ 7) / (1 - 24788 / 10 ^ 7)) <
      (49577 / 10 ^ 7 : ℝ) := by
    apply chapter10_log_ratio_upper_of_partial (by norm_num) (by norm_num)
    norm_num [chapter10LogPartialSum, Finset.sum_range_succ]
  have h6c := chapter10_log_coth_transfer
    (T := (6 : ℝ)) (qlo := 24787 / 10 ^ 7) (qhi := 24788 / 10 ^ 7)
    (cL := 49574 / 10 ^ 7) (cU := 49577 / 10 ^ 7)
    (by norm_num) (by norm_num) h6lo h6hi (by norm_num) h6cl h6cu
  have h6pl : (24756 / 10 ^ 7 : ℝ) <
      Real.log (1 + 24787 / 10 ^ 7) := by
    apply chapter10_log_one_add_lower_of_partial (by norm_num)
    norm_num [chapter10LogPartialSum, Finset.sum_range_succ]
  have h6pu : Real.log (1 + 24788 / 10 ^ 7) <
      (24758 / 10 ^ 7 : ℝ) := by
    apply chapter10_log_one_add_upper_of_partial (by norm_num)
    norm_num [chapter10LogPartialSum, Finset.sum_range_succ]
  have h6p := chapter10_log_one_add_transfer
    (q := Real.exp (-6)) (qlo := 24787 / 10 ^ 7)
    (qhi := 24788 / 10 ^ 7) (cL := 24756 / 10 ^ 7)
    (cU := 24758 / 10 ^ 7) (by norm_num) h6lo h6hi h6pl h6pu
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h17c
  · exact h17p
  · exact h9c
  · exact h9p
  · exact h6c
  · exact h6p

private theorem chapter10_B_series_first_two_decomposition
    {T : ℝ} (hT : 0 < T) :
    chapter10BSeriesTerm T 0 + chapter10BSeriesTerm T 1 +
        chapter10BSeriesTail T 1 =
      ∑' k : ℕ, chapter10BSeriesTerm T k := by
  have h := (chapter08_B_series_summable (T := T) hT).sum_add_tsum_nat_add 2
  change chapter08BSeriesTerm T 0 + chapter08BSeriesTerm T 1 +
      (∑' k : ℕ, chapter08BSeriesTerm T (1 + 1 + k)) =
    ∑' k : ℕ, chapter08BSeriesTerm T k
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
    Finset.sum_range_succ] using h

private theorem chapter10_omitted_B_series_contribution_bound_aux
    {T : ℝ} (hT : 0 < T) (m : ℕ) :
    0 ≤ (2 / T) * chapter10BSeriesTail T m ∧
      (2 / T) * chapter10BSeriesTail T m ≤
        (2 / T) * (1 + T) * Real.exp (-((2 * m + 3 : ℕ) : ℝ) * T) /
          (1 - Real.exp (-2 * T)) := by
  have htail := chapter10_B_series_tail_bound hT m
  have hscale : 0 < 2 / T := by positivity
  constructor
  · exact mul_nonneg (le_of_lt hscale) htail.1
  · have hden : 0 < 1 - Real.exp (-2 * T) := by
      apply sub_pos.mpr
      rw [Real.exp_lt_one_iff]
      linarith
    calc
      (2 / T) * chapter10BSeriesTail T m ≤
          (2 / T) * ((1 + T) * Real.exp (-((2 * m + 3 : ℕ) : ℝ) * T) /
            (1 - Real.exp (-2 * T))) :=
        mul_le_mul_of_nonneg_left htail.2 (le_of_lt hscale)
      _ = (2 / T) * (1 + T) * Real.exp (-((2 * m + 3 : ℕ) : ℝ) * T) /
          (1 - Real.exp (-2 * T)) := by
        field_simp [ne_of_gt hden]

private theorem chapter10_omitted_B_series_first_row_lt_aux :
    (2 / (17 / 5 : ℝ)) * chapter10BSeriesTail (17 / 5 : ℝ) 1 <
      (1.072709 : ℝ) * 10 ^ (-7 : ℤ) := by
  have h17raw := chapter10_alternating_exp_remainder_bound
    (r := (17 : ℝ)) (by norm_num) (M := 100) (by norm_num)
  have h17id := chapter10_alternating_exp_series_identity (17 : ℝ) 100
  have h17le : Real.exp (-17) ≤
      chapter10AlternatingExpPartialSum 17 100 := by
    have hsign : (-1 : ℝ) ^ (100 + 1) = -1 := by norm_num
    rw [hsign] at h17raw
    rw [h17id]
    linarith [h17raw.1]
  have h17 : Real.exp (-17) < (413994 : ℝ) / 10 ^ 13 := by
    calc
      Real.exp (-17) ≤ chapter10AlternatingExpPartialSum 17 100 := h17le
      _ < (413994 : ℝ) / 10 ^ 13 := by
        norm_num [chapter10AlternatingExpPartialSum, Finset.sum_range_succ]
  have h68raw := chapter10_alternating_exp_remainder_bound
    (r := (34 / 5 : ℝ)) (by norm_num) (M := 50) (by norm_num)
  have h68id := chapter10_alternating_exp_series_identity (34 / 5 : ℝ) 50
  have h68le : Real.exp (-(34 / 5 : ℝ)) ≤
      chapter10AlternatingExpPartialSum (34 / 5 : ℝ) 50 := by
    have hsign : (-1 : ℝ) ^ (50 + 1) = -1 := by norm_num
    rw [hsign] at h68raw
    rw [h68id]
    linarith [h68raw.1]
  have h68 : Real.exp (-(34 / 5 : ℝ)) < (111378 : ℝ) / 10 ^ 8 := by
    calc
      Real.exp (-(34 / 5 : ℝ)) ≤
          chapter10AlternatingExpPartialSum (34 / 5 : ℝ) 50 := h68le
      _ < (111378 : ℝ) / 10 ^ 8 := by
        norm_num [chapter10AlternatingExpPartialSum, Finset.sum_range_succ]
  have hbound := chapter10_omitted_B_series_contribution_bound_aux
    (T := (17 / 5 : ℝ)) (by norm_num) 1
  have hden : 0 < 1 - Real.exp (-(34 / 5 : ℝ)) := by
    linarith [h68]
  calc
    (2 / (17 / 5 : ℝ)) * chapter10BSeriesTail (17 / 5 : ℝ) 1 ≤
        (2 / (17 / 5 : ℝ)) * (1 + (17 / 5 : ℝ)) *
          Real.exp (-17) / (1 - Real.exp (-(34 / 5 : ℝ))) := by
      convert hbound.2 using 1 ; norm_num
    _ < (1.072709 : ℝ) * 10 ^ (-7 : ℤ) := by
      apply (div_lt_iff₀ hden).2
      nlinarith [h17, h68]

private theorem chapter10_omitted_B_series_rows_lt_aux :
    ((2 / (9 / 2 : ℝ)) * chapter10BSeriesTail (9 / 2 : ℝ) 1 <
        (4.136261 : ℝ) * 10 ^ (-10 : ℤ)) ∧
      ((2 / (6 : ℝ)) * chapter10BSeriesTail 6 1 <
        (2.183459 : ℝ) * 10 ^ (-13 : ℤ)) := by
  have h45raw := chapter10_alternating_exp_remainder_bound
    (r := (45 / 2 : ℝ)) (by norm_num) (M := 100) (by norm_num)
  have h45id := chapter10_alternating_exp_series_identity (45 / 2 : ℝ) 100
  have h45le : Real.exp (-(45 / 2 : ℝ)) ≤
      chapter10AlternatingExpPartialSum (45 / 2 : ℝ) 100 := by
    have hsign : (-1 : ℝ) ^ (100 + 1) = -1 := by norm_num
    rw [hsign] at h45raw
    rw [h45id]
    linarith [h45raw.1]
  have h45 : Real.exp (-(45 / 2 : ℝ)) < (169189793 : ℝ) / 10 ^ 18 := by
    calc
      Real.exp (-(45 / 2 : ℝ)) ≤
          chapter10AlternatingExpPartialSum (45 / 2 : ℝ) 100 := h45le
      _ < (169189793 : ℝ) / 10 ^ 18 := by
        norm_num [chapter10AlternatingExpPartialSum, Finset.sum_range_succ]
  have h9raw := chapter10_alternating_exp_remainder_bound
    (r := (9 : ℝ)) (by norm_num) (M := 50) (by norm_num)
  have h9id := chapter10_alternating_exp_series_identity (9 : ℝ) 50
  have h9le : Real.exp (-9) ≤
      chapter10AlternatingExpPartialSum 9 50 := by
    have hsign : (-1 : ℝ) ^ (50 + 1) = -1 := by norm_num
    rw [hsign] at h9raw
    rw [h9id]
    linarith [h9raw.1]
  have h9 : Real.exp (-9) < (1234099 : ℝ) / 10 ^ 10 := by
    calc
      Real.exp (-9) ≤ chapter10AlternatingExpPartialSum 9 50 := h9le
      _ < (1234099 : ℝ) / 10 ^ 10 := by
        norm_num [chapter10AlternatingExpPartialSum, Finset.sum_range_succ]
  have h30raw := chapter10_alternating_exp_remainder_bound
    (r := (30 : ℝ)) (by norm_num) (M := 200) (by norm_num)
  have h30id := chapter10_alternating_exp_series_identity (30 : ℝ) 200
  have h30le : Real.exp (-30) ≤
      chapter10AlternatingExpPartialSum 30 200 := by
    have hsign : (-1 : ℝ) ^ (200 + 1) = -1 := by norm_num
    rw [hsign] at h30raw
    rw [h30id]
    linarith [h30raw.1]
  have h30 : Real.exp (-30) < (9357623 : ℝ) / 10 ^ 20 := by
    calc
      Real.exp (-30) ≤ chapter10AlternatingExpPartialSum 30 200 := h30le
      _ < (9357623 : ℝ) / 10 ^ 20 := by
        norm_num [chapter10AlternatingExpPartialSum, Finset.sum_range_succ]
  have h12raw := chapter10_alternating_exp_remainder_bound
    (r := (12 : ℝ)) (by norm_num) (M := 50) (by norm_num)
  have h12id := chapter10_alternating_exp_series_identity (12 : ℝ) 50
  have h12le : Real.exp (-12) ≤
      chapter10AlternatingExpPartialSum 12 50 := by
    have hsign : (-1 : ℝ) ^ (50 + 1) = -1 := by norm_num
    rw [hsign] at h12raw
    rw [h12id]
    linarith [h12raw.1]
  have h12 : Real.exp (-12) < (61443 : ℝ) / 10 ^ 10 := by
    calc
      Real.exp (-12) ≤ chapter10AlternatingExpPartialSum 12 50 := h12le
      _ < (61443 : ℝ) / 10 ^ 10 := by
        norm_num [chapter10AlternatingExpPartialSum, Finset.sum_range_succ]
  have hbound45 := chapter10_omitted_B_series_contribution_bound_aux
    (T := (9 / 2 : ℝ)) (by norm_num) 1
  have hbound6 := chapter10_omitted_B_series_contribution_bound_aux
    (T := (6 : ℝ)) (by norm_num) 1
  have hden9 : 0 < 1 - Real.exp (-9) := by linarith [h9]
  have hden12 : 0 < 1 - Real.exp (-12) := by linarith [h12]
  constructor
  · calc
      (2 / (9 / 2 : ℝ)) * chapter10BSeriesTail (9 / 2 : ℝ) 1 ≤
          (2 / (9 / 2 : ℝ)) * (1 + (9 / 2 : ℝ)) *
            Real.exp (-(45 / 2 : ℝ)) / (1 - Real.exp (-9)) := by
        convert hbound45.2 using 1 ; norm_num
      _ < (4.136261 : ℝ) * 10 ^ (-10 : ℤ) := by
        apply (div_lt_iff₀ hden9).2
        nlinarith [h45, h9]
  · calc
      (2 / (6 : ℝ)) * chapter10BSeriesTail 6 1 ≤
          (2 / (6 : ℝ)) * (1 + (6 : ℝ)) * Real.exp (-30) /
            (1 - Real.exp (-12)) := by
        convert hbound6.2 using 1 ; norm_num
      _ < (2.183459 : ℝ) * 10 ^ (-13 : ℤ) := by
        apply (div_lt_iff₀ hden12).2
        nlinarith [h30, h12]

structure Chapter10ArchimedeanLedgerRow where
  T : ℚ
  A : ℚ
  B_lower : ℚ
  B_upper : ℚ
  C_lower : ℚ
  C_upper : ℚ

def chapter10RowSeventeenOverFive : Chapter10ArchimedeanLedgerRow :=
  { T := 17 / 5
    A := 17 / 10
    B_lower := 139921 / 100000
    B_upper := 139923 / 100000
    C_lower := 95921 / 100000
    C_upper := 95923 / 100000 }

def chapter10RowNineHalves : Chapter10ArchimedeanLedgerRow :=
  { T := 9 / 2
    A := 9 / 4
    B_lower := 123652 / 100000
    B_upper := 123653 / 100000
    C_lower := 87395 / 100000
    C_upper := 87396 / 100000 }

def chapter10RowSix : Chapter10ArchimedeanLedgerRow :=
  { T := 6
    A := 3
    B_lower := 110355 / 100000
    B_upper := 110356 / 100000
    C_lower := 80102 / 100000
    C_upper := 80103 / 100000 }

theorem chapter10_archimedean_ledger_row_seventeen_over_five :
    chapter10AT (17 / 5 : ℝ) = 17 / 10 ∧
      (chapter10RowSeventeenOverFive.B_lower : ℝ) < chapter10BT (17 / 5 : ℝ) ∧
      chapter10BT (17 / 5 : ℝ) < (chapter10RowSeventeenOverFive.B_upper : ℝ) ∧
      (chapter10RowSeventeenOverFive.C_lower : ℝ) < chapter10CT (17 / 5 : ℝ) ∧
      chapter10CT (17 / 5 : ℝ) < (chapter10RowSeventeenOverFive.C_upper : ℝ) := by
  have hT : 0 < (17 / 5 : ℝ) := by norm_num
  have hB := chapter10_B_finite_formula hT
  rw [← chapter10_B_series_first_two_decomposition hT] at hB
  have hC := chapter10_C_finite_formula hT
  rw [chapter10_log_cosh_half_rewrite hT] at hC
  have hpi := chapter10_pi_directed_bounds
  norm_num [chapter10PiLower, chapter10PiUpper] at hpi
  have hpi2lo :
      ((3141592653589793 / 10 ^ 15 : ℝ) ^ 2) < Real.pi ^ 2 := by
    have hpos : 0 < Real.pi + (3141592653589793 / 10 ^ 15 : ℝ) := by
      nlinarith [hpi.1]
    have hmul := mul_pos (sub_pos.mpr hpi.1) hpos
    nlinarith
  have hpi2hi : Real.pi ^ 2 <
      (3141592653589794 / 10 ^ 15 : ℝ) ^ 2 := by
    have hpos : 0 < (3141592653589794 / 10 ^ 15 : ℝ) + Real.pi := by
      nlinarith [hpi.1]
    have hmul := mul_pos (sub_pos.mpr hpi.2) hpos
    nlinarith
  have hlog2 := chapter10_log_two_box
  have hlogs := chapter10_archimedean_log_boxes
  rcases hlogs with ⟨h17c, h17p, h9c, h9p, h6c, h6p⟩
  have hexps := chapter10_exp_boxes
  rcases hexps with ⟨hq17lo, hq17hi, hq9lo, hq9hi, hq6lo, hq6hi⟩
  have hterm0 : chapter10BSeriesTerm (17 / 5 : ℝ) 0 =
      (1 + (17 / 5 : ℝ)) * Real.exp (-(17 / 5 : ℝ)) := by
    norm_num [chapter10BSeriesTerm, chapter08BSeriesTerm, chapter08Odd]
  have hexp3 : Real.exp (-(51 / 5 : ℝ)) =
      (Real.exp (-(17 / 5 : ℝ))) ^ 3 := by
    calc
      Real.exp (-(51 / 5 : ℝ)) =
          Real.exp ((3 : ℕ) * (-(17 / 5 : ℝ))) := by
            congr 1
            norm_num
      _ = (Real.exp (-(17 / 5 : ℝ))) ^ 3 := by
        simpa using (Real.exp_nat_mul (-(17 / 5 : ℝ)) 3)
  have hterm1 : chapter10BSeriesTerm (17 / 5 : ℝ) 1 =
      ((1 + 3 * (17 / 5 : ℝ)) / 9) *
        (Real.exp (-(17 / 5 : ℝ))) ^ 3 := by
    norm_num [chapter10BSeriesTerm, chapter08BSeriesTerm, chapter08Odd]
    rw [hexp3]
    ring
  rw [hterm0, hterm1] at hB
  have hq17powlo :
      (333732 / 10 ^ 7 : ℝ) ^ 3 ≤
        (Real.exp (-(17 / 5 : ℝ))) ^ 3 :=
    chapter10_nonneg_pow_mono (by norm_num) (le_of_lt hq17lo) 3
  have hq17powhi :
      (Real.exp (-(17 / 5 : ℝ))) ^ 3 ≤ (333733 / 10 ^ 7 : ℝ) ^ 3 :=
    chapter10_nonneg_pow_mono (by positivity) (le_of_lt hq17hi) 3
  have hSlo : (1468883 / 10 ^ 7 : ℝ) <
      (1 + (17 / 5 : ℝ)) * Real.exp (-(17 / 5 : ℝ)) +
        ((1 + 3 * (17 / 5 : ℝ)) / 9) *
          (Real.exp (-(17 / 5 : ℝ))) ^ 3 := by
    nlinarith [hq17lo, hq17powlo]
  have hShi :
      (1 + (17 / 5 : ℝ)) * Real.exp (-(17 / 5 : ℝ)) +
        ((1 + 3 * (17 / 5 : ℝ)) / 9) *
          (Real.exp (-(17 / 5 : ℝ))) ^ 3 < (1468888 / 10 ^ 7 : ℝ) := by
    nlinarith [hq17hi, hq17powhi]
  have htail := chapter10_omitted_B_series_contribution_bound_aux
    (T := (17 / 5 : ℝ)) hT 1
  have htailsmall := chapter10_omitted_B_series_first_row_lt_aux
  norm_num at hB hC htail htailsmall hSlo hShi hpi2lo hpi2hi
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · norm_num [chapter10AT]
  · have h : (139921 / 100000 : ℝ) < chapter10BT (17 / 5 : ℝ) := by
      linarith [hB, hlog2.1, hpi2lo, h17c.1, hShi, htailsmall]
    simpa [chapter10RowSeventeenOverFive] using h
  · have h : chapter10BT (17 / 5 : ℝ) < (139923 / 100000 : ℝ) := by
      linarith [hB, hlog2.2, hpi2hi, h17c.2, hSlo, htail.1]
    simpa [chapter10RowSeventeenOverFive] using h
  · have h : (95921 / 100000 : ℝ) < chapter10CT (17 / 5 : ℝ) := by
      linarith [hC, hpi.1, hlog2.2, h17p.2]
    simpa [chapter10RowSeventeenOverFive] using h
  · have h : chapter10CT (17 / 5 : ℝ) < (95923 / 100000 : ℝ) := by
      linarith [hC, hpi.2, hlog2.1, h17p.1]
    simpa [chapter10RowSeventeenOverFive] using h

theorem chapter10_archimedean_ledger_row_nine_halves :
    chapter10AT (9 / 2 : ℝ) = 9 / 4 ∧
      (chapter10RowNineHalves.B_lower : ℝ) < chapter10BT (9 / 2 : ℝ) ∧
      chapter10BT (9 / 2 : ℝ) < (chapter10RowNineHalves.B_upper : ℝ) ∧
      (chapter10RowNineHalves.C_lower : ℝ) < chapter10CT (9 / 2 : ℝ) ∧
      chapter10CT (9 / 2 : ℝ) < (chapter10RowNineHalves.C_upper : ℝ) := by
  have hT : 0 < (9 / 2 : ℝ) := by norm_num
  have hB := chapter10_B_finite_formula hT
  rw [← chapter10_B_series_first_two_decomposition hT] at hB
  have hC := chapter10_C_finite_formula hT
  rw [chapter10_log_cosh_half_rewrite hT] at hC
  have hpi := chapter10_pi_directed_bounds
  norm_num [chapter10PiLower, chapter10PiUpper] at hpi
  have hpi2lo :
      ((3141592653589793 / 10 ^ 15 : ℝ) ^ 2) < Real.pi ^ 2 := by
    have hpos : 0 < Real.pi + (3141592653589793 / 10 ^ 15 : ℝ) := by
      nlinarith [hpi.1]
    have hmul := mul_pos (sub_pos.mpr hpi.1) hpos
    nlinarith
  have hpi2hi : Real.pi ^ 2 <
      (3141592653589794 / 10 ^ 15 : ℝ) ^ 2 := by
    have hpos : 0 < (3141592653589794 / 10 ^ 15 : ℝ) + Real.pi := by
      nlinarith [hpi.1]
    have hmul := mul_pos (sub_pos.mpr hpi.2) hpos
    nlinarith
  have hlog2 := chapter10_log_two_box
  have hlogs := chapter10_archimedean_log_boxes
  rcases hlogs with ⟨h17c, h17p, h9c, h9p, h6c, h6p⟩
  have hexps := chapter10_exp_boxes
  rcases hexps with ⟨hq17lo, hq17hi, hq9lo, hq9hi, hq6lo, hq6hi⟩
  have hterm0 : chapter10BSeriesTerm (9 / 2 : ℝ) 0 =
      (1 + (9 / 2 : ℝ)) * Real.exp (-(9 / 2 : ℝ)) := by
    norm_num [chapter10BSeriesTerm, chapter08BSeriesTerm, chapter08Odd]
  have hexp3 : Real.exp (-(27 / 2 : ℝ)) =
      (Real.exp (-(9 / 2 : ℝ))) ^ 3 := by
    calc
      Real.exp (-(27 / 2 : ℝ)) =
          Real.exp ((3 : ℕ) * (-(9 / 2 : ℝ))) := by
            congr 1
            norm_num
      _ = (Real.exp (-(9 / 2 : ℝ))) ^ 3 := by
        simpa using (Real.exp_nat_mul (-(9 / 2 : ℝ)) 3)
  have hterm1 : chapter10BSeriesTerm (9 / 2 : ℝ) 1 =
      ((1 + 3 * (9 / 2 : ℝ)) / 9) *
        (Real.exp (-(9 / 2 : ℝ))) ^ 3 := by
    norm_num [chapter10BSeriesTerm, chapter08BSeriesTerm, chapter08Odd]
    rw [hexp3]
    ring
  rw [hterm0, hterm1] at hB
  have hq9powlo :
      (111089 / 10 ^ 7 : ℝ) ^ 3 ≤
        (Real.exp (-(9 / 2 : ℝ))) ^ 3 :=
    chapter10_nonneg_pow_mono (by norm_num) (le_of_lt hq9lo) 3
  have hq9powhi :
      (Real.exp (-(9 / 2 : ℝ))) ^ 3 ≤ (111090 / 10 ^ 7 : ℝ) ^ 3 :=
    chapter10_nonneg_pow_mono (by positivity) (le_of_lt hq9hi) 3
  have hSlo : (611011 / 10 ^ 7 : ℝ) <
      (1 + (9 / 2 : ℝ)) * Real.exp (-(9 / 2 : ℝ)) +
        ((1 + 3 * (9 / 2 : ℝ)) / 9) *
          (Real.exp (-(9 / 2 : ℝ))) ^ 3 := by
    nlinarith [hq9lo, hq9powlo]
  have hShi :
      (1 + (9 / 2 : ℝ)) * Real.exp (-(9 / 2 : ℝ)) +
        ((1 + 3 * (9 / 2 : ℝ)) / 9) *
          (Real.exp (-(9 / 2 : ℝ))) ^ 3 < (611018 / 10 ^ 7 : ℝ) := by
    nlinarith [hq9hi, hq9powhi]
  have htail := chapter10_omitted_B_series_contribution_bound_aux
    (T := (9 / 2 : ℝ)) hT 1
  have htailsmall := chapter10_omitted_B_series_rows_lt_aux
  norm_num at hB hC htail htailsmall hSlo hShi hpi2lo hpi2hi
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · norm_num [chapter10AT]
  · have h : (123652 / 100000 : ℝ) < chapter10BT (9 / 2 : ℝ) := by
      linarith [hB, hlog2.1, hpi2lo, h9c.1, hShi, htailsmall.1]
    simpa [chapter10RowNineHalves] using h
  · have h : chapter10BT (9 / 2 : ℝ) < (123653 / 100000 : ℝ) := by
      linarith [hB, hlog2.2, hpi2hi, h9c.2, hSlo, htail.1]
    simpa [chapter10RowNineHalves] using h
  · have h : (87395 / 100000 : ℝ) < chapter10CT (9 / 2 : ℝ) := by
      linarith [hC, hpi.1, hlog2.2, h9p.2]
    simpa [chapter10RowNineHalves] using h
  · have h : chapter10CT (9 / 2 : ℝ) < (87396 / 100000 : ℝ) := by
      linarith [hC, hpi.2, hlog2.1, h9p.1]
    simpa [chapter10RowNineHalves] using h

theorem chapter10_archimedean_ledger_row_six :
    chapter10AT 6 = 3 ∧
      (chapter10RowSix.B_lower : ℝ) < chapter10BT 6 ∧
      chapter10BT 6 < (chapter10RowSix.B_upper : ℝ) ∧
      (chapter10RowSix.C_lower : ℝ) < chapter10CT 6 ∧
      chapter10CT 6 < (chapter10RowSix.C_upper : ℝ) := by
  have hT : 0 < (6 : ℝ) := by norm_num
  have hB := chapter10_B_finite_formula hT
  rw [← chapter10_B_series_first_two_decomposition hT] at hB
  have hC := chapter10_C_finite_formula hT
  rw [chapter10_log_cosh_half_rewrite hT] at hC
  have hpi := chapter10_pi_directed_bounds
  norm_num [chapter10PiLower, chapter10PiUpper] at hpi
  have hpi2lo :
      ((3141592653589793 / 10 ^ 15 : ℝ) ^ 2) < Real.pi ^ 2 := by
    have hpos : 0 < Real.pi + (3141592653589793 / 10 ^ 15 : ℝ) := by
      nlinarith [hpi.1]
    have hmul := mul_pos (sub_pos.mpr hpi.1) hpos
    nlinarith
  have hpi2hi : Real.pi ^ 2 <
      (3141592653589794 / 10 ^ 15 : ℝ) ^ 2 := by
    have hpos : 0 < (3141592653589794 / 10 ^ 15 : ℝ) + Real.pi := by
      nlinarith [hpi.1]
    have hmul := mul_pos (sub_pos.mpr hpi.2) hpos
    nlinarith
  have hlog2 := chapter10_log_two_box
  have hlogs := chapter10_archimedean_log_boxes
  rcases hlogs with ⟨h17c, h17p, h9c, h9p, h6c, h6p⟩
  have hexps := chapter10_exp_boxes
  rcases hexps with ⟨hq17lo, hq17hi, hq9lo, hq9hi, hq6lo, hq6hi⟩
  have hterm0 : chapter10BSeriesTerm 6 0 =
      (1 + (6 : ℝ)) * Real.exp (-6) := by
    norm_num [chapter10BSeriesTerm, chapter08BSeriesTerm, chapter08Odd]
  have hexp3 : Real.exp (-18 : ℝ) = (Real.exp (-6)) ^ 3 := by
    calc
      Real.exp (-18 : ℝ) = Real.exp ((3 : ℕ) * (-6 : ℝ)) := by
        congr 1
        norm_num
      _ = (Real.exp (-6)) ^ 3 := by
        simpa using (Real.exp_nat_mul (-6 : ℝ) 3)
  have hterm1 : chapter10BSeriesTerm 6 1 =
      ((1 + 3 * (6 : ℝ)) / 9) * (Real.exp (-6)) ^ 3 := by
    norm_num [chapter10BSeriesTerm, chapter08BSeriesTerm, chapter08Odd]
    rw [hexp3]
    ring
  rw [hterm0, hterm1] at hB
  have hq6powlo :
      (24787 / 10 ^ 7 : ℝ) ^ 3 ≤ (Real.exp (-6)) ^ 3 :=
    chapter10_nonneg_pow_mono (by norm_num) (le_of_lt hq6lo) 3
  have hq6powhi :
      (Real.exp (-6)) ^ 3 ≤ (24788 / 10 ^ 7 : ℝ) ^ 3 :=
    chapter10_nonneg_pow_mono (by positivity) (le_of_lt hq6hi) 3
  have hSlo : (173509 / 10 ^ 7 : ℝ) <
      (1 + (6 : ℝ)) * Real.exp (-6) +
        ((1 + 3 * (6 : ℝ)) / 9) * (Real.exp (-6)) ^ 3 := by
    nlinarith [hq6lo, hq6powlo]
  have hShi :
      (1 + (6 : ℝ)) * Real.exp (-6) +
        ((1 + 3 * (6 : ℝ)) / 9) * (Real.exp (-6)) ^ 3 <
          (173517 / 10 ^ 7 : ℝ) := by
    nlinarith [hq6hi, hq6powhi]
  have htail := chapter10_omitted_B_series_contribution_bound_aux
    (T := (6 : ℝ)) hT 1
  have htailsmall := chapter10_omitted_B_series_rows_lt_aux
  norm_num at hB hC htail htailsmall hSlo hShi hpi2lo hpi2hi
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · norm_num [chapter10AT]
  · have h : (110355 / 100000 : ℝ) < chapter10BT 6 := by
      linarith [hB, hlog2.1, hpi2lo, h6c.1, hShi, htailsmall.2]
    simpa [chapter10RowSix] using h
  · have h : chapter10BT 6 < (110356 / 100000 : ℝ) := by
      linarith [hB, hlog2.2, hpi2hi, h6c.2, hSlo, htail.1]
    simpa [chapter10RowSix] using h
  · have h : (80102 / 100000 : ℝ) < chapter10CT 6 := by
      linarith [hC, hpi.1, hlog2.2, h6p.2]
    simpa [chapter10RowSix] using h
  · have h : chapter10CT 6 < (80103 / 100000 : ℝ) := by
      linarith [hC, hpi.2, hlog2.1, h6p.1]
    simpa [chapter10RowSix] using h

theorem chapter10_omitted_B_series_contribution_bound
    {T : ℝ} (hT : 0 < T) (m : ℕ) :
    0 ≤ (2 / T) * chapter10BSeriesTail T m ∧
      (2 / T) * chapter10BSeriesTail T m ≤
        (2 / T) * (1 + T) * Real.exp (-((2 * m + 3 : ℕ) : ℝ) * T) /
          (1 - Real.exp (-2 * T)) := by
  have htail := chapter10_B_series_tail_bound hT m
  have hscale : 0 < 2 / T := by positivity
  constructor
  · exact mul_nonneg (le_of_lt hscale) htail.1
  · have hden : 0 < 1 - Real.exp (-2 * T) := by
      apply sub_pos.mpr
      rw [Real.exp_lt_one_iff]
      linarith
    calc
      (2 / T) * chapter10BSeriesTail T m ≤
          (2 / T) * ((1 + T) * Real.exp (-((2 * m + 3 : ℕ) : ℝ) * T) /
            (1 - Real.exp (-2 * T))) :=
        mul_le_mul_of_nonneg_left htail.2 (le_of_lt hscale)
      _ = (2 / T) * (1 + T) * Real.exp (-((2 * m + 3 : ℕ) : ℝ) * T) /
          (1 - Real.exp (-2 * T)) := by
        field_simp [ne_of_gt hden]

theorem chapter10_omitted_B_series_first_row_lt :
    (2 / (17 / 5 : ℝ)) * chapter10BSeriesTail (17 / 5 : ℝ) 1 <
      (1.072709 : ℝ) * 10 ^ (-7 : ℤ) := by
  have h17raw := chapter10_alternating_exp_remainder_bound
    (r := (17 : ℝ)) (by norm_num) (M := 100) (by norm_num)
  have h17id := chapter10_alternating_exp_series_identity (17 : ℝ) 100
  have h17le : Real.exp (-17) ≤
      chapter10AlternatingExpPartialSum 17 100 := by
    have hsign : (-1 : ℝ) ^ (100 + 1) = -1 := by norm_num
    rw [hsign] at h17raw
    rw [h17id]
    linarith [h17raw.1]
  have h17 : Real.exp (-17) < (413994 : ℝ) / 10 ^ 13 := by
    calc
      Real.exp (-17) ≤ chapter10AlternatingExpPartialSum 17 100 := h17le
      _ < (413994 : ℝ) / 10 ^ 13 := by
        norm_num [chapter10AlternatingExpPartialSum, Finset.sum_range_succ]
  have h68raw := chapter10_alternating_exp_remainder_bound
    (r := (34 / 5 : ℝ)) (by norm_num) (M := 50) (by norm_num)
  have h68id := chapter10_alternating_exp_series_identity (34 / 5 : ℝ) 50
  have h68le : Real.exp (-(34 / 5 : ℝ)) ≤
      chapter10AlternatingExpPartialSum (34 / 5 : ℝ) 50 := by
    have hsign : (-1 : ℝ) ^ (50 + 1) = -1 := by norm_num
    rw [hsign] at h68raw
    rw [h68id]
    linarith [h68raw.1]
  have h68 : Real.exp (-(34 / 5 : ℝ)) < (111378 : ℝ) / 10 ^ 8 := by
    calc
      Real.exp (-(34 / 5 : ℝ)) ≤
          chapter10AlternatingExpPartialSum (34 / 5 : ℝ) 50 := h68le
      _ < (111378 : ℝ) / 10 ^ 8 := by
        norm_num [chapter10AlternatingExpPartialSum, Finset.sum_range_succ]
  have hbound := chapter10_omitted_B_series_contribution_bound
    (T := (17 / 5 : ℝ)) (by norm_num) 1
  have hden : 0 < 1 - Real.exp (-(34 / 5 : ℝ)) := by
    linarith [h68]
  calc
    (2 / (17 / 5 : ℝ)) * chapter10BSeriesTail (17 / 5 : ℝ) 1 ≤
        (2 / (17 / 5 : ℝ)) * (1 + (17 / 5 : ℝ)) *
          Real.exp (-17) / (1 - Real.exp (-(34 / 5 : ℝ))) := by
      convert hbound.2 using 1; norm_num
    _ < (1.072709 : ℝ) * 10 ^ (-7 : ℤ) := by
      apply (div_lt_iff₀ hden).2
      nlinarith [h17, h68]

theorem chapter10_omitted_B_series_rows_lt :
    ((2 / (9 / 2 : ℝ)) * chapter10BSeriesTail (9 / 2 : ℝ) 1 <
        (4.136261 : ℝ) * 10 ^ (-10 : ℤ)) ∧
      ((2 / (6 : ℝ)) * chapter10BSeriesTail 6 1 <
        (2.183459 : ℝ) * 10 ^ (-13 : ℤ)) := by
  have h45raw := chapter10_alternating_exp_remainder_bound
    (r := (45 / 2 : ℝ)) (by norm_num) (M := 100) (by norm_num)
  have h45id := chapter10_alternating_exp_series_identity (45 / 2 : ℝ) 100
  have h45le : Real.exp (-(45 / 2 : ℝ)) ≤
      chapter10AlternatingExpPartialSum (45 / 2 : ℝ) 100 := by
    have hsign : (-1 : ℝ) ^ (100 + 1) = -1 := by norm_num
    rw [hsign] at h45raw
    rw [h45id]
    linarith [h45raw.1]
  have h45 : Real.exp (-(45 / 2 : ℝ)) < (169189793 : ℝ) / 10 ^ 18 := by
    calc
      Real.exp (-(45 / 2 : ℝ)) ≤
          chapter10AlternatingExpPartialSum (45 / 2 : ℝ) 100 := h45le
      _ < (169189793 : ℝ) / 10 ^ 18 := by
        norm_num [chapter10AlternatingExpPartialSum, Finset.sum_range_succ]
  have h9raw := chapter10_alternating_exp_remainder_bound
    (r := (9 : ℝ)) (by norm_num) (M := 50) (by norm_num)
  have h9id := chapter10_alternating_exp_series_identity (9 : ℝ) 50
  have h9le : Real.exp (-9) ≤
      chapter10AlternatingExpPartialSum 9 50 := by
    have hsign : (-1 : ℝ) ^ (50 + 1) = -1 := by norm_num
    rw [hsign] at h9raw
    rw [h9id]
    linarith [h9raw.1]
  have h9 : Real.exp (-9) < (1234099 : ℝ) / 10 ^ 10 := by
    calc
      Real.exp (-9) ≤ chapter10AlternatingExpPartialSum 9 50 := h9le
      _ < (1234099 : ℝ) / 10 ^ 10 := by
        norm_num [chapter10AlternatingExpPartialSum, Finset.sum_range_succ]
  have h30raw := chapter10_alternating_exp_remainder_bound
    (r := (30 : ℝ)) (by norm_num) (M := 200) (by norm_num)
  have h30id := chapter10_alternating_exp_series_identity (30 : ℝ) 200
  have h30le : Real.exp (-30) ≤
      chapter10AlternatingExpPartialSum 30 200 := by
    have hsign : (-1 : ℝ) ^ (200 + 1) = -1 := by norm_num
    rw [hsign] at h30raw
    rw [h30id]
    linarith [h30raw.1]
  have h30 : Real.exp (-30) < (9357623 : ℝ) / 10 ^ 20 := by
    calc
      Real.exp (-30) ≤ chapter10AlternatingExpPartialSum 30 200 := h30le
      _ < (9357623 : ℝ) / 10 ^ 20 := by
        norm_num [chapter10AlternatingExpPartialSum, Finset.sum_range_succ]
  have h12raw := chapter10_alternating_exp_remainder_bound
    (r := (12 : ℝ)) (by norm_num) (M := 50) (by norm_num)
  have h12id := chapter10_alternating_exp_series_identity (12 : ℝ) 50
  have h12le : Real.exp (-12) ≤
      chapter10AlternatingExpPartialSum 12 50 := by
    have hsign : (-1 : ℝ) ^ (50 + 1) = -1 := by norm_num
    rw [hsign] at h12raw
    rw [h12id]
    linarith [h12raw.1]
  have h12 : Real.exp (-12) < (61443 : ℝ) / 10 ^ 10 := by
    calc
      Real.exp (-12) ≤ chapter10AlternatingExpPartialSum 12 50 := h12le
      _ < (61443 : ℝ) / 10 ^ 10 := by
        norm_num [chapter10AlternatingExpPartialSum, Finset.sum_range_succ]
  have hbound45 := chapter10_omitted_B_series_contribution_bound
    (T := (9 / 2 : ℝ)) (by norm_num) 1
  have hbound6 := chapter10_omitted_B_series_contribution_bound
    (T := (6 : ℝ)) (by norm_num) 1
  have hden9 : 0 < 1 - Real.exp (-9) := by linarith [h9]
  have hden12 : 0 < 1 - Real.exp (-12) := by linarith [h12]
  constructor
  · calc
      (2 / (9 / 2 : ℝ)) * chapter10BSeriesTail (9 / 2 : ℝ) 1 ≤
          (2 / (9 / 2 : ℝ)) * (1 + (9 / 2 : ℝ)) *
            Real.exp (-(45 / 2 : ℝ)) / (1 - Real.exp (-9)) := by
        convert hbound45.2 using 1; norm_num
      _ < (4.136261 : ℝ) * 10 ^ (-10 : ℤ) := by
        apply (div_lt_iff₀ hden9).2
        nlinarith [h45, h9]
  · calc
      (2 / (6 : ℝ)) * chapter10BSeriesTail 6 1 ≤
          (2 / (6 : ℝ)) * (1 + (6 : ℝ)) * Real.exp (-30) /
            (1 - Real.exp (-12)) := by
        convert hbound6.2 using 1; norm_num
      _ < (2.183459 : ℝ) * 10 ^ (-13 : ℤ) := by
        apply (div_lt_iff₀ hden12).2
        nlinarith [h30, h12]

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter10
