import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Order.Interval.Finset.Floor
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter07.Dependencies
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.Section03PositiveType

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter07

noncomputable section

open MeasureTheory Filter
open scoped Topology
open scoped BigOperators ContDiff Pointwise
open scoped Convolution FourierTransform

/- Fourier positivity is the condition used for the zero term; pointwise
   positivity is the condition used for the prime-power term. -/
def chapter07PrimePositivityCone : Set Chapter07TestFunction :=
  {f | chapter07PointwiseNonnegative f}

def chapter07ZeroPositivityCone : Set Chapter07TestFunction :=
  {f | chapter07FourierNonnegative f}

def chapter07RequiredPositivityCone : Set Chapter07TestFunction :=
  chapter07PrimePositivityCone ∩ chapter07ZeroPositivityCone

theorem chapter07_mem_requiredPositivityCone_iff (f : Chapter07TestFunction) :
    f ∈ chapter07RequiredPositivityCone ↔
      chapter07PointwiseNonnegative f ∧ chapter07FourierNonnegative f := by
  rfl

def chapter07FinitePrimeContribution
    {α : Type*} (weight : α → ℝ) (known : Finset α) : ℝ :=
  Finset.sum known (fun p => weight p)

theorem chapter07_finitePrimeContribution_nonnegative
    {α : Type*} (weight : α → ℝ) (known : Finset α)
    (hweight : ∀ p, 0 ≤ weight p) :
    0 ≤ chapter07FinitePrimeContribution weight known := by
  simp only [chapter07FinitePrimeContribution]
  exact Finset.sum_nonneg (fun p hp => hweight p)

theorem chapter07_finitePrimeContribution_mono
    {α : Type*} (weight : α → ℝ) {known₁ known₂ : Finset α}
    (hknown : known₁ ⊆ known₂) (hweight : ∀ p, 0 ≤ weight p) :
    chapter07FinitePrimeContribution weight known₁ ≤
      chapter07FinitePrimeContribution weight known₂ := by
  simp only [chapter07FinitePrimeContribution]
  exact Finset.sum_le_sum_of_subset_of_nonneg hknown
    (fun p hp hnot => hweight p)

def chapter07WeightedPrimeContribution
    (f : Chapter07TestFunction) {α : Type*}
    (argument weight : α → ℝ) (known : Finset α) : ℝ :=
  Finset.sum known (fun p => weight p * f (argument p))

theorem chapter07_weightedPrimeContribution_nonnegative
    (f : Chapter07TestFunction) {α : Type*}
    (argument weight : α → ℝ) (known : Finset α)
    (hf : chapter07PointwiseNonnegative f)
    (hweight : ∀ p, 0 ≤ weight p) :
    0 ≤ chapter07WeightedPrimeContribution f argument weight known := by
  simp only [chapter07WeightedPrimeContribution]
  exact Finset.sum_nonneg (fun p hp =>
    mul_nonneg (hweight p) (hf (argument p)))

theorem chapter07_weightedPrimeContribution_mono
    (f : Chapter07TestFunction) {α : Type*}
    (argument weight : α → ℝ) {known₁ known₂ : Finset α}
    (hknown : known₁ ⊆ known₂)
    (hf : chapter07PointwiseNonnegative f)
    (hweight : ∀ p, 0 ≤ weight p) :
    chapter07WeightedPrimeContribution f argument weight known₁ ≤
      chapter07WeightedPrimeContribution f argument weight known₂ := by
  simp only [chapter07WeightedPrimeContribution]
  exact Finset.sum_le_sum_of_subset_of_nonneg hknown
    (fun p hp hnot => mul_nonneg (hweight p) (hf (argument p)))

theorem chapter07_discard_nonnegative_prime_term
    (base prime : ℝ) (hprime : 0 ≤ prime) :
    base ≤ base + prime := by
  linarith

def chapter07Gaussian (σ : ℝ) (x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2) / (2 * σ ^ 2))

theorem chapter07_gaussian_fourier_nonnegative (σ : ℝ) (hσ : 0 < σ) :
    chapter07FourierNonnegative (chapter07Gaussian σ) := by
  let b : ℝ := 1 / (2 * σ ^ 2)
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hgauss (x : ℝ) :
      chapter07Gaussian σ x = Real.exp (-b * x ^ 2) := by
    dsimp [chapter07Gaussian, b]
    congr 1
    ring
  have hint : Integrable (chapter07Gaussian σ) := by
    rw [show chapter07Gaussian σ = (fun x : ℝ => Real.exp (-b * x ^ 2)) by
      funext x; exact hgauss x]
    exact integrable_exp_neg_mul_sq hb
  refine ⟨hint, ?_⟩
  intro t
  have hformula :
      chapter07FourierTransform (chapter07Gaussian σ) t =
        ((((Real.pi / b) ^ (1 / 2 : ℝ) *
          Real.exp (-(t ^ 2 / (4 * b)))) : ℝ) : ℂ) := by
    rw [chapter07FourierTransform_eq_integral]
    calc
      (∫ x : ℝ, (chapter07Gaussian σ x : ℂ) *
          Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ))) =
          ∫ x : ℝ, Complex.exp (Complex.I * (-(t : ℂ)) * (x : ℂ)) *
            Complex.exp (-(b : ℂ) * (x : ℂ) ^ 2) := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [hgauss]
        simp only [Complex.ofReal_exp, Complex.ofReal_neg,
          Complex.ofReal_mul, Complex.ofReal_pow]
        rw [mul_comm]
        congr 1
        · congr 1
          ring
      _ = (Real.pi / (b : ℂ)) ^ (1 / 2 : ℂ) *
          Complex.exp (- (-(t : ℂ)) ^ 2 / (4 * (b : ℂ))) := by
        exact fourierIntegral_gaussian (b := (b : ℂ)) (by simpa using hb)
          (-(t : ℂ))
      _ = ((((Real.pi / b) ^ (1 / 2 : ℝ) *
          Real.exp (-(t ^ 2 / (4 * b)))) : ℝ) : ℂ) := by
        have harg :
            - (-(t : ℂ)) ^ 2 / (4 * (b : ℂ)) =
              (-(t ^ 2 / (4 * b)) : ℝ) := by
          norm_num
          ring
        have hpow :
            ((Real.pi / b : ℝ) : ℂ) ^ ((1 / 2 : ℝ) : ℂ) =
              (((Real.pi / b) ^ (1 / 2 : ℝ) : ℝ) : ℂ) :=
          (Complex.ofReal_cpow (by positivity : 0 ≤ Real.pi / b)
            (1 / 2 : ℝ)).symm
        have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
          norm_num
        rw [show (Real.pi : ℂ) / (b : ℂ) =
            ((Real.pi / b : ℝ) : ℂ) by norm_num]
        rw [hhalf]
        rw [hpow]
        rw [harg, ← Complex.ofReal_exp]
        simp only [Complex.ofReal_mul]
  rw [hformula]
  constructor
  · change 0 ≤ (Real.pi / b) ^ (1 / 2 : ℝ) *
      Real.exp (-(t ^ 2 / (4 * b)))
    positivity
  · rfl

private theorem chapter07_abs_pow_gaussian_bound
    (b : ℝ) (hb : 0 < b) (m : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ,
      |x| ^ m * Real.exp (-(b / 2) * x ^ 2) ≤ C := by
  have hlittle :
      (fun y : ℝ => y ^ (m : ℝ) * Real.exp (-(b / 2) * y ^ 2)) =o[atTop]
        (fun y : ℝ => Real.exp (-(1 / 2 : ℝ) * y)) := by
    exact rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg (b := b / 2)
      (by positivity) (m : ℝ)
  have hevent : ∀ᶠ y : ℝ in atTop,
      y ^ (m : ℝ) * Real.exp (-(b / 2) * y ^ 2) ≤ 1 := by
    filter_upwards [hlittle.eventuallyLE, eventually_ge_atTop (0 : ℝ)] with y hy hy0
    have h_exp : Real.exp (-(1 / 2 : ℝ) * y) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    have hleft : 0 ≤ y ^ (m : ℝ) * Real.exp (-(b / 2) * y ^ 2) :=
      mul_nonneg (Real.rpow_nonneg hy0 _) (Real.exp_nonneg _)
    have hright : 0 ≤ Real.exp (-(1 / 2 : ℝ) * y) := Real.exp_nonneg _
    have hy' : y ^ (m : ℝ) * Real.exp (-(b / 2) * y ^ 2) ≤
        Real.exp (-(1 / 2 : ℝ) * y) := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hleft,
        abs_of_nonneg hright] using hy
    exact hy'.trans h_exp
  rcases (eventually_atTop.1 hevent) with ⟨R, hR⟩
  let R' : ℝ := max R 0
  have hR' : ∀ y : ℝ, R' ≤ y →
      y ^ (m : ℝ) * Real.exp (-(b / 2) * y ^ 2) ≤ 1 := by
    intro y hy
    apply hR y
    exact le_trans (le_max_left R 0) hy
  refine ⟨max 1 (R' ^ m), ?_⟩
  intro x
  by_cases hx : R' ≤ |x|
  · have htail := hR' |x| hx
    rw [sq_abs] at htail
    simpa [Real.rpow_natCast] using htail.trans (le_max_left 1 (R' ^ m))
  · have hx' : |x| ≤ R' := le_of_not_ge hx
    have hpow : |x| ^ m ≤ R' ^ m := by
      exact pow_le_pow_left₀ (abs_nonneg x) hx' m
    have hexp : Real.exp (-(b / 2) * x ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith [hb]) (sq_nonneg x)
    calc
      |x| ^ m * Real.exp (-(b / 2) * x ^ 2) ≤ R' ^ m * 1 :=
        mul_le_mul hpow hexp (Real.exp_nonneg _) (by positivity)
      _ = R' ^ m := by ring
      _ ≤ max 1 (R' ^ m) := le_max_right _ _

private theorem chapter07_gaussian_schwartz_decay
    (b : ℝ) (hb : 0 < b) (k n : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ,
      |x| ^ k * ‖iteratedDeriv n (fun y : ℝ => Real.exp (-b * y ^ 2)) x‖ ≤ C := by
  have hq : ContDiff ℝ ∞ (fun y : ℝ => -b * y ^ 2) := by
    fun_prop
  have hderiv (x : ℝ) :
      ‖iteratedDeriv n (fun y : ℝ => Real.exp (-b * y ^ 2)) x‖ ≤
        (n.factorial : ℝ) * Real.exp (-b * x ^ 2) *
          (max 1 (2 * b) * (1 + |x|)) ^ n := by
    let A : ℝ := max 1 (2 * b)
    let D : ℝ := A * (1 + |x|)
    have hA1 : 1 ≤ A := by
      exact le_max_left _ _
    have hA2 : 2 * b ≤ A := by
      exact le_max_right _ _
    have hA0 : 0 ≤ A := by linarith
    have hD1 : 1 ≤ D := by
      dsimp [D]
      exact one_le_mul_of_one_le_of_one_le hA1 (by linarith [abs_nonneg x])
    have hD0 : 0 ≤ D := by linarith
    have hDbase : 2 * b * |x| ≤ D := by
      calc
        2 * b * |x| ≤ A * |x| := by
          exact mul_le_mul_of_nonneg_right hA2 (abs_nonneg x)
        _ ≤ A * (1 + |x|) := by
          gcongr
          linarith
        _ = D := rfl
    have hDbase2 : 2 * b ≤ D := by
      calc
        2 * b ≤ A := hA2
        _ ≤ A * (1 + |x|) := by
          calc
            A = A * 1 := (mul_one A).symm
            _ ≤ A * (1 + |x|) := by
              exact mul_le_mul_of_nonneg_left (by linarith [abs_nonneg x]) hA0
        _ = D := rfl
    have hDtwo : 2 * b ≤ D ^ 2 := by
      exact hDbase2.trans (le_self_pow₀ (n := 2) hD1 (by norm_num))
    have hqderiv (i : ℕ) :
        iteratedDeriv i (fun y : ℝ => -b * y ^ 2) x =
          -b * (Nat.descFactorial 2 i * x ^ (2 - i)) := by
      rw [iteratedDeriv_const_mul_field]
      simp [iteratedDeriv_pow]
    have hD' : ∀ i, 1 ≤ i → i ≤ n →
        ‖iteratedFDeriv ℝ i (fun y : ℝ => -b * y ^ 2) x‖ ≤ D ^ i := by
      intro i hi h_in
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hqderiv]
      by_cases hthree : 3 ≤ i
      · have hz : Nat.descFactorial 2 i = 0 :=
          Nat.descFactorial_eq_zero_iff_lt.mpr hthree
        simp [hz, pow_nonneg hD0]
      · have hi' : i = 1 ∨ i = 2 := by omega
        rcases hi' with rfl | rfl
        · simpa [Nat.descFactorial, pow_one, abs_mul, abs_of_pos hb,
            abs_of_nonneg (abs_nonneg x), mul_assoc, mul_left_comm, mul_comm] using hDbase
        · simpa [Nat.descFactorial, abs_mul, abs_of_pos hb,
            abs_of_nonneg (sq_nonneg x), mul_assoc, mul_left_comm, mul_comm] using hDtwo
    have hC : ∀ i, i ≤ n →
        ‖iteratedFDeriv ℝ i Real.exp ((fun y : ℝ => -b * y ^ 2) x)‖ ≤
          Real.exp ((fun y : ℝ => -b * y ^ 2) x) := by
      intro i h_in
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      have h_exp := congrFun (iteratedDeriv_exp_const_mul i 1)
        ((fun y : ℝ => -b * y ^ 2) x)
      have h_exp' : iteratedDeriv i Real.exp ((fun y : ℝ => -b * y ^ 2) x) =
          Real.exp ((fun y : ℝ => -b * y ^ 2) x) := by
        simpa using h_exp
      rw [h_exp']
      simp [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    have hcomp := norm_iteratedFDeriv_comp_le
      (g := Real.exp) (f := fun y : ℝ => -b * y ^ 2)
      Real.contDiff_exp hq (mod_cast le_top) x (C := Real.exp ((fun y : ℝ => -b * y ^ 2) x))
      (D := D) hC hD'
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    simpa [D, A, Function.comp_def] using hcomp
  obtain ⟨Cdec, hCdec⟩ := chapter07_abs_pow_gaussian_bound b
    (by positivity) (k + n)
  let A : ℝ := max 1 (2 * b)
  refine ⟨max ((n.factorial : ℝ) * (2 * A) ^ n)
      ((n.factorial : ℝ) * A ^ n * 2 ^ n * Cdec), ?_⟩
  intro x
  have hA1 : 1 ≤ A := by exact le_max_left _ _
  have hA0 : 0 ≤ A := by linarith
  by_cases hx : 1 ≤ |x|
  · have hlin : 1 + |x| ≤ 2 * |x| := by linarith
    have hpow : (A * (1 + |x|)) ^ n ≤ (A * (2 * |x|)) ^ n := by
      exact pow_le_pow_left₀ (mul_nonneg hA0 (by positivity))
        (mul_le_mul_of_nonneg_left hlin hA0) n
    have hexp : Real.exp (-b * x ^ 2) ≤
        Real.exp (-(b / 2) * x ^ 2) := by
      exact Real.exp_le_exp.mpr (by nlinarith [hb, sq_nonneg x])
    calc
      |x| ^ k * ‖iteratedDeriv n (fun y : ℝ => Real.exp (-b * y ^ 2)) x‖ ≤
          |x| ^ k * ((n.factorial : ℝ) * Real.exp (-b * x ^ 2) *
            (A * (1 + |x|)) ^ n) := by
        gcongr
        exact hderiv x
      _ ≤ |x| ^ k * ((n.factorial : ℝ) * Real.exp (-b * x ^ 2) *
            (A * (2 * |x|)) ^ n) := by
        gcongr
      _ = ((n.factorial : ℝ) * A ^ n * 2 ^ n) *
            (|x| ^ (k + n) * Real.exp (-b * x ^ 2)) := by ring
      _ ≤ ((n.factorial : ℝ) * A ^ n * 2 ^ n) *
            (|x| ^ (k + n) * Real.exp (-(b / 2) * x ^ 2)) := by
        gcongr
      _ ≤ (n.factorial : ℝ) * A ^ n * 2 ^ n * Cdec := by
        gcongr
        exact hCdec x
      _ ≤ max ((n.factorial : ℝ) * (2 * A) ^ n)
          ((n.factorial : ℝ) * A ^ n * 2 ^ n * Cdec) :=
        le_max_right _ _
  · have hx' : |x| ≤ 1 := le_of_not_ge hx
    have hpow : |x| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg x) hx'
    have hlin : A * (1 + |x|) ≤ 2 * A := by
      calc
        A * (1 + |x|) ≤ A * 2 := by
          exact mul_le_mul_of_nonneg_left (by linarith [hx']) hA0
        _ = 2 * A := by ring
    have hexp : Real.exp (-b * x ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith [hb]) (sq_nonneg x)
    calc
      |x| ^ k * ‖iteratedDeriv n (fun y : ℝ => Real.exp (-b * y ^ 2)) x‖ ≤
          |x| ^ k * ((n.factorial : ℝ) * Real.exp (-b * x ^ 2) *
            (A * (1 + |x|)) ^ n) := by
        gcongr
        exact hderiv x
      _ ≤ |x| ^ k * ((n.factorial : ℝ) * 1 * (2 * A) ^ n) := by
        gcongr
      _ ≤ (n.factorial : ℝ) * (2 * A) ^ n := by
        have hQ : 0 ≤ (n.factorial : ℝ) * (2 * A) ^ n := by positivity
        simpa using (mul_le_mul_of_nonneg_right hpow hQ)
      _ ≤ max ((n.factorial : ℝ) * (2 * A) ^ n)
          ((n.factorial : ℝ) * A ^ n * 2 ^ n * Cdec) :=
        le_max_left _ _

theorem chapter07_gaussian_is_schwartz (σ : ℝ) (hσ : 0 < σ) :
    ∃ g : SchwartzMap ℝ ℝ, ∀ x, g x = chapter07Gaussian σ x := by
  let b : ℝ := 1 / (2 * σ ^ 2)
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hgauss (x : ℝ) :
      chapter07Gaussian σ x = Real.exp (-b * x ^ 2) := by
    dsimp [chapter07Gaussian, b]
    congr 1
    ring
  have hfun : chapter07Gaussian σ =
      (fun x : ℝ => Real.exp (-b * x ^ 2)) := funext hgauss
  refine ⟨{
    toFun := chapter07Gaussian σ
    smooth' := by
      unfold chapter07Gaussian
      fun_prop
    decay' := by
      intro k n
      obtain ⟨C, hC⟩ := chapter07_gaussian_schwartz_decay b hb k n
      refine ⟨C, ?_⟩
      intro x
      rw [hfun]
      simpa only [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hC x
  }, ?_⟩
  intro x
  rfl

theorem chapter07_gaussian_not_compactly_supported (σ : ℝ) (hσ : 0 < σ) :
    ¬HasCompactSupport (chapter07Gaussian σ) := by
  intro hcompact
  have _hσ_nonneg : 0 ≤ σ := hσ.le
  have huniv : Bornology.IsBounded (Set.univ : Set ℝ) := by
    apply hcompact.isBounded.subset
    intro x hx
    apply subset_closure
    simp [Function.mem_support, chapter07Gaussian]
  exact NormedSpace.unbounded_univ ℝ ℝ huniv

/- The preceding explicit-formula chapter supplies field-specific prime-power
   weights.  This field-independent predicate records only the
   absolute-convergence interface needed for a noncompact test function. -/
def chapter07PrimeSeriesAbsolutelyConvergent
    (f : Chapter07TestFunction) (weight : ℕ → ℝ) : Prop :=
  Summable (fun n : ℕ => ‖(weight n : ℝ) * f (Real.log n)‖)

def chapter07GaussianExplicitFormulaHypothesis
    (σ : ℝ) (weight : ℕ → ℝ) : Prop :=
  0 < σ ∧ chapter07PrimeSeriesAbsolutelyConvergent
    (chapter07Gaussian σ) weight

def chapter07Box (T : ℝ) (x : ℝ) : ℝ :=
  if |x| ≤ T / 2 then 1 else 0

def chapter07Autocorrelation
    (g : Chapter07TestFunction) (x : ℝ) : ℝ :=
  ∫ y : ℝ, g y * g (y + x)

def chapter07Triangle (T : ℝ) (x : ℝ) : ℝ :=
  max 0 (1 - |x| / T)

theorem chapter07_autocorrelation_positiveType
    (g : Chapter07TestFunction) (hg : Integrable g)
    (hg2 : Integrable (fun x : ℝ => g x ^ 2)) :
    chapter07PositiveType (chapter07Autocorrelation g) := by
  have hg_memLp : MemLp g 2 :=
    (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2 hg2
  have hpositive :=
    LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05_autocorrelation_is_positive_type
      g hg hg_memLp
  have heven :=
    LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05_autocorrelation_is_even
      g hg hg_memLp
  have hcorr : chapter07Autocorrelation g =
      LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05Autocorrelation g := by
    funext u
    calc
      chapter07Autocorrelation g u =
          LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05Autocorrelation
            g (-u) := by
        simp [chapter07Autocorrelation,
          LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05Autocorrelation,
          LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05Convolution,
          LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05Reflect,
          MeasureTheory.convolution_def, add_comm]
      _ = LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05Autocorrelation
          g u := heven u
  rw [hcorr]
  exact hpositive

theorem chapter07_triangle_eq_normalized_autocorrelation
    (T : ℝ) (hT : 0 < T) (x : ℝ) :
    chapter07Triangle T x =
      (1 / T) * chapter07Autocorrelation (chapter07Box T) x := by
  let A : Set ℝ := Set.Icc (-T / 2) (T / 2)
  have hbox : chapter07Box T = A.indicator (fun _ : ℝ => (1 : ℝ)) := by
    funext y
    by_cases hy : y ∈ A
    · have hy' : -T / 2 ≤ y ∧ y ≤ T / 2 := by simpa [A] using hy
      rw [Set.indicator_of_mem hy]
      have hyabs : |y| ≤ T / 2 := by
        have hy'' : -(T / 2) ≤ y ∧ y ≤ T / 2 := by
          simpa [show -(T / 2) = -T / 2 by ring] using hy'
        exact (abs_le).2 hy''
      simp [chapter07Box, hyabs]
    · have hnot : ¬ |y| ≤ T / 2 := by
        intro h
        apply hy
        have h' := (abs_le).1 h
        simpa [A, show -(T / 2) = -T / 2 by ring] using h'
      rw [Set.indicator_of_notMem hy]
      simp [chapter07Box, hnot]
  have hconv : ∀ u : ℝ,
      chapter07Autocorrelation (chapter07Box T) u =
        (volume : Measure ℝ).real
          (A ∩ (fun y : ℝ => y + u) ⁻¹' A) := by
    intro u
    rw [chapter07Autocorrelation, hbox]
    change (∫ y : ℝ,
        (A.indicator (fun _ : ℝ => (1 : ℝ)) y) *
          (A.indicator (fun _ : ℝ => (1 : ℝ)) (y + u))) = _
    have hmeas : MeasurableSet (A ∩ (fun y : ℝ => y + u) ⁻¹' A) := by
      apply measurableSet_Icc.inter
      exact measurableSet_Icc.preimage (by fun_prop)
    apply (integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))).trans
    · rw [integral_indicator_one hmeas]
    by_cases hy : y ∈ A
    · by_cases hyu : y + u ∈ A
      · have hmem : y ∈ A ∩ (fun y : ℝ => y + u) ⁻¹' A := ⟨hy, hyu⟩
        rw [Set.indicator_of_mem hy, Set.indicator_of_mem hyu,
          Set.indicator_of_mem hmem]
        simp
      · have hnot : y ∉ A ∩ (fun y : ℝ => y + u) ⁻¹' A := by
          intro h
          exact hyu h.2
        rw [Set.indicator_of_mem hy, Set.indicator_of_notMem hyu,
          Set.indicator_of_notMem hnot]
        simp
    · have hnot : y ∉ A ∩ (fun y : ℝ => y + u) ⁻¹' A := by
        intro h
        exact hy h.1
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hnot]
      simp
  have hset (u : ℝ) :
      A ∩ (fun y : ℝ => y + u) ⁻¹' A =
        Set.Icc (max (-T / 2) (-u - T / 2))
          (min (T / 2) (-u + T / 2)) := by
    ext y
    constructor
    · rintro ⟨hyA, hyB⟩
      change -T / 2 ≤ y ∧ y ≤ T / 2 at hyA
      change -T / 2 ≤ y + u ∧ y + u ≤ T / 2 at hyB
      change max (-T / 2) (-u - T / 2) ≤ y ∧
        y ≤ min (T / 2) (-u + T / 2)
      constructor
      · exact max_le hyA.1 (by linarith [hyB.1])
      · exact le_min hyA.2 (by linarith [hyB.2])
    · intro hy
      change max (-T / 2) (-u - T / 2) ≤ y ∧
        y ≤ min (T / 2) (-u + T / 2) at hy
      constructor
      · change -T / 2 ≤ y ∧ y ≤ T / 2
        exact ⟨le_trans (le_max_left _ _) hy.1,
          le_trans hy.2 (min_le_left _ _)⟩
      · change -T / 2 ≤ y + u ∧ y + u ≤ T / 2
        have hyA1 : -T / 2 ≤ y := le_trans (le_max_left _ _) hy.1
        have hyB1 : -u - T / 2 ≤ y := le_trans (le_max_right _ _) hy.1
        have hyA2 : y ≤ T / 2 := le_trans hy.2 (min_le_left _ _)
        have hyB2 : y ≤ -u + T / 2 := le_trans hy.2 (min_le_right _ _)
        constructor <;> linarith
  have hlen (u : ℝ) :
      max (min (T / 2) (u + T / 2) - max (-T / 2) (u - T / 2)) 0 =
        max (T - |u|) 0 := by
    rcases le_total 0 u with hu | hu
    · by_cases hut : u ≤ T
      · have hleft : -T / 2 ≤ u - T / 2 := by linarith
        have hright : T / 2 ≤ u + T / 2 := by linarith
        rw [max_eq_right hleft, min_eq_left hright]
        rw [abs_of_nonneg hu]
        congr 1
        ring
      · have hleft : -T / 2 ≤ u - T / 2 := by linarith
        have hright : T / 2 ≤ u + T / 2 := by linarith
        rw [max_eq_right hleft, min_eq_left hright]
        rw [abs_of_nonneg hu]
        have hnonpos : T - u ≤ 0 := by linarith
        have hdiff : T / 2 - (u - T / 2) = T - u := by ring
        rw [hdiff, max_eq_right hnonpos]
    · have hu' : u ≤ 0 := hu
      by_cases hut : -u ≤ T
      · have hleft : u - T / 2 ≤ -T / 2 := by linarith
        have hright : u + T / 2 ≤ T / 2 := by linarith
        rw [max_eq_left hleft, min_eq_right hright]
        rw [abs_of_nonpos hu']
        congr 1
        ring_nf
      · have hleft : u - T / 2 ≤ -T / 2 := by linarith
        have hright : u + T / 2 ≤ T / 2 := by linarith
        rw [max_eq_left hleft, min_eq_right hright]
        rw [abs_of_nonpos hu']
        have hnonpos : T + u ≤ 0 := by linarith
        have hdiff : u + T / 2 - -T / 2 = T + u := by ring
        have hdiff' : T - -u = T + u := by ring
        rw [hdiff, hdiff', max_eq_right hnonpos]
  rw [hconv x, hset x]
  rw [Real.volume_real_Icc]
  have hlen' :
      max (min (T / 2) (-x + T / 2) - max (-T / 2) (-x - T / 2)) 0 =
        max (T - |x|) 0 := by
    simpa [abs_neg] using hlen (-x)
  rw [hlen']
  unfold chapter07Triangle
  by_cases hnonneg : 0 ≤ T - |x|
  · have hratio : 1 - |x| / T = (T - |x|) / T := by
      field_simp [ne_of_gt hT]
    rw [hratio, max_eq_right (div_nonneg hnonneg hT.le),
      max_eq_left hnonneg]
    field_simp [ne_of_gt hT]
  · have hnonpos : T - |x| ≤ 0 := le_of_not_ge hnonneg
    have hleft : 1 - |x| / T ≤ 0 := by
      apply sub_nonpos.mpr
      apply (le_div_iff₀ hT).2
      simpa using hnonpos
    rw [max_eq_left hleft, max_eq_right hnonpos]
    simp

theorem chapter07_triangle_positiveType (T : ℝ) (hT : 0 < T) :
    chapter07PositiveType (chapter07Triangle T) := by
  let A : Set ℝ := Set.Icc (-T / 2) (T / 2)
  have hbox : chapter07Box T = A.indicator (fun _ : ℝ => (1 : ℝ)) := by
    funext y
    by_cases hy : y ∈ A
    · have hy' : -T / 2 ≤ y ∧ y ≤ T / 2 := by simpa [A] using hy
      rw [Set.indicator_of_mem hy]
      have hyabs : |y| ≤ T / 2 := by
        have hy'' : -(T / 2) ≤ y ∧ y ≤ T / 2 := by
          simpa [show -(T / 2) = -T / 2 by ring] using hy'
        exact (abs_le).2 hy''
      simp [chapter07Box, hyabs]
    · have hnot : ¬ |y| ≤ T / 2 := by
        intro h
        apply hy
        have h' := (abs_le).1 h
        simpa [A, show -(T / 2) = -T / 2 by ring] using h'
      rw [Set.indicator_of_notMem hy]
      simp [chapter07Box, hnot]
  have hAfinite : (volume : Measure ℝ) A ≠ (⊤ : ENNReal) := by
    dsimp [A]
    exact (measure_Icc_lt_top (μ := (volume : Measure ℝ))).ne
  have hbox_memLp : MemLp (chapter07Box T) 2 := by
    rw [hbox]
    exact memLp_indicator_const 2 measurableSet_Icc 1 (Or.inr hAfinite)
  have hbox_integrable : Integrable (chapter07Box T) :=
    memLp_one_iff_integrable.mp (by
      rw [hbox]
      exact memLp_indicator_const 1 measurableSet_Icc 1 (Or.inr hAfinite))
  have hpositive :=
    LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05_autocorrelation_is_positive_type
      (chapter07Box T) hbox_integrable hbox_memLp
  have heven :=
    LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05_autocorrelation_is_even
      (chapter07Box T) hbox_integrable hbox_memLp
  have hcorr : chapter07Autocorrelation (chapter07Box T) =
      LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05Autocorrelation
        (chapter07Box T) := by
    funext u
    calc
      chapter07Autocorrelation (chapter07Box T) u =
          LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05Autocorrelation
            (chapter07Box T) (-u) := by
        simp [chapter07Autocorrelation,
          LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05Autocorrelation,
          LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05Convolution,
          LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05Reflect,
          MeasureTheory.convolution_def, add_comm]
      _ = LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05Autocorrelation
          (chapter07Box T) u := heven u
  have hscaled : chapter07PositiveType (fun x : ℝ =>
      (1 / T) * chapter07Autocorrelation (chapter07Box T) x) := by
    rw [hcorr]
    refine ⟨?_, ?_, ?_⟩
    · exact continuous_const.mul hpositive.continuous
    · exact hpositive.integrable.const_mul _
    · intro t
      have htransform :
          LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05FourierTransform
              (fun x : ℝ =>
            (1 / T) *
              LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05Autocorrelation
                (chapter07Box T) x) t =
            ((1 / T : ℝ) : ℂ) *
              LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05FourierTransform
                (LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05Autocorrelation
                  (chapter07Box T)) t := by
        simp only [LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05FourierTransform,
          Complex.ofReal_mul]
        calc
          (∫ x : ℝ,
                ((1 / T : ℝ) : ℂ) *
                (LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05Autocorrelation
                  (chapter07Box T) x : ℂ) *
                Complex.exp (-(Complex.I * ((t : ℂ) * (x : ℂ))))) =
              ∫ x : ℝ,
                ((1 / T : ℝ) : ℂ) *
                  ((LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05Autocorrelation
                    (chapter07Box T) x : ℂ) *
                    Complex.exp (-(Complex.I * ((t : ℂ) * (x : ℂ))))) := by
            apply integral_congr_ae
            filter_upwards [] with x
            ring
          _ = ((1 / T : ℝ) : ℂ) *
              ∫ x : ℝ,
                (LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05Autocorrelation
                  (chapter07Box T) x : ℂ) *
                  Complex.exp (-(Complex.I * ((t : ℂ) * (x : ℂ)))) := by
            rw [integral_const_mul]
      rw [htransform]
      have hnonneg : 0 ≤ (1 / T : ℝ) := by positivity
      have hre : 0 ≤
          (((1 / T : ℝ) : ℂ) *
            chapter07FourierTransform
              (LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05Autocorrelation
                (chapter07Box T)) t).re := by
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero]
        exact mul_nonneg hnonneg (hpositive.transformNonnegative t).2
      have him :
          (((1 / T : ℝ) : ℂ) *
            chapter07FourierTransform
              (LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05Autocorrelation
                (chapter07Box T)) t).im = 0 := by
        simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul]
        rw [(hpositive.transformNonnegative t).1, mul_zero]
        simp
      exact ⟨him, hre⟩
  have htri : chapter07Triangle T = fun x : ℝ =>
      (1 / T) * chapter07Autocorrelation (chapter07Box T) x := by
    funext x
    exact chapter07_triangle_eq_normalized_autocorrelation T hT x
  rw [htri]
  exact hscaled

theorem chapter07_triangle_pointwiseNonnegative (T : ℝ) :
    chapter07PointwiseNonnegative (chapter07Triangle T) := by
  intro x
  exact le_max_left _ _

theorem chapter07_triangle_integrable (T : ℝ) (hT : 0 < T) :
    Integrable (chapter07Triangle T) := by
  have hcont : Continuous (chapter07Triangle T) := by
    unfold chapter07Triangle
    fun_prop
  have hi : IntegrableOn (chapter07Triangle T) (Set.Icc (-T) T) :=
    hcont.continuousOn.integrableOn_compact isCompact_Icc
  have hzero : ∀ x ∉ Set.Icc (-T) T, chapter07Triangle T x = 0 := by
    intro x hx
    have hx' : T < |x| := by
      have hx_cases : x < -T ∨ T < x := by
        by_contra hcases
        push Not at hcases
        exact hx ⟨hcases.1, hcases.2⟩
      rcases hx_cases with hx' | hx'
      · rw [abs_of_neg (by linarith : x < 0)]
        linarith
      · rw [abs_of_pos (by linarith : 0 < x)]
        exact hx'
    rw [chapter07Triangle, max_eq_left]
    exact (sub_nonpos.mpr ((le_div_iff₀ hT).2 (by nlinarith [hx'])))
  have heq : chapter07Triangle T =
      (Set.Icc (-T) T).indicator (chapter07Triangle T) := by
    funext x
    by_cases hx : x ∈ Set.Icc (-T) T
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator, hx, hzero x hx]
  rw [heq]
  exact hi.integrable_indicator isClosed_Icc.measurableSet

theorem chapter07_triangle_fourier_nonnegative (T : ℝ) (hT : 0 < T) :
    chapter07FourierNonnegative (chapter07Triangle T) := by
  exact chapter07_positiveType_fourierNonnegative (chapter07Triangle T)
    (chapter07_triangle_positiveType T hT)

theorem chapter07_triangle_has_compact_support (T : ℝ) (hT : 0 < T) :
    HasCompactSupport (chapter07Triangle T) := by
  apply HasCompactSupport.intro' isCompact_Icc isClosed_Icc
  intro x hx
  have hx' : T < |x| := by
    have hx_cases : x < -T ∨ T < x := by
      by_contra hcases
      push Not at hcases
      exact hx ⟨hcases.1, hcases.2⟩
    rcases hx_cases with hx' | hx'
    · rw [abs_of_neg (by linarith : x < 0)]
      linarith
    · rw [abs_of_pos (by linarith : 0 < x)]
      exact hx'
  rw [chapter07Triangle, max_eq_left]
  exact (sub_nonpos.mpr ((le_div_iff₀ hT).2 (by nlinarith [hx'])))

theorem chapter07_triangle_not_smooth (T : ℝ) (hT : 0 < T) :
    ¬DifferentiableAt ℝ (chapter07Triangle T) 0 := by
  intro htriangle
  have hI : Set.Ioo (-T) T ∈ 𝓝 (0 : ℝ) := by
    apply IsOpen.mem_nhds isOpen_Ioo
    constructor <;> linarith
  have hlin : DifferentiableAt ℝ
      (fun x : ℝ => T * (1 - chapter07Triangle T x)) 0 := by
    fun_prop
  have habs : DifferentiableAt ℝ (abs : ℝ → ℝ) 0 := by
    apply hlin.congr_of_eventuallyEq
    filter_upwards [hI] with x hx
    have hxabs : |x| < T := (abs_lt).2 ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hnonneg : 0 ≤ 1 - |x| / T := by
      exact (sub_nonneg.mpr ((div_le_one hT).2 hxabs.le))
    simp only [chapter07Triangle, max_eq_right hnonneg]
    field_simp
    ring
  exact not_differentiableAt_abs_zero habs

def chapter07PrimePowerSupport (f : Chapter07TestFunction) : Set ℕ :=
  {n : ℕ | 2 ≤ n ∧ f (Real.log n) ≠ 0}

theorem chapter07_triangle_primePowerSupport_finite
    (T : ℝ) (hT : 0 < T) :
    Set.Finite (chapter07PrimePowerSupport (chapter07Triangle T)) := by
  let N : ℕ := ⌊Real.exp T⌋₊
  have hsub : chapter07PrimePowerSupport (chapter07Triangle T) ⊆
      (Finset.Iic N : Set ℕ) := by
    intro n hn
    have hlog : |Real.log (n : ℝ)| ≤ T := by
      by_contra hlog
      have hlog' : T < |Real.log (n : ℝ)| := lt_of_not_ge hlog
      have hzero : chapter07Triangle T (Real.log n) = 0 := by
        rw [chapter07Triangle, max_eq_left]
        exact (sub_nonpos.mpr ((le_div_iff₀ hT).2 (by nlinarith [hlog'])))
      exact hn.2 hzero
    have hn1 : (1 : ℝ) < n := by
      exact_mod_cast lt_of_lt_of_le (by norm_num) hn.1
    have hlog_le : Real.log (n : ℝ) ≤ T := by
      rw [abs_of_pos (Real.log_pos hn1)] at hlog
      exact hlog
    have hnreal : (n : ℝ) ≤ Real.exp T := Real.le_exp_of_log_le hlog_le
    have hnN : n ∈ Finset.Iic N := by
      apply (Nat.cast_mem_Iic_iff (α := ℝ) (by positivity)).mp
      simpa [N] using hnreal
    exact hnN
  exact (Finset.finite_toSet (Finset.Iic N)).subset hsub

/- A smoothing witness records exactly the properties used when the triangle
   is replaced by a smooth certificate in the next chapter. -/
def chapter07SmoothApproximation
    (F H : Chapter07TestFunction) (ε : ℝ) : Prop :=
    ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧ Integrable H ∧ chapter07Even H ∧
    chapter07PointwiseNonnegative H ∧ chapter07PositiveType H ∧
    H 0 = 1 ∧ ∀ x, |H x - F x| ≤ ε

theorem chapter07_triangle_smoothing_interface
    (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε) :
    ∃ H : Chapter07TestFunction,
      chapter07SmoothApproximation (chapter07Triangle T) H ε := by
  classical
  let r : ℝ := min (T / 8) (ε * T / 64)
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min (by linarith) (by positivity)
  let b : ContDiffBump (0 : ℝ) :=
    { rIn := r / 2
      rOut := r
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  let η : ℝ → ℝ := (b.normed (volume : Measure ℝ))
  have hηint : Integrable η := by
    simpa [η] using b.integrable_normed
  have hηcompact : HasCompactSupport η := by
    simpa [η] using b.hasCompactSupport_normed
  have hηdiff : ContDiff ℝ ∞ η := by
    simpa [η] using b.contDiff_normed
  have hηnonneg : ∀ x : ℝ, 0 ≤ η x := by
    intro x
    simpa [η] using b.nonneg_normed x
  have hηeven : Function.Even η := by
    intro x
    simpa [η] using b.normed_neg x
  have hηmass : ∫ x : ℝ, η x = 1 := by
    simpa [η] using b.integral_normed
  have hηsupport : ∀ x : ℝ, η x ≠ 0 → |x| < r := by
    intro x hx
    have hx' : x ∈ Function.support ((b).normed (volume : Measure ℝ)) := hx
    rw [(b).support_normed_eq] at hx'
    rw [Metric.mem_ball, dist_zero_right] at hx'
    simpa [b] using hx'
  let κ : ℝ → ℝ :=
    LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05Autocorrelation η
  have hηL2 : MemLp η 2 := hηdiff.continuous.memLp_of_hasCompactSupport hηcompact
  have hκpt : chapter07PositiveType κ := by
    dsimp [κ]
    exact LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05_autocorrelation_is_positive_type
      η hηint hηL2
  have hreflectη :
      LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05Reflect η = η := by
    funext x
    exact hηeven x
  have hκeq : κ =
      LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05Convolution η η := by
    simp [κ, LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05Autocorrelation,
      hreflectη]
  have hκcompact : HasCompactSupport κ := by
    rw [hκeq]
    exact hηcompact.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hηcompact
  have hκdiff : ContDiff ℝ ∞ κ := by
    rw [hκeq]
    exact hηcompact.contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) hηdiff hηint.locallyIntegrable
  have hκint : Integrable κ := hκpt.integrable
  have hκnonneg : ∀ x : ℝ, 0 ≤ κ x := by
    intro x
    dsimp [κ]
    unfold LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05Autocorrelation
    unfold LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05Convolution
    apply integral_nonneg
    intro y
    exact mul_nonneg (hηnonneg y) (hηnonneg (-(x - y)))
  have hκeven : Function.Even κ := by
    exact LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05_autocorrelation_is_even
      η hηint hηL2
  have hκmass : ∫ x : ℝ, κ x = 1 := by
    rw [hκeq]
    unfold LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05Convolution
    rw [MeasureTheory.integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ)
      hηint hηint]
    simp [hηmass, ContinuousLinearMap.lsmul_apply]
  have hκsupport : ∀ x : ℝ, κ x ≠ 0 → |x| < 2 * r := by
    intro x hx
    have hxsum : x ∈ Function.support η + Function.support η := by
      apply (MeasureTheory.support_convolution_subset
        (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := (volume : Measure ℝ))
        (f := η) (g := η))
      change LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05Convolution
        η η x ≠ 0
      rw [← hκeq]
      exact hx
    rcases hxsum with ⟨a, ha, c, hc, rfl⟩
    have ha' : |a| < r := hηsupport a ha
    have hc' : |c| < r := hηsupport c hc
    exact (abs_add_le a c).trans_lt (by simpa [two_mul] using add_lt_add ha' hc')
  let F : ℝ → ℝ := chapter07Triangle T
  have hFint : Integrable F := by
    dsimp [F]
    exact chapter07_triangle_integrable T hT
  have hFcompact : HasCompactSupport F := by
    dsimp [F]
    exact chapter07_triangle_has_compact_support T hT
  have hFcont : Continuous F := by
    change Continuous (fun x : ℝ => max 0 (1 - |x| / T))
    exact continuous_const.max (continuous_const.sub (continuous_abs.div_const T))
  have hFnonneg : ∀ x : ℝ, 0 ≤ F x := by
    intro x
    dsimp [F]
    exact le_max_left _ _
  have hFle : ∀ x : ℝ, F x ≤ 1 := by
    intro x
    dsimp [F, chapter07Triangle]
    apply max_le
    · norm_num
    · have : 0 ≤ |x| / T := div_nonneg (abs_nonneg _) hT.le
      linarith
  have hFeven : Function.Even F := by
    intro x
    dsimp [F, chapter07Triangle]
    rw [abs_neg]
  have hFpt : chapter07PositiveType F := by
    dsimp [F]
    exact chapter07_triangle_positiveType T hT
  have hFlip : ∀ x y : ℝ, |F x - F y| ≤ |x - y| / T := by
    intro x y
    dsimp [F, chapter07Triangle]
    calc
      |max 0 (1 - |x| / T) - max 0 (1 - |y| / T)| =
          |max (1 - |x| / T) 0 - max (1 - |y| / T) 0| := by
        rw [max_comm 0, max_comm 0]
      _ ≤ |(1 - |x| / T) - (1 - |y| / T)| :=
        abs_max_sub_max_le_abs _ _ _
      _ = |(|x| - |y|) / T| := by
        rw [show (1 - |x| / T) - (1 - |y| / T) =
          -((|x| - |y|) / T) by ring, abs_neg]
      _ ≤ |x - y| / T := by
        rw [abs_div, abs_of_pos hT]
        exact div_le_div_of_nonneg_right
          (abs_abs_sub_abs_le_abs_sub x y) hT.le
  let R : ℝ → ℝ :=
    LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05Convolution κ F
  have hRcompact : HasCompactSupport R := by
    dsimp [R]
    exact hκcompact.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hFcompact
  have hRdiff : ContDiff ℝ ∞ R := by
    dsimp [R]
    exact hκcompact.contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) hκdiff hFint.locallyIntegrable
  have hRcont : Continuous R := hRdiff.continuous
  have hRint : Integrable R := hRcont.integrable_of_hasCompactSupport hRcompact
  have hRnonneg : ∀ x : ℝ, 0 ≤ R x := by
    intro x
    dsimp [R]
    unfold LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05Convolution
    apply integral_nonneg
    intro y
    exact mul_nonneg (hκnonneg y) (hFnonneg (x - y))
  have hReven : Function.Even R := by
    intro x
    dsimp [R]
    apply MeasureTheory.convolution_neg_of_neg_eq
    · exact Filter.Eventually.of_forall hκeven
    · exact Filter.Eventually.of_forall hFeven
  have hRclose : ∀ x : ℝ, |R x - F x| ≤ 2 * r / T := by
    intro x
    have hsupp : Function.support κ ⊆ Metric.ball (0 : ℝ) (2 * r) := by
      intro y hy
      have hy' : |y| < 2 * r := hκsupport y hy
      simpa [Metric.mem_ball, dist_zero_right] using hy'
    have hlocal : ∀ y ∈ Metric.ball (x : ℝ) (2 * r),
        dist (F y) (F x) ≤ 2 * r / T := by
      intro y hy
      rw [Real.dist_eq]
      have hy' : |y - x| < 2 * r := by
        simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hy
      have hbound := hFlip y x
      rw [abs_sub_comm y x] at hbound
      exact hbound.trans (by
        rw [abs_sub_comm x y]
        exact div_le_div_of_nonneg_right (le_of_lt hy') hT.le)
    have hdist := MeasureTheory.dist_convolution_le
      (μ := (volume : Measure ℝ)) (g := F) (x₀ := x) (R := 2 * r)
      (z₀ := F x) (by positivity) hsupp hκnonneg hκmass
      hFcont.measurable.aestronglyMeasurable hlocal
    simpa [R, LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05Convolution,
      Real.dist_eq] using hdist
  have hRpt : chapter07PositiveType R := by
    refine
      { continuous := hRcont
        integrable := hRint
        transformNonnegative := ?_ }
    intro t
    let ξ : ℝ := t / (2 * Real.pi)
    let κC : ℝ → ℂ := fun x => (κ x : ℂ)
    let FC : ℝ → ℂ := fun x => (F x : ℂ)
    have hκC : Integrable κC := by
      change Integrable (fun x : ℝ => (κ x : ℂ))
      exact hκint.ofReal
    have hFC : Integrable FC := by
      change Integrable (fun x : ℝ => (F x : ℂ))
      exact hFint.ofReal
    have hconv :
        (fun x : ℝ => (R x : ℂ)) =
          κC ⋆[ContinuousLinearMap.lsmul ℂ ℂ] FC := by
      funext x
      unfold R κC FC
      unfold LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05Convolution
      rw [MeasureTheory.convolution_def, MeasureTheory.convolution_def]
      simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
      simp_rw [← Complex.ofReal_mul]
      exact (integral_ofReal).symm
    have hκmath : 𝓕 κC ξ =
        chapter07FourierTransform κ t := by
      symm
      simpa [ξ, κC] using
        (LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05_fourierTransform_eq_mathlib_angular
          κ hκint t)
    have hFmath : 𝓕 FC ξ =
        chapter07FourierTransform F t := by
      symm
      simpa [ξ, FC] using
        (LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05_fourierTransform_eq_mathlib_angular
          F hFint t)
    have hRmath : chapter07FourierTransform R t =
        𝓕 (fun x : ℝ => (R x : ℂ)) ξ := by
      simpa [ξ] using
        (LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05_fourierTransform_eq_mathlib_angular
          R hRint t)
    have hconvFT := Real.fourier_smul_convolution_eq hκC hFC ξ
    have hproduct : chapter07FourierTransform R t =
        chapter07FourierTransform κ t * chapter07FourierTransform F t := by
      calc
        chapter07FourierTransform R t =
            𝓕 (fun x : ℝ => (R x : ℂ)) ξ := hRmath
        _ = 𝓕 (κC ⋆[ContinuousLinearMap.lsmul ℂ ℂ] FC) ξ := by
          rw [hconv]
        _ = (𝓕 κC ξ) • (𝓕 FC ξ) := hconvFT
        _ = chapter07FourierTransform κ t * chapter07FourierTransform F t := by
          rw [hκmath, hFmath]
          rfl
    have hκnonneg' := hκpt.transformNonnegative t
    have hFnonneg' := hFpt.transformNonnegative t
    change (chapter07FourierTransform R t).im = 0 ∧
      0 ≤ (chapter07FourierTransform R t).re
    rw [hproduct, Complex.mul_im, Complex.mul_re]
    constructor
    · rw [hκnonneg'.1, hFnonneg'.1]
      ring
    · rw [hκnonneg'.1, hFnonneg'.1]
      simpa using mul_nonneg hκnonneg'.2 hFnonneg'.2
  have hr8 : r ≤ T / 8 := min_le_left _ _
  have hre : r ≤ ε * T / 64 := min_le_right _ _
  have ha : 0 ≤ 2 * r / T := by positivity
  have ha_quarter : 2 * r / T ≤ (1 : ℝ) / 4 := by
    apply (div_le_iff₀ hT).2
    linarith
  have ha_eps : 4 * (2 * r / T) ≤ ε := by
    calc
      4 * (2 * r / T) = 8 * r / T := by ring
      _ ≤ ε := by
        apply (div_le_iff₀ hT).2
        nlinarith
  have hFzero : F 0 = 1 := by
    simp [F, chapter07Triangle]
  have hRzero_close : |R 0 - 1| ≤ 2 * r / T := by
    simpa [hFzero] using hRclose 0
  have hRzero_lower : 1 - 2 * r / T ≤ R 0 := by
    have hsymm : |1 - R 0| = |R 0 - 1| := abs_sub_comm _ _
    have hleabs : 1 - R 0 ≤ 2 * r / T :=
      (le_abs_self (1 - R 0)).trans (hsymm ▸ hRzero_close)
    linarith
  have hRzero_pos : 0 < R 0 := by
    have hupper : 2 * r / T ≤ (1 : ℝ) / 4 := ha_quarter
    linarith
  let H : ℝ → ℝ := fun x => R x / R 0
  have hHdiff : ContDiff ℝ ∞ H := by
    dsimp [H]
    exact hRdiff.div_const _
  have hHcont : Continuous H := by
    dsimp [H]
    exact hRcont.div_const _
  have hHcompact : HasCompactSupport H := by
    dsimp [H]
    exact hRcompact.mul_right (f' := fun _ : ℝ => (R 0)⁻¹)
  have hHint : Integrable H := hHcont.integrable_of_hasCompactSupport hHcompact
  have hHeven : Function.Even H := by
    intro x
    dsimp [H]
    rw [hReven x]
  have hHnonneg : ∀ x : ℝ, 0 ≤ H x := by
    intro x
    dsimp [H]
    exact div_nonneg (hRnonneg x) hRzero_pos.le
  have hHzero : H 0 = 1 := by
    dsimp [H]
    exact div_self hRzero_pos.ne'
  have hHclose : ∀ x : ℝ, |H x - F x| ≤ ε := by
    intro x
    have hclose := hRclose x
    have hFxabs : |F x| ≤ 1 := by
      exact abs_le.2 ⟨by linarith [hFnonneg x], hFle x⟩
    have hnum : |R x - R 0 * F x| ≤ 2 * r / T + 2 * r / T := by
      calc
        |R x - R 0 * F x| =
            |(R x - F x) + F x * (1 - R 0)| := by
          congr 1
          ring
        _ ≤ |R x - F x| + |F x * (1 - R 0)| := abs_add_le _ _
        _ ≤ 2 * r / T + |F x| * |R 0 - 1| := by
          calc
            |R x - F x| + |F x * (1 - R 0)| =
                |R x - F x| + |F x| * |R 0 - 1| := by
              rw [abs_mul, abs_sub_comm (1 : ℝ) (R 0)]
            _ ≤ 2 * r / T + |F x| * |R 0 - 1| :=
              add_le_add hclose (le_refl _)
        _ ≤ 2 * r / T + 2 * r / T := by
          have hprod : |F x| * |R 0 - 1| ≤ 2 * r / T := by
            calc
              |F x| * |R 0 - 1| ≤ 1 * |R 0 - 1| :=
                mul_le_mul_of_nonneg_right hFxabs (abs_nonneg _)
              _ ≤ 1 * (2 * r / T) :=
                mul_le_mul_of_nonneg_left hRzero_close (by norm_num)
              _ = 2 * r / T := by ring
          exact add_le_add (le_refl _) hprod
    have hrewrite : H x - F x =
        (R x - R 0 * F x) / R 0 := by
      dsimp [H]
      field_simp [hRzero_pos.ne']
    rw [hrewrite, abs_div]
    rw [abs_of_pos hRzero_pos]
    have hden : (1 : ℝ) / 2 ≤ R 0 := by linarith [hRzero_lower, ha_quarter]
    have hquot : (2 * r / T + 2 * r / T) / R 0 ≤
        4 * (2 * r / T) := by
      apply (div_le_iff₀ hRzero_pos).2
      nlinarith [hden, ha]
    exact (div_le_div_of_nonneg_right hnum hRzero_pos.le).trans
      (hquot.trans ha_eps)
  have hHpt : chapter07PositiveType H := by
    refine
      { continuous := hHcont
        integrable := hHint
        transformNonnegative := ?_ }
    intro t
    have hHfourier :=
      LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05_fourier_transform_eq_ofReal_real_transform
        hHint hHeven t
    have hRfourier :=
      LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05_fourier_transform_eq_ofReal_real_transform
        hRint hReven t
    have hHre : (chapter07FourierTransform H t).re =
        chapter07CosineTransform H t := by
      change (LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05FourierTransform H t).re =
        LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05RealFourierTransform H t
      rw [hHfourier]
      simp
    have hHim : (chapter07FourierTransform H t).im = 0 := by
      change (LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05FourierTransform H t).im = 0
      rw [hHfourier]
      simp
    have hRre : (chapter07FourierTransform R t).re =
        chapter07CosineTransform R t := by
      change (LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05FourierTransform R t).re =
        LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05RealFourierTransform R t
      rw [hRfourier]
      simp
    have hRcos : 0 ≤ chapter07CosineTransform R t := by
      rw [← hRre]
      exact hRpt.transformNonnegative t |>.2
    have hscale : chapter07CosineTransform H t =
        chapter07CosineTransform R t / R 0 := by
      unfold chapter07CosineTransform
      change (∫ x : ℝ, (R x / R 0) * Real.cos (t * x)) =
        (∫ x : ℝ, R x * Real.cos (t * x)) / R 0
      have hscale' :
          (fun x : ℝ => (R x / R 0) * Real.cos (t * x)) =
            (fun x : ℝ => (R x * Real.cos (t * x)) / R 0) := by
        funext x
        field_simp [hRzero_pos.ne']
      rw [hscale']
      exact MeasureTheory.integral_div (R 0)
        (fun x : ℝ => R x * Real.cos (t * x))
    have hHcos : 0 ≤ chapter07CosineTransform H t := by
      rw [hscale]
      exact div_nonneg hRcos hRzero_pos.le
    constructor
    · exact hHim
    · simpa [hHre] using hHcos
  refine ⟨H, ?_⟩
  exact ⟨hHdiff, hHcompact, hHint, hHeven, hHnonneg, hHpt, hHzero,
    hHclose⟩

def chapter07IntervalBump (T : ℝ) (x : ℝ) : ℝ :=
  if |x| ≤ T then 1 else 0

theorem chapter07_intervalBump_pointwiseNonnegative (T : ℝ) :
    chapter07PointwiseNonnegative (chapter07IntervalBump T) := by
  intro x
  by_cases hx : |x| ≤ T <;> simp [chapter07IntervalBump, hx]

theorem chapter07_intervalBump_fourier_oscillates (T : ℝ) (hT : 0 < T) :
    ∃ t : ℝ,
      (chapter07FourierTransform (chapter07IntervalBump T) t).re < 0 := by
  let t : ℝ := 3 * Real.pi / (2 * T)
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hbox : chapter07IntervalBump T =
      (Set.Icc (-T) T).indicator (fun _ : ℝ => (1 : ℝ)) := by
    funext x
    by_cases hx : |x| ≤ T
    · have hx' : x ∈ Set.Icc (-T) T := by
        change -T ≤ x ∧ x ≤ T
        constructor
        · have := neg_le_abs x
          linarith
        · exact (le_abs_self x).trans hx
      simp [chapter07IntervalBump, hx, Set.indicator, hx']
    · have hx' : x ∉ Set.Icc (-T) T := by
        intro hx'
        apply hx
        exact (abs_le.2 ⟨by linarith [hx'.1], by linarith [hx'.2]⟩)
      simp [chapter07IntervalBump, hx, Set.indicator, hx']
  have hbox_int : Integrable (chapter07IntervalBump T) := by
    rw [hbox]
    have hfinite : volume (Set.Icc (-T) T) ≠ ⊤ := isCompact_Icc.measure_ne_top
    exact (integrableOn_const (s := Set.Icc (-T) T) hfinite).integrable_indicator
      isClosed_Icc.measurableSet
  have hcos :
      (chapter07FourierTransform (chapter07IntervalBump T) t).re =
        ∫ x in Set.Icc (-T) T, Real.cos (t * x) := by
    rw [chapter07FourierTransform_re_eq_cosineTransform _ hbox_int t]
    simp only [chapter07CosineTransform,
      LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05RealFourierTransform,
      hbox]
    have hind : (fun x : ℝ =>
        (Set.Icc (-T) T).indicator (fun _ : ℝ => (1 : ℝ)) x *
          Real.cos (t * x)) =
        (Set.Icc (-T) T).indicator (fun x : ℝ => Real.cos (t * x)) := by
      funext x
      by_cases hx : x ∈ Set.Icc (-T) T <;>
        simp [Set.indicator, hx]
    rw [hind, integral_indicator isClosed_Icc.measurableSet]
  have hsin_pos : Real.sin (t * T) = -1 := by
    have harg : t * T = 3 * Real.pi / 2 := by
      dsimp [t]
      field_simp
    rw [harg, show 3 * Real.pi / 2 = Real.pi + Real.pi / 2 by ring,
      Real.sin_add]
    simp
  have hsin_neg : Real.sin (t * (-T)) = 1 := by
    rw [show t * (-T) = -(t * T) by ring, Real.sin_neg, hsin_pos]
    norm_num
  refine ⟨t, ?_⟩
  rw [hcos]
  rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  rw [intervalIntegral.integral_comp_mul_left (f := Real.cos) (c := t)
    (by linarith : t ≠ 0)]
  rw [integral_cos, hsin_pos, hsin_neg]
  rw [smul_eq_mul]
  exact mul_neg_of_pos_of_neg (inv_pos.mpr ht) (by norm_num)

theorem chapter07_intervalBump_not_fourierNonnegative (T : ℝ) (hT : 0 < T) :
    ¬chapter07FourierNonnegative (chapter07IntervalBump T) := by
  intro hnonnegative
  obtain ⟨t, ht⟩ := chapter07_intervalBump_fourier_oscillates T hT
  exact (not_lt_of_ge (hnonnegative.2 t).1) ht

def chapter07CosineWave (x : ℝ) : ℝ :=
  Real.cos x

theorem chapter07_cosineWave_positiveDefinite :
    chapter07PositiveDefinite chapter07CosineWave := by
  refine ⟨by
    change Continuous (fun x : ℝ => Real.cos x)
    exact Real.continuous_cos, ?_⟩
  intro n x c
  let A : ℂ := ∑ i, c i * (Real.cos (x i) : ℂ)
  let B : ℂ := ∑ i, c i * (Real.sin (x i) : ℂ)
  have hfactor (u : Fin n → ℝ) :
      (∑ i, ∑ j, c i * star (c j) *
          ((u i : ℂ) * (u j : ℂ))) =
        (∑ i, c i * (u i : ℂ)) *
          star (∑ i, c i * (u i : ℂ)) := by
    calc
      (∑ i, ∑ j, c i * star (c j) *
          ((u i : ℂ) * (u j : ℂ))) =
          ∑ i, ∑ j, (c i * (u i : ℂ)) *
            (star (c j) * (u j : ℂ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        simp [mul_assoc, mul_left_comm, mul_comm]
      _ = ∑ i, (c i * (u i : ℂ)) *
          (∑ j, star (c j) * (u j : ℂ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
      _ = (∑ i, c i * (u i : ℂ)) *
          (∑ j, star (c j) * (u j : ℂ)) := by
        rw [Finset.sum_mul]
      _ = (∑ i, c i * (u i : ℂ)) *
          star (∑ i, c i * (u i : ℂ)) := by
        congr 1
        simp [star_mul, mul_comm]
  have hsplit (u v : Fin n → ℝ) :
      (∑ i, ∑ j, c i * star (c j) *
          ((u i : ℂ) * (u j : ℂ) + (v i : ℂ) * (v j : ℂ))) =
        (∑ i, ∑ j, c i * star (c j) * ((u i : ℂ) * (u j : ℂ))) +
          (∑ i, ∑ j, c i * star (c j) * ((v i : ℂ) * (v j : ℂ))) := by
    calc
      (∑ i, ∑ j, c i * star (c j) *
          ((u i : ℂ) * (u j : ℂ) + (v i : ℂ) * (v j : ℂ))) =
          ∑ i, ∑ j, (c i * star (c j) * ((u i : ℂ) * (u j : ℂ)) +
            c i * star (c j) * ((v i : ℂ) * (v j : ℂ))) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [mul_add]
      _ = (∑ i, ∑ j, c i * star (c j) * ((u i : ℂ) * (u j : ℂ))) +
          (∑ i, ∑ j, c i * star (c j) * ((v i : ℂ) * (v j : ℂ))) := by
        simp only [Finset.sum_add_distrib]
  have hsum :
      (∑ i, ∑ j, c i * star (c j) *
          (chapter07CosineWave (x i - x j) : ℂ)) =
        A * star A + B * star B := by
    simp only [chapter07CosineWave, Real.cos_sub]
    push_cast
    have htrig := hsplit (fun i => Real.cos (x i)) (fun i => Real.sin (x i))
    calc
      _ = (∑ i, ∑ j, c i * star (c j) *
          (Complex.cos (x i) * Complex.cos (x j))) +
          (∑ i, ∑ j, c i * star (c j) *
            (Complex.sin (x i) * Complex.sin (x j))) := by
        simpa only [Complex.ofReal_cos, Complex.ofReal_sin] using htrig
      _ = A * star A + B * star B := by
        simpa [A, B, Complex.ofReal_cos, Complex.ofReal_sin] using
          congrArg₂ (· + ·)
            (hfactor (fun i => Real.cos (x i)))
            (hfactor (fun i => Real.sin (x i)))
  rw [hsum]
  have hA : A * star A = (Complex.normSq A : ℂ) := by
    simpa [Complex.star_def] using Complex.mul_conj A
  have hB : B * star B = (Complex.normSq B : ℂ) := by
    simpa [Complex.star_def] using Complex.mul_conj B
  constructor
  · rw [hA, hB]
    simp only [Complex.add_re, Complex.ofReal_re]
    exact add_nonneg (Complex.normSq_nonneg A) (Complex.normSq_nonneg B)
  · rw [hA, hB]
    simp only [Complex.add_im, Complex.ofReal_im]
    simp

theorem chapter07_cosineWave_not_pointwiseNonnegative :
    ¬chapter07PointwiseNonnegative chapter07CosineWave := by
  intro h
  have hπ := h Real.pi
  simp [chapter07CosineWave] at hπ
  linarith

def chapter07OscillatoryGaussian (σ : ℝ) (x : ℝ) : ℝ :=
  chapter07Gaussian σ x * Real.cos x

theorem chapter07_oscillatoryGaussian_fourierNonnegative
    (σ : ℝ) (hσ : 0 < σ) :
    chapter07FourierNonnegative (chapter07OscillatoryGaussian σ) := by
  let b : ℝ := 1 / (2 * σ ^ 2)
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hgauss (x : ℝ) :
      chapter07Gaussian σ x = Real.exp (-b * x ^ 2) := by
    dsimp [chapter07Gaussian, b]
    congr 1
    ring
  have hgauss_integrable : Integrable (chapter07Gaussian σ) := by
    rw [show chapter07Gaussian σ = (fun x : ℝ => Real.exp (-b * x ^ 2)) by
      funext x; exact hgauss x]
    exact integrable_exp_neg_mul_sq hb
  have hterm (s : ℝ) :
      Integrable (fun x : ℝ =>
        (chapter07Gaussian σ x : ℂ) *
          Complex.exp (-Complex.I * (s : ℂ) * (x : ℂ))) := by
    have hq : Integrable (fun x : ℝ =>
        Complex.exp (-(b : ℂ) * (x : ℂ) ^ 2 +
          (-Complex.I * (s : ℂ)) * (x : ℂ) + 0)) := by
      exact integrable_cexp_quadratic (b := (b : ℂ)) (by simpa using hb)
        (-Complex.I * (s : ℂ)) 0
    convert hq using 1
    funext x
    rw [hgauss]
    simp only [Complex.ofReal_exp, Complex.ofReal_neg,
      Complex.ofReal_mul, Complex.ofReal_pow]
    rw [← Complex.exp_add]
    congr 1
    ring
  have hformula (s : ℝ) :
      chapter07FourierTransform (chapter07Gaussian σ) s =
        ((((Real.pi / b) ^ (1 / 2 : ℝ) *
          Real.exp (-(s ^ 2 / (4 * b)))) : ℝ) : ℂ) := by
    rw [chapter07FourierTransform_eq_integral]
    calc
      (∫ x : ℝ, (chapter07Gaussian σ x : ℂ) *
          Complex.exp (-Complex.I * (s : ℂ) * (x : ℂ))) =
          ∫ x : ℝ, Complex.exp (Complex.I * (-(s : ℂ)) * (x : ℂ)) *
            Complex.exp (-(b : ℂ) * (x : ℂ) ^ 2) := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [hgauss]
        simp only [Complex.ofReal_exp, Complex.ofReal_neg,
          Complex.ofReal_mul, Complex.ofReal_pow]
        rw [mul_comm]
        congr 1
        congr 1
        ring
      _ = (Real.pi / (b : ℂ)) ^ (1 / 2 : ℂ) *
          Complex.exp (- (-(s : ℂ)) ^ 2 / (4 * (b : ℂ))) := by
        exact fourierIntegral_gaussian (b := (b : ℂ)) (by simpa using hb)
          (-(s : ℂ))
      _ = ((((Real.pi / b) ^ (1 / 2 : ℝ) *
          Real.exp (-(s ^ 2 / (4 * b)))) : ℝ) : ℂ) := by
        have harg :
            - (-(s : ℂ)) ^ 2 / (4 * (b : ℂ)) =
              (-(s ^ 2 / (4 * b)) : ℝ) := by
          norm_num
          ring
        have hpow :
            ((Real.pi / b : ℝ) : ℂ) ^ ((1 / 2 : ℝ) : ℂ) =
              (((Real.pi / b) ^ (1 / 2 : ℝ) : ℝ) : ℂ) :=
          (Complex.ofReal_cpow (by positivity : 0 ≤ Real.pi / b)
            (1 / 2 : ℝ)).symm
        have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
          norm_num
        rw [show (Real.pi : ℂ) / (b : ℂ) =
            ((Real.pi / b : ℝ) : ℂ) by norm_num]
        rw [hhalf, hpow, harg, ← Complex.ofReal_exp]
        simp only [Complex.ofReal_mul]
  have hosc_integrable : Integrable (chapter07OscillatoryGaussian σ) := by
    apply Integrable.mono' hgauss_integrable.norm
    · exact hgauss_integrable.1.mul Real.continuous_cos.aestronglyMeasurable
    · filter_upwards [] with x
      change ‖chapter07Gaussian σ x * Real.cos x‖ ≤
        ‖chapter07Gaussian σ x‖
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one x)
  have hcos (x : ℝ) :
      (Real.cos x : ℂ) =
        (Complex.exp (Complex.I * (x : ℂ)) +
          Complex.exp (-Complex.I * (x : ℂ))) / 2 := by
    simp [Complex.ofReal_cos, Complex.cos, mul_comm]
  have hsplit (t : ℝ) :
      chapter07FourierTransform (chapter07OscillatoryGaussian σ) t =
        (1 / 2 : ℂ) *
          (chapter07FourierTransform (chapter07Gaussian σ) (t - 1) +
            chapter07FourierTransform (chapter07Gaussian σ) (t + 1)) := by
    rw [chapter07FourierTransform_eq_integral]
    calc
      (∫ x : ℝ, (chapter07OscillatoryGaussian σ x : ℂ) *
          Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ))) =
          ∫ x : ℝ, (1 / 2 : ℂ) *
            ((chapter07Gaussian σ x : ℂ) *
                Complex.exp (-Complex.I * ((t - 1 : ℝ) : ℂ) * (x : ℂ)) +
              (chapter07Gaussian σ x : ℂ) *
                Complex.exp (-Complex.I * ((t + 1 : ℝ) : ℂ) * (x : ℂ))) := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [chapter07OscillatoryGaussian, Complex.ofReal_mul, hcos]
        have h₁ : Complex.exp (Complex.I * (x : ℂ)) *
              Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ)) =
            Complex.exp (-Complex.I * ((t - 1 : ℝ) : ℂ) * (x : ℂ)) := by
          rw [← Complex.exp_add]
          congr 1
          norm_num
          ring
        have h₂ : Complex.exp (-Complex.I * (x : ℂ)) *
              Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ)) =
            Complex.exp (-Complex.I * ((t + 1 : ℝ) : ℂ) * (x : ℂ)) := by
          rw [← Complex.exp_add]
          congr 1
          norm_num
          ring
        calc
          (chapter07Gaussian σ x : ℂ) *
              ((Complex.exp (Complex.I * (x : ℂ)) +
                Complex.exp (-Complex.I * (x : ℂ))) / 2) *
              Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ)) =
              (1 / 2 : ℂ) *
                ((chapter07Gaussian σ x : ℂ) *
                    (Complex.exp (Complex.I * (x : ℂ)) *
                      Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ))) +
                  (chapter07Gaussian σ x : ℂ) *
                    (Complex.exp (-Complex.I * (x : ℂ)) *
                      Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ)))) := by ring
          _ = (1 / 2 : ℂ) *
                ((chapter07Gaussian σ x : ℂ) *
                    Complex.exp (-Complex.I * ((t - 1 : ℝ) : ℂ) * (x : ℂ)) +
                  (chapter07Gaussian σ x : ℂ) *
                    Complex.exp (-Complex.I * ((t + 1 : ℝ) : ℂ) * (x : ℂ))) := by
            rw [h₁, h₂]
      _ = (1 / 2 : ℂ) *
          ((∫ x : ℝ, (chapter07Gaussian σ x : ℂ) *
              Complex.exp (-Complex.I * ((t - 1 : ℝ) : ℂ) * (x : ℂ))) +
            (∫ x : ℝ, (chapter07Gaussian σ x : ℂ) *
              Complex.exp (-Complex.I * ((t + 1 : ℝ) : ℂ) * (x : ℂ)))) := by
        rw [integral_const_mul]
        rw [integral_add (hterm (t - 1)) (hterm (t + 1))]
      _ = (1 / 2 : ℂ) *
          (chapter07FourierTransform (chapter07Gaussian σ) (t - 1) +
            chapter07FourierTransform (chapter07Gaussian σ) (t + 1)) := by
        rw [chapter07FourierTransform_eq_integral,
          chapter07FourierTransform_eq_integral]
  refine ⟨hosc_integrable, ?_⟩
  intro t
  rw [hsplit, hformula, hformula]
  have hcast :
      (1 / 2 : ℂ) *
          (((((Real.pi / b) ^ (1 / 2 : ℝ) *
            Real.exp (-((t - 1) ^ 2 / (4 * b)))) : ℝ) : ℂ) +
            ((((Real.pi / b) ^ (1 / 2 : ℝ) *
            Real.exp (-((t + 1) ^ 2 / (4 * b)))) : ℝ) : ℂ)) =
        (((1 / 2 : ℝ) *
          ((Real.pi / b) ^ (1 / 2 : ℝ) *
            Real.exp (-((t - 1) ^ 2 / (4 * b))) +
            (Real.pi / b) ^ (1 / 2 : ℝ) *
            Real.exp (-((t + 1) ^ 2 / (4 * b)))) : ℝ) : ℂ) := by
    norm_num
  rw [hcast]
  have hleft : 0 ≤ (Real.pi / b) ^ (1 / 2 : ℝ) *
      Real.exp (-((t - 1) ^ 2 / (4 * b))) := by positivity
  have hright : 0 ≤ (Real.pi / b) ^ (1 / 2 : ℝ) *
      Real.exp (-((t + 1) ^ 2 / (4 * b))) := by positivity
  change 0 ≤ (1 / 2 : ℝ) *
      ((Real.pi / b) ^ (1 / 2 : ℝ) *
        Real.exp (-((t - 1) ^ 2 / (4 * b))) +
      (Real.pi / b) ^ (1 / 2 : ℝ) *
        Real.exp (-((t + 1) ^ 2 / (4 * b)))) ∧ _
  constructor
  · positivity
  · rfl

theorem chapter07_oscillatoryGaussian_positiveType
    (σ : ℝ) (hσ : 0 < σ) :
    chapter07PositiveType (chapter07OscillatoryGaussian σ) := by
  have hcont : Continuous (chapter07OscillatoryGaussian σ) := by
    unfold chapter07OscillatoryGaussian
    apply Continuous.mul
    · unfold chapter07Gaussian
      fun_prop
    · exact Real.continuous_cos
  have hfourier := chapter07_oscillatoryGaussian_fourierNonnegative σ hσ
  refine ⟨hcont, hfourier.1, ?_⟩
  intro t
  exact ⟨(hfourier.2 t).2, (hfourier.2 t).1⟩

theorem chapter07_oscillatoryGaussian_not_pointwiseNonnegative
    (σ : ℝ) (hσ : 0 < σ) :
    ¬chapter07PointwiseNonnegative (chapter07OscillatoryGaussian σ) := by
  intro h
  have _hσ_nonneg : 0 ≤ σ := hσ.le
  have hπ := h Real.pi
  simp [chapter07OscillatoryGaussian, chapter07Gaussian] at hπ
  have hexp : 0 < Real.exp (-(Real.pi ^ 2) / (2 * σ ^ 2)) := Real.exp_pos _
  linarith

theorem chapter07_prime_and_zero_positivity_are_independent :
    (∃ f : Chapter07TestFunction,
      chapter07PointwiseNonnegative f ∧ ¬chapter07FourierNonnegative f) ∧
      (∃ f : Chapter07TestFunction,
        chapter07FourierNonnegative f ∧ ¬chapter07PointwiseNonnegative f) := by
  constructor
  · refine ⟨chapter07IntervalBump 1,
      chapter07_intervalBump_pointwiseNonnegative 1, ?_⟩
    exact chapter07_intervalBump_not_fourierNonnegative 1 (by norm_num)
  · refine ⟨chapter07OscillatoryGaussian 1,
      chapter07_oscillatoryGaussian_fourierNonnegative 1 (by norm_num), ?_⟩
    exact chapter07_oscillatoryGaussian_not_pointwiseNonnegative 1 (by norm_num)

theorem chapter07_optimization_requires_both_positivity_cones
    (F : Chapter07TestFunction)
    (hprime : F ∈ chapter07PrimePositivityCone)
    (hzero : F ∈ chapter07ZeroPositivityCone) :
    F ∈ chapter07RequiredPositivityCone := by
  exact ⟨hprime, hzero⟩

end
end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter07
