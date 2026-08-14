import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06.Dependencies
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06.Section01StatementWithEveryTermVisible
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06

noncomputable section

open MeasureTheory Set Filter NumberField
open scoped BigOperators Topology
open scoped FourierTransform
open scoped ContDiff
open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03
open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04
open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05

/-! ### 6.3. Prime and discriminant terms -/

private def chapter06PrimePowerIndexEquiv
    (K : Type*) [Field K] [NumberField K] :
    Chapter06PrimePower K ≃ Chapter03PrimePower K :=
  { toFun := fun q => (q.1, q.2.1 - 1)
    invFun := fun q => (q.1, ⟨q.2 + 1, Nat.zero_lt_succ _⟩)
    left_inv := by
      rintro ⟨P, ⟨m, hm⟩⟩
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        dsimp
        omega
    right_inv := by
      rintro ⟨P, m⟩
      apply Prod.ext
      · rfl
      · dsimp }

theorem chapter06_bilateral_laplace_inversion
    {F : ℝ → ℝ} (hF : Chapter06SmoothCompactSupport F)
    {c y : ℝ} (hc : 1 < c) (hy : 0 < y) :
    Tendsto (fun T => chapter06LaplaceInversePartial F c y T) atTop
      (𝓝 (F y : ℂ)) := by
  let _ := hc
  let _ := hy
  let g : ℝ → ℂ := fun x => (F x : ℂ) *
    Complex.exp (((c - 1 / 2 : ℝ) : ℂ) * (x : ℂ))
  have hFc : HasCompactSupport (fun x : ℝ => (F x : ℂ)) := by
    simpa [Function.comp_def] using
      hF.2.2.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
  have hgc : HasCompactSupport g := by
    dsimp [g]
    exact hFc.mul_right
  have hFcomp := Complex.ofRealCLM.contDiff.comp hF.2.1
  have hExp : ContDiff ℝ ∞
      (fun x : ℝ => Complex.exp (((c - 1 / 2 : ℝ) : ℂ) * (x : ℂ))) := by
    apply Complex.contDiff_exp.comp
    exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp contDiff_id)
  have hgcd : ContDiff ℝ ∞ g := by
    dsimp [g]
    simpa [Function.comp_def] using hFcomp.mul hExp
  let gs : SchwartzMap ℝ ℂ := hgc.toSchwartzMap hgcd
  have hgi : Integrable g volume := by
    exact hgcd.continuous.integrable_of_hasCompactSupport hgc
  have hfourieri : Integrable (𝓕 g) volume := by
    change Integrable (𝓕 (gs : ℝ → ℂ)) volume
    exact (𝓕 gs).integrable
  have hinv : 𝓕⁻ (𝓕 g) y = g y := by
    exact hgi.fourierInv_fourier_eq hfourieri hgcd.continuous.continuousAt
  have hphi (ξ : ℝ) :
      chapter06Phi F (chapter06VerticalLinePoint c (-(2 * Real.pi * ξ))) =
        𝓕 g ξ := by
    rw [Real.fourier_eq']
    unfold chapter06Phi chapter05BilateralLaplaceTransform chapter05LaplaceKernel
    apply integral_congr_ae
    filter_upwards with x
    dsimp [g, chapter06VerticalLinePoint]
    calc
      (F x : ℂ) * Complex.exp
          ((↑c + ↑(-(2 * Real.pi * ξ)) * Complex.I - 1 / 2) * (x : ℂ)) =
          (F x : ℂ) *
            (Complex.exp (↑(-2 * Real.pi * (ξ * x)) * Complex.I) *
              Complex.exp ((↑(c - 1 / 2) : ℂ) * (x : ℂ))) := by
        rw [← Complex.exp_add]
        congr 1
        simp
        ring
      _ = Complex.exp (↑(-2 * Real.pi * (ξ * x)) * Complex.I) *
          ((F x : ℂ) * Complex.exp ((↑(c - 1 / 2) : ℂ) * (x : ℂ))) := by
        ring
  let H : ℝ → ℂ := fun ξ =>
    Complex.exp (((2 * Real.pi * ξ * y : ℝ) : ℂ) * Complex.I) * 𝓕 g ξ
  have hH : Integrable H volume := by
    change Integrable
      ((fun ξ : ℝ => Complex.exp (((2 * Real.pi * ξ * y : ℝ) : ℂ) * Complex.I)) *
        (𝓕 g)) volume
    have hsmul := hfourieri.bdd_smul (φ := fun ξ : ℝ =>
        Complex.exp (((2 * Real.pi * ξ * y : ℝ) : ℂ) * Complex.I))
      1 (by fun_prop) (by
        filter_upwards with ξ
        rw [Complex.norm_exp]
        simp)
    simpa [smul_eq_mul] using hsmul
  have hfull : (∫ ξ : ℝ, H ξ) = g y := by
    rw [← hinv, Real.fourierInv_eq']
    apply integral_congr_ae
    filter_upwards with ξ
    dsimp [H]
    have hξ : (starRingEnd ℝ) ξ = ξ := by simp
    rw [hξ]
    congr 1
    ring
  have hscale : Tendsto (fun T : ℝ => T / (2 * Real.pi)) atTop atTop := by
    apply (tendsto_div_const_atTop_of_pos (by positivity)).2
    exact tendsto_id
  have hinterval :
      Tendsto (fun T : ℝ =>
        ∫ ξ in (-T / (2 * Real.pi))..(T / (2 * Real.pi)), H ξ) atTop
        (𝓝 (∫ ξ : ℝ, H ξ)) := by
    apply intervalIntegral_tendsto_integral hH
    · simpa [Function.comp_def, neg_div] using tendsto_neg_atTop_atBot.comp hscale
    · exact hscale
  have hpartial (T : ℝ) :
      chapter06LaplaceInversePartial F c y T =
        Complex.exp (-(((c - 1 / 2) * y : ℝ) : ℂ)) *
          (∫ ξ in (-T / (2 * Real.pi))..(T / (2 * Real.pi)), H ξ) := by
    let L : ℝ → ℂ := fun t =>
      chapter06Phi F (chapter06VerticalLinePoint c t) *
        Complex.exp (-((y : ℂ) *
          (chapter06VerticalLinePoint c t - (1 / 2 : ℂ)))) * Complex.I
    let p : ℝ := 2 * Real.pi
    have hp : p ≠ 0 := by
      dsimp [p]
      positivity
    have hleft : p * (-T / p) = -T := by
      field_simp [hp]
    have hright : p * (T / p) = T := by
      field_simp [hp]
    have hneg :
        (∫ t in (-T)..T, L (-t)) = ∫ t in (-T)..T, L t := by
      rw [intervalIntegral.integral_comp_neg]
      simp
    have hsub :
        p • (∫ ξ in (-T / p)..(T / p), L (-(p * ξ))) =
          ∫ t in (-T)..T, L t := by
      calc
        p • (∫ ξ in (-T / p)..(T / p), L (-(p * ξ))) =
            ∫ t in p * (-T / p)..p * (T / p), L (-t) := by
              simpa only [smul_eq_mul] using
                (intervalIntegral.smul_integral_comp_mul_left
                  (f := fun t : ℝ => L (-t))
                  (a := -T / p) (b := T / p) p)
        _ = ∫ t in (-T)..T, L (-t) := by rw [hleft, hright]
        _ = ∫ t in (-T)..T, L t := hneg
    have hL (ξ : ℝ) :
        L (-(2 * Real.pi * ξ)) =
          Complex.exp (-(((c - 1 / 2) * y : ℝ) : ℂ)) * H ξ * Complex.I := by
      dsimp [L, H]
      change chapter06Phi F (chapter06VerticalLinePoint c (-(2 * Real.pi * ξ))) *
          Complex.exp (-((y : ℂ) *
            (chapter06VerticalLinePoint c (-(2 * Real.pi * ξ)) - (1 / 2 : ℂ)))) *
            Complex.I = _
      rw [hphi ξ]
      have hexp :
          Complex.exp (-((y : ℂ) *
            (chapter06VerticalLinePoint c (-(2 * Real.pi * ξ)) - (1 / 2 : ℂ)))) =
            Complex.exp (-(((c - 1 / 2) * y : ℝ) : ℂ)) *
              Complex.exp (((2 * Real.pi * ξ * y : ℝ) : ℂ) * Complex.I) := by
        rw [← Complex.exp_add]
        congr 1
        dsimp [chapter06VerticalLinePoint]
        simp
        ring
      rw [hexp]
      ring
    have hJ :
        (∫ ξ in (-T / p)..(T / p), L (-(p * ξ))) =
          Complex.exp (-(((c - 1 / 2) * y : ℝ) : ℂ)) *
            (∫ ξ in (-T / p)..(T / p), H ξ) * Complex.I := by
      calc
        (∫ ξ in (-T / p)..(T / p), L (-(p * ξ))) =
            ∫ ξ in (-T / p)..(T / p),
              (Complex.exp (-(((c - 1 / 2) * y : ℝ) : ℂ)) * H ξ) *
                Complex.I := by
              apply intervalIntegral.integral_congr
              intro ξ _
              simpa [p] using hL ξ
        _ = Complex.exp (-(((c - 1 / 2) * y : ℝ) : ℂ)) *
              (∫ ξ in (-T / p)..(T / p), H ξ) * Complex.I := by
              rw [intervalIntegral.integral_mul_const,
                intervalIntegral.integral_const_mul]
    change (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
      (∫ t in (-T)..T, L t) = _
    rw [← hsub, hJ]
    rw [Complex.real_smul]
    simp only [p]
    field_simp [Real.pi_ne_zero, Complex.I_ne_zero]
    push_cast
    ring
  have hmain :
      Tendsto
        (fun T : ℝ => Complex.exp (-(((c - 1 / 2) * y : ℝ) : ℂ)) *
          (∫ ξ in (-T / (2 * Real.pi))..(T / (2 * Real.pi)), H ξ)) atTop
        (𝓝 (Complex.exp (-(((c - 1 / 2) * y : ℝ) : ℂ)) * g y)) := by
    simpa [hfull] using
      (tendsto_const_nhds.mul hinterval :
        Tendsto
          (fun T : ℝ => Complex.exp (-(((c - 1 / 2) * y : ℝ) : ℂ)) *
            (∫ ξ in (-T / (2 * Real.pi))..(T / (2 * Real.pi)), H ξ)) atTop
          (𝓝 (Complex.exp (-(((c - 1 / 2) * y : ℝ) : ℂ)) *
            (∫ ξ : ℝ, H ξ))))
  have hmain' :
      Tendsto (fun T => chapter06LaplaceInversePartial F c y T) atTop
        (𝓝 (Complex.exp (-(((c - 1 / 2) * y : ℝ) : ℂ)) * g y)) := by
    apply hmain.congr'
    filter_upwards with T
    exact (hpartial T).symm
  have hval :
      Complex.exp (-(((c - 1 / 2) * y : ℝ) : ℂ)) * g y = (F y : ℂ) := by
    dsimp [g]
    calc
      Complex.exp (-(((c - 1 / 2) * y : ℝ) : ℂ)) *
          ((F y : ℂ) * Complex.exp (((c - 1 / 2 : ℝ) : ℂ) * (y : ℂ))) =
          (F y : ℂ) *
            (Complex.exp (-(((c - 1 / 2) * y : ℝ) : ℂ)) *
              Complex.exp (((c - 1 / 2 : ℝ) : ℂ) * (y : ℂ))) := by ring
      _ = (F y : ℂ) * Complex.exp
          (-(((c - 1 / 2) * y : ℝ) : ℂ) +
            (((c - 1 / 2 : ℝ) : ℂ) * (y : ℂ))) := by
          rw [← Complex.exp_add]
      _ = (F y : ℂ) := by
        have hzero :
            -(((c - 1 / 2) * y : ℝ) : ℂ) +
              (((c - 1 / 2 : ℝ) : ℂ) * (y : ℂ)) = 0 := by
          push_cast
          ring
        rw [hzero, Complex.exp_zero, mul_one]
  rw [hval] at hmain'
  exact hmain'

theorem chapter06_zeta_log_derivative_series_summable
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : 1 < s.re) :
    Summable (fun q : Chapter06PrimePower K =>
      ‖chapter06ZetaLogDerivativeTerm q s‖) := by
  let e := chapter06PrimePowerIndexEquiv K
  have h3 := chapter03_log_derivative_series_absolutely_summable K hs
  have he := e.summable_iff.mpr h3
  apply he.congr
  intro q
  have hm : 0 < q.2.1 := q.2.2
  have hnat : q.2.1 - 1 + 1 = q.2.1 := by omega
  have hcast : ((q.2.1 - 1 + 1 : ℕ) : ℂ) = (q.2.1 : ℂ) := by
    exact_mod_cast hnat
  dsimp [e, chapter06PrimePowerIndexEquiv, chapter06ZetaLogDerivativeTerm,
    chapter06PrimeIdealNorm, chapter03LogDerivativeTerm]
  rw [hcast]
  congr 2
  ring

theorem chapter06_zeta_log_derivative_series_eq
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : 1 < s.re) :
    chapter06ZetaLogDerivative K s = chapter06ZetaLogDerivativeSeries K s := by
  let e := chapter06PrimePowerIndexEquiv K
  have hsum : chapter06ZetaLogDerivativeSeries K s =
      chapter03LogDerivativeSeries K s := by
    unfold chapter06ZetaLogDerivativeSeries
    have h3series :
        (∑' q : Chapter03PrimePower K, chapter03LogDerivativeTerm q s) =
          chapter03LogDerivativeSeries K s :=
      (chapter03_log_derivative_series_summable K hs).tsum_prod
    calc
      (∑' q : Chapter06PrimePower K, chapter06ZetaLogDerivativeTerm q s) =
          ∑' q : Chapter03PrimePower K, chapter03LogDerivativeTerm q s := by
        rw [← e.tsum_eq]
        apply tsum_congr
        intro q
        have hm : 0 < q.2.1 := q.2.2
        have hnat : q.2.1 - 1 + 1 = q.2.1 := by omega
        have hcast : ((q.2.1 - 1 + 1 : ℕ) : ℂ) = (q.2.1 : ℂ) := by
          exact_mod_cast hnat
        dsimp [e, chapter06PrimePowerIndexEquiv, chapter06ZetaLogDerivativeTerm,
          chapter06PrimeIdealNorm, chapter03LogDerivativeTerm]
        rw [hcast]
        congr 2
        ring
      _ = chapter03LogDerivativeSeries K s := h3series
  rw [hsum]
  unfold chapter06ZetaLogDerivative chapter06LogDerivative
  change -(deriv (chapter03DedekindZeta K) s /
    chapter03DedekindZeta K s) = chapter03LogDerivativeSeries K s
  have hformula := chapter03_log_derivative_formula K (s := s) hs
  simpa [div_eq_mul_inv] using hformula

theorem chapter06_zeta_log_derivative_negative_series_eq
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : 1 < s.re) :
    chapter06LogDerivative
        (LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03.chapter03DedekindZeta K)
        s = -chapter06ZetaLogDerivativeSeries K s := by
  calc
    chapter06LogDerivative
        (LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03.chapter03DedekindZeta K)
        s = -chapter06ZetaLogDerivative K s := by
          simp [chapter06ZetaLogDerivative]
    _ = -chapter06ZetaLogDerivativeSeries K s := by
      rw [chapter06_zeta_log_derivative_series_eq K hs]

theorem chapter06_xi_log_derivative_decomposition
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : 1 < s.re) :
    chapter06LogDerivative (chapter06Xi K) s =
      chapter06PoleLogDerivative s + chapter06DiscriminantLogDerivative K +
        chapter06RealGammaLogDerivative K s +
        chapter06ComplexGammaLogDerivative K s -
        chapter06ZetaLogDerivative K s := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hsre : 0 < s.re := lt_trans (by norm_num) hs
  have hs2re : 0 < (s / 2).re := by
    rw [Complex.div_re]
    norm_num [Complex.normSq_apply]
    positivity
  have hD : (chapter06AbsoluteDiscriminant K : ℂ) ≠ 0 := by
    exact_mod_cast (chapter06_absolute_discriminant_pos K).ne'
  have hDlog : Complex.log (chapter06AbsoluteDiscriminant K : ℂ) =
      (Real.log (chapter06AbsoluteDiscriminant K) : ℂ) := by
    rw [Complex.ofReal_log (le_of_lt (chapter06_absolute_discriminant_pos K))]
  have hDpow : (chapter06AbsoluteDiscriminant K : ℂ) ^ (s / 2) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    exact Or.inl hD
  have hGammaS : Complex.Gamma s ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hsre
  have hGammaS2 : Complex.Gamma (s / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hs2re
  have hGammaReal : chapter04GammaReal s ≠ 0 := by
    unfold chapter04GammaReal
    exact mul_ne_zero
      ((Complex.cpow_ne_zero_iff).2
        (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
      hGammaS2
  have hGammaComplex : chapter04GammaComplex s ≠ 0 := by
    unfold chapter04GammaComplex
    exact mul_ne_zero
      ((Complex.cpow_ne_zero_iff).2 (Or.inl
        (mul_ne_zero (by norm_num)
          (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))) hGammaS
  have hGammaRealDiff : DifferentiableAt ℂ chapter04GammaReal s := by
    unfold chapter04GammaReal
    apply DifferentiableAt.mul
    · exact (differentiableAt_id.neg.div_const 2).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    · exact (Complex.differentiableAt_Gamma (s / 2) (by
        intro m h
        have := congrArg Complex.re h
        simp at this
        linarith)).comp s (by fun_prop)
  have hGammaComplexDiff : DifferentiableAt ℂ chapter04GammaComplex s := by
    unfold chapter04GammaComplex
    apply DifferentiableAt.mul
    · exact (differentiableAt_id.neg).const_cpow
        (Or.inl (mul_ne_zero (by norm_num)
          (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
    · exact Complex.differentiableAt_Gamma s (by
        intro m h
        have := congrArg Complex.re h
        simp at this
        linarith)
  have hDiscDiff : DifferentiableAt ℂ
      (fun z : ℂ => (chapter06AbsoluteDiscriminant K : ℂ) ^ (z / 2)) s := by
    exact (differentiableAt_id.div_const 2).const_cpow (Or.inl hD)
  have hDiscLogDeriv : logDeriv
      (fun z : ℂ => (chapter06AbsoluteDiscriminant K : ℂ) ^ (z / 2)) s =
        chapter06DiscriminantLogDerivative K := by
    have hderiv : HasDerivAt
        (fun z : ℂ => (chapter06AbsoluteDiscriminant K : ℂ) ^ (z / 2))
        ((chapter06AbsoluteDiscriminant K : ℂ) ^ (s / 2) *
          Complex.log (chapter06AbsoluteDiscriminant K : ℂ) * (1 / 2)) s := by
      simpa only [id_eq] using
        ((hasDerivAt_id s).div_const 2).const_cpow
          (c := (chapter06AbsoluteDiscriminant K : ℂ)) (Or.inl hD)
    change logDeriv
      (fun z : ℂ => (chapter06AbsoluteDiscriminant K : ℂ) ^ (z / 2)) s = _
    rw [logDeriv_apply, hderiv.deriv, hDlog]
    field_simp [hDpow]
    simp [chapter06DiscriminantLogDerivative]
    ring
  have hArchDiff : DifferentiableAt ℂ (chapter04ArchimedeanFactor K) s := by
    unfold chapter04ArchimedeanFactor
    exact (hGammaRealDiff.pow _).mul (hGammaComplexDiff.pow _)
  have hArchNe : chapter04ArchimedeanFactor K s ≠ 0 := by
    unfold chapter04ArchimedeanFactor
    exact mul_ne_zero (pow_ne_zero _ hGammaReal) (pow_ne_zero _ hGammaComplex)
  have hArchLogDeriv : logDeriv
      (chapter04ArchimedeanFactor K) s =
        chapter06RealGammaLogDerivative K s +
          chapter06ComplexGammaLogDerivative K s := by
    change logDeriv (chapter04ArchimedeanFactor K) s =
      (chapter04RealPlaces K : ℂ) * logDeriv chapter04GammaReal s +
        (chapter04ComplexPlaces K : ℂ) * logDeriv chapter04GammaComplex s
    unfold chapter04ArchimedeanFactor
    rw [logDeriv_mul
      (f := fun z : ℂ => chapter04GammaReal z ^ chapter04RealPlaces K)
      (g := fun z : ℂ => chapter04GammaComplex z ^ chapter04ComplexPlaces K) s
      (pow_ne_zero _ hGammaReal) (pow_ne_zero _ hGammaComplex)
      (hGammaRealDiff.pow _) (hGammaComplexDiff.pow _),
      logDeriv_fun_pow hGammaRealDiff, logDeriv_fun_pow hGammaComplexDiff]
  have hZetaNe : chapter03DedekindZeta K s ≠ 0 :=
    chapter03_dedekind_zeta_ne_zero K hs
  have hZetaDiff : DifferentiableAt ℂ (chapter03DedekindZeta K) s := by
    exact (chapter03_dedekind_zeta_hasDerivAt_of_euler_half_plane K hs).differentiableAt
  have hEulerNe : chapter04EulerCompletedDedekindZeta K s ≠ 0 := by
    change ((chapter06AbsoluteDiscriminant K : ℂ) ^ (s / 2) *
      chapter04ArchimedeanFactor K s) * chapter03DedekindZeta K s ≠ 0
    exact mul_ne_zero (mul_ne_zero hDpow hArchNe) hZetaNe
  have hEulerDiff : DifferentiableAt ℂ
      (chapter04EulerCompletedDedekindZeta K) s := by
    unfold chapter04EulerCompletedDedekindZeta
    exact (hDiscDiff.mul hArchDiff).mul hZetaDiff
  have hEulerLogDeriv : logDeriv
      (chapter04EulerCompletedDedekindZeta K) s =
        chapter06DiscriminantLogDerivative K +
          chapter06RealGammaLogDerivative K s +
          chapter06ComplexGammaLogDerivative K s -
          chapter06ZetaLogDerivative K s := by
    unfold chapter04EulerCompletedDedekindZeta
    change logDeriv
      (fun z : ℂ =>
        ((chapter06AbsoluteDiscriminant K : ℂ) ^ (z / 2) *
          chapter04ArchimedeanFactor K z) *
          chapter03DedekindZeta K z) s = _
    rw [logDeriv_mul
      (f := fun z : ℂ =>
        (chapter06AbsoluteDiscriminant K : ℂ) ^ (z / 2) *
          chapter04ArchimedeanFactor K z)
      (g := fun z : ℂ => chapter03DedekindZeta K z) s
      (mul_ne_zero hDpow hArchNe) hZetaNe
      (hDiscDiff.mul hArchDiff) hZetaDiff,
      logDeriv_mul
        (f := fun z : ℂ => (chapter06AbsoluteDiscriminant K : ℂ) ^ (z / 2))
        (g := fun z : ℂ => chapter04ArchimedeanFactor K z) s
        hDpow hArchNe hDiscDiff hArchDiff,
      hDiscLogDeriv, hArchLogDeriv]
    simp only [chapter06ZetaLogDerivative, chapter06LogDerivative]
    change _ + deriv (chapter03DedekindZeta K) s *
        (chapter03DedekindZeta K s)⁻¹ = _
    ring
  have hxi : chapter06Xi K =ᶠ[𝓝 s]
      (fun z : ℂ => chapter04PoleFactor z *
        chapter04EulerCompletedDedekindZeta K z) := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := by
      exact isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds hs] with z hz
    change chapter04Xi K z = _
    rw [chapter04_xi_eq_pole_factor_mul_completed_zeta K z
      (by intro h; rw [h] at hz; norm_num at hz)
      (by intro h; rw [h] at hz; norm_num at hz),
      chapter04_completed_dedekind_zeta_agrees_on_euler_half_plane K hz]
    simp [chapter04PoleFactor]
  have hxiLogDeriv : chapter06LogDerivative (chapter06Xi K) s =
      chapter06LogDerivative
        (fun z : ℂ => chapter04PoleFactor z *
          chapter04EulerCompletedDedekindZeta K z) s := by
    change logDeriv (chapter06Xi K) s =
      logDeriv (fun z : ℂ => chapter04PoleFactor z *
        chapter04EulerCompletedDedekindZeta K z) s
    exact (logDeriv_congr_nhds hxi).eq_of_nhds
  have hPoleNe : chapter04PoleFactor s ≠ 0 := by
    unfold chapter04PoleFactor
    exact mul_ne_zero (mul_ne_zero (by norm_num) hs0) (sub_ne_zero.mpr hs1)
  have hPoleDiff : DifferentiableAt ℂ chapter04PoleFactor s := by
    unfold chapter04PoleFactor
    fun_prop
  have hPoleLogDeriv : logDeriv chapter04PoleFactor s =
      chapter06PoleLogDerivative s := by
    unfold chapter06PoleLogDerivative
    exact chapter04_pole_factor_log_derivative hs0 hs1
  rw [hxiLogDeriv]
  change logDeriv
    (fun z : ℂ => chapter04PoleFactor z *
      chapter04EulerCompletedDedekindZeta K z) s = _
  rw [logDeriv_mul s hPoleNe hEulerNe hPoleDiff hEulerDiff,
    hPoleLogDeriv, hEulerLogDeriv]
  ring

noncomputable def chapter06PrimeContourTermPartial
    {K : Type*} [Field K] [NumberField K]
    (q : Chapter06PrimePower K) (F : ℝ → ℝ) (c T : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
    (∫ t in (-T)..T,
      chapter06Phi F (chapter06VerticalLinePoint c t) *
        (-chapter06ZetaLogDerivativeTerm q
          (chapter06VerticalLinePoint c t)) * Complex.I)

theorem chapter06_prime_power_contour_inversion
    (K : Type*) [Field K] [NumberField K]
    (q : Chapter06PrimePower K) {F : ℝ → ℝ}
    (hF : Chapter06SmoothCompactSupport F) {c : ℝ} (hc : 1 < c) :
    Tendsto (fun T => chapter06PrimeContourTermPartial q F c T) atTop
      (𝓝 (-chapter06PrimePowerTerm F q)) := by
  have hN : 0 < (chapter06PrimeIdealNorm q.1 : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt (chapter03_prime_ideal_norm_gt_one q.1))
  have hlog : 0 < Real.log (chapter06PrimeIdealNorm q.1 : ℝ) := by
    exact Real.log_pos (by
      exact_mod_cast chapter03_prime_ideal_norm_gt_one q.1)
  have hy : 0 < (q.2.1 : ℝ) * Real.log (chapter06PrimeIdealNorm q.1 : ℝ) := by
    exact mul_pos (by exact_mod_cast q.2.2) hlog
  let N : ℝ := chapter06PrimeIdealNorm q.1
  let y : ℝ := (q.2.1 : ℝ) * Real.log N
  let r : ℝ := -((q.2.1 : ℝ) / 2)
  let a : ℝ := Real.log N * Real.rpow N r
  have hterm (t : ℝ) :
      chapter06ZetaLogDerivativeTerm q (chapter06VerticalLinePoint c t) =
        (a : ℂ) * Complex.exp (-((y : ℂ) *
          (chapter06VerticalLinePoint c t - (1 / 2 : ℂ)))) := by
    have hN' : 0 < N := by simpa [N] using hN
    have hN0' : (N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN'.ne'
    have hN0 : (chapter06PrimeIdealNorm q.1 : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hN.ne'
    have hlog0 :
        Complex.log (chapter06PrimeIdealNorm q.1 : ℂ) =
          (Real.log (chapter06PrimeIdealNorm q.1 : ℝ) : ℂ) :=
      (Complex.ofReal_log hN.le).symm
    have hlogN : Complex.log (N : ℂ) = (Real.log N : ℂ) :=
      (Complex.ofReal_log hN'.le).symm
    unfold chapter06ZetaLogDerivativeTerm
    dsimp [a, N, y, r]
    push_cast
    rw [Complex.cpow_def_of_ne_zero hN0,
      Complex.ofReal_cpow hN.le,
      Complex.cpow_def_of_ne_zero hN0']
    simp only [hlog0, hlogN]
    conv_rhs => rw [mul_assoc]
    rw [← Complex.exp_add]
    congr 2
    push_cast
    simp only [hlog0]
    ring
  have hcontour (T : ℝ) :
      chapter06PrimeContourTermPartial q F c T =
        -(a : ℂ) * chapter06LaplaceInversePartial F c y T := by
    unfold chapter06PrimeContourTermPartial chapter06LaplaceInversePartial
    have hinterval :
        (∫ t in (-T)..T,
          chapter06Phi F (chapter06VerticalLinePoint c t) *
            (-chapter06ZetaLogDerivativeTerm q
              (chapter06VerticalLinePoint c t)) * Complex.I) =
          -(a : ℂ) *
            (∫ t in (-T)..T,
              chapter06Phi F (chapter06VerticalLinePoint c t) *
                Complex.exp (-((y : ℂ) *
                  (chapter06VerticalLinePoint c t - (1 / 2 : ℂ)))) *
                  Complex.I) := by
      calc
        (∫ t in (-T)..T,
            chapter06Phi F (chapter06VerticalLinePoint c t) *
              (-chapter06ZetaLogDerivativeTerm q
                (chapter06VerticalLinePoint c t)) * Complex.I) =
            ∫ t in (-T)..T,
              (-(a : ℂ)) *
                (chapter06Phi F (chapter06VerticalLinePoint c t) *
                  Complex.exp (-((y : ℂ) *
                    (chapter06VerticalLinePoint c t - (1 / 2 : ℂ)))) *
                    Complex.I) := by
          apply intervalIntegral.integral_congr
          intro t _
          dsimp
          rw [hterm t]
          ring
        _ = _ := by rw [intervalIntegral.integral_const_mul]
    rw [hinterval]
    ring
  have hlim :
      Tendsto (fun T : ℝ => -(a : ℂ) *
        chapter06LaplaceInversePartial F c y T) atTop
        (𝓝 (-(a : ℂ) * (F y : ℂ))) := by
    exact tendsto_const_nhds.mul
      (chapter06_bilateral_laplace_inversion hF hc hy)
  have hlim' :
      Tendsto (fun T => chapter06PrimeContourTermPartial q F c T) atTop
        (𝓝 (-(a : ℂ) * (F y : ℂ))) := by
    apply hlim.congr'
    filter_upwards with T
    exact (hcontour T).symm
  have hvalue :
      -(a : ℂ) * (F y : ℂ) = (-(chapter06PrimePowerTerm F q) : ℂ) := by
    simp [a, y, N, r, chapter06PrimePowerTerm]
  rw [hvalue] at hlim'
  exact hlim'

noncomputable def chapter06ZetaPrimeContourPartial
    (K : Type*) [Field K] [NumberField K]
    (F : ℝ → ℝ) (c T : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
    (∫ t in (-T)..T,
      chapter06Phi F (chapter06VerticalLinePoint c t) *
        (-chapter06ZetaLogDerivative K (chapter06VerticalLinePoint c t)) *
          Complex.I)

private theorem chapter06_smooth_compact_vertical_transform_integrable
    {F : ℝ → ℝ} (hF : Chapter06SmoothCompactSupport F) {c : ℝ} :
    Integrable (fun t : ℝ =>
      chapter06Phi F (chapter06VerticalLinePoint c t)) volume := by
  let g : ℝ → ℂ := fun x => (F x : ℂ) *
    Complex.exp (((c - 1 / 2 : ℝ) : ℂ) * (x : ℂ))
  have hFc : HasCompactSupport (fun x : ℝ => (F x : ℂ)) := by
    simpa [Function.comp_def] using
      hF.2.2.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
  have hgc : HasCompactSupport g := by
    dsimp [g]
    exact hFc.mul_right
  have hFcomp := Complex.ofRealCLM.contDiff.comp hF.2.1
  have hExp : ContDiff ℝ ∞
      (fun x : ℝ => Complex.exp (((c - 1 / 2 : ℝ) : ℂ) * (x : ℂ))) := by
    apply Complex.contDiff_exp.comp
    exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp contDiff_id)
  have hgcd : ContDiff ℝ ∞ g := by
    dsimp [g]
    simpa [Function.comp_def] using hFcomp.mul hExp
  let gs : SchwartzMap ℝ ℂ := hgc.toSchwartzMap hgcd
  have hfourieri : Integrable (𝓕 g) volume := by
    change Integrable (𝓕 (gs : ℝ → ℂ)) volume
    exact (𝓕 gs).integrable
  have hphi (ξ : ℝ) :
      chapter06Phi F (chapter06VerticalLinePoint c (-(2 * Real.pi * ξ))) =
        𝓕 g ξ := by
    rw [Real.fourier_eq']
    unfold chapter06Phi chapter05BilateralLaplaceTransform chapter05LaplaceKernel
    apply integral_congr_ae
    filter_upwards with x
    dsimp [g, chapter06VerticalLinePoint]
    calc
      (F x : ℂ) * Complex.exp
          ((↑c + ↑(-(2 * Real.pi * ξ)) * Complex.I - 1 / 2) * (x : ℂ)) =
          (F x : ℂ) *
            (Complex.exp (↑(-2 * Real.pi * (ξ * x)) * Complex.I) *
              Complex.exp ((↑(c - 1 / 2) : ℂ) * (x : ℂ))) := by
        rw [← Complex.exp_add]
        congr 1
        simp
        ring
      _ = Complex.exp (↑(-2 * Real.pi * (ξ * x)) * Complex.I) *
          ((F x : ℂ) * Complex.exp ((↑(c - 1 / 2) : ℂ) * (x : ℂ))) := by
        ring
  have hcomp : Integrable (fun t : ℝ =>
      𝓕 g ((-(1 / (2 * Real.pi))) * t)) volume := by
    apply hfourieri.comp_mul_left'
    apply neg_ne_zero.mpr
    exact one_div_ne_zero (by positivity)
  have heq : (fun t : ℝ =>
      chapter06Phi F (chapter06VerticalLinePoint c t)) =
      (fun t : ℝ => 𝓕 g ((-(1 / (2 * Real.pi))) * t)) := by
    funext t
    have harg : -(2 * Real.pi * (-t / (2 * Real.pi))) = t := by
      field_simp [Real.pi_ne_zero]
    calc
      chapter06Phi F (chapter06VerticalLinePoint c t) =
          chapter06Phi F
            (chapter06VerticalLinePoint c
              (-(2 * Real.pi * (-t / (2 * Real.pi))))) := by rw [harg]
      _ = 𝓕 g (-t / (2 * Real.pi)) := hphi (-t / (2 * Real.pi))
      _ = 𝓕 g ((-(1 / (2 * Real.pi))) * t) := by
        field_simp [Real.pi_ne_zero]
  rw [heq]
  exact hcomp

private theorem chapter06_zeta_term_norm_on_vertical_line
    (K : Type*) [Field K] [NumberField K]
    (q : Chapter06PrimePower K) {c t : ℝ} :
    ‖chapter06ZetaLogDerivativeTerm q
        (chapter06VerticalLinePoint c t)‖ =
      ‖chapter06ZetaLogDerivativeTerm q
        (chapter06VerticalLinePoint c 0)‖ := by
  have hN : 0 < (chapter06PrimeIdealNorm q.1 : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt (chapter03_prime_ideal_norm_gt_one q.1))
  unfold chapter06ZetaLogDerivativeTerm
  unfold chapter06PrimeIdealNorm
  rw [norm_mul, norm_mul,
    Complex.norm_natCast_cpow_of_pos
      (Nat.zero_lt_of_lt (chapter03_prime_ideal_norm_gt_one q.1)),
    Complex.norm_natCast_cpow_of_pos
      (Nat.zero_lt_of_lt (chapter03_prime_ideal_norm_gt_one q.1))]
  simp [chapter06VerticalLinePoint]

private theorem chapter06_zeta_term_continuous_on_vertical_line
    (K : Type*) [Field K] [NumberField K]
    (q : Chapter06PrimePower K) (c : ℝ) :
    Continuous (fun t : ℝ =>
      chapter06ZetaLogDerivativeTerm q
        (chapter06VerticalLinePoint c t)) := by
  have hN : (chapter06PrimeIdealNorm q.1 : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt
      (Nat.zero_lt_of_lt (chapter03_prime_ideal_norm_gt_one q.1)))
  unfold chapter06ZetaLogDerivativeTerm chapter06PrimeIdealNorm
  apply Continuous.mul
  · fun_prop
  · apply Continuous.const_cpow
    · have hline : Continuous (fun t : ℝ =>
          chapter06VerticalLinePoint c t) := by
        unfold chapter06VerticalLinePoint
        fun_prop
      exact (continuous_const.mul hline).neg
    · exact Or.inl hN

theorem chapter06_prime_contour_contribution
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : Chapter06SmoothCompactSupport F) {c : ℝ} (hc : 1 < c) :
    Tendsto (fun T => chapter06ZetaPrimeContourPartial K F c T) atTop
      (𝓝 (-(chapter06PrimeContribution K F) / 2)) := by sorry

noncomputable def chapter06DiscriminantContourPartial
    (K : Type*) [Field K] [NumberField K]
    (F : ℝ → ℝ) (c T : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
    (∫ t in (-T)..T,
      chapter06Phi F (chapter06VerticalLinePoint c t) *
          chapter06DiscriminantLogDerivative K * Complex.I)

private theorem chapter06_bilateral_laplace_inversion_at_zero_basic
    {F : ℝ → ℝ} (hF : Chapter06BasicallyAdmissible F) {c : ℝ} (hc : 1 < c) :
    Tendsto (fun T => chapter06LaplaceInversePartial F c 0 T) atTop
      (𝓝 (F 0 : ℂ)) := by
  let g : ℝ → ℂ := fun x => (F x : ℂ) *
    Complex.exp (((c - 1 / 2 : ℝ) : ℂ) * (x : ℂ))
  have hgc : HasCompactSupport g := by
    dsimp [g]
    exact (hF.compactSupport.comp_left (g := fun y : ℝ => (y : ℂ)) (by simp)).mul_right
  have hcontg : Continuous g := by
    have hFcast : Continuous (fun x : ℝ => (F x : ℂ)) :=
      Complex.continuous_ofReal.comp hF.continuous
    have hExp : Continuous (fun x : ℝ =>
        Complex.exp (((c - 1 / 2 : ℝ) : ℂ) * (x : ℂ))) := by
      fun_prop
    change Continuous (fun x : ℝ => (F x : ℂ) *
      Complex.exp (((c - 1 / 2 : ℝ) : ℂ) * (x : ℂ)))
    exact hFcast.mul hExp
  have hgi : Integrable g volume :=
    hcontg.integrable_of_hasCompactSupport hgc
  let R : ℝ := max |c| 1
  obtain ⟨C, hC, hbound⟩ :=
    chapter05_basically_admissible_vertical_decay hF R (by
      dsimp [R]
      positivity)
  have hcR : |c| ≤ R := by
    exact le_max_left _ _
  have hphi (ξ : ℝ) :
      chapter06Phi F (chapter06VerticalLinePoint c (-(2 * Real.pi * ξ))) =
        𝓕 g ξ := by
    rw [Real.fourier_eq']
    unfold chapter06Phi chapter05BilateralLaplaceTransform chapter05LaplaceKernel
    apply integral_congr_ae
    filter_upwards with x
    dsimp [g, chapter06VerticalLinePoint]
    calc
      (F x : ℂ) * Complex.exp
          ((↑c + ↑(-(2 * Real.pi * ξ)) * Complex.I - 1 / 2) * (x : ℂ)) =
          (F x : ℂ) *
            (Complex.exp (↑(-2 * Real.pi * (ξ * x)) * Complex.I) *
              Complex.exp ((↑(c - 1 / 2) : ℂ) * (x : ℂ))) := by
        rw [← Complex.exp_add]
        congr 1
        simp
        ring_nf
      _ = Complex.exp (↑(-2 * Real.pi * (ξ * x)) * Complex.I) *
          ((F x : ℂ) * Complex.exp ((↑(c - 1 / 2) : ℂ) * (x : ℂ))) := by
        ring
  have hbase : Integrable (fun x : ℝ =>
      (1 + ‖x‖) ^ (-2 : ℝ)) volume := by
    exact integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by norm_num)
  have hmajorReal : Integrable (fun x : ℝ =>
      C / (1 + ‖x‖) ^ 2) volume := by
    convert hbase.const_mul C using 1
    funext x
    rw [div_eq_mul_inv, Real.rpow_neg (by positivity) 2, Real.rpow_two]
  have hcontFourier : Continuous (𝓕 g) := by
    exact VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (innerSL ℝ).continuous₂ hgi
  have hfourieri : Integrable (𝓕 g) volume := by
    apply Integrable.mono' hmajorReal
    · exact hcontFourier.aestronglyMeasurable
    · filter_upwards [] with ξ
      have hline := hbound c (-2 * Real.pi * ξ) hcR
      have habs : |ξ| ≤ |-2 * Real.pi * ξ| := by
        calc
          |ξ| = 1 * |ξ| := by ring
          _ ≤ (2 * Real.pi) * |ξ| := by
            exact mul_le_mul_of_nonneg_right
              (by nlinarith [Real.pi_gt_three]) (abs_nonneg ξ)
          _ = |-2 * Real.pi * ξ| := by
            rw [abs_mul, abs_mul, abs_neg, abs_of_pos Real.pi_pos]
            norm_num
      have hden : 1 + ‖ξ‖ ≤ 1 + |-2 * Real.pi * ξ| := by
        simpa [Real.norm_eq_abs] using add_le_add_left habs 1
      calc
        ‖𝓕 g ξ‖ = ‖chapter06Phi F
            (chapter06VerticalLinePoint c (-(2 * Real.pi * ξ)))‖ := by
              rw [hphi ξ]
        _ ≤ C / (1 + |-2 * Real.pi * ξ|) ^ 2 := by
              simpa [chapter06Phi, chapter06VerticalLinePoint] using hline
        _ ≤ C / (1 + ‖ξ‖) ^ 2 := by
          have hden2 : (1 + ‖ξ‖) ^ 2 ≤
              (1 + |-2 * Real.pi * ξ|) ^ 2 := by
            gcongr
          exact div_le_div_of_nonneg_left hC (by positivity) hden2
  have hinv : 𝓕⁻ (𝓕 g) 0 = g 0 :=
    hgi.fourierInv_fourier_eq hfourieri hcontg.continuousAt
  have hfull : (∫ ξ : ℝ, 𝓕 g ξ) = g 0 := by
    simpa [Real.fourierInv_eq'] using hinv
  have hscale : Tendsto (fun T : ℝ => T / (2 * Real.pi)) atTop atTop := by
    apply (tendsto_div_const_atTop_of_pos (by positivity)).2
    exact tendsto_id
  have hinterval : Tendsto (fun T : ℝ =>
      ∫ ξ in (-T / (2 * Real.pi))..(T / (2 * Real.pi)), 𝓕 g ξ) atTop
      (𝓝 (∫ ξ : ℝ, 𝓕 g ξ)) := by
    apply intervalIntegral_tendsto_integral hfourieri
    · simpa [Function.comp_def, neg_div] using tendsto_neg_atTop_atBot.comp hscale
    · exact hscale
  have hpartial (T : ℝ) :
      chapter06LaplaceInversePartial F c 0 T =
        ∫ ξ in (-T / (2 * Real.pi))..(T / (2 * Real.pi)), 𝓕 g ξ := by
    let L : ℝ → ℂ := fun t =>
      chapter06Phi F (chapter06VerticalLinePoint c t) * Complex.I
    let p : ℝ := 2 * Real.pi
    have hp : p ≠ 0 := by
      dsimp [p]
      positivity
    have hleft : p * (-T / p) = -T := by
      field_simp [hp]
    have hright : p * (T / p) = T := by
      field_simp [hp]
    have hneg :
        (∫ t in (-T)..T, L (-t)) = ∫ t in (-T)..T, L t := by
      rw [intervalIntegral.integral_comp_neg]
      simp
    have hsub :
        p • (∫ ξ in (-T / p)..(T / p), L (-(p * ξ))) =
          ∫ t in (-T)..T, L t := by
      calc
        p • (∫ ξ in (-T / p)..(T / p), L (-(p * ξ))) =
            ∫ t in p * (-T / p)..p * (T / p), L (-t) := by
              simpa only [smul_eq_mul] using
                (intervalIntegral.smul_integral_comp_mul_left
                  (f := fun t : ℝ => L (-t))
                  (a := -T / p) (b := T / p) p)
        _ = ∫ t in (-T)..T, L (-t) := by rw [hleft, hright]
        _ = ∫ t in (-T)..T, L t := hneg
    have hL (ξ : ℝ) :
        L (-(2 * Real.pi * ξ)) = 𝓕 g ξ * Complex.I := by
      change chapter06Phi F
          (chapter06VerticalLinePoint c (-(2 * Real.pi * ξ))) * Complex.I = _
      rw [hphi ξ]
    have hJ :
        (∫ ξ in (-T / p)..(T / p), L (-(p * ξ))) =
          (∫ ξ in (-T / p)..(T / p), 𝓕 g ξ) * Complex.I := by
      calc
        (∫ ξ in (-T / p)..(T / p), L (-(p * ξ))) =
            ∫ ξ in (-T / p)..(T / p), (𝓕 g ξ) * Complex.I := by
              apply intervalIntegral.integral_congr
              intro ξ _
              simpa [p] using hL ξ
        _ = (∫ ξ in (-T / p)..(T / p), 𝓕 g ξ) * Complex.I := by
              rw [intervalIntegral.integral_mul_const]
    unfold chapter06LaplaceInversePartial
    have hzero_integral :
        (∫ t in (-T)..T,
          chapter06Phi F (chapter06VerticalLinePoint c t) *
            Complex.exp (-(((0 : ℝ) : ℂ) *
              (chapter06VerticalLinePoint c t - (1 / 2 : ℂ)))) * Complex.I) =
          ∫ t in (-T)..T, L t := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp [L]
      norm_num
    rw [hzero_integral]
    rw [← hsub, hJ]
    rw [Complex.real_smul]
    simp only [p]
    field_simp [Real.pi_ne_zero, Complex.I_ne_zero]
    push_cast
    ring
  have hmain : Tendsto (fun T : ℝ =>
      ∫ ξ in (-T / (2 * Real.pi))..(T / (2 * Real.pi)), 𝓕 g ξ) atTop
      (𝓝 (g 0)) := by
    simpa [hfull] using hinterval
  have hmain' : Tendsto (fun T => chapter06LaplaceInversePartial F c 0 T) atTop
      (𝓝 (g 0)) := by
    apply hmain.congr'
    filter_upwards with T
    exact (hpartial T).symm
  simpa [g] using hmain'

theorem chapter06_discriminant_contour_contribution
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : Chapter06BasicallyAdmissible F) {c : ℝ} (hc : 1 < c) :
    Tendsto (fun T => chapter06DiscriminantContourPartial K F c T) atTop
      (𝓝 (chapter06DiscriminantLogDerivative K)) := by
  have hzero (T : ℝ) :
      (∫ t in (-T)..T,
        chapter06Phi F (chapter06VerticalLinePoint c t) *
          Complex.exp (-(((0 : ℝ) : ℂ) *
            (chapter06VerticalLinePoint c t - (1 / 2 : ℂ)))) * Complex.I) =
        ∫ t in (-T)..T,
          chapter06Phi F (chapter06VerticalLinePoint c t) * Complex.I := by
    apply intervalIntegral.integral_congr
    intro t _
    norm_num
  have hfactor (T : ℝ) :
      (∫ t in (-T)..T,
        chapter06Phi F (chapter06VerticalLinePoint c t) *
          chapter06DiscriminantLogDerivative K * Complex.I) =
        (∫ t in (-T)..T,
          chapter06Phi F (chapter06VerticalLinePoint c t) * Complex.I) *
            chapter06DiscriminantLogDerivative K := by
    rw [← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  have hEq (T : ℝ) :
      chapter06DiscriminantContourPartial K F c T =
        chapter06DiscriminantLogDerivative K *
          chapter06LaplaceInversePartial F c 0 T := by
    unfold chapter06DiscriminantContourPartial chapter06LaplaceInversePartial
    rw [hzero T, hfactor T]
    ring
  have hlim :=
    (tendsto_const_nhds.mul
      (chapter06_bilateral_laplace_inversion_at_zero_basic hF hc) :
      Tendsto (fun T : ℝ => chapter06DiscriminantLogDerivative K *
        chapter06LaplaceInversePartial F c 0 T) atTop
        (𝓝 (chapter06DiscriminantLogDerivative K * (F 0 : ℂ))))
  have hlim' : Tendsto (fun T : ℝ =>
      chapter06DiscriminantLogDerivative K *
        chapter06LaplaceInversePartial F c 0 T) atTop
      (𝓝 (chapter06DiscriminantLogDerivative K)) := by
    simpa [hF.valueAtZero] using hlim
  apply hlim'.congr'
  filter_upwards [] with T
  exact (hEq T).symm

theorem chapter06_doubled_discriminant_contour_contribution
    (K : Type*) [Field K] [NumberField K] :
    2 * chapter06DiscriminantLogDerivative K =
      (Real.log (chapter06AbsoluteDiscriminant K) : ℂ) := by
  simp [chapter06DiscriminantLogDerivative]; ring

theorem chapter06_prime_power_term_nonzero_implies_log_bound
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hF : chapter06SupportWithin F T)
    {q : Chapter06PrimePower K}
    (hq : chapter06PrimePowerTerm F q ≠ 0) :
    (q.2.1 : ℝ) * Real.log (chapter06PrimeIdealNorm q.1 : ℝ) ≤ T := by
  have _hT : 0 ≤ T := hT
  have hlog : 0 < Real.log (chapter06PrimeIdealNorm q.1 : ℝ) := by
    exact Real.log_pos (by
      exact_mod_cast chapter03_prime_ideal_norm_gt_one q.1)
  have hFq : F ((q.2.1 : ℝ) *
      Real.log (chapter06PrimeIdealNorm q.1 : ℝ)) ≠ 0 := by
    intro hzero
    apply hq
    simp [chapter06PrimePowerTerm, hzero]
  have hmem : ((q.2.1 : ℝ) *
      Real.log (chapter06PrimeIdealNorm q.1 : ℝ)) ∈ Function.support F := hFq
  exact hF hmem |>.2

theorem chapter06_prime_power_term_nonzero_implies_norm_bound
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hF : chapter06SupportWithin F T)
    {q : Chapter06PrimePower K}
    (hq : chapter06PrimePowerTerm F q ≠ 0) :
    Real.rpow (chapter06PrimeIdealNorm q.1 : ℝ) (q.2.1 : ℝ) ≤ Real.exp T := by
  have hlog := chapter06_prime_power_term_nonzero_implies_log_bound K hT hF hq
  have hbase : 0 < (chapter06PrimeIdealNorm q.1 : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt (chapter03_prime_ideal_norm_gt_one q.1))
  calc
    Real.rpow (chapter06PrimeIdealNorm q.1 : ℝ) (q.2.1 : ℝ) =
        Real.exp (Real.log (chapter06PrimeIdealNorm q.1 : ℝ) *
          (q.2.1 : ℝ)) := Real.rpow_def_of_pos hbase _
    _ ≤ Real.exp T := Real.exp_le_exp.mpr (by
      simpa [mul_comm] using hlog)

theorem chapter06_prime_power_support_finite_of_support_within
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hF : chapter06SupportWithin F T) :
    (chapter06PrimePowerSupport (K := K) F).Finite := by
  have _hT : 0 ≤ T := hT
  let B : ℕ := Nat.ceil (Real.exp T)
  let M : ℕ := Nat.ceil (T / Real.log (2 : ℝ))
  let S : Set (Chapter06PrimeIdeal K) :=
    {P | chapter06PrimeIdealNorm P ≤ B}
  let U : Set Chapter06PositiveExponent :=
    {m | m.1 ≤ M}
  have hS : S.Finite := by
    simpa [S, B, chapter06PrimeIdealNorm, chapter03PrimeIdealNorm,
      chapter03AbsoluteIdealNorm] using
      (Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le
        (R := 𝓞 K) B)
  have hU : U.Finite := by
    simpa [U] using
      (Set.finite_le_nat M).preimage (by
        intro a _ b _ hab
        exact Subtype.ext hab)
  have hprod : (S ×ˢ U).Finite := hS.prod hU
  refine hprod.subset ?_
  intro q hq
  change q.1 ∈ S ∧ q.2 ∈ U
  have hterm : chapter06PrimePowerTerm F q ≠ 0 := hq
  have hNgt : 1 < chapter06PrimeIdealNorm q.1 :=
    chapter03_prime_ideal_norm_gt_one q.1
  have hlog : 0 < Real.log (chapter06PrimeIdealNorm q.1 : ℝ) := by
    exact Real.log_pos (by exact_mod_cast hNgt)
  have hFq : F ((q.2.1 : ℝ) *
      Real.log (chapter06PrimeIdealNorm q.1 : ℝ)) ≠ 0 := by
    intro hzero
    apply hterm
    simp [chapter06PrimePowerTerm, hzero]
  have hmem : ((q.2.1 : ℝ) *
      Real.log (chapter06PrimeIdealNorm q.1 : ℝ)) ∈ Function.support F := hFq
  have hbound : (q.2.1 : ℝ) *
      Real.log (chapter06PrimeIdealNorm q.1 : ℝ) ≤ T :=
    hF hmem |>.2
  have hone : (1 : ℝ) ≤ (q.2.1 : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr q.2.2)
  have hlog_le : Real.log (chapter06PrimeIdealNorm q.1 : ℝ) ≤ T := by
    have hmul : Real.log (chapter06PrimeIdealNorm q.1 : ℝ) ≤
        (q.2.1 : ℝ) * Real.log (chapter06PrimeIdealNorm q.1 : ℝ) := by
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right hone (le_of_lt hlog))
    exact hmul.trans hbound
  have hNreal : (chapter06PrimeIdealNorm q.1 : ℝ) ≤ Real.exp T :=
    Real.le_exp_of_log_le hlog_le
  have hNnat : chapter06PrimeIdealNorm q.1 ≤ B := by
    have hceil : Real.exp T ≤ (B : ℝ) := by
      exact Nat.le_ceil _
    exact_mod_cast hNreal.trans hceil
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hN2 : (2 : ℝ) ≤ chapter06PrimeIdealNorm q.1 := by
    have hN2nat : 2 ≤ chapter06PrimeIdealNorm q.1 := by omega
    exact_mod_cast hN2nat
  have hlog2_le : Real.log (2 : ℝ) ≤
      Real.log (chapter06PrimeIdealNorm q.1 : ℝ) :=
    Real.log_le_log (by norm_num) hN2
  have hprod_bound : (q.2.1 : ℝ) * Real.log (2 : ℝ) ≤ T := by
    exact (mul_le_mul_of_nonneg_left hlog2_le (by positivity)).trans hbound
  have hdiv : (q.2.1 : ℝ) ≤ T / Real.log (2 : ℝ) := by
    exact (le_div_iff₀ hlog2).2 hprod_bound
  have hnat : q.2.1 ≤ M := by
    have hceil : T / Real.log (2 : ℝ) ≤ (M : ℝ) := by
      exact Nat.le_ceil _
    exact_mod_cast hdiv.trans hceil
  exact ⟨hNnat, hnat⟩

theorem chapter06_prime_power_term_nonnegative
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : ∀ x, 0 ≤ F x) (q : Chapter06PrimePower K) :
    0 ≤ chapter06PrimePowerTerm F q := by
  unfold chapter06PrimePowerTerm
  have hlog : 0 ≤ Real.log (chapter06PrimeIdealNorm q.1 : ℝ) := by
    exact (Real.log_pos (by
      exact_mod_cast chapter03_prime_ideal_norm_gt_one q.1)).le
  exact mul_nonneg (mul_nonneg hlog
    (Real.rpow_nonneg (by positivity) _)) (hF _)

noncomputable def chapter06FinitePrimePowerContribution
    {K : Type*} [Field K] [NumberField K]
    (F : ℝ → ℝ) (S : Finset (Chapter06PrimePower K)) : ℝ :=
  2 * ∑ q ∈ S, chapter06PrimePowerTerm F q

theorem chapter06_finite_prime_power_contribution_nonnegative
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : ∀ x, 0 ≤ F x) (S : Finset (Chapter06PrimePower K)) :
    0 ≤ chapter06FinitePrimePowerContribution F S := by
  unfold chapter06FinitePrimePowerContribution
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg fun q hq =>
      chapter06_prime_power_term_nonnegative K hF q)

theorem chapter06_finite_prime_power_contribution_mono
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : ∀ x, 0 ≤ F x) {S T : Finset (Chapter06PrimePower K)}
    (hST : S ⊆ T) :
    chapter06FinitePrimePowerContribution F S ≤
      chapter06FinitePrimePowerContribution F T := by
  unfold chapter06FinitePrimePowerContribution
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum_of_subset_of_nonneg hST fun q hq hqS =>
      chapter06_prime_power_term_nonnegative K hF q) (by positivity)

theorem chapter06_prime_contribution_nonnegative
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : Chapter06BasicallyAdmissible F)
    (hFnonnegative : ∀ x, 0 ≤ F x) :
    0 ≤ chapter06PrimeContribution K F := by
  have _hF : Chapter06BasicallyAdmissible F := hF
  unfold chapter06PrimeContribution
  exact mul_nonneg (by positivity)
    (tsum_nonneg fun q => chapter06_prime_power_term_nonnegative K hFnonnegative q)

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06
