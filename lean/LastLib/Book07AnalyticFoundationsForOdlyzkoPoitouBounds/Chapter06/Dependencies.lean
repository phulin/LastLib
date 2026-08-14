import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Topology.Algebra.Support
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03.Dependencies
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03.Section03LogarithmicDerivatives
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04.Section05DiscriminantAndAnalyticConductor
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.Core
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.Section02BasicAdmissibleClass
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.Section04PositivityRegimes

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06

noncomputable section

open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04
open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05
open MeasureTheory Set Filter NumberField
open scoped BigOperators ContDiff Topology

/-!
Shared interfaces for Chapter 6.  Chapter 4 supplies the global completed
Dedekind zeta function, its Xi function, and the basic zero and conductor
interfaces.  This chapter retains an explicit package for the additional
contour-height data needed by the explicit formula, while the book-facing
definitions below use the canonical earlier-chapter and Mathlib objects.
-/

/-! ### Number-field and completion conventions -/

abbrev chapter06Degree (K : Type*) [Field K] [NumberField K] : ℕ :=
  Module.finrank ℚ K

noncomputable abbrev chapter06RealPlaces
    (K : Type*) [Field K] [NumberField K] : ℕ :=
  NumberField.InfinitePlace.nrRealPlaces K

noncomputable abbrev chapter06ComplexPlaces
    (K : Type*) [Field K] [NumberField K] : ℕ :=
  NumberField.InfinitePlace.nrComplexPlaces K

def chapter06Signature (K : Type*) [Field K] [NumberField K] : ℕ × ℕ :=
  (chapter06RealPlaces K, chapter06ComplexPlaces K)

noncomputable def chapter06AbsoluteDiscriminant
    (K : Type*) [Field K] [NumberField K] : ℝ :=
  |(NumberField.discr K : ℝ)|

noncomputable def chapter06RootDiscriminant
    (K : Type*) [Field K] [NumberField K] : ℝ :=
  chapter06AbsoluteDiscriminant K ^ (chapter06Degree K : ℝ)⁻¹

def chapter06GammaReal (s : ℂ) : ℂ :=
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04.chapter04GammaReal s

def chapter06GammaComplex (s : ℂ) : ℂ :=
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04.chapter04GammaComplex s

noncomputable def chapter06EulerCompletedDedekindZeta
    (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04.chapter04EulerCompletedDedekindZeta K s

noncomputable def chapter06CompletedDedekindZeta
    (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04.chapter04CompletedDedekindZeta K s

def chapter06Xi
    (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04.chapter04Xi K s

def chapter06LogDerivative (f : ℂ → ℂ) (s : ℂ) : ℂ :=
  deriv f s / f s

def chapter06AnalyticConductor
    (K : Type*) [Field K] [NumberField K] (t : ℝ) : ℝ :=
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04.chapter04AnalyticConductor K t

def chapter06VerticalLinePoint (σ t : ℝ) : ℂ :=
  (σ : ℂ) + (t : ℂ) * Complex.I

/-! ### Test functions and the three archimedean integrals -/

abbrev Chapter06BasicallyAdmissible (F : ℝ → ℝ) : Prop :=
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.Chapter05BasicallyAdmissible F

abbrev Chapter06GRHAdmissible (F : ℝ → ℝ) : Prop :=
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.Chapter05GRHAdmissible F

abbrev Chapter06UnconditionallyAdmissible (F : ℝ → ℝ) : Prop :=
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.Chapter05UnconditionallyAdmissible F

def chapter06Phi (F : ℝ → ℝ) (s : ℂ) : ℂ :=
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05BilateralLaplaceTransform F s

def Chapter06SmoothCompactSupport (F : ℝ → ℝ) : Prop :=
  Function.Even F ∧ (ContDiff ℝ ∞ F) ∧ HasCompactSupport F

def chapter06A (F : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ in Ioi 0, F x * Real.cosh (x / 2)

def chapter06B (F : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ in Ioi 0, (1 - F x) / (2 * Real.sinh (x / 2))

def chapter06C (F : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ in Ioi 0, (1 - F x) / (2 * Real.cosh (x / 2))

def chapter06GammaConstant : ℝ :=
  Real.eulerMascheroniConstant + Real.log (8 * Real.pi)

def chapter06RealPlaceContribution (F : ℝ → ℝ) : ℝ :=
  chapter06GammaConstant + Real.pi / 2 - chapter06B F - chapter06C F

def chapter06ComplexPlaceContribution (F : ℝ → ℝ) : ℝ :=
  2 * chapter06GammaConstant - 2 * chapter06B F

/-! ### Prime powers -/

abbrev Chapter06PrimeIdeal (K : Type*) [Field K] [NumberField K] :=
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03.Chapter03PrimeIdeal K

abbrev Chapter06PositiveExponent := {m : ℕ // 0 < m}

abbrev Chapter06PrimePower (K : Type*) [Field K] [NumberField K] :=
  Chapter06PrimeIdeal K × Chapter06PositiveExponent

def chapter06PrimeIdealNorm
    {K : Type*} [Field K] [NumberField K] (P : Chapter06PrimeIdeal K) : ℕ :=
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03.chapter03PrimeIdealNorm P

def chapter06PrimePowerTerm
    {K : Type*} [Field K] [NumberField K]
    (F : ℝ → ℝ) (q : Chapter06PrimePower K) : ℝ :=
  Real.log (chapter06PrimeIdealNorm q.1 : ℝ) *
    Real.rpow (chapter06PrimeIdealNorm q.1 : ℝ) (-((q.2.1 : ℝ) / 2)) *
    F ((q.2.1 : ℝ) * Real.log (chapter06PrimeIdealNorm q.1 : ℝ))

def chapter06PrimePowerSupport
    {K : Type*} [Field K] [NumberField K] (F : ℝ → ℝ) : Set (Chapter06PrimePower K) :=
  {q | chapter06PrimePowerTerm F q ≠ 0}

def chapter06SupportWithin (F : ℝ → ℝ) (T : ℝ) : Prop :=
  Function.support F ⊆ Set.Icc (-T) T

noncomputable def chapter06PrimeContribution
    (K : Type*) [Field K] [NumberField K] (F : ℝ → ℝ) : ℝ :=
  2 * ∑' q : Chapter06PrimePower K, chapter06PrimePowerTerm F q

/-! ### The zero spectrum and the contour package -/

def chapter06NontrivialZero
    (K : Type*) [Field K] [NumberField K] (ρ : ℂ) : Prop :=
  chapter06Xi K ρ = 0

def chapter06ZeroPartner (ρ : ℂ) : ℂ :=
  1 - star ρ

theorem chapter06_zero_partner_involutive (ρ : ℂ) :
    chapter06ZeroPartner (chapter06ZeroPartner ρ) = ρ := by
  simp [chapter06ZeroPartner]

def chapter06SimplePoleWithResidue
    (f : ℂ → ℂ) (ρ r : ℂ) : Prop :=
  ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧
    ∀ᶠ s in 𝓝[≠] ρ, f s = r / (s - ρ) + g s

noncomputable def chapter06FiniteMultiplicitySum
    (multiplicity : ℂ → ℕ) (S : Set ℂ) (hS : S.Finite) : ℕ :=
  ∑ ρ ∈ hS.toFinset, multiplicity ρ

structure Chapter06ZeroSpectrum
    (K : Type*) [Field K] [NumberField K] where
  support : Set ℂ
  multiplicity : ℂ → ℕ
  support_iff_multiplicity_ne_zero :
    ∀ ρ, ρ ∈ support ↔ multiplicity ρ ≠ 0
  support_iff_nontrivial_zero :
    ∀ ρ, ρ ∈ support ↔ chapter06NontrivialZero K ρ
  critical_strip :
    ∀ {ρ}, ρ ∈ support → 0 ≤ ρ.re ∧ ρ.re ≤ 1
  functional_equation_partner :
    ∀ {ρ}, ρ ∈ support ↔ 1 - ρ ∈ support
  conjugation_partner :
    ∀ {ρ}, ρ ∈ support ↔ star ρ ∈ support
  multiplicity_functional_equation_partner :
    ∀ ρ, multiplicity (1 - ρ) = multiplicity ρ
  multiplicity_conjugation_partner :
    ∀ ρ, multiplicity (star ρ) = multiplicity ρ
  log_derivative_simple_pole :
    ∀ {ρ}, ρ ∈ support →
      chapter06SimplePoleWithResidue
        (chapter06LogDerivative (chapter06Xi K)) ρ (multiplicity ρ : ℂ)
  locally_finite :
    ∀ T : ℝ, Set.Finite {ρ : ℂ | ρ ∈ support ∧ |ρ.im| < T}
  unit_band_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
      ((chapter06FiniteMultiplicitySum multiplicity
        {ρ : ℂ | ρ ∈ support ∧ T < |ρ.im| ∧ |ρ.im| ≤ T + 1}
        ((locally_finite (T + 2)).subset (by
          intro ρ hρ
          exact ⟨hρ.1,
            lt_of_le_of_lt hρ.2.2 (by linarith)⟩))) : ℝ) ≤
        C * (Real.log (chapter06AbsoluteDiscriminant K) +
          (chapter06Degree K : ℝ) * Real.log (T + 3))

def chapter06CanonicalZeroSupport
    (K : Type*) [Field K] [NumberField K] : Set ℂ :=
  {ρ | chapter06NontrivialZero K ρ}

noncomputable def chapter06CanonicalZeroMultiplicity
    (K : Type*) [Field K] [NumberField K] : ℂ → ℕ :=
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04.chapter04ZeroMultiplicity K

noncomputable def chapter06CanonicalZeroSpectrum
    (K : Type*) [Field K] [NumberField K] : Chapter06ZeroSpectrum K :=
  { support := chapter06CanonicalZeroSupport K
    multiplicity := chapter06CanonicalZeroMultiplicity K
    support_iff_multiplicity_ne_zero := by
      intro ρ
      change chapter04NontrivialZero K ρ ↔
        chapter04ZeroMultiplicity K ρ ≠ 0
      rw [← chapter04_zero_multiplicity_pos_iff (K := K), Nat.pos_iff_ne_zero]
    support_iff_nontrivial_zero := by
      intro ρ
      rfl
    critical_strip := by
      intro ρ hρ
      change chapter06Xi K ρ = 0 at hρ
      simpa [chapter06Xi, chapter06NontrivialZero, chapter04CriticalStrip] using
        (chapter04_nontrivial_zero_in_critical_strip K hρ)
    functional_equation_partner := by
      intro ρ
      unfold chapter06CanonicalZeroSupport chapter06NontrivialZero
      change chapter04Xi K ρ = 0 ↔ chapter04Xi K (1 - ρ) = 0
      constructor
      · intro h
        rw [chapter04_xi_functional_equation K ρ] at h
        exact h
      · intro h
        rw [chapter04_xi_functional_equation K ρ]
        exact h
    conjugation_partner := by
      intro ρ
      exact chapter04_nontrivial_zero_conjugate_iff K ρ
    multiplicity_functional_equation_partner := by
      intro ρ
      change chapter04ZeroMultiplicity K (1 - ρ) =
        chapter04ZeroMultiplicity K ρ
      simpa [chapter04ZeroPartner] using
        (chapter04_zero_multiplicity_partner K (star ρ)).trans
          (chapter04_zero_multiplicity_conjugate K ρ)
    multiplicity_conjugation_partner := by
      intro ρ
      change chapter04ZeroMultiplicity K (star ρ) =
        chapter04ZeroMultiplicity K ρ
      exact chapter04_zero_multiplicity_conjugate K ρ
    log_derivative_simple_pole := by
      intro ρ hρ
      have hxi : AnalyticAt ℂ (chapter04Xi K) ρ :=
        (chapter04_xi_entire K) ρ (Set.mem_univ _)
      have hnot_top : analyticOrderAt (chapter04Xi K) ρ ≠ ⊤ := by
        obtain ⟨z, hz⟩ : ∃ z : ℂ, chapter04Xi K z ≠ 0 := by
          by_contra h'
          push Not at h'
          exact (chapter04_xi_not_identically_zero K) h'
        have hzorder : analyticOrderAt (chapter04Xi K) z ≠ ⊤ := by
          have hzzero : analyticOrderAt (chapter04Xi K) z = 0 :=
            (chapter04_xi_entire K z (Set.mem_univ _)).analyticOrderAt_eq_zero.mpr hz
          rw [hzzero]
          exact ENat.zero_ne_top
        exact (chapter04_xi_entire K).analyticOrderAt_ne_top_of_isPreconnected
          isPreconnected_univ (Set.mem_univ _) (Set.mem_univ _) hzorder
      obtain ⟨g, hg, hg0, hfactor⟩ := hxi.analyticOrderAt_ne_top.mp hnot_top
      have hfactor' : chapter04Xi K =ᶠ[𝓝 ρ]
          (fun z => (z - ρ) ^ chapter04ZeroMultiplicity K ρ • g z) := by
        simpa [chapter04ZeroMultiplicity, analyticOrderNatAt] using hfactor
      refine ⟨fun z => deriv g z / g z, hg.deriv.div hg hg0, ?_⟩
      change ∀ᶠ s in 𝓝[≠] ρ,
        deriv (chapter04Xi K) s / chapter04Xi K s =
          (chapter04ZeroMultiplicity K ρ : ℂ) / (s - ρ) + deriv g s / g s
      have hlog := logDeriv_congr_nhdsNE
        (hfactor'.filter_mono nhdsWithin_le_nhds)
      have hne : ∀ᶠ s : ℂ in 𝓝[≠] ρ, s ≠ ρ := by
        exact self_mem_nhdsWithin
      filter_upwards [hlog,
        (hg.continuousAt.eventually_ne hg0).filter_mono nhdsWithin_le_nhds,
        (hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds),
        hne] with s hs hgs hgsanalytic hne
      rw [show deriv (chapter04Xi K) s / chapter04Xi K s =
        logDeriv (chapter04Xi K) s by rfl, hs]
      rw [show logDeriv (fun z => (z - ρ) ^ chapter04ZeroMultiplicity K ρ • g z) s =
        logDeriv (fun z => (z - ρ) ^ chapter04ZeroMultiplicity K ρ) s +
          logDeriv g s by
            simpa only [smul_eq_mul] using
              (logDeriv_mul
                (f := fun z : ℂ => (z - ρ) ^ chapter04ZeroMultiplicity K ρ)
                (g := g) s
                (pow_ne_zero (chapter04ZeroMultiplicity K ρ)
                  (sub_ne_zero.mpr hne)) hgs
                (by fun_prop) hgsanalytic.differentiableAt)]
      rw [logDeriv_fun_pow (f := fun z : ℂ => z - ρ) (x := s) (by fun_prop)
        (chapter04ZeroMultiplicity K ρ)]
      simp [logDeriv_apply, div_eq_mul_inv]
    locally_finite := by
      intro T
      apply (chapter04_zero_band_finite K T).subset
      intro ρ hρ
      change chapter04NontrivialZero K ρ ∧ |ρ.im| ≤ T
      exact ⟨hρ.1, hρ.2.le⟩
    unit_band_bound := by
      obtain ⟨C, hC, hbound⟩ := chapter04_zero_counting_unit_band_bound
      refine ⟨C, hC, ?_⟩
      intro T hT
      let A : Set ℂ := chapter04ZeroBand K (T + 1)
      let B : Set ℂ := chapter04ZeroBand K T
      let D : Set ℂ := {ρ : ℂ |
        chapter04NontrivialZero K ρ ∧ T < |ρ.im| ∧ |ρ.im| ≤ T + 1}
      have hA : A.Finite := by
        exact chapter04_zero_band_finite K (T + 1)
      have hB : B.Finite := by
        exact chapter04_zero_band_finite K T
      have hBA : B ⊆ A := by
        intro ρ hρ
        change chapter04NontrivialZero K ρ ∧ |ρ.im| ≤ T at hρ
        change chapter04NontrivialZero K ρ ∧ |ρ.im| ≤ T + 1
        exact ⟨hρ.1, by linarith⟩
      have hD : D.Finite := by
        apply (chapter04_zero_band_finite K (T + 1)).subset
        intro ρ hρ
        change chapter04NontrivialZero K ρ ∧ |ρ.im| ≤ T + 1
        exact ⟨hρ.1, hρ.2.2⟩
      have hD_eq : D = A \ B := by
        ext ρ
        change (chapter04NontrivialZero K ρ ∧ T < |ρ.im| ∧
            |ρ.im| ≤ T + 1) ↔
          ((chapter04NontrivialZero K ρ ∧ |ρ.im| ≤ T + 1) ∧
            ¬ (chapter04NontrivialZero K ρ ∧ |ρ.im| ≤ T))
        constructor
        · rintro ⟨hz, hlow, hupp⟩
          refine ⟨⟨hz, hupp⟩, ?_⟩
          rintro ⟨_, hle⟩
          exact (not_lt_of_ge hle) hlow
        · rintro ⟨⟨hz, hupp⟩, hnot⟩
          refine ⟨hz, ?_, hupp⟩
          exact lt_of_not_ge (fun hle => hnot ⟨hz, hle⟩)
      have hsumD :
          hD.toFinset.sum (fun ρ => chapter04ZeroMultiplicity K ρ) =
            hA.toFinset.sum (fun ρ => chapter04ZeroMultiplicity K ρ) -
              hB.toFinset.sum (fun ρ => chapter04ZeroMultiplicity K ρ) := by
        have hsubAB : hB.toFinset ⊆ hA.toFinset :=
          (Set.Finite.toFinset_subset_toFinset).2 hBA
        have hDfin : hD.toFinset = hA.toFinset \ hB.toFinset := by
          ext ρ
          simpa only [hD.mem_toFinset, hA.mem_toFinset, hB.mem_toFinset,
            Finset.mem_sdiff, Set.mem_sdiff] using Set.ext_iff.mp hD_eq ρ
        rw [hDfin]
        have hsumAdd :
            hA.toFinset.sum (fun ρ => chapter04ZeroMultiplicity K ρ) =
              (hA.toFinset \ hB.toFinset).sum
                  (fun ρ => chapter04ZeroMultiplicity K ρ) +
                hB.toFinset.sum (fun ρ => chapter04ZeroMultiplicity K ρ) := by
          rw [Finset.sum_sdiff hsubAB]
        omega
      have hSD :
          {ρ : ℂ | ρ ∈ chapter06CanonicalZeroSupport K ∧
            T < |ρ.im| ∧ |ρ.im| ≤ T + 1} = D := by
        ext ρ
        simp [chapter06CanonicalZeroSupport, chapter06NontrivialZero,
          chapter06Xi, chapter04NontrivialZero, D]
      have hS :
          {ρ : ℂ | ρ ∈ chapter06CanonicalZeroSupport K ∧
            T < |ρ.im| ∧ |ρ.im| ≤ T + 1}.Finite := by
        rw [hSD]
        exact hD
      have hfinset : hS.toFinset = hD.toFinset :=
        Set.Finite.toFinset_inj.mpr hSD
      have hcount :
          ((chapter06FiniteMultiplicitySum
            (chapter06CanonicalZeroMultiplicity K)
            {ρ : ℂ | ρ ∈ chapter06CanonicalZeroSupport K ∧
              T < |ρ.im| ∧ |ρ.im| ≤ T + 1} hS) : ℝ) =
            ((chapter04ZeroCounting K (T + 1) -
              chapter04ZeroCounting K T : ℕ) : ℝ) := by
        unfold chapter06FiniteMultiplicitySum
        rw [hfinset]
        simp only [chapter06CanonicalZeroMultiplicity]
        rw [hsumD]
        rfl
      change ((chapter06FiniteMultiplicitySum
        (chapter06CanonicalZeroMultiplicity K)
        {ρ : ℂ | ρ ∈ chapter06CanonicalZeroSupport K ∧
          T < |ρ.im| ∧ |ρ.im| ≤ T + 1} hS) : ℝ) ≤ _
      rw [hcount]
      exact hbound T hT K
    }

/-
Chapter 4 supplies the completed-zeta zero facts.  The height field here
records the order-one estimate and the inverse-polynomial choice of contour
heights used in §6.2.  It is deliberately an input interface for that
remaining contour data, not an axiom or a conclusion engineered from the
explicit formula.
-/
structure Chapter06ContourHeightSequence
    (K : Type*) [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) (c : ℝ) where
  height : ℕ → ℝ
  tendsToInfinity : Tendsto height atTop atTop
  positive : ∀ j, 0 < height j
  separationExponent : ℕ
  separationExponent_ge_two : 2 ≤ separationExponent
  separationConstant : ℝ
  separationConstant_pos : 0 < separationConstant
  avoids_zero_ordinates :
    ∀ (j : ℕ) (ρ : ℂ), ρ ∈ Z.support →
      separationConstant /
          Real.rpow (height j + 3) (separationExponent : ℝ) ≤
        |height j - ρ.im|
  logDerivativeBound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (σ : ℝ),
      1 - c ≤ σ → σ ≤ c →
      ‖chapter06LogDerivative (chapter06Xi K)
          (chapter06VerticalLinePoint σ (height j))‖ ≤
        C * (height j + 3) ^ separationExponent *
            (Real.log (chapter06AnalyticConductor K (height j))) ^ 2 ∧
      ‖chapter06LogDerivative (chapter06Xi K)
          (chapter06VerticalLinePoint σ (-height j))‖ ≤
        C * (height j + 3) ^ separationExponent *
            (Real.log (chapter06AnalyticConductor K (height j))) ^ 2

structure Chapter06ZetaAnalyticPackage
    (K : Type*) [Field K] [NumberField K] where
  xi_entire : AnalyticOnNhd ℂ (chapter06Xi K) Set.univ
  functional_equation : ∀ s : ℂ, chapter06Xi K s = chapter06Xi K (1 - s)
  conjugation_symmetry : ∀ s : ℂ,
    chapter06Xi K (star s) = star (chapter06Xi K s)
  zeros : Chapter06ZeroSpectrum K
  contour_heights : ∀ c : ℝ, 1 < c →
    Chapter06ContourHeightSequence K zeros c

/-!
Chapter 4 supplies the canonical completed-zeta, zero, and growth data.  The
remaining contour-height construction is the analytic input proved in this
chapter, so expose the resulting package as a nonempty interface rather than
making the book's explicit formula permanently conditional on a caller-built
duplicate package.
-/
theorem chapter06_zeta_analytic_package_nonempty
    (K : Type*) [Field K] [NumberField K] :
    Nonempty (Chapter06ZetaAnalyticPackage K) := by
  sorry

noncomputable def chapter06CanonicalZetaAnalyticPackage
    (K : Type*) [Field K] [NumberField K] :
  Chapter06ZetaAnalyticPackage K :=
  { xi_entire := by
      change AnalyticOnNhd ℂ (chapter04Xi K) Set.univ
      exact chapter04_xi_entire K
    functional_equation := by
      intro s
      exact chapter04_xi_functional_equation K s
    conjugation_symmetry := by
      intro s
      exact chapter04_xi_conjugation_symmetry K s
    zeros := chapter06CanonicalZeroSpectrum K
    contour_heights := by sorry }

@[simp] theorem chapter06_canonical_zeta_analytic_package_zeros
    (K : Type*) [Field K] [NumberField K] :
    (chapter06CanonicalZetaAnalyticPackage K).zeros =
      chapter06CanonicalZeroSpectrum K := by
  rfl

theorem chapter06_canonical_zero_support_spec
    (K : Type*) [Field K] [NumberField K] (ρ : ℂ) :
    ρ ∈ chapter06CanonicalZeroSupport K ↔
      chapter06NontrivialZero K ρ := by
  rfl

theorem chapter06_canonical_zero_functional_equation_partner
    (K : Type*) [Field K] [NumberField K] (ρ : ℂ) :
    ρ ∈ chapter06CanonicalZeroSupport K ↔
      1 - ρ ∈ chapter06CanonicalZeroSupport K := by
  exact (chapter06CanonicalZeroSpectrum K).functional_equation_partner

theorem chapter06_canonical_zero_conjugation_partner
    (K : Type*) [Field K] [NumberField K] (ρ : ℂ) :
    ρ ∈ chapter06CanonicalZeroSupport K ↔
      star ρ ∈ chapter06CanonicalZeroSupport K := by
  exact (chapter06CanonicalZeroSpectrum K).conjugation_partner

theorem chapter06_canonical_zero_partner_support
    (K : Type*) [Field K] [NumberField K] (ρ : ℂ) :
    ρ ∈ chapter06CanonicalZeroSupport K ↔
      chapter06ZeroPartner ρ ∈ chapter06CanonicalZeroSupport K := by
  change ρ ∈ (chapter06CanonicalZeroSpectrum K).support ↔
    1 - star ρ ∈ (chapter06CanonicalZeroSpectrum K).support
  constructor
  · intro hρ
    exact (chapter06CanonicalZeroSpectrum K).functional_equation_partner.mp
      ((chapter06CanonicalZeroSpectrum K).conjugation_partner.mp hρ)
  · intro hρ
    exact (chapter06CanonicalZeroSpectrum K).conjugation_partner.mpr
      ((chapter06CanonicalZeroSpectrum K).functional_equation_partner.mpr hρ)

theorem chapter06_canonical_zero_multiplicity_functional_equation_partner
    (K : Type*) [Field K] [NumberField K] (ρ : ℂ) :
    chapter06CanonicalZeroMultiplicity K (1 - ρ) =
      chapter06CanonicalZeroMultiplicity K ρ := by
  change chapter04ZeroMultiplicity K (1 - ρ) =
    chapter04ZeroMultiplicity K ρ
  simpa [chapter04ZeroPartner] using
    (chapter04_zero_multiplicity_partner K (star ρ)).trans
      (chapter04_zero_multiplicity_conjugate K ρ)

theorem chapter06_canonical_zero_multiplicity_conjugation_partner
    (K : Type*) [Field K] [NumberField K] (ρ : ℂ) :
    chapter06CanonicalZeroMultiplicity K (star ρ) =
      chapter06CanonicalZeroMultiplicity K ρ := by
  exact chapter04_zero_multiplicity_conjugate K ρ

theorem chapter06_canonical_zero_multiplicity_partner
    (K : Type*) [Field K] [NumberField K] (ρ : ℂ) :
    chapter06CanonicalZeroMultiplicity K (chapter06ZeroPartner ρ) =
      chapter06CanonicalZeroMultiplicity K ρ := by
  exact chapter04_zero_multiplicity_partner K ρ

theorem chapter06_canonical_zero_locally_finite_norm
    (K : Type*) [Field K] [NumberField K] (R : ℝ) :
    Set.Finite {ρ : ℂ |
      ρ ∈ chapter06CanonicalZeroSupport K ∧ ‖ρ‖ ≤ R} := by
  apply (chapter04_zero_band_finite K R).subset
  intro ρ hρ
  change chapter04NontrivialZero K ρ ∧ |ρ.im| ≤ R
  exact ⟨hρ.1, (Complex.abs_im_le_norm ρ).trans hρ.2⟩

def chapter06ZeroCountingFunction
    {K : Type*} [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) (T : ℝ) : ℕ :=
  chapter06FiniteMultiplicitySum Z.multiplicity
    {ρ : ℂ | ρ ∈ Z.support ∧ |ρ.im| ≤ T}
    ((Z.locally_finite (T + 1)).subset (by
      intro ρ hρ
      exact ⟨hρ.1, lt_of_le_of_lt hρ.2 (by linarith)⟩))

def chapter06ZeroBandCount
    {K : Type*} [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) (T : ℝ) : ℕ :=
  chapter06FiniteMultiplicitySum Z.multiplicity
    {ρ : ℂ |
      ρ ∈ Z.support ∧ T < |ρ.im| ∧ |ρ.im| ≤ T + 1}
    ((Z.locally_finite (T + 2)).subset (by
      intro ρ hρ
      exact ⟨hρ.1,
        lt_of_le_of_lt hρ.2.2 (by linarith)⟩))

/-! ### Symmetric zero sums -/

def chapter06ZeroWindow
    {K : Type*} [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) (T : ℝ) : Set ℂ :=
  {ρ | ρ ∈ Z.support ∧ |ρ.im| < T}

noncomputable def chapter06ZeroWindowFinset
    {K : Type*} [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) (T : ℝ) : Finset ℂ :=
  (Z.locally_finite T).toFinset

def chapter06ZeroSummand
    {K : Type*} [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) (F : ℝ → ℝ) (ρ : ℂ) : ℂ :=
  (Z.multiplicity ρ : ℂ) * chapter06Phi F ρ

theorem chapter06_zero_summand_summable_of_basic
    (K : Type*) [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) {F : ℝ → ℝ}
    (hF : Chapter06BasicallyAdmissible F) :
    Summable (fun ρ : ℂ => chapter06ZeroSummand Z F ρ) := by
  classical
  let S : ℕ → Set ℂ := fun n => {ρ | (ρ ∉ Z.support ∧ n = 0) ∨
    (ρ ∈ Z.support ∧ Nat.ceil |ρ.im| = n)}
  have hpartition : ∀ ρ : ℂ, ∃! n : ℕ, ρ ∈ S n := by
    intro ρ
    by_cases hρ : ρ ∈ Z.support
    · refine ⟨Nat.ceil |ρ.im|, ?_, ?_⟩
      · exact Or.inr ⟨hρ, rfl⟩
      · intro n hn
        change (ρ ∉ Z.support ∧ n = 0) ∨
          (ρ ∈ Z.support ∧ Nat.ceil |ρ.im| = n) at hn
        rcases hn with ⟨hnρ, hn0⟩ | hn
        · exact False.elim (hnρ hρ)
        · exact hn.2.symm
    · refine ⟨0, ?_, ?_⟩
      · exact Or.inl ⟨hρ, rfl⟩
      · intro n hn
        change (ρ ∉ Z.support ∧ n = 0) ∨
          (ρ ∈ Z.support ∧ Nat.ceil |ρ.im| = n) at hn
        rcases hn with ⟨_, hn0⟩ | hn
        · exact hn0
        · exact False.elim (hρ hn.1)
  let f : ℂ → ℂ := fun ρ => chapter06ZeroSummand Z F ρ
  let b : ℂ → ℝ := fun ρ => ‖f ρ‖
  have hfiniteS : ∀ n : ℕ, 0 < n → (S n).Finite := by
    intro n hn
    apply (Z.locally_finite ((n : ℝ) + 1)).subset
    intro ρ hρ
    change (ρ ∉ Z.support ∧ n = 0) ∨
      (ρ ∈ Z.support ∧ Nat.ceil |ρ.im| = n) at hρ
    rcases hρ with ⟨_, hn0⟩ | hρ
    · omega
    · refine ⟨hρ.1, ?_⟩
      have hupper : |ρ.im| ≤ (n : ℝ) := (Nat.ceil_le).mp hρ.2.le
      linarith
  have hfinite_component : ∀ n : ℕ, Summable (fun ρ : S n => b ρ) := by
    intro n
    by_cases hn : n = 0
    · subst n
      let P : Set (S 0) :=
        Subtype.val ⁻¹' {ρ : ℂ | ρ ∈ Z.support ∧ |ρ.im| < 1}
      have hP : P.Finite := by
        have hP' : Set.Finite
            ((Subtype.val : S 0 → ℂ) ⁻¹'
              {ρ : ℂ | ρ ∈ Z.support ∧ |ρ.im| < 1}) :=
          (Z.locally_finite (1 : ℝ)).preimage
            (fun x _ y _ hxy => Subtype.ext hxy)
        simpa [P] using hP'
      exact summable_of_ne_finset_zero (s := hP.toFinset) (by
        intro ρ hρ
        have hmzero : Z.multiplicity (ρ : ℂ) = 0 := by
          apply Nat.eq_zero_of_not_pos
          intro hmpos
          have hsupport : (ρ : ℂ) ∈ Z.support :=
            (Z.support_iff_multiplicity_ne_zero (ρ : ℂ)).mpr
              (Nat.ne_of_gt hmpos)
          have hS := ρ.property
          change ((ρ : ℂ) ∉ Z.support ∧ 0 = 0) ∨
            ((ρ : ℂ) ∈ Z.support ∧ Nat.ceil |(ρ : ℂ).im| = 0) at hS
          rcases hS with ⟨hnot, _⟩ | hS
          · exact hnot hsupport
          · have hheight : |(ρ : ℂ).im| ≤ (0 : ℝ) := by
              simpa using (Nat.ceil_le).mp hS.2.le
            apply hρ
            exact hP.mem_toFinset.mpr ⟨hsupport, by linarith⟩
        simp [b, f, chapter06ZeroSummand, hmzero])
    · let hFintype : Fintype (S n) :=
        (hfiniteS n (Nat.pos_of_ne_zero hn)).fintype
      exact summable_of_ne_finset_zero (s := @Finset.univ (S n) hFintype)
        (fun ρ hρ => False.elim (hρ (by simp)))
  have htsum_finite : ∀ (T : Set ℂ) (hT : T.Finite),
      (∑' ρ : T, b ρ) = hT.toFinset.sum b := by
    intro T hT
    rw [tsum_subtype]
    have hsum : hT.toFinset.sum (T.indicator b) = hT.toFinset.sum b := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      rw [Set.indicator_of_mem]
      exact hT.mem_toFinset.mp hρ
    rw [← hsum]
    exact (hasSum_sum_of_ne_finset_zero (f := T.indicator b)
      (s := hT.toFinset) (by
        intro ρ hρ
        have hmem : ρ ∉ T := by
          intro hmem
          exact hρ (hT.mem_toFinset.mpr hmem)
        simp [Set.indicator, hmem])).tsum_eq
  obtain ⟨Cdec, hCdec, hdecay⟩ :=
    chapter05_basically_admissible_vertical_decay hF 1 (by norm_num)
  have hrepr : ∀ ρ : ℂ, ρ = (ρ.re : ℂ) + (ρ.im : ℂ) * Complex.I := by
    intro ρ
    apply Complex.ext <;> simp
  have hnorm : ∀ ρ : ℂ, b ρ =
      (Z.multiplicity ρ : ℝ) * ‖chapter06Phi F ρ‖ := by
    intro ρ
    simp [b, f, chapter06ZeroSummand]
  have hterm : ∀ (n : ℕ), 0 < n → ∀ ρ : ℂ,
      ρ ∈ Z.support → (n : ℝ) - 1 < |ρ.im| → |ρ.im| ≤ (n : ℝ) →
      b ρ ≤ (Z.multiplicity ρ : ℝ) * (Cdec / (n : ℝ) ^ 2) := by
    intro n hn ρ hρsupport hlow hupper
    have hstrip := Z.critical_strip hρsupport
    have hre : |ρ.re| ≤ (1 : ℝ) := by
      rw [abs_of_nonneg hstrip.1]
      exact hstrip.2
    have htrans := hdecay ρ.re ρ.im hre
    have htrans' : ‖chapter06Phi F ρ‖ ≤
        Cdec / (1 + |ρ.im|) ^ 2 := by
      calc
        ‖chapter06Phi F ρ‖ =
            ‖chapter06Phi F ((ρ.re : ℂ) + (ρ.im : ℂ) * Complex.I)‖ := by
          exact congrArg norm
            (congrArg (chapter06Phi F) (hrepr ρ))
        _ ≤ Cdec / (1 + |ρ.im|) ^ 2 := htrans
    have hden : (n : ℝ) ^ 2 ≤ (1 + |ρ.im|) ^ 2 := by
      nlinarith [abs_nonneg ρ.im, hlow]
    have hdiv : Cdec / (1 + |ρ.im|) ^ 2 ≤ Cdec / (n : ℝ) ^ 2 := by
      by_cases hCdecpos : 0 < Cdec
      · apply (div_le_div_iff_of_pos_left hCdecpos (by positivity) (by positivity)).2
        exact hden
      · have hCdec0 : Cdec = 0 :=
          le_antisymm (le_of_not_gt hCdecpos) hCdec
        simp [hCdec0]
    rw [hnorm]
    have hfinal : ‖chapter06Phi F ρ‖ ≤ Cdec / (n : ℝ) ^ 2 :=
      htrans'.trans hdiv
    exact mul_le_mul_of_nonneg_left hfinal (by positivity)
  obtain ⟨Ccount, hCcount, hcount⟩ := Z.unit_band_bound
  have hcountdiff : ∀ n : ℕ, 0 < n →
      (chapter06ZeroBandCount Z ((n : ℝ) - 1) : ℝ) ≤
        Ccount * (Real.log (chapter06AbsoluteDiscriminant K) +
          (chapter06Degree K : ℝ) * Real.log ((n : ℝ) + 2)) := by
    intro n hn
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hraw := hcount ((n : ℝ) - 1) (by linarith)
    simpa only [chapter06ZeroBandCount,
      show (n : ℝ) - 1 + 3 = (n : ℝ) + 2 by ring] using hraw
  have hshell_le : ∀ n : ℕ, 0 < n →
      (∑' ρ : S n, b ρ) ≤
        (Cdec / (n : ℝ) ^ 2) * (chapter06ZeroBandCount Z ((n : ℝ) - 1) : ℝ) := by
    intro n hn
    let D : Set ℂ := {ρ | ρ ∈ Z.support ∧
      (n : ℝ) - 1 < |ρ.im| ∧ |ρ.im| ≤ (n : ℝ) - 1 + 1}
    have hD : D.Finite := by
      apply (Z.locally_finite ((n : ℝ) + 1)).subset
      intro ρ hρ
      change ρ ∈ Z.support ∧ |ρ.im| < (n : ℝ) + 1
      exact ⟨hρ.1, by linarith [hρ.2.2]⟩
    have hsub : S n ⊆ D := by
      intro ρ hρ
      change (ρ ∉ Z.support ∧ n = 0) ∨
        (ρ ∈ Z.support ∧ Nat.ceil |ρ.im| = n) at hρ
      rcases hρ with ⟨_, hn0⟩ | hρ
      · omega
      · have hupper : |ρ.im| ≤ (n : ℝ) := (Nat.ceil_le).mp hρ.2.le
        have hceil_lower : n - 1 < Nat.ceil |ρ.im| := by
          rw [hρ.2]
          omega
        have hlow0 : ((n - 1 : ℕ) : ℝ) < |ρ.im| :=
          (Nat.lt_ceil).mp hceil_lower
        have hn1 : 1 ≤ n := hn
        have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
          rw [Nat.cast_sub hn1]
          norm_num
        exact ⟨hρ.1, by simpa [hcast] using hlow0, by linarith [hupper]⟩
    have hsubfin : (hfiniteS n hn).toFinset ⊆ hD.toFinset :=
      (Set.Finite.toFinset_subset_toFinset).2 hsub
    have hsubsum : (hfiniteS n hn).toFinset.sum b ≤ hD.toFinset.sum b :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubfin
        (fun _ _ _ => norm_nonneg _)
    have hDcount :
        (chapter06ZeroBandCount Z ((n : ℝ) - 1) : ℝ) =
          (hD.toFinset.sum (fun ρ => Z.multiplicity ρ) : ℝ) := by
      unfold chapter06ZeroBandCount
      change ((chapter06FiniteMultiplicitySum Z.multiplicity D _ : ℕ) : ℝ) = _
      norm_cast
    rw [htsum_finite (S n) (hfiniteS n hn)]
    calc
      (hfiniteS n hn).toFinset.sum b ≤ hD.toFinset.sum b := hsubsum
      _ ≤ hD.toFinset.sum (fun ρ =>
          (Z.multiplicity ρ : ℝ) * (Cdec / (n : ℝ) ^ 2)) := by
        apply Finset.sum_le_sum
        intro ρ hρ
        have hρD := hD.mem_toFinset.mp hρ
        exact hterm n hn ρ hρD.1 hρD.2.1 (by linarith [hρD.2.2])
      _ = (Cdec / (n : ℝ) ^ 2) *
          hD.toFinset.sum (fun ρ => (Z.multiplicity ρ : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ρ hρ
        ring
      _ = (Cdec / (n : ℝ) ^ 2) *
          (chapter06ZeroBandCount Z ((n : ℝ) - 1) : ℝ) := by
        rw [hDcount]
  have hconst : ∀ n : ℕ, 0 < n →
      1 / (n : ℝ) ^ 2 ≤ 4 / ((n : ℝ) + 1) ^ 2 := by
    intro n hn
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [show (1 : ℝ) ≤ n by exact_mod_cast hn]
  have hsqrt : ∀ n : ℕ, 0 < n →
      ((n : ℝ) + 2) ^ (1 / 2 : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
    intro n hn
    have hbase : (n : ℝ) + 2 ≤ 4 * (n : ℝ) := by
      have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    calc
      ((n : ℝ) + 2) ^ (1 / 2 : ℝ) ≤ (4 * (n : ℝ)) ^ (1 / 2 : ℝ) := by
        apply Real.rpow_le_rpow (by positivity) hbase
        norm_num
      _ = 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) (by positivity)]
        norm_num
  have hsqrt2 : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
    rw [← Real.sqrt_eq_rpow]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hp2 : (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 4 := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num)]
    norm_num
    nlinarith [hsqrt2]
  have hratio : ∀ n : ℕ, 0 < n →
      (n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ 2 ≤
        4 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ) := by
    intro n hn
    have hnreal : (0 : ℝ) < n := by positivity
    have hbase : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by
      have hnone : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hz : ((n : ℝ) + 1) ^ (3 / 2 : ℝ) ≤
        4 * (n : ℝ) ^ (3 / 2 : ℝ) := by
      calc
        ((n : ℝ) + 1) ^ (3 / 2 : ℝ) ≤
            (2 * (n : ℝ)) ^ (3 / 2 : ℝ) := by
          apply Real.rpow_le_rpow (by positivity) hbase
          norm_num
        _ = (2 : ℝ) ^ (3 / 2 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) := by
          rw [Real.mul_rpow (by norm_num) (by positivity)]
        _ ≤ 4 * (n : ℝ) ^ (3 / 2 : ℝ) := by
          gcongr
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have hprod : (n : ℝ) ^ (1 / 2 : ℝ) *
          ((n : ℝ) + 1) ^ (3 / 2 : ℝ) ≤ 4 * (n : ℝ) ^ 2 := by
      calc
        _ ≤ (n : ℝ) ^ (1 / 2 : ℝ) *
            (4 * (n : ℝ) ^ (3 / 2 : ℝ)) := by
          gcongr
        _ = 4 * ((n : ℝ) ^ (1 / 2 : ℝ) *
            (n : ℝ) ^ (3 / 2 : ℝ)) := by ring
        _ = 4 * (n : ℝ) ^ 2 := by
          rw [← Real.rpow_add hnreal]
          norm_num
    exact hprod
  have hlog : ∀ n : ℕ,
      Real.log ((n : ℝ) + 2) ≤ 2 * ((n : ℝ) + 2) ^ (1 / 2 : ℝ) := by
    intro n
    have h := Real.log_le_rpow_div (show 0 ≤ (n : ℝ) + 2 by positivity)
      (show (0 : ℝ) < 1 / 2 by norm_num)
    convert h using 1
    norm_num
    ring
  let v : ℕ → ℝ := fun n => ∑' ρ : S n, b ρ
  have hA0 : 0 ≤ v 0 := by
    dsimp [v]
    exact tsum_nonneg (fun ρ => norm_nonneg (f (ρ : ℂ)))
  let A : ℝ := v 0 + 4 * Cdec * Ccount *
    |Real.log (chapter06AbsoluteDiscriminant K)|
  let B : ℝ := 16 * Cdec * Ccount * (chapter06Degree K : ℝ)
  let q : ℕ → ℝ := fun n =>
    A / ((n : ℝ) + 1) ^ 2 + B / ((n : ℝ) + 1) ^ (3 / 2 : ℝ)
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hq1 : Summable (fun n : ℕ =>
      (1 : ℝ) / ((n : ℝ) + 1) ^ 2) := by
    have h := (Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num)
    convert h using 1
    funext n
    have hn : 0 ≤ (n : ℝ) + 1 := by positivity
    rw [abs_of_nonneg hn]
    norm_num [Real.rpow_natCast]
  have hq2 : Summable (fun n : ℕ =>
      (1 : ℝ) / ((n : ℝ) + 1) ^ (3 / 2 : ℝ)) := by
    have h := (Real.summable_one_div_nat_add_rpow 1 (3 / 2)).2 (by norm_num)
    convert h using 1
    funext n
    rw [abs_of_nonneg (by positivity)]
  have hq : Summable q := by
    dsimp [q]
    simpa [div_eq_mul_inv] using (hq1.mul_left A).add (hq2.mul_left B)
  have hvq : ∀ n : ℕ, v n ≤ q n := by
    intro n
    by_cases hn : n = 0
    · subst n
      dsimp [q, A]
      norm_num
      have htermA : 0 ≤ 4 * Cdec * Ccount *
          |Real.log (chapter06AbsoluteDiscriminant K)| := by positivity
      have htermB : 0 ≤ 16 * Cdec * Ccount *
          (chapter06Degree K : ℝ) := by positivity
      linarith
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hinner :
          Real.log (chapter06AbsoluteDiscriminant K) +
            (chapter06Degree K : ℝ) * Real.log ((n : ℝ) + 2) ≤
          |Real.log (chapter06AbsoluteDiscriminant K)| +
            (chapter06Degree K : ℝ) *
              (2 * ((n : ℝ) + 2) ^ (1 / 2 : ℝ)) := by
        gcongr
        · exact le_abs_self _
        · exact hlog n
      have hbase : v n ≤
          (Cdec / (n : ℝ) ^ 2) *
            (Ccount * (Real.log (chapter06AbsoluteDiscriminant K) +
              (chapter06Degree K : ℝ) * Real.log ((n : ℝ) + 2))) := by
        exact (hshell_le n hnpos).trans
          (mul_le_mul_of_nonneg_left (hcountdiff n hnpos) (by positivity))
      have harith :
          (Cdec / (n : ℝ) ^ 2) *
              (Ccount * (Real.log (chapter06AbsoluteDiscriminant K) +
                (chapter06Degree K : ℝ) * Real.log ((n : ℝ) + 2))) ≤
            (v 0 + 4 * Cdec * Ccount *
                |Real.log (chapter06AbsoluteDiscriminant K)|) /
                ((n : ℝ) + 1) ^ 2 +
              (16 * Cdec * Ccount * (chapter06Degree K : ℝ)) /
                ((n : ℝ) + 1) ^ (3 / 2 : ℝ) := by
        have hleft :
            (Cdec / (n : ℝ) ^ 2) *
                (Ccount * (Real.log (chapter06AbsoluteDiscriminant K) +
                  (chapter06Degree K : ℝ) * Real.log ((n : ℝ) + 2))) ≤
              (Cdec / (n : ℝ) ^ 2) *
                (Ccount * (|Real.log (chapter06AbsoluteDiscriminant K)| +
                  (chapter06Degree K : ℝ) *
                    (2 * ((n : ℝ) + 2) ^ (1 / 2 : ℝ)))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hinner hCcount) (by positivity)
        calc
          _ ≤ (Cdec / (n : ℝ) ^ 2) *
              (Ccount * (|Real.log (chapter06AbsoluteDiscriminant K)| +
                (chapter06Degree K : ℝ) *
                  (2 * ((n : ℝ) + 2) ^ (1 / 2 : ℝ)))) := hleft
          _ = (Cdec * Ccount *
                |Real.log (chapter06AbsoluteDiscriminant K)|) /
                (n : ℝ) ^ 2 +
              (2 * Cdec * Ccount * (chapter06Degree K : ℝ)) *
                (((n : ℝ) + 2) ^ (1 / 2 : ℝ) / (n : ℝ) ^ 2) := by ring
          _ ≤ (4 * Cdec * Ccount *
                |Real.log (chapter06AbsoluteDiscriminant K)|) /
                ((n : ℝ) + 1) ^ 2 +
              (2 * Cdec * Ccount * (chapter06Degree K : ℝ)) *
                (8 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ)) := by
            have hfirst :
                (Cdec * Ccount *
                  |Real.log (chapter06AbsoluteDiscriminant K)|) /
                    (n : ℝ) ^ 2 ≤
                  (4 * Cdec * Ccount *
                    |Real.log (chapter06AbsoluteDiscriminant K)|) /
                    ((n : ℝ) + 1) ^ 2 := by
              have hcoef : 0 ≤ Cdec * Ccount *
                  |Real.log (chapter06AbsoluteDiscriminant K)| := by positivity
              calc
                _ = (Cdec * Ccount *
                    |Real.log (chapter06AbsoluteDiscriminant K)|) *
                      (1 / (n : ℝ) ^ 2) := by ring
                _ ≤ (Cdec * Ccount *
                    |Real.log (chapter06AbsoluteDiscriminant K)|) *
                      (4 / ((n : ℝ) + 1) ^ 2) := by
                  exact mul_le_mul_of_nonneg_left (hconst n hnpos) hcoef
                _ = _ := by ring
            have hsqrtbound :
                ((n : ℝ) + 2) ^ (1 / 2 : ℝ) / (n : ℝ) ^ 2 ≤
                  8 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ) := by
              calc
                _ ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ 2 :=
                  div_le_div_of_nonneg_right (hsqrt n hnpos) (by positivity)
                _ = 2 * ((n : ℝ) ^ (1 / 2 : ℝ) /
                    (n : ℝ) ^ 2) := by ring
                _ ≤ 2 * (4 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ)) := by
                  exact mul_le_mul_of_nonneg_left (hratio n hnpos) (by norm_num)
                _ = 8 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ) := by ring
            have hcoef2 : 0 ≤ 2 * Cdec * Ccount *
                (chapter06Degree K : ℝ) := by positivity
            exact add_le_add hfirst
              (mul_le_mul_of_nonneg_left hsqrtbound hcoef2)
          _ ≤ (v 0 + 4 * Cdec * Ccount *
                |Real.log (chapter06AbsoluteDiscriminant K)|) /
                ((n : ℝ) + 1) ^ 2 +
              (16 * Cdec * Ccount * (chapter06Degree K : ℝ)) /
                ((n : ℝ) + 1) ^ (3 / 2 : ℝ) := by
            have hfirst :
                (4 * Cdec * Ccount *
                  |Real.log (chapter06AbsoluteDiscriminant K)|) /
                    ((n : ℝ) + 1) ^ 2 ≤
                  (v 0 + 4 * Cdec * Ccount *
                    |Real.log (chapter06AbsoluteDiscriminant K)|) /
                    ((n : ℝ) + 1) ^ 2 := by
              exact (div_le_div_of_nonneg_right
                (le_add_of_nonneg_left hA0) (by positivity))
            have hsecond :
                (2 * Cdec * Ccount * (chapter06Degree K : ℝ)) *
                    (8 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ)) =
                  (16 * Cdec * Ccount * (chapter06Degree K : ℝ)) /
                    ((n : ℝ) + 1) ^ (3 / 2 : ℝ) := by ring
            exact add_le_add hfirst (le_of_eq hsecond)
      exact hbase.trans harith
  have hv : Summable v := by
    apply Summable.of_norm_bounded hq
    intro n
    have hv_nonneg : 0 ≤ v n := by
      dsimp [v]
      exact tsum_nonneg (fun ρ => norm_nonneg (f (ρ : ℂ)))
    rw [Real.norm_eq_abs, abs_of_nonneg hv_nonneg]
    exact hvq n
  have hpart := summable_partition (f := b)
    (fun ρ => norm_nonneg (f ρ)) hpartition
  have hb : Summable b := by
    apply hpart.mpr
    refine ⟨hfinite_component, ?_⟩
    simpa [v] using hv
  have hnormsum : Summable (fun ρ : ℂ => ‖f ρ‖) := by
    simpa [b] using hb
  have hf : Summable f := hnormsum.of_norm
  simpa [f] using hf

noncomputable def chapter06SymmetricZeroSum
    {K : Type*} [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) (F : ℝ → ℝ) : ℂ :=
  ∑' ρ : ℂ, chapter06ZeroSummand Z F ρ

noncomputable def chapter06ZeroPartialSum
    {K : Type*} [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) (F : ℝ → ℝ) (T : ℝ) : ℂ :=
  ∑ ρ ∈ chapter06ZeroWindowFinset Z T, chapter06ZeroSummand Z F ρ

def chapter06ZeroContribution
    {K : Type*} [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) (F : ℝ → ℝ) : ℝ :=
  (chapter06SymmetricZeroSum Z F).re

def chapter06GRH {K : Type*} [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) : Prop :=
  ∀ ρ, ρ ∈ Z.support → ρ.re = 1 / 2

theorem chapter06_grh_zero_representation
    {K : Type*} [Field K] [NumberField K]
    {Z : Chapter06ZeroSpectrum K} (hGRH : chapter06GRH Z)
    {ρ : ℂ} (hρ : ρ ∈ Z.support) :
    ∃ γ : ℝ, ρ = (1 / 2 : ℂ) + Complex.I * (γ : ℂ) := by
  refine ⟨ρ.im, ?_⟩
  apply Complex.ext
  · simpa using hGRH ρ hρ
  · simp

theorem chapter06_canonical_zero_summand_eq
    (K : Type*) [Field K] [NumberField K] (F : ℝ → ℝ) (ρ : ℂ) :
    chapter06ZeroSummand (chapter06CanonicalZeroSpectrum K) F ρ =
      (chapter06CanonicalZeroMultiplicity K ρ : ℂ) *
        LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05BilateralLaplaceTransform F ρ := by
  rfl

theorem chapter06_canonical_zero_sum_eq_chapter05
    (K : Type*) [Field K] [NumberField K] (F : ℝ → ℝ) :
    chapter06SymmetricZeroSum (chapter06CanonicalZeroSpectrum K) F =
      LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05SymmetricZeroSum K F := by
  rfl

theorem chapter06_canonical_unconditional_zero_pair_nonnegative
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : Chapter06UnconditionallyAdmissible F) {ρ : ℂ}
    (hρ : ρ ∈ (chapter06CanonicalZeroSpectrum K).support) :
    0 ≤
      (chapter06ZeroSummand (chapter06CanonicalZeroSpectrum K) F ρ +
        chapter06ZeroSummand (chapter06CanonicalZeroSpectrum K) F
          (chapter06ZeroPartner ρ)).re := by
  have hstrip : 0 ≤ ρ.re ∧ ρ.re ≤ 1 :=
    (chapter06CanonicalZeroSpectrum K).critical_strip hρ
  have hpair :=
    chapter05_unconditionally_admissible_strip_paired_nonnegative hF
      ρ.re ρ.im hstrip.1 hstrip.2
  have hρrepr : ρ = (ρ.re : ℂ) + (ρ.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have hpartnerrepr : chapter06ZeroPartner ρ =
      ((1 - ρ.re : ℝ) : ℂ) + (ρ.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [chapter06ZeroPartner]
  have hm := chapter06_canonical_zero_multiplicity_partner K ρ
  have hphiρ : chapter05BilateralLaplaceTransform F ρ =
      chapter05BilateralLaplaceTransform F
        ((ρ.re : ℂ) + (ρ.im : ℂ) * Complex.I) := by
    rw [hρrepr]
    simp
  have hphipartner : chapter05BilateralLaplaceTransform F
        (chapter06ZeroPartner ρ) =
      chapter05BilateralLaplaceTransform F
        (((1 - ρ.re : ℝ) : ℂ) + (ρ.im : ℂ) * Complex.I) := by
    rw [hpartnerrepr]
  have hsum :
      chapter06ZeroSummand (chapter06CanonicalZeroSpectrum K) F ρ +
          chapter06ZeroSummand (chapter06CanonicalZeroSpectrum K) F
            (chapter06ZeroPartner ρ) =
        (chapter06CanonicalZeroMultiplicity K ρ : ℂ) *
          chapter05PairedLaplaceTransform F ρ.re ρ.im := by
    rw [chapter06_canonical_zero_summand_eq K F ρ,
      chapter06_canonical_zero_summand_eq K F (chapter06ZeroPartner ρ), hm,
      hphiρ, hphipartner]
    simp [chapter05PairedLaplaceTransform]
    ring
  rw [hsum]
  simpa [Complex.mul_re] using
    (mul_nonneg (show 0 ≤ (chapter06CanonicalZeroMultiplicity K ρ : ℝ) by
      positivity) hpair.2)

theorem chapter06_canonical_grh_zero_summand_nonnegative
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : Chapter06GRHAdmissible F)
    (hGRH : chapter06GRH (chapter06CanonicalZeroSpectrum K)) {ρ : ℂ}
    (hρ : ρ ∈ (chapter06CanonicalZeroSpectrum K).support) :
    0 ≤
      (chapter06ZeroSummand (chapter06CanonicalZeroSpectrum K) F ρ).re := by
  obtain ⟨γ, hγ⟩ := chapter06_grh_zero_representation hGRH hρ
  have hγ' : ρ = (1 / 2 : ℂ) + (γ : ℂ) * Complex.I := by
    calc
      ρ = (1 / 2 : ℂ) + Complex.I * (γ : ℂ) := hγ
      _ = (1 / 2 : ℂ) + (γ : ℂ) * Complex.I := by ring
  have hcentral :=
    chapter05_grh_admissible_central_line_nonnegative hF γ
  have hmγ : chapter06CanonicalZeroMultiplicity K
      ((1 / 2 : ℂ) + (γ : ℂ) * Complex.I) =
    chapter06CanonicalZeroMultiplicity K ρ := by
    rw [← hγ']
  rw [chapter06_canonical_zero_summand_eq K F ρ, hγ']
  rw [hmγ]
  simpa [Complex.mul_re] using
    (mul_nonneg (show 0 ≤ (chapter06CanonicalZeroMultiplicity K ρ : ℝ) by
      positivity) hcentral.2)

theorem chapter06_canonical_unconditional_zero_contribution_nonnegative
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : Chapter06UnconditionallyAdmissible F) :
    0 ≤ chapter06ZeroContribution (chapter06CanonicalZeroSpectrum K) F := by
  let f : ℂ → ℂ := fun ρ =>
    chapter06ZeroSummand (chapter06CanonicalZeroSpectrum K) F ρ
  let e : ℂ ≃ ℂ :=
    { toFun := chapter06ZeroPartner
      invFun := chapter06ZeroPartner
      left_inv := chapter06_zero_partner_involutive
      right_inv := chapter06_zero_partner_involutive }
  have hs : Summable f := by
    simpa only [f, chapter06_canonical_zero_summand_eq,
      chapter06CanonicalZeroMultiplicity] using
      chapter05_symmetric_zero_sum_summable K hF.1
  have hse : Summable (fun ρ : ℂ => f (e ρ)) := by
    exact e.summable_iff.mpr hs
  have hpair : ∀ ρ : ℂ, 0 ≤ (f ρ + f (e ρ)).re := by
    intro ρ
    by_cases hρ : ρ ∈ (chapter06CanonicalZeroSpectrum K).support
    · simpa [f, e] using
        chapter06_canonical_unconditional_zero_pair_nonnegative K hF hρ
    · have hm : (chapter06CanonicalZeroSpectrum K).multiplicity ρ = 0 := by
        apply Nat.eq_zero_of_not_pos
        intro hmpos
        apply hρ
        exact ((chapter06CanonicalZeroSpectrum K).support_iff_multiplicity_ne_zero ρ).mpr
          (Nat.ne_of_gt hmpos)
      have hρe : e ρ ∉ (chapter06CanonicalZeroSpectrum K).support := by
        intro hρe
        apply hρ
        have hstar : star ρ ∈ (chapter06CanonicalZeroSpectrum K).support := by
          apply ((chapter06CanonicalZeroSpectrum K).functional_equation_partner
            (ρ := star ρ)).mpr
          simpa [e, chapter06ZeroPartner] using hρe
        exact ((chapter06CanonicalZeroSpectrum K).conjugation_partner
          (ρ := ρ)).mpr hstar
      have hme : (chapter06CanonicalZeroSpectrum K).multiplicity (e ρ) = 0 := by
        apply Nat.eq_zero_of_not_pos
        intro hmpos
        apply hρe
        exact ((chapter06CanonicalZeroSpectrum K).support_iff_multiplicity_ne_zero (e ρ)).mpr
          (Nat.ne_of_gt hmpos)
      simp [f, chapter06ZeroSummand, hm, hme]
  have hsum :
      (∑' ρ : ℂ, (f ρ + f (e ρ))) =
        (∑' ρ : ℂ, f ρ) + (∑' ρ : ℂ, f (e ρ)) :=
    hs.tsum_add hse
  have hsum_e : (∑' ρ : ℂ, f (e ρ)) = ∑' ρ : ℂ, f ρ := by
    exact e.tsum_eq f
  have hpair_nonneg : 0 ≤ (∑' ρ : ℂ, (f ρ + f (e ρ))).re := by
    have hmap := Complex.reCLM.map_tsum (hs.add hse)
    have hmap' :
        (∑' ρ : ℂ, (f ρ + f (e ρ))).re =
          ∑' ρ : ℂ, (f ρ + f (e ρ)).re := by
      simpa using hmap
    rw [hmap']
    exact tsum_nonneg (fun ρ => hpair ρ)
  have htwice : 0 ≤ 2 * (∑' ρ : ℂ, f ρ).re := by
    have hsum_re :
        (∑' ρ : ℂ, (f ρ + f (e ρ))).re = 2 * (∑' ρ : ℂ, f ρ).re := by
      rw [hsum, hsum_e]
      simp [Complex.add_re]
      ring
    rw [hsum_re] at hpair_nonneg
    exact hpair_nonneg
  change 0 ≤ (∑' ρ : ℂ, f ρ).re
  linarith

theorem chapter06_canonical_grh_zero_contribution_nonnegative
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : Chapter06GRHAdmissible F)
    (hGRH : chapter06GRH (chapter06CanonicalZeroSpectrum K)) :
    0 ≤ chapter06ZeroContribution (chapter06CanonicalZeroSpectrum K) F := by
  let f : ℂ → ℂ := fun ρ =>
    chapter06ZeroSummand (chapter06CanonicalZeroSpectrum K) F ρ
  have hs : Summable f := by
    simpa only [f, chapter06_canonical_zero_summand_eq,
      chapter06CanonicalZeroMultiplicity] using
      chapter05_symmetric_zero_sum_summable K hF.basic
  have hterm : ∀ ρ : ℂ, 0 ≤ (f ρ).re := by
    intro ρ
    by_cases hρ : ρ ∈ (chapter06CanonicalZeroSpectrum K).support
    · simpa [f] using chapter06_canonical_grh_zero_summand_nonnegative K hF hGRH hρ
    · have hm : (chapter06CanonicalZeroSpectrum K).multiplicity ρ = 0 := by
        apply Nat.eq_zero_of_not_pos
        intro hmpos
        apply hρ
        exact ((chapter06CanonicalZeroSpectrum K).support_iff_multiplicity_ne_zero ρ).mpr
          (Nat.ne_of_gt hmpos)
      simp [f, chapter06ZeroSummand, hm]
  have hmap := Complex.reCLM.map_tsum hs
  have hreal :
      (∑' ρ : ℂ, f ρ).re = ∑' ρ : ℂ, (f ρ).re := by
    simpa using hmap
  change 0 ≤ (∑' ρ : ℂ, f ρ).re
  rw [hreal]
  exact tsum_nonneg (fun ρ => hterm ρ)

def chapter06ExplicitFormulaRightHandSide
    (K : Type*) [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) (F : ℝ → ℝ) : ℝ :=
  (chapter06Degree K : ℝ) * chapter06GammaConstant +
    (chapter06RealPlaces K : ℝ) * (Real.pi / 2) -
    4 * chapter06A F - (chapter06Degree K : ℝ) * chapter06B F -
    (chapter06RealPlaces K : ℝ) * chapter06C F +
    chapter06ZeroContribution Z F + chapter06PrimeContribution K F

/-! ### The contour and Laplace-inversion conventions -/

def chapter06ContourRectangle (c T : ℝ) : Set ℂ :=
  {s | 1 - c ≤ s.re ∧ s.re ≤ c ∧ |s.im| ≤ T}

def chapter06ContourIntegrand
    {K : Type*} [Field K] [NumberField K]
    (F : ℝ → ℝ) (s : ℂ) : ℂ :=
  chapter06LogDerivative (chapter06Xi K) s * chapter06Phi F s

noncomputable def chapter06RightVerticalIntegral
    {K : Type*} [Field K] [NumberField K]
    (F : ℝ → ℝ) (c T : ℝ) : ℂ :=
  ∫ t in (-T)..T,
    chapter06ContourIntegrand (K := K) F (chapter06VerticalLinePoint c t) * Complex.I

noncomputable def chapter06LeftVerticalIntegral
    {K : Type*} [Field K] [NumberField K]
    (F : ℝ → ℝ) (c T : ℝ) : ℂ :=
  ∫ t in (-T)..T,
    chapter06ContourIntegrand (K := K) F
      (chapter06VerticalLinePoint (1 - c) t) * Complex.I

noncomputable def chapter06TopHorizontalIntegral
    {K : Type*} [Field K] [NumberField K]
    (F : ℝ → ℝ) (c T : ℝ) : ℂ :=
  ∫ σ in c..(1 - c),
    chapter06ContourIntegrand (K := K) F (chapter06VerticalLinePoint σ T)

noncomputable def chapter06BottomHorizontalIntegral
    {K : Type*} [Field K] [NumberField K]
    (F : ℝ → ℝ) (c T : ℝ) : ℂ :=
  ∫ σ in (1 - c)..c,
    chapter06ContourIntegrand (K := K) F (chapter06VerticalLinePoint σ (-T))

noncomputable def chapter06HorizontalError
    {K : Type*} [Field K] [NumberField K]
    (F : ℝ → ℝ) (c T : ℝ) : ℂ :=
  -((1 / (2 * (Real.pi : ℂ) * Complex.I)) *
    (chapter06TopHorizontalIntegral (K := K) F c T +
      chapter06BottomHorizontalIntegral (K := K) F c T))

noncomputable def chapter06ContourResidueSum
    {K : Type*} [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) (F : ℝ → ℝ) (T : ℝ) : ℂ :=
  ∑ ρ ∈ chapter06ZeroWindowFinset Z T, chapter06ZeroSummand Z F ρ

noncomputable def chapter06LaplaceInversePartial
    (F : ℝ → ℝ) (c y T : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
    (∫ t in (-T)..T,
      chapter06Phi F (chapter06VerticalLinePoint c t) *
          Complex.exp (-((y : ℂ) *
            (chapter06VerticalLinePoint c t - (1 / 2 : ℂ)))) * Complex.I)

/-! ### Logarithmic derivatives and prime-power inversion -/

def chapter06ZetaLogDerivativeTerm
    {K : Type*} [Field K] [NumberField K]
    (q : Chapter06PrimePower K) (s : ℂ) : ℂ :=
  (Real.log (chapter06PrimeIdealNorm q.1 : ℝ) : ℂ) *
    (chapter06PrimeIdealNorm q.1 : ℂ) ^ (-((q.2.1 : ℂ) * s))

def chapter06ZetaLogDerivativeSeries
    (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  ∑' q : Chapter06PrimePower K, chapter06ZetaLogDerivativeTerm q s

def chapter06ZetaLogDerivative
    (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  -chapter06LogDerivative
    (LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03.chapter03DedekindZeta K) s

def chapter06PoleLogDerivative (s : ℂ) : ℂ :=
  1 / s + 1 / (s - 1)

def chapter06DiscriminantLogDerivative
    (K : Type*) [Field K] [NumberField K] : ℂ :=
  (Real.log (chapter06AbsoluteDiscriminant K) : ℂ) / 2

def chapter06RealGammaLogDerivative
    (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  (chapter06RealPlaces K : ℂ) * chapter06LogDerivative chapter06GammaReal s

def chapter06ComplexGammaLogDerivative
    (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  (chapter06ComplexPlaces K : ℂ) * chapter06LogDerivative chapter06GammaComplex s

def chapter06ApproximateIdentity (η : ℕ → ℝ → ℝ) : Prop :=
  (∀ n, Integrable (η n)) ∧
    (∀ n, HasCompactSupport (η n)) ∧
    (∃ R : ℝ, 0 ≤ R ∧ ∀ n, Function.support (η n) ⊆ Set.Icc (-R) R) ∧
    (∀ n, ContDiff ℝ ∞ (η n)) ∧
    (∀ n x, 0 ≤ η n x) ∧
    (∀ n x, η n (-x) = η n x) ∧
    (∀ n, ∫ x : ℝ, η n x = 1) ∧
    (∀ φ : ℝ → ℝ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun n => ∫ x : ℝ, η n x * φ x) atTop (𝓝 (φ 0)))

noncomputable def chapter06SmoothedConvolution
    (η : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05Convolution
    (η n) F

noncomputable def chapter06OriginCorrectionFactor
    (η : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (n : ℕ) : ℝ :=
  if chapter06SmoothedConvolution η F n 0 = 0 then 1 else
    (chapter06SmoothedConvolution η F n 0)⁻¹

noncomputable def chapter06SmoothedTestFunction
    (η : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  fun x => chapter06OriginCorrectionFactor η F n *
    chapter06SmoothedConvolution η F n x

/-! ### The source's limiting diagnostic -/

def chapter06AsymptoticExpression (α B C pole : ℝ) : ℝ :=
  chapter06GammaConstant + α * (Real.pi / 2) - pole - B - α * C

def chapter06UniversalLowerBoundExpression
    (K : Type*) [Field K] [NumberField K] (F : ℝ → ℝ) : ℝ :=
  (chapter06Degree K : ℝ) * chapter06GammaConstant +
    (chapter06RealPlaces K : ℝ) * (Real.pi / 2) -
    4 * chapter06A F - (chapter06Degree K : ℝ) * chapter06B F -
    (chapter06RealPlaces K : ℝ) * chapter06C F

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06
