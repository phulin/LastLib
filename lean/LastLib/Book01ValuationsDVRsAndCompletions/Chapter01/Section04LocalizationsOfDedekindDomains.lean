import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.FractionalIdeal.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter01

open scoped Polynomial nonZeroDivisors
open Set Function Ideal
open scoped BigOperators

noncomputable section

/-! # Chapter 1: Measuring vanishing

This file is a statement-generation pass for Chapter 1 of *Valuations, DVRs, and
Completions*.  The declarations below follow Sections 1.1--1.5 in order. -/

/-! # Book 1, Chapter 1, Section 1.4: Localizations of Dedekind Domains
-/

/-! ## 1.4 Localizations of Dedekind domains -/

section DedekindLocalizations

open scoped nonZeroDivisors

variable {A K : Type*} [CommRing A] [Field K] [Algebra A K]
  [IsFractionRing A K] [IsDedekindDomain A]

/-- The nonzero prime corresponding to a height-one point of a Dedekind domain. -/
def chapterPrimeOfHeightOne (P : IsDedekindDomain.HeightOneSpectrum A) : Ideal A :=
  P.asIdeal

/-- The exponent of a height-one prime in the principal fractional ideal `(x)`. -/
def dedekindExponent (P : IsDedekindDomain.HeightOneSpectrum A) (x : K) : ℤ :=
  FractionalIdeal.count K P (FractionalIdeal.spanSingleton A⁰ x)

/-- The principal fractional ideal used in the factorization statements. -/
def chapterPrincipalFractionalIdeal (x : K) : FractionalIdeal A⁰ K :=
  FractionalIdeal.spanSingleton A⁰ x

theorem dedekindExponent_valuation
    (P : IsDedekindDomain.HeightOneSpectrum A) {x : K} (hx : x ≠ 0) :
    P.valuation K x = WithZero.exp (-(dedekindExponent P x)) := by
  obtain ⟨a, d, hd, hxrep⟩ := IsFractionRing.div_surjective A x
  have ha : a ≠ 0 := by
    intro ha
    apply hx
    rw [← hxrep, ha, map_zero, zero_div]
  have hI : FractionalIdeal.spanSingleton A⁰ x ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx
  have hfac : FractionalIdeal.spanSingleton A⁰ x =
      FractionalIdeal.spanSingleton A⁰ (algebraMap A K d)⁻¹ *
        (Ideal.span ({a} : Set A) : FractionalIdeal A⁰ K) := by
    rw [← hxrep, FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
    apply congr_arg
    rw [div_eq_mul_inv, mul_comm]
  have hcount := FractionalIdeal.count_well_defined K P hI hfac
  have hcount' : dedekindExponent P x =
      (multiplicity P.asIdeal (Ideal.span ({a} : Set A)) : ℤ) -
        multiplicity P.asIdeal (Ideal.span ({d} : Set A)) := by
    unfold dedekindExponent
    rw [hcount, Ideal.count_associates_factors_eq
      (Submodule.span_singleton_eq_bot.mp.mt ha) P.isPrime P.ne_bot,
      IsDedekindDomain.HeightOneSpectrum.count_normalizedFactors_eq_multiplicity
        (Submodule.span_singleton_eq_bot.mp.mt ha) P,
      Ideal.count_associates_factors_eq
        (Submodule.span_singleton_eq_bot.mp.mt
          (mem_nonZeroDivisors_iff_ne_zero.mp hd)) P.isPrime P.ne_bot,
      IsDedekindDomain.HeightOneSpectrum.count_normalizedFactors_eq_multiplicity
        (Submodule.span_singleton_eq_bot.mp.mt
          (mem_nonZeroDivisors_iff_ne_zero.mp hd)) P]
  have hmk : IsLocalization.mk' K a ⟨d, hd⟩ =
      algebraMap A K a / algebraMap A K d :=
    IsFractionRing.mk'_eq_div ⟨d, hd⟩
  conv_lhs => rw [← hxrep, ← hmk]
  rw [P.valuation_of_mk',
    P.intValuation_eq_exp_neg_multiplicity ha,
    P.intValuation_eq_exp_neg_multiplicity
      (mem_nonZeroDivisors_iff_ne_zero.mp hd), ← WithZero.exp_sub]
  congr 1
  rw [hcount']
  ring

/-- A nonzero principal fractional ideal factors over the height-one primes. -/
theorem dedekind_principal_fractional_ideal_factorization {x : K} (hx : x ≠ 0) :
    ∏ᶠ P : IsDedekindDomain.HeightOneSpectrum A,
      (P.asIdeal : FractionalIdeal A⁰ K) ^ dedekindExponent P x =
        chapterPrincipalFractionalIdeal x := by
  unfold chapterPrincipalFractionalIdeal dedekindExponent
  apply FractionalIdeal.finprod_heightOneSpectrum_factorization'
  exact FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx

/-- Only finitely many height-one exponents of a nonzero principal fractional
ideal are nonzero. -/
theorem dedekindExponent_finite_support {x : K} (_hx : x ≠ 0) :
    {P : IsDedekindDomain.HeightOneSpectrum A | dedekindExponent P x ≠ 0}.Finite := by
  have h := FractionalIdeal.finite_factors
    (FractionalIdeal.spanSingleton A⁰ x)
  have h' : ∀ᶠ P : IsDedekindDomain.HeightOneSpectrum A in Filter.cofinite,
      dedekindExponent P x = 0 := by
    simpa [dedekindExponent] using h
  exact (Filter.eventually_cofinite.1 h')

/-- The exponent is additive under multiplication of nonzero elements. -/
theorem dedekindExponent_mul (P : IsDedekindDomain.HeightOneSpectrum A)
    {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    dedekindExponent P (x * y) = dedekindExponent P x + dedekindExponent P y := by
  unfold dedekindExponent
  rw [show FractionalIdeal.spanSingleton A⁰ (x * y) =
      FractionalIdeal.spanSingleton A⁰ x * FractionalIdeal.spanSingleton A⁰ y by
        rw [← FractionalIdeal.spanSingleton_mul_spanSingleton]]
  exact FractionalIdeal.count_mul K P
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy)

/-- The exponent of an element that is a unit of the Dedekind domain is zero. -/
theorem dedekindExponent_unit (P : IsDedekindDomain.HeightOneSpectrum A)
    (u : Aˣ) :
    dedekindExponent P (algebraMap A K (u : A)) = 0 := by
  unfold dedekindExponent
  rw [show FractionalIdeal.spanSingleton A⁰ (algebraMap A K (u : A)) =
      FractionalIdeal.spanSingleton A⁰ (1 : K) by
        apply FractionalIdeal.spanSingleton_eq_spanSingleton.mpr
        refine ⟨u⁻¹, ?_⟩
        rw [Units.smul_def, Algebra.smul_def]
        simp,
    FractionalIdeal.spanSingleton_one]
  exact FractionalIdeal.count_one K P

/-- The Dedekind exponent satisfies the valuation inequality under addition. -/
theorem dedekindExponent_add (P : IsDedekindDomain.HeightOneSpectrum A)
    {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (dedekindExponent P x) (dedekindExponent P y) ≤
      dedekindExponent P (x + y) := by
  have hval := map_add_le_max (P.valuation K) x y
  rw [dedekindExponent_valuation P hx, dedekindExponent_valuation P hy,
    dedekindExponent_valuation P hxy] at hval
  rcases le_total (dedekindExponent P x) (dedekindExponent P y) with hxy' | hyx'
  · have hmax : max (WithZero.exp (-(dedekindExponent P x)))
        (WithZero.exp (-(dedekindExponent P y))) =
        WithZero.exp (-(dedekindExponent P x)) := by
      rw [max_eq_left]
      simp only [WithZero.exp_le_exp]
      omega
    rw [hmax] at hval
    rw [WithZero.exp_le_exp] at hval
    omega
  · have hmax : max (WithZero.exp (-(dedekindExponent P x)))
        (WithZero.exp (-(dedekindExponent P y))) =
        WithZero.exp (-(dedekindExponent P y)) := by
      rw [max_eq_right]
      simp only [WithZero.exp_le_exp]
      omega
    rw [hmax] at hval
    rw [WithZero.exp_le_exp] at hval
    omega

/-- Unequal Dedekind exponents cannot cancel in a sum. -/
theorem dedekindExponent_add_of_ne (P : IsDedekindDomain.HeightOneSpectrum A)
    {x y : K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hne : dedekindExponent P x ≠ dedekindExponent P y) :
    dedekindExponent P (x + y) = min (dedekindExponent P x) (dedekindExponent P y) := by
  have hxy : x + y ≠ 0 := by
    intro hxy
    apply hne
    have hyneg : y = -x := eq_neg_of_add_eq_zero_right hxy
    have hnegone : dedekindExponent P (-1 : K) = 0 := by
      simpa using (dedekindExponent_unit (A := A) (K := K) P (-1 : Aˣ))
    rw [hyneg]
    calc
      dedekindExponent P x =
          dedekindExponent P ((-1 : K) * x) := by
        rw [dedekindExponent_mul P (by simp) hx, hnegone, zero_add]
      _ = dedekindExponent P (-x) := by
        rw [show -x = (-1 : K) * x by ring,
          dedekindExponent_mul P (by simp) hx, hnegone, zero_add]
  have hneval : P.valuation K x ≠ P.valuation K y := by
    intro hval
    rw [dedekindExponent_valuation P hx, dedekindExponent_valuation P hy] at hval
    have : dedekindExponent P x = dedekindExponent P y := by
      rw [WithZero.exp_inj] at hval
      omega
    exact hne this
  have hval := Valuation.map_add_of_distinct_val (P.valuation K) hneval
  rw [dedekindExponent_valuation P hx, dedekindExponent_valuation P hy,
    dedekindExponent_valuation P hxy] at hval
  rcases le_total (dedekindExponent P x) (dedekindExponent P y) with hxy' | hyx'
  · rw [max_eq_left] at hval
    · rw [WithZero.exp_inj] at hval
      omega
    · simp only [WithZero.exp_le_exp]
      omega
  · rw [max_eq_right] at hval
    · rw [WithZero.exp_inj] at hval
      omega
    · simp only [WithZero.exp_le_exp]
      omega

/-- The exponent of an inverse is the negative exponent. -/
theorem dedekindExponent_inv (P : IsDedekindDomain.HeightOneSpectrum A)
    {x : K} (_hx : x ≠ 0) :
    dedekindExponent P x⁻¹ = -dedekindExponent P x := by
  unfold dedekindExponent
  rw [show FractionalIdeal.spanSingleton A⁰ x⁻¹ =
      (FractionalIdeal.spanSingleton A⁰ x)⁻¹ by
        rw [← FractionalIdeal.spanSingleton_inv]]
  exact FractionalIdeal.count_inv K P _

/-- Every element of the fraction field can be tested in a localization at a
prime using a denominator outside that prime. -/
def IsInChapterLocalizationAtPrime (P : Ideal A) [P.IsPrime] (x : K) : Prop :=
  ∃ a : A, ∃ s : P.primeCompl,
    x * algebraMap A K (s : A) = algebraMap A K a

/-- A denominator outside `P` contributes no `P`-factor. -/
theorem dedekindExponent_primeCompl_eq_zero
    (P : IsDedekindDomain.HeightOneSpectrum A) (s : P.asIdeal.primeCompl) :
    dedekindExponent P (algebraMap A K (s : A)) = 0 := by
  have hs : algebraMap A K (s : A) ≠ 0 :=
    map_ne_zero_of_mem_nonZeroDivisors _ (IsFractionRing.injective A K)
      (P.asIdeal.primeCompl_le_nonZeroDivisors s.2)
  have hval := dedekindExponent_valuation P hs
  rw [P.valuation_of_algebraMap,
    P.intValuation_eq_one_iff.mpr s.2, ← WithZero.exp_zero] at hval
  rw [WithZero.exp_inj] at hval
  omega

/-- Membership in the localization at `P` is exactly nonnegative `P`-adic
exponent. -/
theorem localization_membership_iff_dedekindExponent_nonnegative
    (P : IsDedekindDomain.HeightOneSpectrum A) (x : K) :
    IsInChapterLocalizationAtPrime P.asIdeal x ↔ 0 ≤ dedekindExponent P x := by
  by_cases hx : x = 0
  · subst x
    constructor
    · intro _
      simp [dedekindExponent, FractionalIdeal.spanSingleton_zero,
        FractionalIdeal.count_zero]
    · intro _
      exact ⟨0, ⟨1, P.asIdeal.primeCompl.one_mem⟩, by simp⟩
  constructor
  · rintro ⟨a, s, hxs⟩
    have hval : P.valuation K x ≤ 1 := by
      calc
        P.valuation K x = P.valuation K x * 1 := by simp
        _ = P.valuation K (x * algebraMap A K (s : A)) := by
          rw [map_mul, P.valuation_of_algebraMap,
            P.intValuation_eq_one_iff.mpr s.2]
        _ = P.valuation K (algebraMap A K a) := by rw [hxs]
        _ ≤ 1 := P.valuation_le_one a
    have hval' := dedekindExponent_valuation P hx
    rw [hval', ← WithZero.exp_zero, WithZero.exp_le_exp] at hval
    omega
  · intro h
    exact P.exists_primeCompl_mul_eq_of_integer x (by
      have hval := dedekindExponent_valuation P hx
      rw [hval, ← WithZero.exp_zero, WithZero.exp_le_exp]
      omega)

/-- A general nonzero prime of a Dedekind domain gives a height-one spectrum
point. -/
def chapterHeightOneSpectrumOfPrime (P : Ideal A) [P.IsPrime] (hP : P ≠ ⊥) :
    IsDedekindDomain.HeightOneSpectrum A :=
  ⟨P, inferInstance, hP⟩

/-- The localization at a nonzero prime is a discrete valuation ring. -/
theorem dedekind_localization_at_nonzero_prime_isDVR (P : Ideal A) [P.IsPrime]
    (hP : P ≠ ⊥) :
    IsDiscreteValuationRing (Localization P.primeCompl) := by
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
    A hP (Localization P.primeCompl)

end DedekindLocalizations

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter01
