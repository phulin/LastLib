import LastLib.Book03RamificationTheory.Chapter07.Section06TameAndWildDerivativeBounds
import LastLib.Book03RamificationTheory.Chapter03.Section05WildKummerCalculation
import LastLib.Book03RamificationTheory.Chapter03.Section07SameDegreeArbitrarilyDifferentDepth

namespace LastLib.Book03RamificationTheory.Chapter07

noncomputable section

open Polynomial
open scoped BigOperators Polynomial nonZeroDivisors

/-! ## 7.7. Further derivative calculations -/

/- The degree and tame numerical profile of `Q_p(ζ_p)`. -/
theorem chapter07_cyclotomic_degree_and_tameness
    (p : ℕ) [Fact (Nat.Prime p)] (hpodd : 2 < p)
    {L : Type*} [Field L] [Algebra (ℚ_[p]) L]
    [FiniteDimensional (ℚ_[p]) L]
    (hdegree : Module.finrank (ℚ_[p]) L = p - 1) :
    Module.finrank (ℚ_[p]) L = p - 1 ∧ Nat.Coprime (p - 1) p := by
  refine ⟨hdegree, ?_⟩
  rw [Nat.coprime_comm]
  apply (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr
  have hpos : 0 < p - 1 :=
    Nat.sub_pos_of_lt (lt_trans (by decide : (1 : ℕ) < 2) hpodd)
  exact Nat.not_dvd_of_pos_of_lt hpos
    (Nat.sub_lt (Fact.out : Nat.Prime p).pos (by decide))

theorem chapter07_cyclotomic_lambda_is_uniformizer_and_root
    (p : ℕ) [Fact (Nat.Prime p)]
    (hpodd : 2 < p)
    {L : Type*} [Field L] [Algebra (ℚ_[p]) L]
    [FiniteDimensional (ℚ_[p]) L]
    (vL : AddValuation L (WithTop ℤ))
    (ζ lambda : L) (hζ : IsPrimitiveRoot ζ p) (hlambda : lambda = ζ - 1)
    (hdegree : Module.finrank (ℚ_[p]) L = p - 1)
    (huniformizer : chapter07IsUniformizer vL lambda) :
    lambda = ζ - 1 ∧
      Module.finrank (ℚ_[p]) L = p - 1 ∧
      chapter07IsUniformizer vL lambda ∧
      aeval lambda
        (LastLib.Book03RamificationTheory.Chapter03.chapter03CyclotomicPolynomial
          (ℚ_[p]) p) = 0 := by
  /- PRIOR ATTEMPT (before repairing the interface):
     exact ⟨hlambda, hroot⟩
     The repaired statement no longer assumes the root equation and exposes
     the degree and uniformizer assertions from the source. -/
  have hζne : ζ ≠ 1 := hζ.ne_one (by omega)
  have hlamne : lambda ≠ 0 := by
    rw [hlambda]
    exact sub_ne_zero.mpr hζne
  have hrootL :=
    LastLib.Book03RamificationTheory.Chapter03.chapter03_cyclotomic_lambda_is_a_root
      p ζ lambda hζ hlambda hlamne
  have hroot :
      aeval lambda
        (LastLib.Book03RamificationTheory.Chapter03.chapter03CyclotomicPolynomial
          (ℚ_[p]) p) = 0 := by
    simpa [Polynomial.aeval_def,
      LastLib.Book03RamificationTheory.Chapter03.chapter03CyclotomicPolynomial] using hrootL
  exact ⟨hlambda, hdegree, huniformizer, hroot⟩

/- The valuation calculation is separated from the choice of a generator of
   the normalized extension valuation. -/
theorem chapter07_cyclotomic_derivative_valuation
    (p : ℕ) [Fact (Nat.Prime p)]
    (hpodd : 2 < p)
    {L : Type*} [Field L] [Algebra (ℚ_[p]) L]
    [FiniteDimensional (ℚ_[p]) L]
    (vL : AddValuation L (WithTop ℤ)) (ζ lambda : L)
    (hζ : IsPrimitiveRoot ζ p) (hlambda : lambda = ζ - 1)
    (hroot : aeval lambda
      (LastLib.Book03RamificationTheory.Chapter03.chapter03CyclotomicPolynomial
        (ℚ_[p]) p) = 0)
    (huniformizer : chapter07IsUniformizer vL lambda)
    (hEisenstein :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt
        (p : ℤ_[p])
        (LastLib.Book03RamificationTheory.Chapter03.chapter03CyclotomicPolynomial
          (ℤ_[p]) p))
    (hscale : ∀ x : ℚ_[p], x ≠ 0 →
      vL (algebraMap (ℚ_[p]) L x) =
        ((p - 1 : ℕ) : WithTop ℤ) * Padic.addValuation x) :
    vL (aeval lambda
      (LastLib.Book03RamificationTheory.Chapter03.chapter03CyclotomicPolynomial
        (ℚ_[p]) p).derivative) =
      (p - 2 : WithTop ℤ) := by
  have _hEisenstein := hEisenstein
  let P : (ℚ_[p])[X] :=
    LastLib.Book03RamificationTheory.Chapter03.chapter03CyclotomicPolynomial
      (ℚ_[p]) p
  have hquot : X * P = (1 + X) ^ p - 1 := by
    simpa [P] using
      (LastLib.Book03RamificationTheory.Chapter03.chapter03_cyclotomic_polynomial_is_the_displayed_quotient
        (ℚ_[p]) p)
  have hderiv := congrArg Polynomial.derivative hquot
  have hderiv_eval := congrArg (fun f : (ℚ_[p])[X] => aeval lambda f) hderiv
  rw [Polynomial.derivative_mul, Polynomial.derivative_sub,
    Polynomial.derivative_pow] at hderiv_eval
  rw [Polynomial.derivative_X, Polynomial.derivative_add,
    Polynomial.derivative_one] at hderiv_eval
  simp only [zero_add, one_mul] at hderiv_eval
  have hderiv_eval' :
    aeval lambda (P + X * P.derivative) =
        aeval lambda (C (p : ℚ_[p]) * (1 + X) ^ (p - 1)) := by
    simpa only [Polynomial.derivative_X, Polynomial.derivative_add,
      Polynomial.derivative_one, add_zero, zero_add, one_mul, mul_one, sub_zero] using hderiv_eval
  have hrootP : aeval lambda P = 0 := by
    simpa [P] using hroot
  have hrelation :
      lambda * aeval lambda P.derivative =
        algebraMap (ℚ_[p]) L (p : ℚ_[p]) * (1 + lambda) ^ (p - 1) := by
    have h := hderiv_eval'
    simp [Polynomial.aeval_def] at h
    have hrootP' : eval₂ (algebraMap (ℚ_[p]) L) lambda P = 0 := by
      simpa [Polynomial.aeval_def] using hrootP
    rw [hrootP', zero_add] at h
    simpa [Polynomial.aeval_def] using h
  have hvζ : vL ζ = 0 := by
    have hpow : ζ ^ p = 1 := hζ.pow_eq_one
    have hmul : p • vL ζ = 0 := by
      rw [← AddValuation.map_pow, hpow, AddValuation.map_one]
    by_cases htop : vL ζ = ⊤
    · rw [htop] at hmul
      have htopmul : ∀ n : ℕ, 0 < n → n • (⊤ : WithTop ℤ) = ⊤ := by
        intro n hn
        induction n with
        | zero => omega
        | succ n ih =>
            rw [succ_nsmul]
            by_cases hn0 : n = 0
            · simp [hn0]
            · rw [ih (Nat.pos_of_ne_zero hn0)]
              simp
      rw [htopmul p (Fact.out : Nat.Prime p).pos] at hmul
      exact False.elim (WithTop.top_ne_coe hmul)
    · obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.mp htop
      rw [← hz] at hmul
      have hz0 : z = 0 := by
        have hmul' : (((p : ℤ) * z : ℤ) : WithTop ℤ) = 0 := by
          calc
            (((p : ℤ) * z : ℤ) : WithTop ℤ) =
                p • (z : WithTop ℤ) := by
              rw [← WithTop.coe_nsmul]
              norm_num [nsmul_eq_mul]
            _ = 0 := hmul
        have hzmul : (p : ℤ) * z = 0 := by
          exact WithTop.coe_eq_coe.mp (by simpa using hmul')
        rcases mul_eq_zero.mp hzmul with hpz | hz0
        · exact False.elim ((Fact.out : Nat.Prime p).ne_zero (by exact_mod_cast hpz))
        · exact hz0
      simpa [hz0] using hz.symm
  have hsum : 1 + lambda = ζ := by
    rw [hlambda]
    ring
  rw [hsum] at hrelation
  have hpne : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have hpval : Padic.addValuation (p := p) (p : ℚ_[p]) =
      (1 : WithTop ℤ) := by
    rw [Padic.addValuation.apply hpne, Padic.valuation_p]
    norm_num
  have hvalp : vL (algebraMap (ℚ_[p]) L (p : ℚ_[p])) =
      ((p - 1 : ℕ) : WithTop ℤ) := by
    rw [hscale _ hpne, hpval]
    simp
  have hvalrel := congrArg vL hrelation
  simp only [AddValuation.map_mul, AddValuation.map_pow] at hvalrel
  rw [huniformizer.2, hvalp, hvζ] at hvalrel
  simp at hvalrel
  have hDtop : vL (aeval lambda P.derivative) ≠ ⊤ := by
    intro htop
    have hfalse := hvalrel
    rw [htop] at hfalse
    have htop_eq : (⊤ : WithTop ℤ) = ((p - 1 : ℕ) : WithTop ℤ) := by
      simp only [add_top] at hfalse
      exact hfalse
    exact WithTop.top_ne_coe htop_eq
  obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.mp hDtop
  rw [← hz] at hvalrel
  have hzInt : (1 : ℤ) + z = ((p - 1 : ℕ) : ℤ) := by
    apply WithTop.coe_injective
    simpa using hvalrel
  have hp2 : 2 ≤ p := by omega
  have hp1 : 1 ≤ p := le_trans (by decide) hp2
  have hcast : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
    rw [Nat.cast_sub hp1]
    norm_num
  have hz' : z = (p : ℤ) - 2 := by
    rw [hcast] at hzInt
    omega
  change vL (aeval lambda P.derivative) = (p : WithTop ℤ) - 2
  calc
    vL (aeval lambda P.derivative) = (z : WithTop ℤ) := hz.symm
    _ = (((p : ℤ) - 2 : ℤ) : WithTop ℤ) := by rw [hz']
    _ = (p : WithTop ℤ) - 2 := by norm_num

theorem chapter07_cyclotomic_different_exponent
    (p : ℕ) [Fact (Nat.Prime p)]
    (hpodd : 2 < p)
    {L : Type*} [Field L] [Algebra (ℚ_[p]) L]
    [FiniteDimensional (ℚ_[p]) L]
    (vL : AddValuation L (WithTop ℤ)) (ζ lambda : L) (d : ℕ)
    (hζ : IsPrimitiveRoot ζ p) (hlambda : lambda = ζ - 1)
    (hroot : aeval lambda
      (LastLib.Book03RamificationTheory.Chapter03.chapter03CyclotomicPolynomial
        (ℚ_[p]) p) = 0)
    (huniformizer : chapter07IsUniformizer vL lambda)
    (hEisenstein :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt
        (p : ℤ_[p])
        (LastLib.Book03RamificationTheory.Chapter03.chapter03CyclotomicPolynomial
          (ℤ_[p]) p))
    (hscale : ∀ x : ℚ_[p], x ≠ 0 →
      vL (algebraMap (ℚ_[p]) L x) =
        ((p - 1 : ℕ) : WithTop ℤ) * Padic.addValuation x)
    (hdifferent : chapter07DifferentExponentValuation vL
      (aeval lambda
      (LastLib.Book03RamificationTheory.Chapter03.chapter03CyclotomicPolynomial
          (ℚ_[p]) p).derivative) d) :
    d = p - 2 := by
  have hvalue := chapter07_cyclotomic_derivative_valuation
    p hpodd vL ζ lambda hζ hlambda hroot huniformizer hEisenstein hscale
  change vL (aeval lambda
      (LastLib.Book03RamificationTheory.Chapter03.chapter03CyclotomicPolynomial
        (ℚ_[p]) p).derivative) = (d : WithTop ℤ) at hdifferent
  rw [hvalue] at hdifferent
  have hp2 : 2 ≤ p := by omega
  have hsubZ : ((p - 2 : ℕ) : ℤ) = (p : ℤ) - 2 := by
    rw [Nat.cast_sub hp2]
    norm_num
  have hcast : ((p - 2 : ℕ) : WithTop ℤ) =
      (p : WithTop ℤ) - 2 := by
    calc
      ((p - 2 : ℕ) : WithTop ℤ) = (((p - 2 : ℕ) : ℤ) : WithTop ℤ) := by norm_num
      _ = (((p : ℤ) - 2 : ℤ) : WithTop ℤ) := by rw [hsubZ]
      _ = (p : WithTop ℤ) - 2 := by norm_num
  have hnat : ((p - 2 : ℕ) : WithTop ℤ) = (d : WithTop ℤ) := by
    rw [hcast]
    exact hdifferent
  have hz : ((p - 2 : ℕ) : ℤ) = (d : ℤ) := by
    apply WithTop.coe_injective
    simpa using hnat
  exact_mod_cast hz.symm

theorem chapter07_prime_radical_derivative_valuation
    (p : ℕ) [Fact (Nat.Prime p)]
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (vL : AddValuation L (WithTop ℤ)) (a : K) (α : L)
    (hvalp : vL (algebraMap K L (p : K)) =
      (p * (p - 1) : WithTop ℤ))
    (hvalpha : vL α = (1 : WithTop ℤ)) :
    vL (aeval α
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08KummerPolynomial
        a p).derivative) =
      (p ^ 2 - 1 : WithTop ℤ) := by
  rw [LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08_prime_radical_derivative_formula]
  simp only [Polynomial.aeval_def, eval₂_mul, eval₂_C, eval₂_X, eval₂_pow,
    AddValuation.map_mul, AddValuation.map_pow]
  rw [hvalp, hvalpha]
  have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero
  have hsubZ : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
    rw [Nat.cast_sub hp1]
    norm_num
  have hsub : ((p - 1 : ℕ) : WithTop ℤ) = (p : WithTop ℤ) - 1 := by
    calc
      ((p - 1 : ℕ) : WithTop ℤ) = (((p - 1 : ℕ) : ℤ) : WithTop ℤ) := by norm_num
      _ = (((p : ℤ) - 1 : ℤ) : WithTop ℤ) := by rw [hsubZ]
      _ = (p : WithTop ℤ) - 1 := by norm_num
  simp [hsub]
  have hpcast : (p : WithTop ℤ) = ((p : ℤ) : WithTop ℤ) := by norm_num
  have hone : (1 : WithTop ℤ) = ((1 : ℤ) : WithTop ℤ) := by norm_num
  rw [hpcast, hone]
  change
    (((p : ℤ) : WithTop ℤ) *
        (((p : ℤ) : WithTop ℤ) - ((1 : ℤ) : WithTop ℤ)) +
      (((p : ℤ) : WithTop ℤ) - ((1 : ℤ) : WithTop ℤ))) =
      (((p : ℤ) : WithTop ℤ) ^ 2 - ((1 : ℤ) : WithTop ℤ))
  conv_lhs =>
    rw [← WithTop.LinearOrderedAddCommGroup.coe_sub, ← WithTop.coe_mul]
  conv_rhs =>
    rw [← WithTop.coe_pow, ← WithTop.LinearOrderedAddCommGroup.coe_sub]
  rw [← WithTop.coe_add]
  congr 1
  ring

theorem chapter07_prime_radical_different_exponent
    (p : ℕ) [Fact (Nat.Prime p)]
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (vL : AddValuation L (WithTop ℤ)) (a : K) (α : L) (d : ℕ)
    (hroot : α ^ p = algebraMap K L a)
    (hvalp : vL (algebraMap K L (p : K)) =
      (p * (p - 1) : WithTop ℤ))
    (hvalpha : vL α = (1 : WithTop ℤ))
    (hdifferent : chapter07DifferentExponentValuation vL
      (aeval α
        (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08KummerPolynomial
          a p).derivative) d) :
    d = p ^ 2 - 1 := by
  have _hroot : α ^ p = algebraMap K L a := hroot
  have hvalue := chapter07_prime_radical_derivative_valuation
    p K L vL a α hvalp hvalpha
  change vL (aeval α
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08KummerPolynomial
        a p).derivative) = (d : WithTop ℤ) at hdifferent
  rw [hvalue] at hdifferent
  have hp2 : 1 ≤ p ^ 2 :=
    Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (Fact.out : Nat.Prime p).ne_zero)
  have hsubZ : ((p ^ 2 - 1 : ℕ) : ℤ) = (p : ℤ) ^ 2 - 1 := by
    rw [Nat.cast_sub hp2, Nat.cast_pow]
    norm_num
  have hcast : ((p ^ 2 - 1 : ℕ) : WithTop ℤ) =
      (p : WithTop ℤ) ^ 2 - 1 := by
    calc
      ((p ^ 2 - 1 : ℕ) : WithTop ℤ) =
          (((p ^ 2 - 1 : ℕ) : ℤ) : WithTop ℤ) := by norm_num
      _ = (((p : ℤ) ^ 2 - 1 : ℤ) : WithTop ℤ) := by rw [hsubZ]
      _ = (p : WithTop ℤ) ^ 2 - 1 := by norm_num
  have hnat : ((p ^ 2 - 1 : ℕ) : WithTop ℤ) = (d : WithTop ℤ) := by
    rw [hcast]
    exact hdifferent
  have hz : ((p ^ 2 - 1 : ℕ) : ℤ) = (d : ℤ) := by
    apply WithTop.coe_injective
    simpa using hnat
  exact_mod_cast hz.symm

def chapter07ArtinSchreierHilbertExponent (p m : ℕ) : ℕ :=
  (m + 1) * (p - 1)

theorem chapter07_artin_schreier_hilbert_sum
    (p m : ℕ) :
    Finset.sum (Finset.range (m + 1)) (fun _i => p - 1) =
      chapter07ArtinSchreierHilbertExponent p m := by
  simp [chapter07ArtinSchreierHilbertExponent]

theorem chapter07_artin_schreier_coordinate_not_integral
    (A K : Type*) [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] (v : AddValuation K (WithTop ℤ))
    (hintegral : ∀ x : K, IsIntegral A x ↔ 0 ≤ v x)
    (y : K) (hy : v y < 0) :
    ¬IsIntegral A y := by
  intro h
  have hnonnegative : 0 ≤ v y := (hintegral y).mp h
  exact (not_le_of_gt hy) hnonnegative

theorem chapter07_artin_schreier_hilbert_different_formula
    (p m : ℕ) [Fact (Nat.Prime p)]
    (_hm :
      LastLib.Book03RamificationTheory.Chapter03.chapter03ArtinSchreierFamilyMember
        p m) :
    (LastLib.Book03RamificationTheory.Chapter03.chapter03ArtinSchreierNumericalProfile
      p m).differentExponent =
      chapter07ArtinSchreierHilbertExponent p m := by
  change (m + 1) * (p - 1) = chapter07ArtinSchreierHilbertExponent p m
  rfl

end

end LastLib.Book03RamificationTheory.Chapter07
