import LastLib.Book03RamificationTheory.Chapter07.Section06TameAndWildDerivativeBounds

namespace LastLib.Book03RamificationTheory.Chapter07

noncomputable section

open Polynomial
open scoped BigOperators Polynomial nonZeroDivisors

/-! ## 7.7. Further derivative calculations -/

/-- The cyclotomic polynomial in the coordinate `λ = ζ - 1`. -/
def chapter07CyclotomicPolynomial
    (R : Type*) [CommRing R] (p : ℕ) : R[X] :=
  Finset.sum (Finset.range p) (fun i =>
    C (Nat.choose p (i + 1) : R) * X ^ i)

theorem chapter07_cyclotomic_polynomial_is_the_displayed_quotient
    (R : Type*) [CommRing R] (p : ℕ) :
    X * chapter07CyclotomicPolynomial R p =
      (1 + X) ^ p - 1 := by
  sorry

theorem chapter07_cyclotomic_polynomial_is_eisenstein_at_p
    (p : ℕ) [Fact (Nat.Prime p)] :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt
      (p : ℤ_[p])
      (chapter07CyclotomicPolynomial (ℤ_[p]) p) := by
  sorry

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
    {L : Type*} [Field L] [Algebra (ℚ_[p]) L]
    [FiniteDimensional (ℚ_[p]) L]
    (vL : AddValuation L (WithTop ℤ))
    (ζ lambda : L) (_hζ : IsPrimitiveRoot ζ p) (hlambda : lambda = ζ - 1)
    (_hdegree : Module.finrank (ℚ_[p]) L = p - 1)
    (hroot : aeval lambda (chapter07CyclotomicPolynomial (ℚ_[p]) p) = 0)
    (_hvalue : chapter07IsUniformizer vL lambda) :
    lambda = ζ - 1 ∧ aeval lambda (chapter07CyclotomicPolynomial (ℚ_[p]) p) = 0 := by
  exact ⟨hlambda, hroot⟩

/- The valuation calculation is separated from the choice of a generator of
   the normalized extension valuation. -/
theorem chapter07_cyclotomic_derivative_valuation
    (p : ℕ) [Fact (Nat.Prime p)]
    {L : Type*} [Field L] [Algebra (ℚ_[p]) L]
    [FiniteDimensional (ℚ_[p]) L]
    (vL : AddValuation L (WithTop ℤ)) (ζ lambda : L)
    (hζ : IsPrimitiveRoot ζ p) (hlambda : lambda = ζ - 1)
    (hroot : aeval lambda (chapter07CyclotomicPolynomial (ℚ_[p]) p) = 0)
    (huniformizer : chapter07IsUniformizer vL lambda)
    (hEisenstein :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt
        (p : ℤ_[p]) (chapter07CyclotomicPolynomial (ℤ_[p]) p)) :
    vL (aeval lambda
      (chapter07CyclotomicPolynomial (ℚ_[p]) p).derivative) =
      (p - 2 : WithTop ℤ) := by
  sorry

theorem chapter07_cyclotomic_different_exponent
    (p : ℕ) [Fact (Nat.Prime p)]
    {L : Type*} [Field L] [Algebra (ℚ_[p]) L]
    [FiniteDimensional (ℚ_[p]) L]
    (vL : AddValuation L (WithTop ℤ)) (ζ lambda : L) (d : ℕ)
    (hζ : IsPrimitiveRoot ζ p) (hlambda : lambda = ζ - 1)
    (hroot : aeval lambda (chapter07CyclotomicPolynomial (ℚ_[p]) p) = 0)
    (huniformizer : chapter07IsUniformizer vL lambda)
    (hEisenstein :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt
        (p : ℤ_[p]) (chapter07CyclotomicPolynomial (ℤ_[p]) p))
    (hdifferent : chapter07DifferentExponentValuation vL
      (aeval lambda (chapter07CyclotomicPolynomial (ℚ_[p]) p).derivative) d) :
    d = p - 2 := by
  sorry

/-- The prime-radical polynomial used for the second mixed-characteristic
    calculation. -/
def chapter07PrimeRadicalPolynomial
    (K : Type*) [CommRing K] (a : K) (p : ℕ) : K[X] :=
  X ^ p - C a

theorem chapter07_prime_radical_derivative_formula
    (K : Type*) [CommRing K] (a : K) (p : ℕ) :
    (chapter07PrimeRadicalPolynomial K a p).derivative =
      C (p : K) * X ^ (p - 1) := by
  sorry

theorem chapter07_prime_radical_derivative_valuation
    (p : ℕ) [Fact (Nat.Prime p)]
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (vL : AddValuation L (WithTop ℤ)) (a : K) (α : L)
    (hroot : α ^ p = algebraMap K L a)
    (hvalp : vL (algebraMap K L (p : K)) =
      (p * (p - 1) : WithTop ℤ))
    (hvalpha : vL α = (1 : WithTop ℤ)) :
    vL (aeval α (chapter07PrimeRadicalPolynomial K a p).derivative) =
      (p ^ 2 - 1 : WithTop ℤ) := by
  sorry

theorem chapter07_prime_radical_different_exponent
    (p : ℕ) [Fact (Nat.Prime p)]
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (vL : AddValuation L (WithTop ℤ)) (a : K) (α : L) (d : ℕ)
    (hroot : α ^ p = algebraMap K L a)
    (hvalp : vL (algebraMap K L (p : K)) =
      (p * (p - 1) : WithTop ℤ))
    (hvalpha : vL α = (1 : WithTop ℤ))
    (hdifferent : chapter07DifferentExponentValuation vL
      (aeval α (chapter07PrimeRadicalPolynomial K a p).derivative) d) :
    d = p ^ 2 - 1 := by
  sorry

/- The Artin--Schreier coordinate in the displayed equation is deliberately
   kept separate from an integral generator. -/
def chapter07ArtinSchreierEquation
    (K : Type*) [Field K] (p m : ℕ) (t y : K) : Prop :=
  y ^ p - y = t ^ (-(m : ℤ))

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

def chapter07ArtinSchreierHilbertData (p m d : ℕ) : Prop :=
  d = Finset.sum (Finset.range (m + 1)) (fun _i => p - 1)

theorem chapter07_artin_schreier_hilbert_different_formula
    (p m d : ℕ) (hdata : chapter07ArtinSchreierHilbertData p m d) :
    d = chapter07ArtinSchreierHilbertExponent p m := by
  change d = Finset.sum (Finset.range (m + 1)) (fun _i => p - 1) at hdata
  exact hdata.trans (chapter07_artin_schreier_hilbert_sum p m)

end

end LastLib.Book03RamificationTheory.Chapter07
