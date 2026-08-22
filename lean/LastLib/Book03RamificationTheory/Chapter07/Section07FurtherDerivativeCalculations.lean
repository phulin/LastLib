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
  sorry

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
  sorry

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
  sorry

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
      (aeval α
        (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08KummerPolynomial
          a p).derivative) d) :
    d = p ^ 2 - 1 := by
  sorry

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
