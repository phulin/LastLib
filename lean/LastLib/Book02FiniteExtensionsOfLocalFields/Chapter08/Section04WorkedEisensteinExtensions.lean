import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.Section03UniformizersAndMinimalPolynomials
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter03

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08

noncomputable section

open Polynomial
open scoped WithTop

/-! # 8.4. Worked Eisenstein extensions -/

/-- The radical polynomial `T^n - a` used in the examples. -/
def chapter08RadicalPolynomial
    {R : Type*} [CommRing R] (a : R) (n : ℕ) : R[X] :=
  X ^ n - C a

/-- Book §8.4: `T^n - π` is Eisenstein at a generator of the maximal ideal
of a DVR. -/
theorem chapter08_radical_polynomial_is_eisenstein
    {A : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    (π : A) (hπ : IsLocalRing.maximalIdeal A = Ideal.span ({π} : Set A))
    (n : ℕ) (hn : 0 < n) :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt π
      (chapter08RadicalPolynomial π n) := by
  sorry

/-- The integral model of `T^n-p` over the p-adic integers. -/
def chapter08PadicIntegralRadicalPolynomial
    (p n : ℕ) [Fact p.Prime] : (ℤ_[p])[X] :=
  chapter08RadicalPolynomial (p : ℤ_[p]) n

/-- The same p-adic polynomial after mapping its coefficients to `ℚ_[p]`. -/
def chapter08PadicRadicalPolynomial
    (p n : ℕ) [Fact p.Prime] : (ℚ_[p])[X] :=
  (chapter08PadicIntegralRadicalPolynomial p n).map (algebraMap (ℤ_[p]) (ℚ_[p]))

/-- Book §8.4: for every prime `p` and positive `n`, `T^n-p` is Eisenstein
over `ℤ_[p]`, including the wild case `p ∣ n`. -/
theorem chapter08_padic_radical_polynomial_is_eisenstein
    (p n : ℕ) [Fact p.Prime] (hn : 0 < n) :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt (p : ℤ_[p])
      (chapter08PadicIntegralRadicalPolynomial p n) := by
  sorry

/-- Book §8.4: adjoining a root of `T^n-p` gives the stated totally ramified
p-adic profile and the generated integral ring. -/
theorem chapter08_padic_radical_extension
    (p n : ℕ) [Fact p.Prime] (hn : 0 < n)
    {L : Type*} [Field L]
    [Algebra (ℚ_[p]) L] [FiniteDimensional (ℚ_[p]) L]
    [Algebra (ℤ_[p]) L]
    [IsScalarTower (ℤ_[p]) (ℚ_[p]) L]
    (α : L)
    (hroot : aeval α (chapter08PadicRadicalPolynomial p n) = 0)
    (hgen : Algebra.adjoin (ℚ_[p]) ({α} : Set L) = ⊤)
    (hdegree : Module.finrank (ℚ_[p]) L = n) :
    ∃ q : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10FiniteExtensionProfile,
      q.degree = n ∧ q.ramificationIndex = n ∧ q.residueDegree = 1 ∧
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10TotallyRamified q ∧
        (integralClosure (ℤ_[p]) L : Set L) =
          (Algebra.adjoin (ℤ_[p]) ({α} : Set L) : Set L) := by
  sorry

/-- The equal-characteristic radical polynomial over `k((t))`. -/
def chapter08LaurentRadicalPolynomial
    (k : Type*) [Field k] (n : ℕ) : (LaurentSeries k)[X] :=
  chapter08RadicalPolynomial
    (LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.laurentSeriesUniformizer k) n

/-- A radical polynomial with exponent prime to the characteristic is
separable, provided its constant term is nonzero. -/
theorem chapter08_radical_polynomial_separable_of_coprime_exponent
    {K : Type*} [Field K] (a : K) (p n : ℕ)
    [Fact p.Prime] [CharP K p]
    (ha : a ≠ 0) (hcoprime : Nat.Coprime n p) :
    (chapter08RadicalPolynomial a n).Separable := by
  sorry

/-- In characteristic `p`, the derivative of `T^p-a` vanishes. -/
theorem chapter08_char_p_radical_derivative_zero
    {K : Type*} [Field K] (a : K) (p : ℕ) [CharP K p] :
    (chapter08RadicalPolynomial a p).derivative = 0 := by
  sorry

/-- Book §8.4: in equal characteristic `p`, the exponent-`p` radical is the
purely inseparable endpoint, while the valuation-theoretic profile remains
the same as in the separable Eisenstein examples. -/
theorem chapter08_laurent_radical_purely_inseparable_profile
    {k L : Type*} [Field k] [Field L]
    [Algebra (LaurentSeries k) L] [FiniteDimensional (LaurentSeries k) L]
    [IsPurelyInseparable (LaurentSeries k) L]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (α : L)
    (hroot : aeval α (chapter08LaurentRadicalPolynomial k p) = 0)
    (hgen : Algebra.adjoin (LaurentSeries k) ({α} : Set L) = ⊤)
    (hdegree : Module.finrank (LaurentSeries k) L = p)
    (vK : AddValuation (LaurentSeries k) (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (hval : vK.IsEquiv
      (AddValuation.comap (algebraMap (LaurentSeries k) L) vL))
    (hresidue : LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree vK vL hval = 1) :
    ∃ q : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10FiniteExtensionProfile,
      q.degree = p ∧ q.ramificationIndex = p ∧ q.residueDegree = 1 ∧
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10TotallyRamified q := by
  sorry

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08
