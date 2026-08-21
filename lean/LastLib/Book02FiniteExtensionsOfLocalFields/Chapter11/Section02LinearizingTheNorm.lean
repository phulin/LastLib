import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.Section01TheLocalNormFiltration

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11

noncomputable section

open scoped BigOperators Polynomial
open Module

/-! ## 11.2. Linearizing the norm -/

/- The terms of degree at least two are represented by the exact remainder after
   subtracting the constant and trace terms. -/
def chapter11NormRemainder
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (x : L) : K :=
  Algebra.norm K (1 + x) - 1 - Algebra.trace K L x

/- The determinant identity is recorded at the coefficient level: the
   coefficient of degree one in `det(1 + X M)` is `tr(M)`. -/
theorem chapter11_det_one_add_has_trace_linear_coefficient
    (K : Type*) [CommRing K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) :
    (Matrix.det (1 + (Polynomial.X : K[X]) • M.map Polynomial.C)).coeff 1 =
      Matrix.trace M := by
  sorry

/- The same coefficient calculation for multiplication by an element of a
   finite free algebra. -/
theorem chapter11_norm_determinant_has_trace_linear_coefficient
    (K L : Type*) [CommRing K] [CommRing L] [Algebra K L]
    [Module.Free K L] [Module.Finite K L]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L) (x : L) :
    (Matrix.det
        (1 + (Polynomial.X : K[X]) • (Algebra.leftMulMatrix b x).map Polynomial.C)).coeff 1 =
      Algebra.trace K L x := by
  sorry

/- The first-order norm expansion with its canonical higher-order remainder. -/
theorem chapter11_norm_one_add_linearizes_to_trace
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (x : L) :
    Algebra.norm K (1 + x) =
      1 + Algebra.trace K L x + chapter11NormRemainder K L x := by
  sorry

/- The omitted determinant terms have valuation at least `2n`, and restriction
   of an extension valuation turns that into the displayed ceiling bound. -/
theorem chapter11_norm_remainder_has_depth
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (e f : ℕ) (he : 0 < e)
    (hext : chapter11ValuationExtension vK vL)
    (hscale : chapter11ValuationScaling vK vL e)
    (hnorm : chapter11NormValuationFormula K L vK vL f)
    (hcompleteK : chapter11ValuationComplete vK)
    (hcompleteL : chapter11ValuationComplete vL)
    (n : ℕ) (hn : 1 ≤ n) (x : L)
    (hx : x ∈ chapter11ValuationIdealPowerSet vL n) :
    vK (chapter11NormRemainder K L x) ≥
      ((chapter11CeilDiv (2 * n) e : ℤ) : WithTop ℤ) := by
  sorry

/- Trace obeys the corresponding coarse depth bound. -/
theorem chapter11_trace_principal_ideal_depth_bound
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (e : ℕ) (he : 0 < e)
    (hext : chapter11ValuationExtension vK vL)
    (hscale : chapter11ValuationScaling vK vL e)
    (hcompleteK : chapter11ValuationComplete vK)
    (hcompleteL : chapter11ValuationComplete vL) (n : ℕ) (hn : 1 ≤ n) :
    chapter11TraceImage K L vL n ⊆
      chapter11ValuationIdealPowerSet vK (chapter11CeilDiv n e) := by
  sorry

/- Inseparability can make the trace map vanish; this is the precise caveat
   behind the separability hypothesis in first-layer lifting. -/
theorem chapter11_trace_vanishes_for_nonseparable_extension
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (hsep : ¬Algebra.IsSeparable K L) :
    Algebra.trace K L = 0 := by
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11
