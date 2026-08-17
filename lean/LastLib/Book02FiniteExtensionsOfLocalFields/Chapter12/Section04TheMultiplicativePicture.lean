import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12.Section03TheGaloisPicture
import Mathlib.Topology.Algebra.Polynomial

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12

noncomputable section

open Polynomial
open scoped BigOperators

/-! ## 12.4. Stability of simple roots -/

/-- The monic degree-`d` polynomial with coefficient vector `a`, where
`a i` is the coefficient of `T^i`. -/
def chapter12MonicPolynomial
    {K : Type*} [Semiring K] (d : ℕ) (a : Fin d → K) : K[X] :=
  (X : K[X]) ^ d + ∑ i : Fin d, C (a i) * X ^ (i : ℕ)

/-- The lower-coefficient vector of a polynomial in the fixed degree-parameter
space. -/
def chapter12CoefficientVector
    {K : Type*} [Semiring K] (d : ℕ) (f : K[X]) : Fin d → K :=
  fun i => f.coeff (i : ℕ)

/-- A monic polynomial of degree `d` is recovered from its lower
coefficients. -/
theorem chapter12_monic_polynomial_recovered_from_coefficients
    {K : Type*} [Field K] (f : K[X]) (d : ℕ)
    (hf_monic : f.Monic) (hf_degree : f.natDegree = d) :
    chapter12MonicPolynomial d (chapter12CoefficientVector d f) = f := by
  sorry

/-- Separability is exactly the nonvanishing derivative condition at a root. -/
theorem chapter12_simple_root_has_nonzero_derivative
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (f : K[X]) (hf_separable : f.Separable) (z : L)
    (hz : aeval z f = 0) :
    aeval z f.derivative ≠ 0 := by
  sorry

/--
Simultaneous stability of all simple roots.  `M` is a finite splitting field
and the supplied root list records its distinct roots.  The conclusion keeps
the coefficient neighborhood in `K^d`, returns one root in each prescribed
ball, asserts uniqueness in that ball, and records that all roots factor in
`M`.
-/
theorem chapter12_simultaneous_stability_of_simple_roots
    {K M : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] [NormedField M] [NormedAlgebra K M]
    [FiniteDimensional K M]
    (f : K[X]) (d : ℕ)
    (hf_monic : f.Monic) (hf_degree : f.natDegree = d)
    (hf_separable : f.Separable)
    (hsplits : (f.map (algebraMap K M)).Splits)
    (roots : Fin d → M)
    (hroot : ∀ i, aeval (roots i) f = 0)
    (hexhaustive : ∀ z : M, aeval z f = 0 → ∃ i, z = roots i)
    (hinjective : Function.Injective roots)
    (r : Fin d → ℝ) (hr : ∀ i, 0 < r i)
    (hballs : ∀ i j, i ≠ j →
      Disjoint (Metric.ball (roots i) (r i)) (Metric.ball (roots j) (r j))) :
    ∃ U : Set (Fin d → K), IsOpen U ∧
      chapter12CoefficientVector d f ∈ U ∧
      ∀ b : Fin d → K, b ∈ U →
        ∃ β : Fin d → M,
          (∀ i, aeval (β i) (chapter12MonicPolynomial d b) = 0 ∧
            β i ∈ Metric.ball (roots i) (r i)) ∧
          (∀ (i : Fin d) (z : M), aeval z (chapter12MonicPolynomial d b) = 0 →
            z ∈ Metric.ball (roots i) (r i) → z = β i) ∧
          Polynomial.map (algebraMap K M) (chapter12MonicPolynomial d b) =
            ∏ i : Fin d, ((X : M[X]) - C (β i)) := by
  sorry

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12
