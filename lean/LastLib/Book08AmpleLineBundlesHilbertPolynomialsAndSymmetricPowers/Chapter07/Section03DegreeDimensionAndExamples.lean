import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter07.Section02PolynomialOfProjectiveScheme

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter07

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open Polynomial

/-! ## 7.3. Degree, dimension, and examples -/

def Chapter07NonzeroCoherentSheaf
    {X : Scheme.{u}} (F : Chapter07CoherentSheaf X) : Prop :=
  ¬ IsZero F.sheaf

theorem chapter07_degree_dimension_and_leading_term
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (S : Chapter07HilbertSetup k C)
    (D : Chapter07SupportDimensionCertificate S.F)
    (hDimensionData : Chapter07HilbertPolynomialDimensionCertificate S D)
    (hF : Chapter07NonzeroCoherentSheaf S.F) :
    ∃ e : ℕ, 0 < e ∧
      (chapter07HilbertPolynomial S).natDegree = D.dimension ∧
      (chapter07HilbertPolynomial S).leadingCoeff =
        (e : ℚ) / Nat.factorial D.dimension := by
  sorry

theorem chapter07_hilbert_polynomial_has_positive_degree_coefficient
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (S : Chapter07HilbertSetup k C)
    (D : Chapter07SupportDimensionCertificate S.F)
    (hDimensionData : Chapter07HilbertPolynomialDimensionCertificate S D)
    (hF : Chapter07NonzeroCoherentSheaf S.F) :
    ∃ e : ℕ, 0 < e ∧
      (chapter07HilbertPolynomial S).coeff D.dimension =
        (e : ℚ) / Nat.factorial D.dimension := by
  sorry

/-!
The error term records the lower-dimensional contribution left by a hyperplane
which is not assumed to be a nonzerodivisor on every associated component.
-/
structure Chapter07HyperplaneSection
    {k : Type u} [Field k]
    (C : Chapter07PolarizedScheme k) where
  H : Scheme.{u}
  inclusion : H ⟶ C.X
  isClosedImmersion : IsClosedImmersion inclusion

/-! The colon/kernel correction in the general hyperplane argument is carried
by an explicit lower-dimensional error profile.  The Euler relation is the
cohomological content of the restriction sequence; the support disjunction
is the dimension estimate used for the error polynomial. -/
structure Chapter07HyperplaneRestrictionData
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (H : Chapter07HyperplaneSection C)
    (S R : Chapter07HilbertSetup k C) (d : ℕ) where
  error : Chapter07HilbertSetup k C
  eulerRelation : ∀ n : ℕ,
    chapter07EulerCharacteristicAtInteger S (n : ℤ) -
        chapter07EulerCharacteristicAtInteger S ((n : ℤ) - 1) =
      chapter07EulerCharacteristicAtInteger R (n : ℤ) -
        chapter07EulerCharacteristicAtInteger error ((n : ℤ) - 1)
  errorLowerDimensional :
    IsZero error.F.sheaf ∨
      ∃ D : Chapter07SupportDimensionCertificate error.F,
        ¬ IsZero error.F.sheaf ∧ D.dimension < d ∧
          Nonempty (Chapter07HilbertPolynomialDimensionCertificate error D)

def chapter07FiniteDifference (P : Polynomial ℚ) : Polynomial ℚ :=
  P - P.comp (Polynomial.X - Polynomial.C 1)

theorem chapter07_finiteDifference_eval
    (P : Polynomial ℚ) (n : ℤ) :
    (chapter07FiniteDifference P).eval (n : ℚ) =
      P.eval (n : ℚ) - P.eval ((n - 1 : ℤ) : ℚ) := by
  sorry

theorem chapter07_hyperplane_finite_difference
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (S R : Chapter07HilbertSetup k C)
    (H : Chapter07HyperplaneSection C)
    (d : ℕ)
    (hDim : ∃ D : Chapter07SupportDimensionCertificate S.F,
      D.dimension = d)
    (hRestriction :
      Nonempty (Chapter07HyperplaneRestrictionData H S R d)) :
    ∃ E : Polynomial ℚ,
      (E = 0 ∨ E.natDegree < d) ∧
        chapter07FiniteDifference (chapter07HilbertPolynomial S) =
          chapter07HilbertPolynomial R + E := by
  sorry

theorem chapter07_zero_dimensional_polynomial_is_total_length
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (D : Chapter07ZeroDimensionalHilbertData (k := k) (C := C)) :
    chapter07HilbertPolynomial D.setup = Polynomial.C (D.length : ℚ) := by
  exact chapter07_zero_dimensional_hilbert_polynomial D

theorem chapter07_projective_curve_hilbert_polynomial_shape
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (S : Chapter07HilbertSetup k C)
    (D : Chapter07SupportDimensionCertificate S.F)
    (hDimensionData : Chapter07HilbertPolynomialDimensionCertificate S D)
    (hcurve : D.dimension = 1)
    (hF : Chapter07NonzeroCoherentSheaf S.F) :
    ∃ e : ℕ, 0 < e ∧ ∃ c : ℚ,
      chapter07HilbertPolynomial S =
        Polynomial.C (e : ℚ) * Polynomial.X + Polynomial.C c := by
  sorry

/-!
The union sequence is the sheaf-theoretic form of inclusion--exclusion:
`0 → 𝓞_{Y ∪ Z} → 𝓞_Y ⊕ 𝓞_Z → 𝓞_{Y ∩ Z} → 0`.
-/
structure Chapter07UnionHilbertData
    {k : Type u} [Field k]
    (C : Chapter07PolarizedScheme k) where
  union : Chapter07HilbertSetup k C
  left : Chapter07HilbertSetup k C
  right : Chapter07HilbertSetup k C
  intersection : Chapter07HilbertSetup k C
  middle : Chapter07HilbertSetup k C
  exactSequence : Chapter07ShortExactSequence union.F middle.F intersection.F
  euler_additive : ∀ n : ℕ,
    chapter07EulerCharacteristic middle n =
      chapter07EulerCharacteristic union n +
        chapter07EulerCharacteristic intersection n
  middle_euler_additive : ∀ n : ℕ,
    chapter07EulerCharacteristic middle n =
      chapter07EulerCharacteristic left n +
        chapter07EulerCharacteristic right n

theorem chapter07_union_hilbert_polynomial_inclusion_exclusion
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (D : Chapter07UnionHilbertData C) :
    chapter07HilbertPolynomial D.union =
      chapter07HilbertPolynomial D.left +
        chapter07HilbertPolynomial D.right -
          chapter07HilbertPolynomial D.intersection := by
  sorry

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter07
