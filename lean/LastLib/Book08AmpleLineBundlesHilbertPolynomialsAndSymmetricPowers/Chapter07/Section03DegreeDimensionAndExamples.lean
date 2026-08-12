import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter07.Section02PolynomialOfProjectiveScheme

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter07

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open Polynomial

/-! ## 7.3. Degree, dimension, and examples -/

/- LOCAL_DEPENDENCY_GUESS: the preceding coherent-sheaf chapters should
replace the certificate field below by their canonical support and Krull
dimension API.  The dimension is deliberately attached to the sheaf, not to
the polarization, so the later invariance statement is meaningful. -/
structure Chapter07SupportDimensionCertificate
    {X : Scheme.{u}} (F : Chapter07CoherentSheaf X) where
  dimension : ℕ
  isSupportDimension : Prop

def Chapter07NonzeroCoherentSheaf
    {X : Scheme.{u}} (F : Chapter07CoherentSheaf X) : Prop :=
  ¬ IsZero F.sheaf

theorem chapter07_degree_dimension_and_leading_term
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (S : Chapter07HilbertSetup k C)
    (D : Chapter07SupportDimensionCertificate S.F)
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
  isHyperplaneSection : Prop
  isGeneral : Prop

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
    /- LOCAL_DEPENDENCY_GUESS: replace this proposition by the canonical
    restriction exact sequence and its lower-dimensional support certificate. -/
    (hRestriction : Prop) :
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
  middlePolynomial :
    chapter07HilbertPolynomial middle =
      chapter07HilbertPolynomial left + chapter07HilbertPolynomial right
  representsUnion : Prop
  representsIntersection : Prop

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
