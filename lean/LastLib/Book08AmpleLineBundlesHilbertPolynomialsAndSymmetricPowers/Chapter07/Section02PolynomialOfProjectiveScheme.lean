import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter07.Section01FromDimensionsToAPolynomial

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter07

noncomputable section

universe u

open CategoryTheory
open AlgebraicGeometry
open Polynomial

/-! ## 7.2. The polynomial of a projective scheme -/

def chapter07ProjectiveSpaceHilbertPolynomial (r : ℕ) : Polynomial ℚ :=
  chapter07BinomialPolynomial r 0

@[simp] theorem chapter07_projectiveSpaceHilbertPolynomial_eval
    (r n : ℕ) :
    (chapter07ProjectiveSpaceHilbertPolynomial r).eval (n : ℚ) =
      (Nat.choose (n + r) r : ℚ) := by
  simpa [chapter07ProjectiveSpaceHilbertPolynomial] using
    chapter07_binomialPolynomial_eval r 0 n (Nat.zero_le n)

def chapter07HypersurfaceHilbertPolynomial (r e : ℕ) : Polynomial ℚ :=
  chapter07ProjectiveSpaceHilbertPolynomial r - chapter07BinomialPolynomial r e

def chapter07PlaneCurveHilbertPolynomial (e : ℕ) : Polynomial ℚ :=
  Polynomial.C (e : ℚ) * Polynomial.X + Polynomial.C 1 -
    Polynomial.C (((e : ℚ) - 1) * ((e : ℚ) - 2) / 2)

structure Chapter07ClosedSubschemeOfProjectiveSpace
    (k : Type u) [Field k] where
  r : ℕ
  Z : Scheme.{u}
  inclusion : Z ⟶ chapter07ProjectiveSpace k r
  closedImmersion : IsClosedImmersion inclusion
  structureMap : Z ⟶ chapter07BaseScheme k
  overBase :
    inclusion ≫ chapter07ProjectiveSpaceToBase k r = structureMap

/-!
The cohomological additivity input is stated separately from exactness.  It
is the reusable bridge supplied by the long exact cohomology sequence, and it
keeps this chapter independent of a particular cohomology implementation.
-/
theorem chapter07_hilbert_polynomial_additive_of_short_exact
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    {A B D : Chapter07HilbertSetup k C}
    (hseq : Chapter07ShortExactSequence A.F B.F D.F)
    (hEuler : ∀ n : ℕ,
      chapter07EulerCharacteristic B n =
        chapter07EulerCharacteristic A n + chapter07EulerCharacteristic D n) :
    chapter07HilbertPolynomial B =
      chapter07HilbertPolynomial A + chapter07HilbertPolynomial D := by
  sorry

theorem chapter07_hilbert_polynomial_subtractive_of_short_exact
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    {A B D : Chapter07HilbertSetup k C}
    (hseq : Chapter07ShortExactSequence A.F B.F D.F)
    (hEuler : ∀ n : ℕ,
      chapter07EulerCharacteristic B n =
        chapter07EulerCharacteristic A n + chapter07EulerCharacteristic D n) :
    chapter07HilbertPolynomial D =
      chapter07HilbertPolynomial B - chapter07HilbertPolynomial A := by
  sorry

/-!
This record packages the ideal sequence
`0 → 𝓘_Z → 𝓞_{ℙ^r} → 𝓞_Z → 0` together with the two standard inputs needed
to identify its terms.  The `ambientPolynomial` field is the projective-space
calculation, not the closed-subscheme conclusion proved below.
-/
structure Chapter07ClosedSubschemeHilbertData
    (k : Type u) [Field k]
    (C : Chapter07PolarizedScheme k) where
  subscheme : Chapter07ClosedSubschemeOfProjectiveSpace k
  ambientIdentification : C.X ≅ chapter07ProjectiveSpace k subscheme.r
  ambientIdentification_overBase :
    ambientIdentification.hom ≫ chapter07ProjectiveSpaceToBase k subscheme.r =
      C.structureMap
  ambientPolarization :
    C.L.sheaf ≅
      (Scheme.Modules.pullback ambientIdentification.hom).obj
        (chapter07ProjectiveSpaceTautologicalLineBundle k subscheme.r).sheaf
  ambient : Chapter07HilbertSetup k C
  ideal : Chapter07HilbertSetup k C
  structureSheaf : Chapter07HilbertSetup k C
  idealSequence : Chapter07ShortExactSequence ideal.F ambient.F structureSheaf.F
  idealInjection_mono : Mono idealSequence.injection
  closedStructureSheaf : Chapter07CoherentSheaf subscheme.Z
  structureSheafPushforward :
    structureSheaf.F.sheaf ≅
      (Scheme.Modules.pushforward
        (subscheme.inclusion ≫ ambientIdentification.inv)).obj closedStructureSheaf.sheaf
  ambientPolynomial :
    chapter07HilbertPolynomial ambient =
      chapter07ProjectiveSpaceHilbertPolynomial subscheme.r
  euler_additive : ∀ n : ℕ,
      chapter07EulerCharacteristic ambient n =
      chapter07EulerCharacteristic ideal n +
        chapter07EulerCharacteristic structureSheaf n

theorem chapter07_closed_subscheme_hilbert_polynomial
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (D : Chapter07ClosedSubschemeHilbertData k C) :
    chapter07HilbertPolynomial D.structureSheaf =
      chapter07ProjectiveSpaceHilbertPolynomial D.subscheme.r -
        chapter07HilbertPolynomial D.ideal := by
  sorry

theorem chapter07_closed_subscheme_hilbert_function_eventually
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (D : Chapter07ClosedSubschemeHilbertData k C) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      chapter07HilbertFunction D.structureSheaf n =
        Nat.choose (n + D.subscheme.r) D.subscheme.r -
          chapter07HilbertFunction D.ideal n := by
  sorry

structure Chapter07HypersurfaceHilbertData
    (k : Type u) [Field k]
    (C : Chapter07PolarizedScheme k) where
  closedSubscheme : Chapter07ClosedSubschemeHilbertData k C
  degree : ℕ
  degreePositive : 0 < degree
  ideal_euler_characteristic_shift : ∀ n : ℕ,
    chapter07EulerCharacteristicAtInteger closedSubscheme.ideal (n : ℤ) =
      chapter07EulerCharacteristicAtInteger closedSubscheme.ambient
        ((n : ℤ) - (degree : ℤ))

theorem chapter07_hypersurface_hilbert_polynomial
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (D : Chapter07HypersurfaceHilbertData k C) :
    chapter07HilbertPolynomial D.closedSubscheme.structureSheaf =
      chapter07HypersurfaceHilbertPolynomial D.closedSubscheme.subscheme.r D.degree := by
  sorry

theorem chapter07_hypersurface_hilbert_polynomial_eval
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (D : Chapter07HypersurfaceHilbertData k C) (n : ℕ)
    (hn : D.degree ≤ n) :
    (chapter07HilbertPolynomial D.closedSubscheme.structureSheaf).eval (n : ℚ) =
      (Nat.choose (n + D.closedSubscheme.subscheme.r)
        D.closedSubscheme.subscheme.r : ℚ) -
        (Nat.choose (n + D.closedSubscheme.subscheme.r - D.degree)
          D.closedSubscheme.subscheme.r : ℚ) := by
  sorry

/-!
No smoothness field occurs in the hypersurface data: the formula is
scheme-theoretic and applies equally to singular and nonreduced hypersurfaces.
-/
theorem chapter07_plane_curve_hilbert_polynomial
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (D : Chapter07HypersurfaceHilbertData k C)
    (hplane : D.closedSubscheme.subscheme.r = 2) :
    chapter07HilbertPolynomial D.closedSubscheme.structureSheaf =
      chapter07PlaneCurveHilbertPolynomial D.degree := by
  sorry

theorem chapter07_plane_curve_hilbert_polynomial_eval
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (D : Chapter07HypersurfaceHilbertData k C)
    (hplane : D.closedSubscheme.subscheme.r = 2) (n : ℕ) :
    (chapter07HilbertPolynomial D.closedSubscheme.structureSheaf).eval (n : ℚ) =
      (D.degree : ℚ) * n + 1 -
        (((D.degree : ℚ) - 1) * ((D.degree : ℚ) - 2) / 2) := by
  sorry

/-! A zero-dimensional coherent sheaf is represented by its total length. -/
structure Chapter07ZeroDimensionalHilbertData
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k} where
  setup : Chapter07HilbertSetup k C
  length : ℕ
  supportDimension : Chapter07SupportDimensionCertificate setup.F
  supportDimension_zero : supportDimension.dimension = 0
  eulerCharacteristic_eq_length : ∀ n : ℕ,
    chapter07EulerCharacteristic setup n = (length : ℤ)

theorem chapter07_zero_dimensional_hilbert_polynomial
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (D : Chapter07ZeroDimensionalHilbertData (k := k) (C := C)) :
    chapter07HilbertPolynomial D.setup = Polynomial.C (D.length : ℚ) := by
  sorry

structure Chapter07DoubledPointHilbertData
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k} where
  doubled : Chapter07ZeroDimensionalHilbertData (k := k) (C := C)
  reducedSupport : Chapter07ZeroDimensionalHilbertData (k := k) (C := C)
  thickeningSequence :
    Chapter07ShortExactSequence reducedSupport.setup.F doubled.setup.F
      reducedSupport.setup.F
  doubledLength : doubled.length = 2
  reducedLength : reducedSupport.length = 1

theorem chapter07_doubled_point_hilbert_polynomials
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (D : Chapter07DoubledPointHilbertData (k := k) (C := C)) :
    chapter07HilbertPolynomial D.doubled.setup = Polynomial.C 2 ∧
      chapter07HilbertPolynomial D.reducedSupport.setup = Polynomial.C 1 := by
  sorry

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter07
