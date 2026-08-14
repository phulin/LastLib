import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter11.Dependencies

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter11

noncomputable section

open AlgebraicGeometry CategoryTheory
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04

universe u

/-! ### 11.3 Consequences and examples -/

/-- On an integral curve, a nonzero global section has an effective zero
divisor whose degree is the degree of its line bundle. -/
theorem chapter11_nonzero_section_has_effective_zero_divisor
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier]
    [Chapter11SectionZeroDivisorTheory C]
    (L : Chapter11LineBundle C.carrier) (s : Chapter11H0 C L)
    (hs : s ≠ 0) :
    Nonempty (Chapter11SectionZeroDivisor C L s) :=
  Chapter11SectionZeroDivisorTheory.zero_divisor_of_nonzero_section L s hs

/-- Negative degree forbids nonzero sections on an integral curve. -/
theorem chapter11_negative_degree_no_nonzero_sections
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier]
    [Chapter11SectionZeroDivisorTheory C]
    (L : Chapter11LineBundle C.carrier)
    (hdegree : chapter11Degree L < 0) :
    ∀ s : Chapter11H0 C L, s = 0 := by
  sorry

theorem chapter11_negative_degree_h0_finrank_eq_zero
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier]
    [Chapter11SectionZeroDivisorTheory C]
    (L : Chapter11LineBundle C.carrier)
    (hdegree : chapter11Degree L < 0) :
    chapter11H0Finrank C L = 0 := by
  sorry

/-- The source warning, made precise as an existential property of a
reducible curve and a line bundle with a nonzero section but negative total
degree. -/
def Chapter11TotalDegreeNegativeCounterexample {k : Type u} [Field k]
    (C : Chapter11ProperGorensteinCurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier] : Prop :=
  Nonempty (Chapter11ReducibleNegativeDegreeSection C)

/-- A reducible nodal curve supplies the warning example; its section is
supported on a component of positive degree while the total degree is
negative. -/
theorem chapter11_reducible_total_degree_negative_does_not_force_vanishing
    {k : Type u} [Field k]
    (C : Chapter11ProperGorensteinCurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier]
    (hcounter : Chapter11TotalDegreeNegativeCounterexample C) :
    ¬ (∀ (L : Chapter11LineBundle C.carrier),
      chapter11Degree L < 0 →
        ∀ s : Chapter11CohomologySpace C.carrier C.structureMap L.module 0,
          s = 0) := by
  sorry

/-- The canonical bundle has exactly `g` global sections (11.3). -/
theorem chapter11_h0_canonical_bundle_eq_genus
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11PicardTheory C.carrier]
    [Chapter11DualizingSheafTheory C.carrier]
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11CohomologyIsomorphismTheory C.carrier C.structureMap]
    [Chapter11ConnectedGlobalSections C]
    [Chapter11SerreDualityTheory C] :
    chapter11H0Finrank C (chapter11CanonicalBundle (X := C.carrier)) = C.genus := by
  sorry

/-- For a chosen canonical divisor, its degree is `2g-2` (11.4). -/
theorem chapter11_degree_canonical_divisor_eq_two_genus_sub_two
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11PicardTheory C.carrier]
    [Chapter11DegreeTheory C.carrier]
    [Chapter11DualizingSheafTheory C.carrier]
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11EffectiveDecompositionTheory C]
    [Chapter11EffectiveCartierTwistSequenceTheory C]
    [Chapter11CohomologyIsomorphismTheory C.carrier C.structureMap]
    [Chapter11ConnectedGlobalSections C]
    [Chapter11EulerCharacteristicTheory C.carrier C.structureMap]
    [Chapter11SerreDualityTheory C]
    (K : Chapter11CanonicalDivisor C) :
    K.divisor.degree = 2 * (C.genus : ℤ) - 2 := by
  sorry

theorem chapter11_degree_canonical_bundle_eq_two_genus_sub_two
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11PicardTheory C.carrier]
    [Chapter11DegreeTheory C.carrier]
    [Chapter11DualizingSheafTheory C.carrier]
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11EffectiveDecompositionTheory C]
    [Chapter11EffectiveCartierTwistSequenceTheory C]
    [Chapter11CohomologyIsomorphismTheory C.carrier C.structureMap]
    [Chapter11ConnectedGlobalSections C]
    [Chapter11EulerCharacteristicTheory C.carrier C.structureMap]
    [Chapter11SerreDualityTheory C]
    (K : Chapter11CanonicalDivisor C) :
    chapter11Degree (chapter11CanonicalBundle (X := C.carrier)) =
      2 * (C.genus : ℤ) - 2 := by
  sorry

/-! ### The projective-line example -/

/-- The two numerical formulas occurring on `ℙ¹`. -/
def chapter11ProjectiveLineH0Dimension (n : ℤ) : ℕ :=
  if 0 ≤ n then Int.toNat n + 1 else 0

def chapter11ProjectiveLineH1Dimension (n : ℤ) : ℕ :=
  Int.toNat (max (-n - 1) 0)

/-- A projective-line presentation of twists `𝒪(n)` and their cohomology. -/
structure Chapter11ProjectiveLineData (k : Type u) [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier] where
  projectiveLineIso : C.carrier ≅ chapter04ProjectiveLine k
  projectiveLine_over_base :
    projectiveLineIso.hom ≫ chapter04ProjectiveLineStructureMap k = C.structureMap
  genus_zero : C.genus = 0
  twist : ℤ → Chapter11LineBundle C.carrier
  degree_twist : ∀ n, chapter11Degree (twist n) = n
  h0_twist : ∀ n,
    chapter11H0Finrank C (twist n) = chapter11ProjectiveLineH0Dimension n
  h1_twist : ∀ n,
    chapter11H1Finrank C (twist n) = chapter11ProjectiveLineH1Dimension n

theorem chapter11_projective_line_h0_formula
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier]
    (P : Chapter11ProjectiveLineData k C) (n : ℤ) :
    chapter11H0Finrank C (P.twist n) =
      if 0 ≤ n then Int.toNat n + 1 else 0 := by
  exact P.h0_twist n

theorem chapter11_projective_line_h1_formula
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier]
    (P : Chapter11ProjectiveLineData k C) (n : ℤ) :
    chapter11H1Finrank C (P.twist n) = Int.toNat (max (-n - 1) 0) := by
  exact P.h1_twist n

/-- The projective-line formulas realize all terms of the divisor form of
Riemann--Roch. -/
theorem chapter11_projective_line_realizes_riemann_roch_terms
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier]
    (P : Chapter11ProjectiveLineData k C) (n : ℤ) :
    chapter11EulerCharacteristicOfLineBundle C (P.twist n) = n + 1 := by
  sorry

/-! ### Genus one and higher genus -/

def Chapter11HasNonzeroSection {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    (L : Chapter11LineBundle C.carrier) : Prop :=
  ∃ s : Chapter11H0 C L, s ≠ 0

theorem chapter11_genus_one_canonical_bundle_degree_zero
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    (hgenus : C.genus = 1)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier]
    [Chapter11EffectiveDecompositionTheory C]
    [Chapter11EffectiveCartierTwistSequenceTheory C]
    [Chapter11DualizingSheafTheory C.carrier]
    [Chapter11CohomologyIsomorphismTheory C.carrier C.structureMap]
    [Chapter11ConnectedGlobalSections C]
    [Chapter11EulerCharacteristicTheory C.carrier C.structureMap]
    [Chapter11SerreDualityTheory C]
    (K : Chapter11CanonicalDivisor C) :
    chapter11Degree (chapter11CanonicalBundle (X := C.carrier)) = 0 := by
  sorry

theorem chapter11_genus_one_canonical_bundle_has_nonzero_section
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    (hgenus : C.genus = 1)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier]
    [Chapter11DualizingSheafTheory C.carrier]
    [Chapter11CohomologyIsomorphismTheory C.carrier C.structureMap]
    [Chapter11ConnectedGlobalSections C]
    [Chapter11SerreDualityTheory C] :
    Chapter11HasNonzeroSection C
      (chapter11CanonicalBundle (X := C.carrier)) := by
  sorry

theorem chapter11_genus_one_canonical_bundle_is_trivial
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    (hgenus : C.genus = 1)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier]
    [Chapter11SectionZeroDivisorTheory C]
    [Chapter11DualizingSheafTheory C.carrier]
    (hdegree : chapter11Degree (chapter11CanonicalBundle (X := C.carrier)) = 0)
    (hsection : Chapter11HasNonzeroSection C
      (chapter11CanonicalBundle (X := C.carrier))) :
    chapter11LineBundleTrivial
      (chapter11CanonicalBundle (X := C.carrier)) := by
  sorry

/-- The canonical linear system is the family of nonzero canonical sections. -/
def chapter11CanonicalLinearSystem {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11DualizingSheafTheory C.carrier] : Set
      (Chapter11H0 C (chapter11CanonicalBundle (X := C.carrier))) :=
  {s | s ≠ 0}

theorem chapter11_canonical_sections_define_canonical_linear_system
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11DualizingSheafTheory C.carrier]
    (s : Chapter11H0 C (chapter11CanonicalBundle (X := C.carrier))) :
    s ∈ chapter11CanonicalLinearSystem C ↔ s ≠ 0 := by
  rfl

theorem chapter11_canonical_bundle_has_positive_degree_for_genus_at_least_two
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier]
    [Chapter11DualizingSheafTheory C.carrier]
    (hgenus : 2 ≤ C.genus)
    (hdegree : chapter11Degree (chapter11CanonicalBundle (X := C.carrier)) =
      2 * (C.genus : ℤ) - 2) :
    0 < chapter11Degree (chapter11CanonicalBundle (X := C.carrier)) := by
  sorry

/-! ### Global generation and very ampleness -/

theorem chapter11_evaluation_surjective_of_degree_ge_two_genus
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier]
    [Chapter11DualizingSheafTheory C.carrier]
    [Chapter11SerreDualityTheory C]
    [Chapter11GeometricBaseChangeTheory C]
    [Chapter11FiberTheory C]
    [Chapter11PointTwistTheory C]
    [Chapter11PointEvaluationTheory C]
    (L : Chapter11LineBundle C.carrier)
    (hcanonicalDegree :
      chapter11Degree (chapter11CanonicalBundle (X := C.carrier)) =
        2 * (C.genus : ℤ) - 2)
    (hnegative : ∀ (p : Chapter11GeometricPoint C)
      (M : Chapter11LineBundle (chapter11GeometricBaseChange C p)),
      chapter11Degree M < 0 →
        chapter11GeometricCohomologyFinrank C p M 0 = 0)
    (hdegree : 2 * (C.genus : ℤ) ≤ chapter11Degree L)
    (p : Chapter11GeometricPoint C) :
    Function.Surjective (chapter11EvaluationMap C L p) := by
  sorry

theorem chapter11_line_bundle_globally_generated_of_degree_ge_two_genus
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier]
    [Chapter11DualizingSheafTheory C.carrier]
    [Chapter11SerreDualityTheory C]
    [Chapter11GeometricBaseChangeTheory C]
    [Chapter11FiberTheory C]
    [Chapter11PointTwistTheory C]
    [Chapter11PointEvaluationTheory C]
    (L : Chapter11LineBundle C.carrier)
    (hcanonicalDegree :
      chapter11Degree (chapter11CanonicalBundle (X := C.carrier)) =
        2 * (C.genus : ℤ) - 2)
    (hnegative : ∀ (p : Chapter11GeometricPoint C)
      (M : Chapter11LineBundle (chapter11GeometricBaseChange C p)),
      chapter11Degree M < 0 →
        chapter11GeometricCohomologyFinrank C p M 0 = 0)
    (hdegree : 2 * (C.genus : ℤ) ≤ chapter11Degree L) :
    chapter11GloballyGenerated C L := by
  sorry

theorem chapter11_line_bundle_base_field_criterion_of_degree_ge_two_genus_plus_one
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier]
    [Chapter11DualizingSheafTheory C.carrier]
    [Chapter11SerreDualityTheory C]
    [Chapter11GeometricBaseChangeTheory C]
    [Chapter11FiberTheory C]
    [Chapter11PointTwistTheory C]
    [Chapter11PointEvaluationTheory C]
    [Chapter11LengthTwoRestrictionTheory C]
    [Chapter11LengthTwoTwistTheory C]
    (L : Chapter11LineBundle C.carrier)
    (hcanonicalDegree :
      chapter11Degree (chapter11CanonicalBundle (X := C.carrier)) =
        2 * (C.genus : ℤ) - 2)
    (hnegative : ∀ (p : Chapter11GeometricPoint C)
      (M : Chapter11LineBundle (chapter11GeometricBaseChange C p)),
      chapter11Degree M < 0 →
        chapter11GeometricCohomologyFinrank C p M 0 = 0)
    (hdegree : 2 * (C.genus : ℤ) + 1 ≤ chapter11Degree L) :
    chapter11BaseFieldGenerationAndLengthTwoSeparation C L := by
  sorry

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter11
