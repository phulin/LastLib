import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter15.Dependencies

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter15

noncomputable section

open AlgebraicGeometry CategoryTheory Set
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter11
open LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter05
open LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter07
open LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter12
open LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13
open LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter14
open scoped BigOperators

universe u v

/-! ## 15.2 A calculation protocol -/

/-! The diagonal equations are kept as a standalone predicate so a calculation can
record the fiber relation before specializing to a particular matrix implementation. -/

def chapter15FiberEquation {r : ℕ}
    (m : Fin r → ℕ) (M : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) : Prop :=
  ∑ j, (m j : ℤ) * M i j = 0

theorem chapter15_fiber_equation_from_component_matrix
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (i : Fin T.r) :
    chapter15FiberEquation T.multiplicity (chapter13IntersectionMatrix T) i := by
  sorry

theorem chapter15_fiber_multiplicity_vector_is_in_matrix_kernel
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)) :
    chapter13MatrixKernel (chapter13IntersectionMatrix T)
      (chapter13FiberMultiplicityVector T) := by
  exact chapter13_multiplicity_vector_in_kernel T

theorem chapter15_component_matrix_is_symmetric
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)) :
    ∀ i j, chapter13IntersectionMatrix T i j =
      chapter13IntersectionMatrix T j i := by
  exact chapter13_intersection_matrix_symmetric T

/-! A transverse point has local number one, so its global contribution is the
residue degree rather than an unweighted one. -/

def chapter15TransverseContribution (residueDegree : ℕ) : ℤ :=
  (1 : ℤ) * (residueDegree : ℤ)

theorem chapter15_transverse_contribution_is_residue_degree
    (residueDegree : ℕ) :
    chapter15TransverseContribution residueDegree = (residueDegree : ℤ) := by
  simp [chapter15TransverseContribution]

def chapter15ProperLocalContribution
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (C D : Chapter15LocalEffectiveCartierCurve A)
    (hproper : Chapter07ProperIntersectionAt C D)
    (residueDegree : ℕ) : ℤ :=
  chapter15ProperLocalIntersectionContribution C D hproper residueDegree

theorem chapter15_proper_local_contribution_is_length_times_residue_degree
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (C D : Chapter15LocalEffectiveCartierCurve A)
    (hproper : Chapter07ProperIntersectionAt C D)
    (residueDegree : ℕ) :
    chapter15ProperLocalContribution C D hproper residueDegree =
      (Chapter07LocalIntersectionNumber C D : ℤ) * (residueDegree : ℤ) := by
  rfl

/-! ### Adjunction sign checks -/

def chapter15AdjunctionEquation
    (arithmeticGenus canonicalIntersection selfIntersection : ℤ) : Prop :=
  2 * arithmeticGenus - 2 = canonicalIntersection + selfIntersection

def chapter15RationalMinusOneAdjunctionTest
    (arithmeticGenus canonicalIntersection selfIntersection : ℤ) : Prop :=
  arithmeticGenus = 0 ∧ canonicalIntersection = -1 ∧ selfIntersection = -1

def chapter15RationalMinusTwoAdjunctionTest
    (arithmeticGenus canonicalIntersection selfIntersection : ℤ) : Prop :=
  arithmeticGenus = 0 ∧ canonicalIntersection = 0 ∧ selfIntersection = -2

theorem chapter15_rational_minus_one_curve_has_canonical_intersection_minus_one
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    [Chapter12IntersectionTheory X]
    {s : Chapter12ClosedPoint X}
    (P : Chapter12RelativeLCIPresentation X)
    (K : Chapter12RelativeCanonicalDivisor P)
    (E : Chapter12VerticalCurve X s)
    [Chapter11PicardTheory E.carrier]
    [Chapter12CurveEulerCharacteristicTheory E.toChapter12Curve]
    (N : Chapter12ConormalFactor E)
    (A : Chapter12VerticalAdjunctionData P E N)
    (hgenus : chapter12ArithmeticGenus E.toChapter12Curve = 0)
    (hsquare : chapter12SelfIntersection E.toChapter12Curve = -1) :
    chapter12Intersection K.divisor E.toChapter12Curve = -1 := by
  exact chapter12_minus_one_curve_has_canonical_intersection_minus_one
    P K E N A hgenus hsquare

theorem chapter15_rational_minus_two_curve_has_canonical_intersection_zero
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    [Chapter12IntersectionTheory X]
    {s : Chapter12ClosedPoint X}
    (P : Chapter12RelativeLCIPresentation X)
    (K : Chapter12RelativeCanonicalDivisor P)
    (E : Chapter12VerticalCurve X s)
    [Chapter11PicardTheory E.carrier]
    [Chapter12CurveEulerCharacteristicTheory E.toChapter12Curve]
    (N : Chapter12ConormalFactor E)
    (A : Chapter12VerticalAdjunctionData P E N)
    (hgenus : chapter12ArithmeticGenus E.toChapter12Curve = 0)
    (hsquare : chapter12SelfIntersection E.toChapter12Curve = -2) :
    chapter12Intersection K.divisor E.toChapter12Curve = 0 := by
  exact chapter12_minus_two_curve_has_canonical_intersection_zero
    P K E N A hgenus hsquare

/-! ### Degree-zero vectors and normalization -/

theorem chapter15_degree_zero_component_vector_is_balanced
    {r : ℕ} {F : Chapter14FiberMatrix r}
    (D : Chapter14HorizontalDivisor F) :
    ∑ i, F.multiplicity i * D.componentIntersections i = 0 := by
  exact chapter14_equation_14_1 D

theorem chapter15_weighted_normalized_correction_exists_unique
    {r : ℕ} (F : Chapter14FiberMatrix r)
    (D : Chapter14HorizontalDivisor F) :
    ∃! v : Chapter14RationalVerticalDivisor F,
      chapter14Balanced F
        (fun i => (D.componentIntersections i : ℚ)) v ∧
        chapter14WeightedNormalization v := by
  exact chapter14_weighted_normalization_exists_unique F D

theorem chapter15_chosen_component_normalized_correction_exists_unique
    {r : ℕ} (F : Chapter14FiberMatrix r)
    (D : Chapter14HorizontalDivisor F) (i₀ : Fin r) :
    ∃! v : Chapter14RationalVerticalDivisor F,
      chapter14Balanced F
        (fun i => (D.componentIntersections i : ℚ)) v ∧
        chapter14ChosenComponentNormalization i₀ v := by
  exact chapter14_chosen_component_normalization_exists_unique F D i₀

theorem chapter15_balancing_solutions_are_unique_modulo_the_full_fiber
    {r : ℕ} {F : Chapter14FiberMatrix r}
    {D : Chapter14HorizontalDivisor F}
    {v w : Chapter14RationalVerticalDivisor F}
    (hv : chapter14Balanced F
      (fun i => (D.componentIntersections i : ℚ)) v)
    (hw : chapter14Balanced F
      (fun i => (D.componentIntersections i : ℚ)) w) :
    chapter14RationallyEquivalentModuloFiber F v w := by
  exact chapter14_vertical_correction_unique_mod_fiber hv hw

theorem chapter15_correction_pairing_is_rational
    {r : ℕ} {F : Chapter14FiberMatrix r}
    (I : Chapter14LocalIntersectionData F)
    (D G : Chapter14HorizontalDivisor F)
    (hgeneric : I.genericDisjoint D G)
    (v : Chapter14RationalVerticalDivisor F) :
    ∃ q : ℚ, chapter14CorrectedLocalPairing I D G hgeneric v = q := by
  exact ⟨chapter14CorrectedLocalPairing I D G hgeneric v, rfl⟩

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter15
