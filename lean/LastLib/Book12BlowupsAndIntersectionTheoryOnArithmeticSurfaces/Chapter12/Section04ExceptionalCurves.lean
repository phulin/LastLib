import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter12.Section03ArithmeticGenusAndBlowup

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter12

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

/-! ### 12.4 The numerical test for exceptional curves -/

structure Chapter12RationalVerticalCurveData
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    [Chapter12IntersectionTheory X]
    {s : Chapter12ClosedPoint X}
    (E : Chapter12VerticalCurve X s)
    [Chapter11PicardTheory E.carrier]
    [Chapter12CurveEulerCharacteristicTheory E.toChapter12Curve] where
  projectiveLineOverResidueField : Prop
  rational : Prop
  arithmeticGenus_zero : chapter12ArithmeticGenus E.toChapter12Curve = 0

def chapter12NumericalExceptionalTest
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    [Chapter12IntersectionTheory X]
    (P : Chapter12RelativeLCIPresentation X)
    (K : Chapter12RelativeCanonicalDivisor P)
    (E : Chapter12Curve X)
    [Chapter12CurveEulerCharacteristicTheory E] : Prop :=
  E.vertical ∧
    chapter12ArithmeticGenus E = 0 ∧
    chapter12SelfIntersection E = -1 ∧
    chapter12Intersection K.divisor E = -1

theorem chapter12_projective_line_vertical_curve_has_genus_zero
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    [Chapter12IntersectionTheory X]
    {s : Chapter12ClosedPoint X}
    (E : Chapter12VerticalCurve X s)
    [Chapter11PicardTheory E.carrier]
    [Chapter12CurveEulerCharacteristicTheory E.toChapter12Curve]
    (R : Chapter12RationalVerticalCurveData E) :
    chapter12ArithmeticGenus E.toChapter12Curve = 0 :=
  R.arithmeticGenus_zero

theorem chapter12_rational_exceptional_curve_adjunction
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
    (hgenus : chapter12ArithmeticGenus E.toChapter12Curve = 0) :
    chapter12Intersection K.divisor E.toChapter12Curve +
        chapter12SelfIntersection E.toChapter12Curve = -2 := by
  sorry

theorem chapter12_minus_one_curve_has_canonical_intersection_minus_one
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
  sorry

theorem chapter12_minus_two_curve_has_canonical_intersection_zero
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
  sorry

/-! The inverse-blowup geometry is kept separate from the numerical test. -/

structure Chapter12GeometricExceptionalCurveData
    {X Y : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter11PicardTheory Y.carrier]
    [Chapter12IntersectionTheory X] [Chapter12IntersectionTheory Y]
    {s : Chapter12ClosedPoint X}
    (B : Chapter12PointBlowup X Y s) where
  curve : Chapter12Curve Y
  isExceptional : curve = B.exceptional
  curve_vertical : curve.vertical
  projectiveLineOverResidueField : Prop
  normalBundle : Chapter11LineBundle curve.carrier
  normalBundle_is_O_minus_one : Prop
  contraction : Prop
  contraction_is_inverse_regular_point_blowup : Prop

def chapter12GeometricExceptionalCurve
    {X Y : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter11PicardTheory Y.carrier]
    [Chapter12IntersectionTheory X] [Chapter12IntersectionTheory Y]
    {s : Chapter12ClosedPoint X}
    (B : Chapter12PointBlowup X Y s)
    (G : Chapter12GeometricExceptionalCurveData B) : Prop :=
  G.contraction_is_inverse_regular_point_blowup

theorem chapter12_geometric_exceptional_curve_has_minus_one_self_intersection
    {X Y : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter11PicardTheory Y.carrier]
    [Chapter12IntersectionTheory X] [Chapter12IntersectionTheory Y]
    {s : Chapter12ClosedPoint X}
    (B : Chapter12PointBlowup X Y s)
    (G : Chapter12GeometricExceptionalCurveData B)
    (hresidue : B.residueDegree = 1) :
    chapter12SelfIntersection G.curve = -1 := by
  sorry

theorem chapter12_geometric_exceptional_curve_has_numerical_test
    {X Y : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter11PicardTheory Y.carrier]
    [Chapter12IntersectionTheory X] [Chapter12IntersectionTheory Y]
    {s : Chapter12ClosedPoint X}
    (B : Chapter12PointBlowup X Y s)
    (G : Chapter12GeometricExceptionalCurveData B)
    [Chapter12CurveEulerCharacteristicTheory G.curve]
    (P : Chapter12RelativeLCIPresentation X)
    (Q : Chapter12RelativeLCIPresentation Y)
    (K : Chapter12RelativeCanonicalDivisor P)
    (hgenus : chapter12ArithmeticGenus G.curve = 0)
    (hresidue : B.residueDegree = 1) :
    chapter12NumericalExceptionalTest Q
      (chapter12CompatibleCanonicalDivisor B P Q K) G.curve := by
  sorry

/-! A numerical `(-1)` label does not contain the projective-line, normal
bundle, or contraction data needed for an inverse point blowup. -/

structure Chapter12ExceptionalCurveRecognitionData
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    [Chapter12IntersectionTheory X]
    (P : Chapter12RelativeLCIPresentation X)
    (K : Chapter12RelativeCanonicalDivisor P)
    (E : Chapter12Curve X)
    [Chapter12CurveEulerCharacteristicTheory E] where
  numericalTest : chapter12NumericalExceptionalTest P K E
  projectiveLineGeometry : Prop
  normalBundleGeometry : Prop
  contractionToRegularSurface : Prop
  inversePointBlowup : Prop

structure Chapter12MinusTwoChainData
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    [Chapter12IntersectionTheory X]
    (P : Chapter12RelativeLCIPresentation X)
    (K : Chapter12RelativeCanonicalDivisor P) where
  length : ℕ
  component : Fin length → Chapter12Curve X
  componentArithmeticGenus : Fin length → ℤ
  component_genus_zero : ∀ i, componentArithmeticGenus i = 0
  component_square_minus_two : ∀ i,
    chapter12SelfIntersection (component i) = -2
  chain_intersections : Prop
  rationalDoublePointResolution : Prop

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter12
