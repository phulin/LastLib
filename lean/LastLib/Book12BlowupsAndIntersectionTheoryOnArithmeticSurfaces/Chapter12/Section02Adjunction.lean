import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter12.Section01RelativeCanonicalDivisors

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter12

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter11

universe u v

/-! ### 12.2 Adjunction -/

structure Chapter12VerticalAdjunctionData
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    [Chapter12IntersectionTheory X]
    {s : Chapter12ClosedPoint X}
    (P : Chapter12RelativeLCIPresentation X)
    (C : Chapter12VerticalCurve X s)
    [Chapter11PicardTheory C.carrier]
    [Chapter12CurveEulerCharacteristicTheory C.toChapter12Curve]
    (N : Chapter12ConormalFactor C) where
  curveDualizing : Chapter11LineBundle C.carrier
  curveDualizing_is_dualizing : Prop
  transitivity_identification : Prop
  adjunctionIso : Chapter11LineBundleIso curveDualizing
    (chapter11Tensor
      (chapter12PullbackLineBundle C.inclusion
        (chapter11Tensor P.omega C.divisor.lineBundle))
      N.lineBundle)
  curveDualizing_degree :
    chapter12DegreeOnCurve C.toChapter12Curve curveDualizing =
      -2 * chapter12EulerCharacteristic C.toChapter12Curve

def chapter12VerticalAdjunctionBundle
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    {s : Chapter12ClosedPoint X}
    (P : Chapter12RelativeLCIPresentation X)
    (C : Chapter12VerticalCurve X s)
    [Chapter11PicardTheory C.carrier] :
    Chapter11LineBundle C.carrier :=
  chapter12PullbackLineBundle C.inclusion
    (chapter11Tensor P.omega C.divisor.lineBundle)

theorem chapter12_conormal_factor_has_degree_zero
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    [Chapter12IntersectionTheory X]
    {s : Chapter12ClosedPoint X}
    (C : Chapter12VerticalCurve X s)
    [Chapter11PicardTheory C.carrier]
    (N : Chapter12ConormalFactor C) :
    chapter12DegreeOnCurve C.toChapter12Curve N.lineBundle = 0 :=
  N.degree_zero

theorem chapter12_dualizing_curve_degree_eq_neg_two_euler_characteristic
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    [Chapter12IntersectionTheory X]
    {s : Chapter12ClosedPoint X}
    (P : Chapter12RelativeLCIPresentation X)
    (C : Chapter12VerticalCurve X s)
    [Chapter11PicardTheory C.carrier]
    [Chapter12CurveEulerCharacteristicTheory C.toChapter12Curve]
    (N : Chapter12ConormalFactor C)
    (A : Chapter12VerticalAdjunctionData P C N) :
    chapter12DegreeOnCurve C.toChapter12Curve A.curveDualizing =
      -2 * chapter12EulerCharacteristic C.toChapter12Curve :=
  A.curveDualizing_degree

def chapter12_vertical_adjunction_isomorphism
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    [Chapter12IntersectionTheory X]
    {s : Chapter12ClosedPoint X}
    (P : Chapter12RelativeLCIPresentation X)
    (C : Chapter12VerticalCurve X s)
    [Chapter11PicardTheory C.carrier]
    [Chapter12CurveEulerCharacteristicTheory C.toChapter12Curve]
    (N : Chapter12ConormalFactor C)
    (A : Chapter12VerticalAdjunctionData P C N) :
    Chapter11LineBundleIso A.curveDualizing
      (chapter11Tensor (chapter12VerticalAdjunctionBundle P C) N.lineBundle) := by
  exact A.adjunctionIso

def chapter12VerticalAdjunctionFormula
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    [Chapter12IntersectionTheory X]
    {s : Chapter12ClosedPoint X}
    (P : Chapter12RelativeLCIPresentation X)
    (K : Chapter12RelativeCanonicalDivisor P)
    (C : Chapter12VerticalCurve X s)
    [Chapter12CurveEulerCharacteristicTheory C.toChapter12Curve] : Prop :=
  2 * chapter12ArithmeticGenus C.toChapter12Curve - 2 =
    chapter12Intersection K.divisor C.toChapter12Curve +
      chapter12SelfIntersection C.toChapter12Curve

theorem chapter12_vertical_adjunction_formula
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    [Chapter12IntersectionTheory X]
    {s : Chapter12ClosedPoint X}
    (P : Chapter12RelativeLCIPresentation X)
    (K : Chapter12RelativeCanonicalDivisor P)
    (C : Chapter12VerticalCurve X s)
    [Chapter11PicardTheory C.carrier]
    [Chapter12CurveEulerCharacteristicTheory C.toChapter12Curve]
    (N : Chapter12ConormalFactor C)
    (A : Chapter12VerticalAdjunctionData P C N) :
    chapter12VerticalAdjunctionFormula P K C := by
  sorry

theorem chapter12_vertical_adjunction_formula_expanded
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    [Chapter12IntersectionTheory X]
    {s : Chapter12ClosedPoint X}
    (P : Chapter12RelativeLCIPresentation X)
    (K : Chapter12RelativeCanonicalDivisor P)
    (C : Chapter12VerticalCurve X s)
    [Chapter11PicardTheory C.carrier]
    [Chapter12CurveEulerCharacteristicTheory C.toChapter12Curve]
    (N : Chapter12ConormalFactor C)
    (A : Chapter12VerticalAdjunctionData P C N) :
    2 * chapter12ArithmeticGenus C.toChapter12Curve - 2 =
      chapter12Intersection K.divisor C.toChapter12Curve +
        chapter12SelfIntersection C.toChapter12Curve := by
  exact chapter12_vertical_adjunction_formula P K C N A

/-! A vertical adjunction witness keeps the conormal factor visible.  A
uniformizer gives a trivialization only after a choice; its degree is zero
without making that choice. -/

structure Chapter12UniformizerTrivialization
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    [Chapter12IntersectionTheory X]
    {s : Chapter12ClosedPoint X}
    (D : Chapter12LocalDVRData X s)
    (C : Chapter12VerticalCurve X s)
    [Chapter11PicardTheory C.carrier]
    (N : Chapter12ConormalFactor C) where
  chosen_uniformizer : Prop
  trivializes_conormal_factor : Prop

theorem chapter12_uniformizer_trivializes_conormal_factor
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    [Chapter12IntersectionTheory X]
    {s : Chapter12ClosedPoint X}
    (D : Chapter12LocalDVRData X s)
    (C : Chapter12VerticalCurve X s)
    [Chapter11PicardTheory C.carrier]
    (N : Chapter12ConormalFactor C)
    (U : Chapter12UniformizerTrivialization D C N) :
    U.trivializes_conormal_factor :=
  by sorry

structure Chapter12RelativeAdjunctionData
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    (P : Chapter12RelativeLCIPresentation X)
    (H : Chapter12RelativeEffectiveCartierDivisor X)
    [Chapter11PicardTheory H.carrier] where
  relativeDualizing : Chapter11LineBundle H.carrier
  relativeDualizing_is_dualizing : Prop
  adjunctionIso : Chapter11LineBundleIso relativeDualizing
    (chapter12PullbackLineBundle H.inclusion
      (chapter11Tensor P.omega H.divisor.lineBundle))

def chapter12RelativeAdjunctionBundle
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    (P : Chapter12RelativeLCIPresentation X)
    (H : Chapter12RelativeEffectiveCartierDivisor X)
    [Chapter11PicardTheory H.carrier] :
    Chapter11LineBundle H.carrier :=
  chapter12PullbackLineBundle H.inclusion
    (chapter11Tensor P.omega H.divisor.lineBundle)

def chapter12_relative_effective_cartier_adjunction
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    (P : Chapter12RelativeLCIPresentation X)
    (H : Chapter12RelativeEffectiveCartierDivisor X)
    [Chapter11PicardTheory H.carrier]
    (A : Chapter12RelativeAdjunctionData P H) :
    Chapter11LineBundleIso A.relativeDualizing
      (chapter12RelativeAdjunctionBundle P H) := by
  exact A.adjunctionIso

theorem chapter12_constant_field_comparison_scales_invariants
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    [Chapter12IntersectionTheory X]
    {s : Chapter12ClosedPoint X}
    (C : Chapter12VerticalCurve X s)
    [Chapter11PicardTheory C.carrier]
    (A : Chapter12FiniteConstantFieldComparison C) :
    A.eulerCharacteristicOverResidueField =
        (A.residueDegree : ℤ) * A.eulerCharacteristicOverConstantField ∧
      ∀ L, A.degreeOverResidueField L =
        (A.residueDegree : ℤ) * A.degreeOverConstantField L := by
  exact ⟨A.euler_scale, A.degree_scale⟩

/- LOCAL_DEPENDENCY_GUESS: the correction term for adjunction on a singular
non-Gorenstein surface is not present in the pinned dualizing API. -/
structure Chapter12NonGorensteinAdjunctionCorrection
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    [Chapter12IntersectionTheory X]
    {s : Chapter12ClosedPoint X}
    (P : Chapter12RelativeLCIPresentation X)
    (K : Chapter12RelativeCanonicalDivisor P)
    (C : Chapter12VerticalCurve X s)
    [Chapter12CurveEulerCharacteristicTheory C.toChapter12Curve] where
  ambientNotGorenstein : ¬P.gorenstein
  correction : ℤ
  correctedAdjunction :
    2 * chapter12ArithmeticGenus C.toChapter12Curve - 2 =
      chapter12Intersection K.divisor C.toChapter12Curve +
        chapter12SelfIntersection C.toChapter12Curve + correction

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter12
