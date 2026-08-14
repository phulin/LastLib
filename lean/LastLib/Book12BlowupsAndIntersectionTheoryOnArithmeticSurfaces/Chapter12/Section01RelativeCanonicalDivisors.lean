import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter12.Dependencies

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter12

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter11

universe u v

/-! ### 12.1 Relative canonical divisors -/

/- LOCAL_DEPENDENCY_GUESS: the pinned lci and dualizing-sheaf APIs do not yet
package a local smooth presentation together with its determinant line. -/
structure Chapter12RelativeLCIPresentation
    (X : Chapter12ArithmeticSurface)
    [Chapter11PicardTheory X.carrier] where
  ambient : Scheme.{u}
  ambientStructureMap : ambient ⟶ X.base
  immersion : X.carrier ⟶ ambient
  factorization : immersion ≫ ambientStructureMap = X.structureMap
  ambientSmoothOverBase : Prop
  definingIdeal : X.carrier.Modules
  definingIdealRegularSequence : Prop
  conormalModule : X.carrier.Modules
  ambientDifferentials : X.carrier.Modules
  relativeDifferentials : X.carrier.Modules
  conormalInclusion : conormalModule ⟶ ambientDifferentials
  differentialProjection : ambientDifferentials ⟶ relativeDifferentials
  conormalCompZero : conormalInclusion ≫ differentialProjection = 0
  conormalInclusion_mono : Mono conormalInclusion
  differentialProjection_epi : Epi differentialProjection
  conormalExact :
    (ShortComplex.mk conormalInclusion differentialProjection
      conormalCompZero).Exact
  conormal_is_ideal_quotient : Prop
  conormalDeterminant : Chapter11LineBundle X.carrier
  differentialsDeterminant : Chapter11LineBundle X.carrier
  conormalDeterminant_identification : Prop
  differentialsDeterminant_identification : Prop
  omega : Chapter11LineBundle X.carrier
  relativeDualizingSheaf : X.carrier.Modules
  omega_is_relativeDualizingSheaf : Prop
  omega_module_identification : omega.module ≅ relativeDualizingSheaf
  determinant_formula : Chapter11LineBundleIso omega
    (chapter11Tensor (chapter11Dual conormalDeterminant)
      differentialsDeterminant)
  relativeDimensionOne : Prop
  lci : Prop
  gorenstein : Prop
  lci_base_change : Prop

def chapter12HasRelativeLCIPresentation
    (X : Chapter12ArithmeticSurface)
    [Chapter11PicardTheory X.carrier] : Prop :=
  Nonempty (Chapter12RelativeLCIPresentation X)

theorem chapter12_arithmetic_surface_is_relative_lci
    (X : Chapter12ArithmeticSurface)
    [Chapter11PicardTheory X.carrier] :
    chapter12HasRelativeLCIPresentation X := by
  sorry

structure Chapter12LocalDVRData
    (X : Chapter12ArithmeticSurface) (s : Chapter12ClosedPoint X) where
  ring : Type u
  [commRing : CommRing ring]
  [localRing : IsLocalRing ring]
  [domain : IsDomain ring]
  isDVR : Prop
  uniformizer : ring
  uniformizer_is_uniformizer : Prop
  identifies_with_stalk_localization : Prop

attribute [instance] Chapter12LocalDVRData.commRing
  Chapter12LocalDVRData.localRing Chapter12LocalDVRData.domain

def chapter12RelativeCanonicalBundle
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    (P : Chapter12RelativeLCIPresentation X) :
    Chapter11LineBundle X.carrier :=
  P.omega

/-! The determinant formula is exposed as its own theorem so later uses do not
need to unpack the presentation record. -/

def chapter12_relative_dualizing_determinant_formula
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    (P : Chapter12RelativeLCIPresentation X) :
    Chapter11LineBundleIso (chapter12RelativeCanonicalBundle P)
      (chapter11Tensor (chapter11Dual P.conormalDeterminant)
        P.differentialsDeterminant) :=
  P.determinant_formula

theorem chapter12_relative_conormal_sequence_exact
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    (P : Chapter12RelativeLCIPresentation X) :
    (ShortComplex.mk P.conormalInclusion P.differentialProjection
      P.conormalCompZero).Exact :=
  P.conormalExact

theorem chapter12_relative_dualizing_sheaf_identification
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    (P : Chapter12RelativeLCIPresentation X) :
    P.omega_is_relativeDualizingSheaf :=
  by sorry

theorem chapter12_relative_dualizing_is_line_bundle
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    (P : Chapter12RelativeLCIPresentation X) :
    P.gorenstein := by
  sorry

structure Chapter12RelativeCanonicalDivisor
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    (P : Chapter12RelativeLCIPresentation X) where
  divisor : Chapter12CartierDivisor X
  associated : Chapter11LineBundleIso divisor.lineBundle
    (chapter12RelativeCanonicalBundle P)

def chapter12_relative_canonical_divisor_associated
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    (P : Chapter12RelativeLCIPresentation X)
    (K : Chapter12RelativeCanonicalDivisor P) :
    Chapter11LineBundleIso K.divisor.lineBundle
      (chapter12RelativeCanonicalBundle P) :=
  K.associated

theorem chapter12_relative_canonical_divisors_are_principal_difference
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    [Chapter12PrincipalDivisorTheory X]
    (P : Chapter12RelativeLCIPresentation X)
    (K K' : Chapter12RelativeCanonicalDivisor P) :
    Chapter12PrincipalDivisorTheory.principalDifference K.divisor K'.divisor := by
  sorry

theorem chapter12_relative_canonical_divisor_intersection_independent
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter12IntersectionTheory X]
    [Chapter12PrincipalDivisorTheory X]
    (P : Chapter12RelativeLCIPresentation X)
    (K K' : Chapter12RelativeCanonicalDivisor P)
    (C : Chapter12Curve X) :
    chapter12Intersection K.divisor C =
      chapter12Intersection K'.divisor C := by
  apply chapter12_intersection_linearEquiv C
  exact Chapter12PrincipalDivisorTheory.principalDifference_implies_linearEquiv
    (chapter12_relative_canonical_divisors_are_principal_difference P K K')

/-! The local chart comparison fixes the sign in the blowup formula. -/

structure Chapter12BlowupCanonicalChartComparison where
  chartRing : Type u
  [chartRing_commRing : CommRing chartRing]
  localU : chartRing
  localV : chartRing
  localT : chartRing
  tau : chartRing
  tauY : chartRing
  pullbackTau : chartRing
  chart_equation : localV = localU * localT
  determinant_comparison : pullbackTau = localU * tauY
  vanishingOrder : ℕ
  vanishingOrder_eq_one : vanishingOrder = 1

attribute [instance] Chapter12BlowupCanonicalChartComparison.chartRing_commRing

theorem chapter12_blowup_chart_canonical_comparison
    (A : Chapter12BlowupCanonicalChartComparison) :
    A.pullbackTau = A.localU * A.tauY := by sorry

def chapter12_relative_dualizing_line_blowup_isomorphism
    {X Y : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter11PicardTheory Y.carrier]
    [Chapter12IntersectionTheory X] [Chapter12IntersectionTheory Y]
    {s : Chapter12ClosedPoint X}
    (B : Chapter12PointBlowup X Y s)
    (P : Chapter12RelativeLCIPresentation X)
    (Q : Chapter12RelativeLCIPresentation Y) :
    Chapter11LineBundleIso Q.omega
      (chapter11Tensor (chapter12PullbackLineBundle B.map P.omega)
        B.exceptional.divisor.lineBundle) := by
  sorry

def chapter12CanonicalBlowupFormula
    {X Y : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter11PicardTheory Y.carrier]
    [Chapter12IntersectionTheory X] [Chapter12IntersectionTheory Y]
    {s : Chapter12ClosedPoint X}
    (B : Chapter12PointBlowup X Y s)
    {P : Chapter12RelativeLCIPresentation X}
    {Q : Chapter12RelativeLCIPresentation Y}
    (K : Chapter12RelativeCanonicalDivisor P)
    (L : Chapter12RelativeCanonicalDivisor Q) : Prop :=
  chapter12DivisorLinearEquiv L.divisor
    (chapter12DivisorAdd (chapter12PullbackDivisor B.map K.divisor)
      B.exceptional.divisor)

noncomputable def chapter12CompatibleCanonicalDivisor
    {X Y : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter11PicardTheory Y.carrier]
    [Chapter12IntersectionTheory X] [Chapter12IntersectionTheory Y]
    {s : Chapter12ClosedPoint X}
    (B : Chapter12PointBlowup X Y s)
    (P : Chapter12RelativeLCIPresentation X)
    (Q : Chapter12RelativeLCIPresentation Y)
    (K : Chapter12RelativeCanonicalDivisor P) :
    Chapter12RelativeCanonicalDivisor Q where
  divisor := chapter12DivisorAdd (chapter12PullbackDivisor B.map K.divisor)
    B.exceptional.divisor
  associated := by
    sorry

theorem chapter12_relative_canonical_divisor_blowup_formula
    {X Y : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter11PicardTheory Y.carrier]
    [Chapter12IntersectionTheory X] [Chapter12IntersectionTheory Y]
    {s : Chapter12ClosedPoint X}
    (B : Chapter12PointBlowup X Y s)
    (P : Chapter12RelativeLCIPresentation X)
    (Q : Chapter12RelativeLCIPresentation Y)
    (K : Chapter12RelativeCanonicalDivisor P) :
    chapter12CanonicalBlowupFormula B K
      (chapter12CompatibleCanonicalDivisor B P Q K) := by
  exact chapter12_divisorLinearEquiv_refl _

/-! The projection formula used in the exceptional-curve calculation is
exposed independently of any particular pushforward implementation. -/

structure Chapter12ProjectionFormulaData
    {X Y : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter11PicardTheory Y.carrier]
    [Chapter12IntersectionTheory X] [Chapter12IntersectionTheory Y]
    (f : Y.carrier ⟶ X.carrier) where
  pushforwardCurve : Chapter12Curve Y → Chapter12Curve X
  pushforward_preserves_curve_properties : Prop
  projection_formula : ∀ D C,
    chapter12Intersection (chapter12PullbackDivisor f D) C =
      chapter12Intersection D (pushforwardCurve C)

theorem chapter12_projection_formula
    {X Y : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter11PicardTheory Y.carrier]
    [Chapter12IntersectionTheory X] [Chapter12IntersectionTheory Y]
    (f : Y.carrier ⟶ X.carrier)
    (P : Chapter12ProjectionFormulaData f)
    (D : Chapter12CartierDivisor X) (C : Chapter12Curve Y) :
    chapter12Intersection (chapter12PullbackDivisor f D) C =
      chapter12Intersection D (P.pushforwardCurve C) := by
  exact P.projection_formula D C

theorem chapter12_exceptional_square_over_rational_center
    {X Y : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter11PicardTheory Y.carrier]
    [Chapter12IntersectionTheory X] [Chapter12IntersectionTheory Y]
    {s : Chapter12ClosedPoint X}
    (B : Chapter12PointBlowup X Y s)
    (hresidue : B.residueDegree = 1) :
    chapter12SelfIntersection B.exceptional = -1 := by
  rw [B.exceptional_square]
  simp [hresidue]

theorem chapter12_canonical_intersection_exceptional_eq_self
    {X Y : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter11PicardTheory Y.carrier]
    [Chapter12IntersectionTheory X] [Chapter12IntersectionTheory Y]
    {s : Chapter12ClosedPoint X}
    (B : Chapter12PointBlowup X Y s)
    {P : Chapter12RelativeLCIPresentation X}
    {Q : Chapter12RelativeLCIPresentation Y}
    (K : Chapter12RelativeCanonicalDivisor P)
    (L : Chapter12RelativeCanonicalDivisor Q)
    (hformula : chapter12CanonicalBlowupFormula B K L) :
    chapter12Intersection L.divisor B.exceptional =
      chapter12SelfIntersection B.exceptional := by
  sorry

theorem chapter12_canonical_intersection_exceptional
    {X Y : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter11PicardTheory Y.carrier]
    [Chapter12IntersectionTheory X] [Chapter12IntersectionTheory Y]
    {s : Chapter12ClosedPoint X}
    (B : Chapter12PointBlowup X Y s)
    {P : Chapter12RelativeLCIPresentation X}
    {Q : Chapter12RelativeLCIPresentation Y}
    (K : Chapter12RelativeCanonicalDivisor P)
    (L : Chapter12RelativeCanonicalDivisor Q)
    (hformula : chapter12CanonicalBlowupFormula B K L) :
    chapter12Intersection L.divisor B.exceptional =
      -(chapter12BlowupDegree B : ℤ) := by
  rw [chapter12_canonical_intersection_exceptional_eq_self B K L hformula]
  exact B.exceptional_square

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter12
