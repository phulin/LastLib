import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.LinearAlgebra.Dimension.Finite
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter11.Dependencies

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter12

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter11
open scoped BigOperators

universe u v

/-!
Shared interfaces for Chapter 12.

The pinned project already supplies schemes, residue fields, proper and flat
morphisms, sheaves of modules, and the Book 9 line-bundle interface.  It does
not yet package regular arithmetic surfaces, arbitrary Cartier divisors,
relative dualizing lines, or surface intersection pairings.  The records
below keep those missing geometric interfaces explicit while using canonical
scheme and sheaf objects for the data that is available.
-/

/-! ### Arithmetic surfaces and closed fibers -/

structure Chapter12ArithmeticSurface where
  base : Scheme.{u}
  carrier : Scheme.{u}
  structureMap : carrier ⟶ base
  base_excellent : Prop
  base_connected : Prop
  base_dedekind : Prop
  integral : Prop
  regular : Prop
  proper : IsProper structureMap
  flat : Flat structureMap
  relativeDimensionOne : Prop
  fibersMayBeNonreduced : Prop
  genericFiberSmooth : Prop
  genericFiberGeometricallyConnected : Prop

structure Chapter12ClosedPoint (X : Chapter12ArithmeticSurface) where
  point : X.base
  closed : IsClosed ({point} : Set X.base)

abbrev Chapter12ResidueField {X : Chapter12ArithmeticSurface}
    (s : Chapter12ClosedPoint X) : Type u :=
  X.base.residueField s.point

/-! ### Cartier divisors and line-bundle operations -/

/- LOCAL_DEPENDENCY_GUESS: the pinned snapshot has effective Cartier ideals and
line bundles but no arbitrary Cartier-divisor object carrying its associated
line bundle.  This wrapper is the smallest book-facing interface needed by
the canonical and intersection formulas below. -/
structure Chapter12CartierDivisor (X : Chapter12ArithmeticSurface)
    [Chapter11PicardTheory X.carrier] where
  lineBundle : Chapter11LineBundle X.carrier
  cartier : Prop

def chapter12ZeroDivisor (X : Chapter12ArithmeticSurface)
    [Chapter11PicardTheory X.carrier] : Chapter12CartierDivisor X where
  lineBundle := chapter11StructureSheafLineBundle X.carrier
  cartier := by sorry

def chapter12DivisorAdd {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    (D E : Chapter12CartierDivisor X) : Chapter12CartierDivisor X where
  lineBundle := chapter11Tensor D.lineBundle E.lineBundle
  cartier := by sorry

def chapter12DivisorNeg {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    (D : Chapter12CartierDivisor X) : Chapter12CartierDivisor X where
  lineBundle := chapter11Dual D.lineBundle
  cartier := by sorry

def chapter12DivisorSub {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    (D E : Chapter12CartierDivisor X) : Chapter12CartierDivisor X :=
  chapter12DivisorAdd D (chapter12DivisorNeg E)

@[ext]
theorem chapter12_cartierDivisor_ext {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    {D E : Chapter12CartierDivisor X}
    (hlineBundle : D.lineBundle = E.lineBundle) : D = E := by
  cases D
  cases E
  cases hlineBundle
  rfl

def chapter12DivisorNatMul {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    (D : Chapter12CartierDivisor X) : ℕ → Chapter12CartierDivisor X
  | 0 => chapter12ZeroDivisor X
  | n + 1 => chapter12DivisorAdd (chapter12DivisorNatMul D n) D

@[simp]
theorem chapter12_divisorNatMul_zero {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] (D : Chapter12CartierDivisor X) :
    chapter12DivisorNatMul D 0 = chapter12ZeroDivisor X :=
  rfl

@[simp]
theorem chapter12_divisorNatMul_succ {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] (D : Chapter12CartierDivisor X) (n : ℕ) :
    chapter12DivisorNatMul D (n + 1) =
      chapter12DivisorAdd (chapter12DivisorNatMul D n) D :=
  rfl

def chapter12PullbackLineBundle {X Y : Scheme.{u}}
    (f : Y ⟶ X) (L : Chapter11LineBundle X) : Chapter11LineBundle Y :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.chapter09PullbackLineBundle
    f L

def chapter12PullbackDivisor {X Y : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter11PicardTheory Y.carrier]
    (f : Y.carrier ⟶ X.carrier) (D : Chapter12CartierDivisor X) :
    Chapter12CartierDivisor Y where
  lineBundle := chapter12PullbackLineBundle f D.lineBundle
  cartier := by sorry

def chapter12DivisorLinearEquiv {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    (D E : Chapter12CartierDivisor X) : Prop :=
  chapter11LineBundleIsomorphic D.lineBundle E.lineBundle

theorem chapter12_divisorLinearEquiv_refl {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] (D : Chapter12CartierDivisor X) :
    chapter12DivisorLinearEquiv D D := by
  exact chapter11_lineBundleIsomorphic_refl D.lineBundle

theorem chapter12_divisorLinearEquiv_symm {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    {D E : Chapter12CartierDivisor X}
    (h : chapter12DivisorLinearEquiv D E) :
    chapter12DivisorLinearEquiv E D := by
  exact chapter11LineBundleIsomorphic_symm h

theorem chapter12_divisorLinearEquiv_trans {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    {D E F : Chapter12CartierDivisor X}
    (hDE : chapter12DivisorLinearEquiv D E)
    (hEF : chapter12DivisorLinearEquiv E F) :
    chapter12DivisorLinearEquiv D F := by
  exact chapter11_lineBundle_isomorphic_trans hDE hEF

/- LOCAL_DEPENDENCY_GUESS: rational functions and the principal-divisor
relation are not yet connected to the pinned Cartier line-bundle wrapper. -/
class Chapter12PrincipalDivisorTheory (X : Chapter12ArithmeticSurface)
    [Chapter11PicardTheory X.carrier] where
  principalDifference : Chapter12CartierDivisor X →
    Chapter12CartierDivisor X → Prop
  principalDifference_refl : ∀ D, principalDifference D D
  principalDifference_symm : ∀ {D E},
    principalDifference D E → principalDifference E D
  principalDifference_trans : ∀ {D E F},
    principalDifference D E → principalDifference E F → principalDifference D F
  principalDifference_implies_linearEquiv : ∀ {D E},
    principalDifference D E → chapter12DivisorLinearEquiv D E

structure Chapter12VerticalCurve (X : Chapter12ArithmeticSurface)
    (s : Chapter12ClosedPoint X)
    [Chapter11PicardTheory X.carrier] where
  carrier : Scheme.{u}
  inclusion : carrier ⟶ X.carrier
  divisor : Chapter12CartierDivisor X
  integral : Prop
  codimensionOne : Prop
  effectiveCartier : Prop
  supportedOver : Prop
  properOverResidueField : Prop
  constantFieldFiniteOverResidueField : Prop

structure Chapter12Curve (X : Chapter12ArithmeticSurface)
    [Chapter11PicardTheory X.carrier] where
  carrier : Scheme.{u}
  inclusion : carrier ⟶ X.carrier
  divisor : Chapter12CartierDivisor X
  integral : Prop
  codimensionOne : Prop
  effectiveCartier : Prop
  proper : Prop
  vertical : Prop

def Chapter12VerticalCurve.toChapter12Curve
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    {s : Chapter12ClosedPoint X}
    (C : Chapter12VerticalCurve X s) : Chapter12Curve X where
  carrier := C.carrier
  inclusion := C.inclusion
  divisor := C.divisor
  integral := C.integral
  codimensionOne := C.codimensionOne
  effectiveCartier := C.effectiveCartier
  proper := C.properOverResidueField
  vertical := C.supportedOver

/- LOCAL_DEPENDENCY_GUESS: the numerical degree of a restricted line bundle
and its compatibility with the surface pairing are not exposed by the
pinned sheaf API.  This class records only that missing numerical interface. -/
class Chapter12IntersectionTheory (X : Chapter12ArithmeticSurface)
    [Chapter11PicardTheory X.carrier] where
  degree : ∀ (C : Chapter12Curve X), Chapter11LineBundle C.carrier → ℤ
  pairing : Chapter12CartierDivisor X → Chapter12Curve X → ℤ
  pairing_eq_degree_restriction :
    ∀ D C, pairing D C =
      degree C (chapter12PullbackLineBundle C.inclusion D.lineBundle)
  pairing_add_left : ∀ D E C,
    pairing (chapter12DivisorAdd D E) C = pairing D C + pairing E C
  pairing_neg_left : ∀ D C,
    pairing (chapter12DivisorNeg D) C = -pairing D C
  pairing_linearEquiv : ∀ {D E} C,
    chapter12DivisorLinearEquiv D E → pairing D C = pairing E C
  curve_pairing_symmetric : ∀ C D,
    pairing C.divisor D = pairing D.divisor C

def chapter12DegreeOnCurve {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter12IntersectionTheory X]
    (C : Chapter12Curve X) (L : Chapter11LineBundle C.carrier) : ℤ :=
  Chapter12IntersectionTheory.degree C L

def chapter12Intersection {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter12IntersectionTheory X]
    (D : Chapter12CartierDivisor X) (C : Chapter12Curve X) : ℤ :=
  Chapter12IntersectionTheory.pairing D C

def chapter12SelfIntersection {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter12IntersectionTheory X]
    (C : Chapter12Curve X) : ℤ :=
  chapter12Intersection C.divisor C

theorem chapter12_intersection_eq_degree_restriction
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter12IntersectionTheory X]
    (D : Chapter12CartierDivisor X) (C : Chapter12Curve X) :
    chapter12Intersection D C =
      chapter12DegreeOnCurve C
        (chapter12PullbackLineBundle C.inclusion D.lineBundle) := by
  exact Chapter12IntersectionTheory.pairing_eq_degree_restriction D C

theorem chapter12_intersection_add_left
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter12IntersectionTheory X]
    (D E : Chapter12CartierDivisor X) (C : Chapter12Curve X) :
    chapter12Intersection (chapter12DivisorAdd D E) C =
      chapter12Intersection D C + chapter12Intersection E C := by
  exact Chapter12IntersectionTheory.pairing_add_left D E C

theorem chapter12_intersection_neg_left
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter12IntersectionTheory X]
    (D : Chapter12CartierDivisor X) (C : Chapter12Curve X) :
    chapter12Intersection (chapter12DivisorNeg D) C =
      -chapter12Intersection D C := by
  exact Chapter12IntersectionTheory.pairing_neg_left D C

theorem chapter12_intersection_sub_left
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter12IntersectionTheory X]
    (D E : Chapter12CartierDivisor X) (C : Chapter12Curve X) :
    chapter12Intersection (chapter12DivisorSub D E) C =
      chapter12Intersection D C - chapter12Intersection E C := by
  rw [chapter12DivisorSub, chapter12_intersection_add_left,
    chapter12_intersection_neg_left]
  simp [sub_eq_add_neg]

theorem chapter12_intersection_linearEquiv
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter12IntersectionTheory X]
    {D E : Chapter12CartierDivisor X} (C : Chapter12Curve X)
    (h : chapter12DivisorLinearEquiv D E) :
    chapter12Intersection D C = chapter12Intersection E C := by
  exact Chapter12IntersectionTheory.pairing_linearEquiv C h

theorem chapter12_curve_intersection_symmetric
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter12IntersectionTheory X]
    (C D : Chapter12Curve X) :
    chapter12Intersection C.divisor D =
      chapter12Intersection D.divisor C := by
  exact Chapter12IntersectionTheory.curve_pairing_symmetric C D

class Chapter12CurveEulerCharacteristicTheory
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] (C : Chapter12Curve X) where
  structureSheaf : C.carrier.Modules
  structureSheaf_identification : Prop
  eulerCharacteristic : ℤ

def chapter12EulerCharacteristic
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    (C : Chapter12Curve X)
    [Chapter12CurveEulerCharacteristicTheory C] : ℤ :=
  Chapter12CurveEulerCharacteristicTheory.eulerCharacteristic C

def chapter12ArithmeticGenus
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    (C : Chapter12Curve X)
    [Chapter12CurveEulerCharacteristicTheory C] : ℤ :=
  1 - chapter12EulerCharacteristic C

theorem chapter12_arithmetic_genus_eq_one_sub_euler_characteristic
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    (C : Chapter12Curve X)
    [Chapter12CurveEulerCharacteristicTheory C] :
    chapter12ArithmeticGenus C = 1 - chapter12EulerCharacteristic C :=
  rfl

/-! ### Point blowups and transform interfaces -/

/- LOCAL_DEPENDENCY_GUESS: the pinned tree has relative Proj and ideal-sheaf
pieces but no consolidated point-blowup record carrying the exceptional curve,
its residue degree, and the numerical transform maps. -/
structure Chapter12PointBlowup
    (X Y : Chapter12ArithmeticSurface)
    [Chapter11PicardTheory X.carrier] [Chapter11PicardTheory Y.carrier]
    [Chapter12IntersectionTheory X] [Chapter12IntersectionTheory Y]
    (s : Chapter12ClosedPoint X) where
  map : Y.carrier ⟶ X.carrier
  center : X.carrier
  centerClosed : IsClosed ({center} : Set X.carrier)
  center_over_closed_point : X.structureMap center = s.point
  sameBase : Y.base = X.base
  isBlowup : Prop
  projective : Prop
  birational : Prop
  regular : Prop
  map_over_base : Prop
  exceptional : Chapter12Curve Y
  exceptionalEffective : Prop
  exceptionalVertical : Prop
  exceptional_vertical_curve : exceptional.vertical
  exceptionalProjectiveNormalDirections : Prop
  residueDegree : ℕ
  residueDegree_is_residue_extension_degree : Prop
  exceptional_square : chapter12SelfIntersection exceptional =
    -(residueDegree : ℤ)
  pullback_orthogonal_to_exceptional : ∀ D : Chapter12CartierDivisor X,
    chapter12Intersection (chapter12PullbackDivisor map D) exceptional = 0

def chapter12BlowupDegree
    {X Y : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter11PicardTheory Y.carrier]
    [Chapter12IntersectionTheory X] [Chapter12IntersectionTheory Y]
    {s : Chapter12ClosedPoint X}
    (B : Chapter12PointBlowup X Y s) : ℕ :=
  B.residueDegree

def chapter12StrictTransformDivisor
    {X Y : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter11PicardTheory Y.carrier]
    [Chapter12IntersectionTheory X] [Chapter12IntersectionTheory Y]
    {s : Chapter12ClosedPoint X}
    (B : Chapter12PointBlowup X Y s)
    (D : Chapter12CartierDivisor X) (m : ℕ) :
    Chapter12CartierDivisor Y :=
  chapter12DivisorSub (chapter12PullbackDivisor B.map D)
    (chapter12DivisorNatMul B.exceptional.divisor m)

theorem chapter12_strict_transform_formula
    {X Y : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter11PicardTheory Y.carrier]
    [Chapter12IntersectionTheory X] [Chapter12IntersectionTheory Y]
    {s : Chapter12ClosedPoint X}
    (B : Chapter12PointBlowup X Y s)
    (D : Chapter12CartierDivisor X) (m : ℕ) :
    chapter12StrictTransformDivisor B D m =
      chapter12DivisorSub (chapter12PullbackDivisor B.map D)
        (chapter12DivisorNatMul B.exceptional.divisor m) :=
  rfl

/-! ### Relative effective divisors and constant-field bookkeeping -/

structure Chapter12RelativeEffectiveCartierDivisor
    (X : Chapter12ArithmeticSurface)
    [Chapter11PicardTheory X.carrier] where
  carrier : Scheme.{u}
  inclusion : carrier ⟶ X.carrier
  divisor : Chapter12CartierDivisor X
  effectiveCartier : Prop
  finiteFlatOverBase : Prop

structure Chapter12ConormalFactor
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    {s : Chapter12ClosedPoint X}
    (C : Chapter12VerticalCurve X s)
    [Chapter11PicardTheory C.carrier] [Chapter12IntersectionTheory X] where
  lineBundle : Chapter11LineBundle C.carrier
  identifiedWithConormal : Prop
  oneDimensionalOverResidueField : Prop
  degree_zero : chapter12DegreeOnCurve C.toChapter12Curve lineBundle = 0

structure Chapter12FiniteConstantFieldComparison
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    [Chapter12IntersectionTheory X]
    {s : Chapter12ClosedPoint X}
    (C : Chapter12VerticalCurve X s)
    [Chapter11PicardTheory C.carrier] where
  constantField : Type u
  [constantField_field : Field constantField]
  [constantField_algebra : Algebra (Chapter12ResidueField s) constantField]
  finite : FiniteDimensional (Chapter12ResidueField s) constantField
  residueDegree : ℕ
  eulerCharacteristicOverResidueField : ℤ
  eulerCharacteristicOverConstantField : ℤ
  degreeOverResidueField : Chapter11LineBundle C.carrier → ℤ
  degreeOverConstantField : Chapter11LineBundle C.carrier → ℤ
  euler_scale : eulerCharacteristicOverResidueField =
    (residueDegree : ℤ) * eulerCharacteristicOverConstantField
  degree_scale : ∀ L,
    degreeOverResidueField L = (residueDegree : ℤ) * degreeOverConstantField L

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter12
