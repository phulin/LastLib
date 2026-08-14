import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter01.Section01FromModelsToComparisons

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter01

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter05
open scoped AlgebraicGeometry BigOperators

universe u v

/-! ## 1.2. The two dimensions in an arithmetic surface -/

/-- A vertical prime curve presented as a proper regular integral curve over a field. -/
structure Chapter01VerticalComponentCurve
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    (C : Chapter01Curve X.carrier)
    (s : B.carrier) where
  curve : Chapter05ProperRegularIntegralCurve (B.carrier.residueField s)
  basePoint_closed : IsClosed ({s} : Set B.carrier)
  carrier_eq : curve.carrier = C.closedSubscheme.subscheme
  lies_over :
    ∀ y : C.closedSubscheme.subscheme,
      X.structureMap (C.closedSubscheme.subschemeι y) = s

/- LOCAL_DEPENDENCY_GUESS: the component-to-proper-curve identification is
the standard properness/dimension argument for a vertical codimension-one
subscheme of a regular arithmetic surface; the pinned scheme API does not
bundle it in the required residue-field form. -/
theorem chapter01_vertical_component_has_proper_curve_realization
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    (C : Chapter01Curve X.carrier)
    (hC : chapter01CurveIsVertical C) :
    ∃ s : B.carrier, IsClosed ({s} : Set B.carrier) ∧
      s ≠ chapter01GenericPoint B ∧
      Nonempty (Chapter01VerticalComponentCurve C s) := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: restriction of a divisor's Cartier line bundle to
a proper vertical curve and its degree are not combined by a single pinned
declaration.  This interface fixes the source convention
`(D ⋅ C) = deg_k O_X(D)|_C`. -/
class Chapter01VerticalIntersectionTheory
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    (X : Chapter01RegularArithmeticSurface B) where
  restrictionLineBundle :
    ∀ (_D : Chapter01Divisor X.carrier) (C : Chapter01Curve X.carrier),
      Chapter01LineBundle C.closedSubscheme.subscheme
  degree :
    ∀ (C : Chapter01Curve X.carrier),
      Chapter01LineBundle C.closedSubscheme.subscheme → ℤ
  intersection :
    ∀ (_D : Chapter01Divisor X.carrier) (C : Chapter01Curve X.carrier),
      chapter01CurveIsVertical C → ℤ
  intersection_eq_degree :
    ∀ (D : Chapter01Divisor X.carrier) (C : Chapter01Curve X.carrier)
      (hC : chapter01CurveIsVertical C),
      intersection D C hC = degree C (restrictionLineBundle D C)
  selfIntersection :
    ∀ (C : Chapter01Curve X.carrier),
      chapter01CurveIsVertical C → ℤ

def chapter01VerticalIntersection
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    [Chapter01VerticalIntersectionTheory X]
    (D : Chapter01Divisor X.carrier)
    (C : Chapter01Curve X.carrier)
    (hC : chapter01CurveIsVertical C) : ℤ :=
  Chapter01VerticalIntersectionTheory.intersection D C hC

def chapter01VerticalSelfIntersection
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    [Chapter01VerticalIntersectionTheory X]
    (C : Chapter01Curve X.carrier)
    (hC : chapter01CurveIsVertical C) : ℤ :=
  Chapter01VerticalIntersectionTheory.selfIntersection C hC

theorem chapter01_vertical_intersection_is_restriction_degree
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    [Chapter01VerticalIntersectionTheory X]
    (D : Chapter01Divisor X.carrier)
    (C : Chapter01Curve X.carrier)
    (hC : chapter01CurveIsVertical C) :
    chapter01VerticalIntersection D C hC =
      Chapter01VerticalIntersectionTheory.degree C
        (Chapter01VerticalIntersectionTheory.restrictionLineBundle D C) := by
  exact Chapter01VerticalIntersectionTheory.intersection_eq_degree D C hC

/-! ### Horizontal curves and the absence of a base-independent integer degree -/

def chapter01HorizontalCurveMap
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    (C : Chapter01Curve X.carrier) :
    C.closedSubscheme.subscheme ⟶ B.carrier :=
  C.closedSubscheme.subschemeι ≫ X.structureMap

def chapter01HorizontalCurveIsFiniteOverBase
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    (C : Chapter01Curve X.carrier) : Prop :=
  IsFinite (chapter01HorizontalCurveMap C)

/- LOCAL_DEPENDENCY_GUESS: properness plus the horizontal codimension-one
condition gives the finite morphism to the Dedekind base. -/
theorem chapter01_horizontal_curve_is_finite_over_base
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    (C : Chapter01Curve X.carrier)
    (hC : chapter01CurveIsHorizontal C) :
    chapter01HorizontalCurveIsFiniteOverBase C := by
  sorry

/-- A horizontal normal bundle is retained as a line bundle and its Picard class. -/
structure Chapter01HorizontalNormalBundleData
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    (C : Chapter01Curve X.carrier)
    (hC : chapter01CurveIsHorizontal C) where
  normalBundle : Chapter01LineBundle C.closedSubscheme.subscheme
  normalBundleClass : Chapter01LineBundleClass C.closedSubscheme.subscheme
  normalBundleClass_eq :
    normalBundleClass = chapter04LineBundleClass normalBundle

/- LOCAL_DEPENDENCY_GUESS: construction of the normal line bundle of a
Cartier prime curve from its conormal ideal is not exposed in the pinned
sheaf API in the exact form required here. -/
theorem chapter01_horizontal_curve_has_normal_bundle_class
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    (C : Chapter01Curve X.carrier)
    (hC : chapter01CurveIsHorizontal C) :
    Nonempty (Chapter01HorizontalNormalBundleData C hC) := by
  sorry

/-! ### Numerical targets -/

def chapter01ZeroCycleValuedPairing
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    [Chapter01ZeroCycleIntersectionTheory X]
    (D G : Chapter01Divisor X.carrier) : Chapter01ZeroCycle B.carrier :=
  Chapter01ZeroCycleIntersectionTheory.pairing D G

def chapter01BaseClassValuedPairing
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    [Chapter01BaseClassIntersectionTheory X]
    (D G : Chapter01Divisor X.carrier) : Chapter01LineBundleClass B.carrier :=
  Chapter01BaseClassIntersectionTheory.pairing D G

def chapter01ZeroCyclePairingAfterDegree
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    [Chapter01ZeroCycleIntersectionTheory X]
    (d : Chapter01SpecifiedDegreeMap (Chapter01ZeroCycle B.carrier))
    (D G : Chapter01Divisor X.carrier) : ℤ :=
  chapter01ApplySpecifiedDegree d (chapter01ZeroCycleValuedPairing D G)

def chapter01BaseClassPairingAfterDegree
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    [Chapter01BaseClassIntersectionTheory X]
    (d : Chapter01SpecifiedDegreeMap (Chapter01LineBundleClass B.carrier))
    (D G : Chapter01Divisor X.carrier) : ℤ :=
  chapter01ApplySpecifiedDegree d (chapter01BaseClassValuedPairing D G)

theorem chapter01_global_pairing_integer_requires_specified_degree_map
    {A : Type u} (d : Chapter01SpecifiedDegreeMap A) (a : A) :
    chapter01ApplySpecifiedDegree d a = d.degree a := by
  rfl

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter01
