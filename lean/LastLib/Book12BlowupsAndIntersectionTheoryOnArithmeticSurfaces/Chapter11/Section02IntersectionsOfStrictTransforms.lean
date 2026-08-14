import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter11.Dependencies

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter11

noncomputable section

classical

open AlgebraicGeometry CategoryTheory
open scoped BigOperators

universe u v

/-! ### 11.2 Intersections of strict transforms -/

/-- The total-transform formula extends linearly from prime Cartier curves to
all signed Cartier divisors.  This is the reusable bridge behind (11.5). -/
theorem chapter11_total_transform_eq_strict_plus_exceptional
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (b : Chapter11PointBlowup p)
    (D : Chapter11Divisor X) :
    chapter11TotalTransform b D =
      chapter11StrictTransformDivisor b D +
        chapter11DivisorMultiplicity D p • chapter11ExceptionalDivisor b := by
  sorry

/-- Projection for two total transforms, with both sides in the chosen
numerical intersection context. -/
theorem chapter11_total_transform_intersection_formula
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (b : Chapter11PointBlowup p)
    (P : Chapter11PointBlowupProjectionData b)
    (D G : Chapter11Divisor X)
    (hscope : P.source.scope ∧ P.target.scope) :
    P.target.pairing (chapter11TotalTransform b D)
        (chapter11TotalTransform b G) =
      P.source.pairing D G := by
  sorry

/-- The strict-transform intersection formula (11.5). -/
theorem chapter11_strict_transform_intersection_formula
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (b : Chapter11PointBlowup p)
    (P : Chapter11PointBlowupProjectionData b)
    (D G : Chapter11Divisor X)
    (hscope : P.source.scope ∧ P.target.scope) :
    P.target.pairing (chapter11StrictTransformDivisor b D)
        (chapter11StrictTransformDivisor b G) =
      P.source.pairing D G -
        chapter11DivisorMultiplicity D p *
          chapter11DivisorMultiplicity G p *
            (chapter11ResidueDegree p : ℤ) := by
  sorry

/-- The local separation formula (11.6).  The explicit
`source_no_common`/`strict_no_common` fields are the proper-intersection
hypotheses inherited from the length definition in Chapter 7. -/
theorem chapter11_local_intersection_separation
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (b : Chapter11PointBlowup p)
    [Chapter11LocalIntersectionTheory X]
    [Chapter11LocalIntersectionTheory b.target]
    (D G : Chapter11Divisor X)
    (F : Chapter11ExceptionalContactData b D G) :
    chapter11LocalIntersection D G F.source_no_common p =
      chapter11DivisorMultiplicity D p *
          chapter11DivisorMultiplicity G p +
        chapter11ExceptionalContactContribution F := by
  sorry

/-- A named alias emphasizing that (11.6) separates the first-order contact
from the remaining infinitely-near contact. -/
theorem chapter11_separation_theorem
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (b : Chapter11PointBlowup p)
    [Chapter11LocalIntersectionTheory X]
    [Chapter11LocalIntersectionTheory b.target]
    (D G : Chapter11Divisor X)
    (F : Chapter11ExceptionalContactData b D G) :
    chapter11LocalIntersection D G F.source_no_common p =
      chapter11DivisorMultiplicity D p *
          chapter11DivisorMultiplicity G p +
        chapter11ExceptionalContactContribution F := by
  exact chapter11_local_intersection_separation b D G F

/-- Taking `D = G` in a numerical global or vertical context gives (11.7). -/
theorem chapter11_strict_self_intersection_formula
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (b : Chapter11PointBlowup p)
    (P : Chapter11PointBlowupProjectionData b)
    (D : Chapter11Divisor X)
    (hscope : P.source.scope ∧ P.target.scope) :
    P.target.pairing (chapter11StrictTransformDivisor b D)
        (chapter11StrictTransformDivisor b D) =
      P.source.pairing D D -
        chapter11DivisorMultiplicity D p *
          chapter11DivisorMultiplicity D p *
            (chapter11ResidueDegree p : ℤ) := by
  sorry

/-- The curve-specialized form of (11.7), with the source notation
`m = m_x(D)` visible. -/
theorem chapter11_curve_strict_self_intersection_formula
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (b : Chapter11PointBlowup p)
    (P : Chapter11PointBlowupProjectionData b)
    (D : Chapter11CartierCurve X)
    (hscope : P.source.scope ∧ P.target.scope) :
    P.target.pairing
        (chapter11StrictTransformDivisor b (chapter11CurveAsDivisor D))
        (chapter11StrictTransformDivisor b (chapter11CurveAsDivisor D)) =
      P.source.pairing (chapter11CurveAsDivisor D)
          (chapter11CurveAsDivisor D) -
        (D.multiplicity p : ℤ) * (D.multiplicity p : ℤ) *
          (chapter11ResidueDegree p : ℤ) := by
  sorry

/-- If a Cartier curve is smooth at the center, the multiplicity in (11.1)
is one. -/
theorem chapter11_smooth_curve_multiplicity_one
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    (D : Chapter11CartierCurve X)
    (p : Chapter11SurfacePoint X)
    (hmem : chapter11PointLiesOnCurve D p)
    (hsmooth : D.smoothAt p) :
    D.multiplicity p = 1 := by
  exact D.multiplicity_one_of_smoothAt p hmem hsmooth

/-- Away from the center, the strict transform is the pullback and the
self-intersection is unchanged. -/
theorem chapter11_strict_transform_unchanged_off_center
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (b : Chapter11PointBlowup p)
    (D : Chapter11CartierCurve X)
    (hnotmem : ¬ chapter11PointLiesOnCurve D p) :
    D.multiplicity p = 0 ∧
      chapter11TotalTransform b (chapter11CurveAsDivisor D) =
        chapter11StrictTransformDivisor b (chapter11CurveAsDivisor D) := by
  sorry

theorem chapter11_self_intersection_unchanged_off_center
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (b : Chapter11PointBlowup p)
    (P : Chapter11PointBlowupProjectionData b)
    (D : Chapter11CartierCurve X)
    (hnotmem : ¬ chapter11PointLiesOnCurve D p)
    (hscope : P.source.scope ∧ P.target.scope) :
    P.target.pairing
        (chapter11StrictTransformDivisor b (chapter11CurveAsDivisor D))
        (chapter11StrictTransformDivisor b (chapter11CurveAsDivisor D)) =
      P.source.pairing (chapter11CurveAsDivisor D)
        (chapter11CurveAsDivisor D) := by
  sorry

/-! ### The tangent-pair example -/

/-- Book-facing data for two smooth curves tangent to order `r` at a rational
point.  The local contact order is kept as the canonical local-intersection
assertion, while the resolution theorem below supplies the successive
unit-multiplicity blowups. -/
structure Chapter11TangentPair
    {S : Chapter11ArithmeticBase}
    (X : Chapter11ArithmeticSurface S)
    [Chapter11LocalIntersectionTheory X] where
  D G : Chapter11CartierCurve X
  point : Chapter11SurfacePoint X
  rational_point : chapter11ResidueDegree point = 1
  D_smooth : D.smoothAt point
  G_smooth : G.smoothAt point
  D_mem : chapter11PointLiesOnCurve D point
  G_mem : chapter11PointLiesOnCurve G point
  no_common :
    chapter11NoCommonComponent
      (chapter11CurveAsDivisor D) (chapter11CurveAsDivisor G)
  tangentOrder : ℕ
  contact_order :
    chapter11LocalIntersection
      (chapter11CurveAsDivisor D)
      (chapter11CurveAsDivisor G)
      no_common point = tangentOrder

theorem chapter11_tangent_pair_intersection_is_order
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    [Chapter11LocalIntersectionTheory X]
    (T : Chapter11TangentPair X) :
    chapter11LocalIntersection
        (chapter11CurveAsDivisor T.D)
        (chapter11CurveAsDivisor T.G)
        T.no_common T.point = T.tangentOrder := by
  exact T.contact_order

/- LOCAL_DEPENDENCY_GUESS: existence of the iterated tangent-point sequence
is supplied by the local chart calculation in the preceding blowup chapters;
the abstract API records the exact conclusions used by this example. -/
structure Chapter11TangentPairResolution
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    [Chapter11LocalIntersectionTheory X]
    (T : Chapter11TangentPair X) where
  sequence : Chapter11PointBlowupSequence S
  initial_stage : sequence.stage 0 = X
  initial_point : Prop
  length_eq_order : sequence.length = T.tangentOrder
  unit_multiplicity_at_each_center : Prop
  final_strict_transforms_disjoint : Prop

theorem chapter11_tangent_pair_successive_blowups_separate
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    [Chapter11LocalIntersectionTheory X]
    (T : Chapter11TangentPair X) :
    Nonempty (Chapter11TangentPairResolution T) := by
  sorry

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter11
