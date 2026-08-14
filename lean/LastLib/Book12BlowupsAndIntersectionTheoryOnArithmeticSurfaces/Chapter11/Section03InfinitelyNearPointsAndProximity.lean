import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter11.Dependencies

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter11

noncomputable section

classical

open AlgebraicGeometry CategoryTheory
open scoped BigOperators

universe u v

/-! ### 11.3 Infinitely near points and proximity -/

/-- The iterated intersection decomposition over the centers of a chosen
sequence of point blowups (11.8). -/
theorem chapter11_iterated_blowup_intersection_decomposition
    {S : Chapter11ArithmeticBase}
    (Q : Chapter11PointBlowupSequence S)
    [Chapter11LocalIntersectionTheory (Q.stage 0)]
    (H : Chapter11IteratedIntersectionData Q) :
    chapter11LocalIntersection H.D H.G H.source_no_common H.original_point =
      (∑ j,
        H.multiplicityD j * H.multiplicityG j *
          (H.center_degree j : ℤ)) + H.residualIntersection := by
  sorry

/-- Once the selected sequence makes the final strict transforms disjoint,
the residual term in (11.8) is zero. -/
theorem chapter11_iterated_blowup_residual_zero_of_disjoint
    {S : Chapter11ArithmeticBase}
    (Q : Chapter11PointBlowupSequence S)
    [Chapter11LocalIntersectionTheory (Q.stage 0)]
    (H : Chapter11IteratedIntersectionData Q)
    (hdisjoint : H.final_strict_transforms_disjoint) :
    H.residualIntersection = 0 := by
  sorry

/-- The creation-time exceptional square is `-d_i`, where `d_i` is the
residue degree of the center. -/
theorem chapter11_creation_square_of_exceptional_curve
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (b : Chapter11PointBlowup p)
    (I : Chapter11NumericalIntersectionContext b.target)
    (hscope : I.scope) :
    I.pairing (chapter11ExceptionalDivisor b)
        (chapter11ExceptionalDivisor b) =
      -(chapter11ResidueDegree p : ℤ) := by
  sorry

/-- If a later center lies on the strict transform of an earlier exceptional
curve, its final square is lower by the residue degree of the later center
over the base point (the specialization of (11.7)). -/
theorem chapter11_proximity_square_decrease
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (first : Chapter11PointBlowup p)
    (q : Chapter11SurfacePoint first.target)
    (later : Chapter11PointBlowup q)
    (P : Chapter11ProximityData first q later)
    (hscope : P.before.scope ∧ P.after.scope) :
    P.after.pairing
        (chapter11CurveAsDivisor (later.strictTransform P.oldComponent))
        (chapter11CurveAsDivisor (later.strictTransform P.oldComponent)) =
      P.before.pairing (chapter11CurveAsDivisor P.oldComponent)
          (chapter11CurveAsDivisor P.oldComponent) -
        (chapter11ResidueDegree q : ℤ) := by
  sorry

/-- The two components through a later center each lose one base-residue
degree of self-intersection. -/
theorem chapter11_double_proximity_square_decrease_first
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (first : Chapter11PointBlowup p)
    (q : Chapter11SurfacePoint first.target)
    (later : Chapter11PointBlowup q)
    (P : Chapter11DoubleProximityData first q later)
    (hscope : P.before.scope ∧ P.after.scope) :
    P.after.pairing
        (chapter11CurveAsDivisor (later.strictTransform P.component₁))
        (chapter11CurveAsDivisor (later.strictTransform P.component₁)) =
      P.before.pairing (chapter11CurveAsDivisor P.component₁)
          (chapter11CurveAsDivisor P.component₁) -
        (chapter11ResidueDegree q : ℤ) := by
  sorry

theorem chapter11_double_proximity_square_decrease_second
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (first : Chapter11PointBlowup p)
    (q : Chapter11SurfacePoint first.target)
    (later : Chapter11PointBlowup q)
    (P : Chapter11DoubleProximityData first q later)
    (hscope : P.before.scope ∧ P.after.scope) :
    P.after.pairing
        (chapter11CurveAsDivisor (later.strictTransform P.component₂))
        (chapter11CurveAsDivisor (later.strictTransform P.component₂)) =
      P.before.pairing (chapter11CurveAsDivisor P.component₂)
          (chapter11CurveAsDivisor P.component₂) -
        (chapter11ResidueDegree q : ℤ) := by
  sorry

/-- The new exceptional curve meets each of the two components through the
center. -/
theorem chapter11_double_proximity_new_exceptional_meets_both
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (first : Chapter11PointBlowup p)
    (q : Chapter11SurfacePoint first.target)
    (later : Chapter11PointBlowup q)
    (P : Chapter11DoubleProximityData first q later)
    (hscope : P.before.scope ∧ P.after.scope) :
    chapter11CurvesMeet
        (later.strictTransform P.component₁) later.exceptionalCurve ∧
      chapter11CurvesMeet
        (later.strictTransform P.component₂) later.exceptionalCurve := by
  sorry

/-- The square-decrease theorem shows that a creation-time `-1` label need not
remain `-1` on the final surface. -/
theorem chapter11_creation_label_changes_after_later_blowup
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (first : Chapter11PointBlowup p)
    (q : Chapter11SurfacePoint first.target)
    (later : Chapter11PointBlowup q)
    (P : Chapter11ProximityData first q later)
    (hcreation : P.creationSquare =
      P.before.pairing (chapter11CurveAsDivisor P.oldComponent)
        (chapter11CurveAsDivisor P.oldComponent))
    (hscope : P.before.scope ∧ P.after.scope) :
    P.after.pairing
        (chapter11CurveAsDivisor (later.strictTransform P.oldComponent))
        (chapter11CurveAsDivisor (later.strictTransform P.oldComponent)) =
      P.creationSquare - (chapter11ResidueDegree q : ℤ) := by
  sorry

/-- The final strict-transform convention for a resolution graph. -/
theorem chapter11_resolution_graph_records_final_squares
    {S : Chapter11ArithmeticBase}
    (G : Chapter11ResolutionGraph S) (i : G.component) :
    G.finalSquare i =
      G.intersectionContext.pairing
        (chapter11CurveAsDivisor (G.finalStrictTransform i))
        (chapter11CurveAsDivisor (G.finalStrictTransform i)) := by
  exact G.finalSquare_eq_intersection i

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter11
