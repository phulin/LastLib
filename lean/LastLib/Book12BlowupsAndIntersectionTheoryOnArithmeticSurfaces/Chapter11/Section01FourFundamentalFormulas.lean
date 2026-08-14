import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter11.Dependencies

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter11

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v

/-! ### 11.1 The four fundamental formulas -/

/-- The exceptional-factor calculation for the total transform of a Cartier
curve through the center (11.1). -/
theorem chapter11_total_transform_formula
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (b : Chapter11PointBlowup p)
    (D : Chapter11CartierCurve X)
    (hmem : chapter11PointLiesOnCurve D p) :
    chapter11TotalTransform b (chapter11CurveAsDivisor D) =
      chapter11StrictTransformDivisor b (chapter11CurveAsDivisor D) +
        (D.multiplicity p : ℤ) • chapter11ExceptionalDivisor b := by
  sorry

theorem chapter11_total_transform_ideal_is_pullback
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (b : Chapter11PointBlowup p)
    (D : Chapter11CartierCurve X) :
    chapter11TotalTransformIdeal b D = D.cartierDivisor.ideal.comap b.map := by
  sorry

/-- The exceptional curve has normal-bundle degree `-d_x` (11.2). -/
theorem chapter11_exceptional_self_intersection
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (b : Chapter11PointBlowup p)
    (I : Chapter11NumericalIntersectionContext b.target)
    (N : Chapter11ExceptionalIntersectionBridge b I) :
    I.pairing (chapter11ExceptionalDivisor b)
      (chapter11ExceptionalDivisor b) =
      -(chapter11ResidueDegree p : ℤ) := by
  sorry

/-- Orthogonality of a total transform and the exceptional curve (11.3).
The projection data are the earlier proper-map projection formula specialized
to the contracted exceptional curve. -/
theorem chapter11_total_transform_exceptional_orthogonal
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (b : Chapter11PointBlowup p)
    (P : Chapter11PointBlowupProjectionData b)
    (D : Chapter11Divisor X)
    (hscope : P.source.scope ∧ P.target.scope) :
    P.target.pairing (chapter11TotalTransform b D)
      (chapter11ExceptionalDivisor b) = 0 := by
  sorry

/-- Intersecting (11.1) with the exceptional curve gives the positive tangent
cone contribution (11.4). -/
theorem chapter11_strict_transform_exceptional_intersection
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (b : Chapter11PointBlowup p)
    (P : Chapter11PointBlowupProjectionData b)
    (D : Chapter11CartierCurve X)
    (hmem : chapter11PointLiesOnCurve D p)
    (hscope : P.source.scope ∧ P.target.scope) :
    P.target.pairing
        (chapter11StrictTransformDivisor b (chapter11CurveAsDivisor D))
        (chapter11ExceptionalDivisor b) =
      (D.multiplicity p : ℤ) * chapter11ResidueDegree p := by
  sorry

/-- The compatibility equation obtained by intersecting (11.1) with `E`.
This is the displayed intermediate identity used to pass from (11.2)--(11.3)
to (11.4). -/
theorem chapter11_orthogonality_expansion
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (b : Chapter11PointBlowup p)
    (P : Chapter11PointBlowupProjectionData b)
    (D : Chapter11CartierCurve X)
    (hmem : chapter11PointLiesOnCurve D p)
    (hscope : P.source.scope ∧ P.target.scope) :
    0 =
      P.target.pairing
          (chapter11StrictTransformDivisor b (chapter11CurveAsDivisor D))
          (chapter11ExceptionalDivisor b) +
        (D.multiplicity p : ℤ) *
          P.target.pairing (chapter11ExceptionalDivisor b)
            (chapter11ExceptionalDivisor b) := by
  sorry

/-- The four formulas are available as one source-order package. -/
theorem chapter11_four_fundamental_formulas
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (b : Chapter11PointBlowup p)
    (P : Chapter11PointBlowupProjectionData b)
    (D : Chapter11CartierCurve X)
    (hmem : chapter11PointLiesOnCurve D p)
    (hscope : P.source.scope ∧ P.target.scope) :
    chapter11TotalTransform b (chapter11CurveAsDivisor D) =
          chapter11StrictTransformDivisor b (chapter11CurveAsDivisor D) +
            (D.multiplicity p : ℤ) • chapter11ExceptionalDivisor b ∧
      P.target.pairing (chapter11ExceptionalDivisor b)
          (chapter11ExceptionalDivisor b) =
        -(chapter11ResidueDegree p : ℤ) ∧
      P.target.pairing
          (chapter11TotalTransform b (chapter11CurveAsDivisor D))
          (chapter11ExceptionalDivisor b) = 0 ∧
      P.target.pairing
          (chapter11StrictTransformDivisor b (chapter11CurveAsDivisor D))
          (chapter11ExceptionalDivisor b) =
        (D.multiplicity p : ℤ) * chapter11ResidueDegree p := by
  sorry

/- The numerical scope is intentionally supplied by `P`: if `D` is vertical,
the pairing is the fiberwise degree pairing; if `D` is horizontal, only the
divisor identity and pairings against the vertical exceptional curve are used. -/

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter11
