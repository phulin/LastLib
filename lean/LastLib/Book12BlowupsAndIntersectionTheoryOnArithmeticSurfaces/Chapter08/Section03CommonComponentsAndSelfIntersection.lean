import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter08.Section02DivisorsWithVerticalCurves

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter08

noncomputable section

open scoped BigOperators

/-! ## 8.3 Common components and self-intersection -/

structure Chapter08VerticalDivisor
    (X : Chapter08ArithmeticSurface)
    (s : Chapter08BaseClosedPoint X) where
  support : Finset (Chapter08VerticalCurve X)
  coefficient : Chapter08VerticalCurve X → ℤ
  sameFiber : ∀ C ∈ support, C.basePoint = s
  support_contains_nonzero :
    ∀ C, coefficient C ≠ 0 → C ∈ support

noncomputable def chapter08VerticalDivisorAdd
    {X : Chapter08ArithmeticSurface} {s : Chapter08BaseClosedPoint X}
    (V W : Chapter08VerticalDivisor X s) : Chapter08VerticalDivisor X s :=
  by
    classical
    exact
      { support := V.support ∪ W.support
        coefficient := fun C => V.coefficient C + W.coefficient C
        sameFiber := by
          intro C hC
          rcases Finset.mem_union.mp hC with hC | hC
          · exact V.sameFiber C hC
          · exact W.sameFiber C hC
        support_contains_nonzero := by
          intro C hC
          by_cases hV : V.coefficient C = 0
          · have hW : W.coefficient C ≠ 0 := by
              intro hW
              apply hC
              simp [hV, hW]
            exact Finset.mem_union.mpr (Or.inr (W.support_contains_nonzero C hW))
          · exact Finset.mem_union.mpr (Or.inl (V.support_contains_nonzero C hV)) }

instance {X : Chapter08ArithmeticSurface} {s : Chapter08BaseClosedPoint X} :
    Add (Chapter08VerticalDivisor X s) where
  add := chapter08VerticalDivisorAdd

def chapter08VerticalDivisorIsEffective
    {X : Chapter08ArithmeticSurface} {s : Chapter08BaseClosedPoint X}
    (V : Chapter08VerticalDivisor X s) : Prop :=
  ∀ C, 0 ≤ V.coefficient C

def chapter08VerticalDivisorPairing
    {X : Chapter08ArithmeticSurface} {s : Chapter08BaseClosedPoint X}
    [∀ C : Chapter08VerticalCurve X, Chapter08CurveDegreeTheory C]
    (V W : Chapter08VerticalDivisor X s) : ℤ := by
  classical
  exact ∑ C ∈ V.support, ∑ E ∈ W.support,
    V.coefficient C * W.coefficient E *
      chapter08DivisorCurveIntersection C.asCartierDivisor E

theorem chapter08_vertical_divisor_pairing_eq_double_sum
    {X : Chapter08ArithmeticSurface} {s : Chapter08BaseClosedPoint X}
    [∀ C : Chapter08VerticalCurve X, Chapter08CurveDegreeTheory C]
    (V W : Chapter08VerticalDivisor X s) :
    chapter08VerticalDivisorPairing V W =
      ∑ C ∈ V.support, ∑ E ∈ W.support,
        V.coefficient C * W.coefficient E *
          chapter08DivisorCurveIntersection C.asCartierDivisor E := by
  rfl

theorem chapter08_vertical_curve_intersection_symmetric
    {X : Chapter08ArithmeticSurface}
    (C E : Chapter08VerticalCurve X)
    [Chapter08CurveDegreeTheory C] [Chapter08CurveDegreeTheory E] :
    chapter08DivisorCurveIntersection C.asCartierDivisor E =
      chapter08DivisorCurveIntersection E.asCartierDivisor C := by
  sorry

theorem chapter08_vertical_divisor_pairing_symmetric
    {X : Chapter08ArithmeticSurface} {s : Chapter08BaseClosedPoint X}
    [∀ C : Chapter08VerticalCurve X, Chapter08CurveDegreeTheory C]
    (V W : Chapter08VerticalDivisor X s) :
    chapter08VerticalDivisorPairing V W =
      chapter08VerticalDivisorPairing W V := by
  sorry

theorem chapter08_vertical_divisor_pairing_additive_left
    {X : Chapter08ArithmeticSurface} {s : Chapter08BaseClosedPoint X}
    [∀ C : Chapter08VerticalCurve X, Chapter08CurveDegreeTheory C]
    (V V' W : Chapter08VerticalDivisor X s) :
    chapter08VerticalDivisorPairing (V + V') W =
      chapter08VerticalDivisorPairing V W +
        chapter08VerticalDivisorPairing V' W := by
  sorry

theorem chapter08_vertical_divisor_pairing_additive_right
    {X : Chapter08ArithmeticSurface} {s : Chapter08BaseClosedPoint X}
    [∀ C : Chapter08VerticalCurve X, Chapter08CurveDegreeTheory C]
    (V W W' : Chapter08VerticalDivisor X s) :
    chapter08VerticalDivisorPairing V (W + W') =
      chapter08VerticalDivisorPairing V W +
        chapter08VerticalDivisorPairing V W' := by
  sorry

theorem chapter08_principal_divisor_restriction_isomorphic_structureSheaf
    {X : Chapter08ArithmeticSurface}
    (f : Chapter08PrincipalDivisorData X)
    (C : Chapter08VerticalCurve X) :
    chapter08LineBundleIsomorphic
      (chapter08DivisorLineBundleRestriction f.divisor C)
      (chapter08StructureSheafLineBundle C.prime.carrier) := by
  sorry

theorem chapter08_principal_divisor_intersection_with_vertical_curve_zero
    {X : Chapter08ArithmeticSurface}
    (f : Chapter08PrincipalDivisorData X)
    (C : Chapter08VerticalCurve X)
    [Chapter08CurveDegreeTheory C] :
    chapter08DivisorCurveIntersection f.divisor C = 0 := by
  calc
    chapter08DivisorCurveIntersection f.divisor C =
        chapter08Degree C (chapter08StructureSheafLineBundle C.prime.carrier) := by
      exact Chapter08CurveDegreeTheory.degree_isomorphic
        (chapter08_principal_divisor_restriction_isomorphic_structureSheaf f C)
    _ = 0 := Chapter08CurveDegreeTheory.degree_structureSheaf

def chapter08PrincipalDivisorVerticalPairingWithCurve
    {X : Chapter08ArithmeticSurface}
    (f : Chapter08PrincipalDivisorData X) (C : Chapter08VerticalCurve X)
    [Chapter08CurveDegreeTheory C] : ℤ :=
  chapter08DivisorCurveIntersection f.divisor C

theorem chapter08_principal_divisor_vertical_pairing_is_zero
    {X : Chapter08ArithmeticSurface}
    (f : Chapter08PrincipalDivisorData X) (C : Chapter08VerticalCurve X)
    [Chapter08CurveDegreeTheory C] :
    chapter08PrincipalDivisorVerticalPairingWithCurve f C = 0 := by
  exact chapter08_principal_divisor_intersection_with_vertical_curve_zero f C

/- The formal pairing includes the diagonal terms.  This is the numerical
meaning of common components and avoids interpreting a diagonal term as a set
of points where a curve meets itself. -/
theorem chapter08_vertical_curve_selfIntersection_eq_normal_degree
    {X : Chapter08ArithmeticSurface} (C : Chapter08VerticalCurve X)
    [Chapter08CurveDegreeTheory C] :
    chapter08DivisorCurveIntersection C.asCartierDivisor C =
      chapter08Degree C (chapter08NormalBundle C) := by
  exact chapter08_curve_selfIntersection_eq_degree_normalBundle C

structure Chapter08RationalPointBlowupExceptionalCurve
    {X : Chapter08ArithmeticSurface}
    (C : Chapter08VerticalCurve X)
    [Chapter08CurveDegreeTheory C] where
  isExceptionalCurveOfRationalPointBlowup : Prop
  normalBundle_is_OminusOne : Prop
  normalBundle_degree : chapter08Degree C (chapter08NormalBundle C) = -1

theorem chapter08_rational_point_blowup_exceptional_curve_square_eq_minus_one
    {X : Chapter08ArithmeticSurface}
    {C : Chapter08VerticalCurve X}
    [Chapter08CurveDegreeTheory C]
    (E : Chapter08RationalPointBlowupExceptionalCurve C) :
    chapter08DivisorCurveIntersection C.asCartierDivisor C = -1 := by
  rw [chapter08_vertical_curve_selfIntersection_eq_normal_degree C]
  exact E.normalBundle_degree

end
end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter08
