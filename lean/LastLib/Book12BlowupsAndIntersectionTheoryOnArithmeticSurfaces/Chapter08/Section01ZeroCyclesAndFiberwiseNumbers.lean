import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter08.Dependencies

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter08

noncomputable section

open scoped BigOperators

/-! ## 8.1 Zero-cycles and fiberwise numbers -/

def chapter08IntersectionZeroCycle
    {X : Chapter08ArithmeticSurface}
    [Chapter08LocalIntersectionTheory X]
    {D G : Chapter08CartierDivisor X}
    (I : Chapter08ProperIntersectionWitness D G) : Chapter08ZeroCycle X := by
  classical
  exact ∑ x ∈ I.support,
    (chapter08LocalIntersectionMultiplicity D G x : ℤ) • chapter08PointCycle x

theorem chapter08_finite_intersection_of_generic_disjoint
    {X : Chapter08ArithmeticSurface}
    [Chapter08LocalIntersectionTheory X]
    (D G : Chapter08CartierDivisor X)
    (hcommon : chapter08NoCommonIrreducibleComponent D G)
    (hgeneric : chapter08HorizontalGenericDisjoint D G) :
    Nonempty (Chapter08ProperIntersectionWitness D G) := by
  rcases Chapter08LocalIntersectionTheory.finite_intersection_support
      D G hcommon hgeneric with ⟨support, hsupport⟩
  exact ⟨{
    support := support
    support_contains_nonzero := hsupport
    noCommonComponent := hcommon
    horizontalGenericDisjoint := hgeneric }⟩

theorem chapter08_intersection_zeroCycle_eq_sum_local_multiplicities
    {X : Chapter08ArithmeticSurface}
    [Chapter08LocalIntersectionTheory X]
    {D G : Chapter08CartierDivisor X}
    (I : Chapter08ProperIntersectionWitness D G) :
    chapter08IntersectionZeroCycle I =
      ∑ x ∈ I.support,
        (chapter08LocalIntersectionMultiplicity D G x : ℤ) • chapter08PointCycle x := by
  rfl

def chapter08FiberwiseIntersection
    {X : Chapter08ArithmeticSurface}
    [Chapter08LocalIntersectionTheory X]
    {D G : Chapter08CartierDivisor X}
    (I : Chapter08ProperIntersectionWitness D G)
    (s : Chapter08BaseClosedPoint X) : ℤ := by
  classical
  exact ∑ x ∈ I.support.filter (chapter08PointInFiber X s),
    (chapter08LocalIntersectionMultiplicity D G x : ℤ) * (x.residueDegree : ℤ)

theorem chapter08_fiberwise_intersection_eq_weighted_sum
    {X : Chapter08ArithmeticSurface}
    [Chapter08LocalIntersectionTheory X]
    {D G : Chapter08CartierDivisor X}
    (I : Chapter08ProperIntersectionWitness D G)
    (s : Chapter08BaseClosedPoint X) :
    chapter08FiberwiseIntersection I s =
      (by
        classical
        exact ∑ x ∈ I.support.filter (chapter08PointInFiber X s),
          (chapter08LocalIntersectionMultiplicity D G x : ℤ) *
            (x.residueDegree : ℤ)) := by
  rfl

theorem chapter08_fiberwise_intersection_is_an_integer
    {X : Chapter08ArithmeticSurface}
    [Chapter08LocalIntersectionTheory X]
    {D G : Chapter08CartierDivisor X}
    (I : Chapter08ProperIntersectionWitness D G)
    (s : Chapter08BaseClosedPoint X) :
    ∃ n : ℤ, chapter08FiberwiseIntersection I s = n := by
  exact ⟨chapter08FiberwiseIntersection I s, rfl⟩

theorem chapter08_fiberwise_intersection_nonnegative
    {X : Chapter08ArithmeticSurface}
    [Chapter08LocalIntersectionTheory X]
    {D G : Chapter08CartierDivisor X}
    (I : Chapter08ProperIntersectionWitness D G)
    (hD : chapter08CartierDivisorIsEffective D)
    (hG : chapter08CartierDivisorIsEffective G)
    (s : Chapter08BaseClosedPoint X) :
    0 ≤ chapter08FiberwiseIntersection I s := by
  sorry

def chapter08FiberwiseIntersectionDivisor
    {X : Chapter08ArithmeticSurface}
    [Chapter08LocalIntersectionTheory X]
    {D G : Chapter08CartierDivisor X}
    (I : Chapter08ProperIntersectionWitness D G) : Chapter08BaseDivisor X := by
  classical
  exact ∑ x ∈ I.support,
    Finsupp.single x.basePoint
      ((chapter08LocalIntersectionMultiplicity D G x : ℤ) * (x.residueDegree : ℤ))

theorem chapter08_fiberwise_intersection_divisor_apply
    {X : Chapter08ArithmeticSurface}
    [Chapter08LocalIntersectionTheory X]
    {D G : Chapter08CartierDivisor X}
    (I : Chapter08ProperIntersectionWitness D G)
    (s : Chapter08BaseClosedPoint X) :
    chapter08FiberwiseIntersectionDivisor I s =
      chapter08FiberwiseIntersection I s := by
  sorry

theorem chapter08_only_finitely_many_fibers_contribute
    {X : Chapter08ArithmeticSurface}
    [Chapter08LocalIntersectionTheory X]
    {D G : Chapter08CartierDivisor X}
    (I : Chapter08ProperIntersectionWitness D G)
    (hX : chapter08ProperOverBase X) :
    ∃ t : Finset (Chapter08BaseClosedPoint X),
      ∀ s, chapter08FiberwiseIntersection I s ≠ 0 → s ∈ t := by
  classical
  exact ⟨(chapter08FiberwiseIntersectionDivisor I).support, by
    intro s hs
    sorry⟩

/- The hypotheses used in the finite construction are kept visible as a
book-facing predicate.  It is intentionally stronger than the mere existence
of a finite formal sum: generic disjointness is what removes horizontal
intersection data from the vertical calculation. -/
def chapter08FiniteVerticalIntersectionSituation
    {X : Chapter08ArithmeticSurface}
    (D G : Chapter08CartierDivisor X) : Prop :=
  chapter08NoCommonIrreducibleComponent D G ∧
    chapter08HorizontalGenericDisjoint D G

structure Chapter08HorizontalIntersectionData
    {X : Chapter08ArithmeticSurface}
    (D G : Chapter08CartierDivisor X) where
  divisorComponent : Chapter08PrimeCurve X
  divisorComponent_mem : D.coefficient divisorComponent ≠ 0
  otherComponent : Chapter08PrimeCurve X
  otherComponent_mem : G.coefficient otherComponent ≠ 0
  divisorComponent_horizontal : divisorComponent.horizontal
  otherComponent_horizontal : otherComponent.horizontal
  genericPoint_eq :
    divisorComponent.genericPoint = otherComponent.genericPoint

theorem chapter08_generic_intersection_has_horizontal_closure_data
    {X : Chapter08ArithmeticSurface}
    {D G : Chapter08CartierDivisor X}
    (h : chapter08HorizontalGenericIntersection D G) :
    Nonempty (Chapter08HorizontalIntersectionData D G) := by
  rcases h with ⟨C, hC, E, hE, hCh, hEh, hgeneric⟩
  exact ⟨{
    divisorComponent := C
    divisorComponent_mem := hC
    otherComponent := E
    otherComponent_mem := hE
    divisorComponent_horizontal := hCh
    otherComponent_horizontal := hEh
    genericPoint_eq := hgeneric }⟩

theorem chapter08_relative_curve_distinct_horizontal_components_generic_disjoint
    {X : Chapter08ArithmeticSurface}
    (hX : X.relativeDimensionOne)
    (C E : Chapter08PrimeCurve X)
    (hC : C.horizontal) (hE : E.horizontal)
    (hCirr : C.irreducible) (hEirr : E.irreducible)
    (hneq : C ≠ E) :
    C.genericPoint ≠ E.genericPoint := by
  sorry

def chapter08GlobalIntersectionNumber
    {X : Chapter08ArithmeticSurface}
    [Chapter08LocalIntersectionTheory X]
    {D G : Chapter08CartierDivisor X}
    (I : Chapter08ProperIntersectionWitness D G)
    (d : Chapter08BaseDegreeChoice X) : ℤ :=
  chapter08FiberwiseDegree d (chapter08FiberwiseIntersectionDivisor I)

theorem chapter08_global_intersection_number_is_degree_of_base_divisor
    {X : Chapter08ArithmeticSurface}
    [Chapter08LocalIntersectionTheory X]
    {D G : Chapter08CartierDivisor X}
    (I : Chapter08ProperIntersectionWitness D G)
    (d : Chapter08BaseDegreeChoice X) :
    chapter08GlobalIntersectionNumber I d =
      d.degree (chapter08FiberwiseIntersectionDivisor I) := by
  rfl

end
end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter08
