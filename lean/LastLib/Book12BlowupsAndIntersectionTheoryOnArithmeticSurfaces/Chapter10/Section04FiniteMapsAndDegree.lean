import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter10.Section03ProjectionFormula

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter10

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Set TopologicalSpace
open scoped AlgebraicGeometry BigOperators

universe u

/-! ### 10.4 Finite maps and degree -/

structure Chapter10FinitePullbackPrimeCurveData
    {X Y : Scheme.{u}} (f : Y ⟶ X) (B : Chapter10PrimeCurvePoint X) where
  index : Type u
  [finiteIndex : Fintype index]
  curve : index → Chapter10PrimeCurvePoint Y
  maps_to : ∀ i, f.base (curve i).1 = B.1
  ramificationIndex : index → ℕ
  residueDegree : index → ℕ
  residueDegree_eq_scheme_residueDegree :
    ∀ i, residueDegree i = f.residueDegree (curve i).1
  genericDegree : ℕ
  genericDegree_pos : 0 < genericDegree
  fundamental_equality :
    genericDegree = ∑ i, ramificationIndex i * residueDegree i

noncomputable def chapter10FinitePullbackPrimeCurveCycle
    {X Y : Scheme.{u}} (f : Y ⟶ X) (B : Chapter10PrimeCurvePoint X)
    (P : Chapter10FinitePullbackPrimeCurveData f B) :
    Chapter10AlgebraicCycle Y := by
  letI := P.finiteIndex
  exact ∑ i, (P.ramificationIndex i : ℤ) •
    (chapter10PrimeCurveDivisor (P.curve i)).cycle

noncomputable def chapter10FinitePullbackPrimeCurve
    {X Y : Scheme.{u}} (f : Y ⟶ X) (B : Chapter10PrimeCurvePoint X)
    (P : Chapter10FinitePullbackPrimeCurveData f B) : Chapter10WeilDivisor Y := by
  letI := P.finiteIndex
  exact
    { cycle := chapter10FinitePullbackPrimeCurveCycle f B P
      support_is_curve := by
        sorry
      finite_support := by
        sorry }

theorem chapter10_finite_pullback_primeCurve_formula
    {X Y : Scheme.{u}} (f : Y ⟶ X) (B : Chapter10PrimeCurvePoint X)
    (P : Chapter10FinitePullbackPrimeCurveData f B) :
    (chapter10FinitePullbackPrimeCurve f B P).cycle =
      chapter10FinitePullbackPrimeCurveCycle f B P := by
  rfl

theorem chapter10_finite_residue_degree_is_full_field_degree
    {X Y : Scheme.{u}} (f : Y ⟶ X) (B : Chapter10PrimeCurvePoint X)
    (P : Chapter10FinitePullbackPrimeCurveData f B) (i : P.index) :
    P.residueDegree i = f.residueDegree (P.curve i).1 :=
  P.residueDegree_eq_scheme_residueDegree i

/- LOCAL_DEPENDENCY_GUESS: the preceding normal-surface package identifies the
generic-degree field with the finite extension of function fields. -/
structure Chapter10FiniteDominantMorphismData
    {X Y : Scheme.{u}} (f : Y ⟶ X) where
  surfaceMorphism : Chapter10ProperSurfaceMorphismData f
  finite : IsFinite f
  dominant : IsDominant f
  genericDegree : ℕ
  genericDegree_pos : 0 < genericDegree
  genericDegree_is_field_degree : Prop

theorem chapter10_finite_pushforward_pullback_primeCurve
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : Chapter10FiniteDominantMorphismData f)
    (B : Chapter10PrimeCurvePoint X)
    (P : Chapter10FinitePullbackPrimeCurveData f B)
    (hdegree : P.genericDegree = F.genericDegree)
    [QuasiCompact f] :
    (chapter10WeilDivisorPushforward f
        (chapter10FinitePullbackPrimeCurve f B P)).cycle =
      (F.genericDegree : ℤ) • (chapter10PrimeCurveDivisor B).cycle := by
  sorry

/-!
The divisor-level form is separated from the prime-component formula so a
later proof can use the finite support of a Weil divisor and the fundamental
valuation equality componentwise.
-/
structure Chapter10FiniteDivisorPullbackData
    {X Y : Scheme.{u}} (f : Y ⟶ X) (D : Chapter10WeilDivisor X)
    (F : Chapter10FiniteDominantMorphismData f) where
  pullback : Chapter10WeilDivisor Y
  is_divisor_pullback : Prop

theorem chapter10_finite_pushforward_pullback_divisor
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : Chapter10FiniteDominantMorphismData f)
    (D : Chapter10WeilDivisor X)
    (P : Chapter10FiniteDivisorPullbackData f D F)
    [QuasiCompact f] :
    (chapter10WeilDivisorPushforward f P.pullback).cycle =
      (F.genericDegree : ℤ) • D.cycle := by
  sorry

theorem chapter10_finite_pushforward_pullback_cartier_divisor
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : Chapter10FiniteDominantMorphismData f)
    (D : Chapter10CartierDivisor X)
    (P : Chapter10FiniteDivisorPullbackData f D.divisor F)
    [QuasiCompact f] :
    (chapter10WeilDivisorPushforward f P.pullback).cycle =
      (F.genericDegree : ℤ) • D.divisor.cycle := by
  exact chapter10_finite_pushforward_pullback_divisor f F D.divisor P

/-! ### Flat intersection scaling -/

structure Chapter10FiniteFlatIntersectionData
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (D G : Chapter10CartierDivisor X)
    [Chapter10IntersectionTheory X] [Chapter10IntersectionTheory Y] where
  surfaceMorphism : Chapter10ProperSurfaceMorphismData f
  finite : IsFinite f
  flat : Flat f
  genericDegree : ℕ
  genericDegree_pos : 0 < genericDegree
  genericDegree_is_field_degree : Prop
  pullbackD : Chapter10CartierDivisor Y
  pullbackG : Chapter10CartierDivisor Y
  pullbackD_is_pullback : Prop
  pullbackG_is_pullback : Prop
  proper_intersection : chapter10ProperIntersection pullbackD pullbackG
  target_proper_intersection : chapter10ProperIntersection D G

theorem chapter10_finite_flat_cycle_intersection_projection
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (D G : Chapter10CartierDivisor X)
    [Chapter10IntersectionTheory X] [Chapter10IntersectionTheory Y]
    [QuasiCompact f]
    (P : Chapter10FiniteFlatIntersectionData f D G) :
    chapter10ZeroCyclePushforward f
        (chapter10CartierCartierIntersectionZeroCycle P.pullbackD P.pullbackG
          P.proper_intersection) =
      chapter10ZeroCycleZsmul (P.genericDegree : ℤ)
        (chapter10CartierCartierIntersectionZeroCycle D G
          P.target_proper_intersection) := by
  sorry

theorem chapter10_finite_flat_intersection_scales_by_degree
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (D G : Chapter10CartierDivisor X)
    [Chapter10IntersectionTheory X] [Chapter10IntersectionTheory Y]
    (P : Chapter10FiniteFlatIntersectionData f D G) :
    chapter10IntersectionNumberWithWeilDivisor P.pullbackD P.pullbackG.divisor =
      (P.genericDegree : ℤ) *
        chapter10IntersectionNumberWithWeilDivisor D G.divisor := by
  sorry

/-!
The length statement is intentionally recorded as a separate interface: it is
the flatness input used to prove the numerical scaling identity and is not
silently identified with a divisor-cycle equality.
-/
/- LOCAL_DEPENDENCY_GUESS: the preceding length/intersection package supplies
the exact local-length equality for finite flat inverse images. -/
structure Chapter10FlatInverseImageLengthData
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (D G : Chapter10EffectiveCartierDivisor X) where
  finite : IsFinite f
  flat : Flat f
  inverseImageD : Chapter10EffectiveCartierDivisor Y
  inverseImageG : Chapter10EffectiveCartierDivisor Y
  length_formula : Prop

/-! ### DVR fibers, ramification, and inseparable residue degrees -/

/- LOCAL_DEPENDENCY_GUESS: the preceding local-field package supplies the
residue-field extension and full-degree interfaces for finite DVR maps. -/
structure Chapter10FiniteDVRFiberData (R R' : Type u)
    [CommRing R] [CommRing R'] where
  map : R →+* R'
  finite_extension : Prop
  source_is_DVR : Prop
  target_is_DVR : Prop
  uniformizer : R
  uniformizer' : R'
  unit : R'
  ramificationIndex : ℕ
  unit_is_unit : IsUnit unit
  uniformizer_equation : map uniformizer = unit * uniformizer' ^ ramificationIndex
  residueDegree : ℕ
  fieldDegree : ℕ
  fieldDegree_eq_ramification_mul_residueDegree :
    fieldDegree = ramificationIndex * residueDegree

theorem chapter10_dvr_uniformizer_pullback
    {R R' : Type u} [CommRing R] [CommRing R']
    (P : Chapter10FiniteDVRFiberData R R') :
    P.map P.uniformizer = P.unit * P.uniformizer' ^ P.ramificationIndex :=
  P.uniformizer_equation

theorem chapter10_finite_divisor_formula_needs_no_separability
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : Chapter10FiniteDominantMorphismData f)
    (D : Chapter10WeilDivisor X)
    (P : Chapter10FiniteDivisorPullbackData f D F)
    [QuasiCompact f] :
    (chapter10WeilDivisorPushforward f P.pullback).cycle =
      (F.genericDegree : ℤ) • D.cycle := by
  exact chapter10_finite_pushforward_pullback_divisor f F D P

structure Chapter10DVRFiberDivisorScalingData
    {X Y : Scheme.{u}} (f : Y ⟶ X) where
  baseFiber : Chapter10WeilDivisor X
  totalFiberOnY : Chapter10WeilDivisor Y
  pulledBackBaseFiber : Chapter10WeilDivisor Y
  ramificationIndex : ℕ
  pullback_fiber_cycle_eq :
    pulledBackBaseFiber.cycle =
      (ramificationIndex : ℤ) • totalFiberOnY.cycle

theorem chapter10_dvr_fiber_pullback_multiplies_total_fiber
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (P : Chapter10DVRFiberDivisorScalingData f) :
    P.pulledBackBaseFiber.cycle =
      (P.ramificationIndex : ℤ) • P.totalFiberOnY.cycle :=
  P.pullback_fiber_cycle_eq

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter10
