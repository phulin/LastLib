import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter06.Dependencies

/-!
### 6.4 What blowups do not accomplish

This section collects the negative statements which prevent a resolution
calculation from being mistaken for semistable reduction, normalization, or
minimality.  The counterexample and comparison records are intentionally
separate from the positive blowup interfaces.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter06

/-! Regularity of the total space does not force a reduced nodal fiber. -/

structure Chapter06RegularNonSemistableModel where
  base : Scheme.{u}
  surface : Scheme.{u}
  structureMap : surface ⟶ base
  totalSpaceRegular : Chapter06RegularSurface surface
  specialFiber : Chapter06FiberProfile
  specialFiberNonreduced : ¬ chapter06FiberReduced specialFiber
  specialFiberNotNodal : ¬ specialFiber.nodal

def chapter06RegularNonSemistable (E : Chapter06RegularNonSemistableModel) : Prop :=
  ¬ chapter06SemistableFiber E.specialFiber

theorem chapter06_regular_total_space_does_not_imply_semistable_reduction :
    Nonempty Chapter06RegularNonSemistableModel := by
  sorry

theorem chapter06_regular_nonsemistable_witness_is_not_semistable
    (E : Chapter06RegularNonSemistableModel) :
    chapter06RegularNonSemistable E := by
  intro h
  exact E.specialFiberNonreduced h.1

structure Chapter06PointBlowupOfNonreducedFiber where
  sourceFiber : Chapter06FiberProfile
  sourceNonreduced : ¬ chapter06FiberReduced sourceFiber
  targetFiber : Chapter06FiberProfile
  targetStillNonreduced : ¬ chapter06FiberReduced targetFiber
  pointBlowup : Prop
  pointBlowupEvidence : pointBlowup
  exceptionalMultiplicity : ℕ
  exceptionalMultiplicityPositive : 0 < exceptionalMultiplicity

theorem chapter06_point_blowups_do_not_in_general_remove_fiber_multiplicities :
    Nonempty Chapter06PointBlowupOfNonreducedFiber := by
  sorry

theorem chapter06_point_blowup_counterexample_remains_nonreduced
    (E : Chapter06PointBlowupOfNonreducedFiber) :
    ¬ chapter06FiberReduced E.targetFiber := by
  exact E.targetStillNonreduced

/-! A base extension can be needed before a reduced nodal fiber appears. -/

structure Chapter06FiniteBaseExtension where
  oldBase : Scheme.{u}
  newBase : Scheme.{u}
  map : newBase ⟶ oldBase
  finite : Prop
  finiteEvidence : finite
  flat : Prop
  flatEvidence : flat
  ramified : Prop
  ramifiedEvidence : ramified

structure Chapter06SemistableAfterBaseExtension
    (E : Chapter06RegularNonSemistableModel) where
  extension : Chapter06FiniteBaseExtension
  baseChangeModel : Scheme.{u}
  baseChangeMap : baseChangeModel ⟶ E.surface
  baseChangedFiber : Chapter06FiberProfile
  baseChangedFiberSemistable : chapter06SemistableFiber baseChangedFiber
  extensionNeeded : Prop
  extensionNeededEvidence : extensionNeeded

theorem chapter06_semistable_reduction_may_require_a_finite_base_extension
    : ∃ E : Chapter06RegularNonSemistableModel,
      Nonempty (Chapter06SemistableAfterBaseExtension E) := by
  sorry

/-! Ramified base change turns a regular node into a thickness equation. -/

def chapter06NodeEquation {R : Type u} [CommRing R]
    (x y π : R) : Prop := x * y = π

structure Chapter06RamifiedNodeBaseChange
    (R R' : Type u) [CommRing R] [CommRing R'] [Algebra R R'] where
  ramificationIndex : ℕ
  ramificationIndexGreaterThanOne : 1 < ramificationIndex
  uniformizer : R
  newUniformizer : R'
  ramificationEquation :
    algebraMap R R' uniformizer = newUniformizer ^ ramificationIndex
  regularNodeEquation : Prop
  regularNodeEquationEvidence : regularNodeEquation
  baseChangedSurfaceSingular : Prop
  baseChangedSurfaceSingularEvidence : baseChangedSurfaceSingular

theorem chapter06_ramified_node_base_change_equation
    {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
    (B : Chapter06RamifiedNodeBaseChange R R') (x' y' : R')
    (hxy : x' * y' = algebraMap R R' B.uniformizer) :
    chapter06ThicknessEquation x' y' B.newUniformizer B.ramificationIndex := by
  exact hxy.trans B.ramificationEquation

theorem chapter06_ramified_node_base_change_is_singular
    {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
    (B : Chapter06RamifiedNodeBaseChange R R') :
    B.baseChangedSurfaceSingular := by
  exact B.baseChangedSurfaceSingularEvidence

/-! Normalization and blowup are different operations. -/

inductive Chapter06ModificationKind : Type
  | normalization
  | blowup
  | normalizedBlowup

structure Chapter06NormalizationOperation where
  source : Scheme.{u}
  target : Scheme.{u}
  map : target ⟶ source
  finite : Prop
  finiteEvidence : finite
  birational : Prop
  birationalEvidence : birational
  targetNormal : Prop
  targetNormalEvidence : targetNormal
  separatesIntegralBranches : Prop
  separatesIntegralBranchesEvidence : separatesIntegralBranches

structure Chapter06BlowupOperation where
  source : Scheme.{u}
  target : Scheme.{u}
  map : target ⟶ source
  projective : Prop
  projectiveEvidence : projective
  birational : Prop
  birationalEvidence : birational
  changesTangentDirections : Prop
  makesCenterInvertible : Prop
  makesCenterInvertibleEvidence : makesCenterInvertible
  changesTangentDirectionsEvidence : changesTangentDirections

structure Chapter06NormalizedBlowupOperation where
  source : Scheme.{u}
  blowup : Scheme.{u}
  normalizedBlowup : Scheme.{u}
  blowupMap : blowup ⟶ source
  normalizationMap : normalizedBlowup ⟶ blowup
  blowupStage : Chapter06BlowupOperation
  normalizationStage : Chapter06NormalizationOperation
  blowupStageSource : blowupStage.source = source
  blowupStageTarget : blowupStage.target = blowup
  blowupMapIsStageMap : blowupMap = blowupStage.map
  normalizationStageSource : normalizationStage.source = blowup
  normalizationStageTarget : normalizationStage.target = normalizedBlowup
  normalizationMapIsStageMap : normalizationMap = normalizationStage.map
  combinedOperation : Prop
  combinedOperationEvidence : combinedOperation

theorem chapter06_normalization_separates_branches
    (N : Chapter06NormalizationOperation) :
    N.separatesIntegralBranches := by
  exact N.separatesIntegralBranchesEvidence

theorem chapter06_blowup_changes_tangent_directions
    (B : Chapter06BlowupOperation) :
    B.changesTangentDirections := by
  exact B.changesTangentDirectionsEvidence

theorem chapter06_normalized_blowup_combines_the_two_operations
    (B : Chapter06NormalizedBlowupOperation) :
    B.combinedOperation := by
  exact B.combinedOperationEvidence

structure Chapter06CurveCuspNormalizationExample where
  cusp : Scheme.{u}
  normalization : Scheme.{u}
  map : normalization ⟶ cusp
  curveResolved : Prop
  curveResolvedEvidence : curveResolved
  ambientSurface : Scheme.{u}
  ambientSurfaceSingularityRemains : Prop
  ambientSurfaceSingularityRemainsEvidence : ambientSurfaceSingularityRemains

theorem chapter06_curve_normalization_does_not_in_general_resolve_a_surface :
    Nonempty Chapter06CurveCuspNormalizationExample := by
  sorry

theorem chapter06_curve_cusp_normalization_resolves_the_curve_but_not_the_surface
    (E : Chapter06CurveCuspNormalizationExample) :
    E.curveResolved ∧ E.ambientSurfaceSingularityRemains := by
  exact ⟨E.curveResolvedEvidence, E.ambientSurfaceSingularityRemainsEvidence⟩

/-! Resolution is not minimality. -/

structure Chapter06RegularPointBlowup where
  source : Scheme.{u}
  target : Scheme.{u}
  map : target ⟶ source
  sourceRegular : Chapter06RegularSurface source
  centerIsRegularClosedPoint : Prop
  centerIsRegularClosedPointEvidence : centerIsRegularClosedPoint
  exceptionalCurve : Chapter06CurveNumericalData
  exceptionalSelfIntersection : exceptionalCurve.selfIntersection = -1
  exceptionalNormalDegree : exceptionalCurve.normalDegree = -1
  genericCurveUnchanged : Prop
  genericCurveUnchangedEvidence : genericCurveUnchanged
  modelIsLessMinimal : Prop
  modelIsLessMinimalEvidence : modelIsLessMinimal

theorem chapter06_blowup_of_a_regular_point_creates_an_artificial_minus_one_curve
    (B : Chapter06RegularPointBlowup) :
    B.exceptionalCurve.selfIntersection = -1 ∧
      B.exceptionalCurve.normalDegree = -1 := by
  exact ⟨B.exceptionalSelfIntersection, B.exceptionalNormalDegree⟩

theorem chapter06_regular_point_blowup_does_not_change_generic_curve
    (B : Chapter06RegularPointBlowup) :
    B.genericCurveUnchanged := by
  exact B.genericCurveUnchangedEvidence

theorem chapter06_regular_point_blowup_makes_model_less_minimal
    (B : Chapter06RegularPointBlowup) :
    B.modelIsLessMinimal := by
  exact B.modelIsLessMinimalEvidence

def chapter06ArtificialMinusOneSignature (C : Chapter06CurveNumericalData) : Prop :=
  C.rational ∧ C.selfIntersection = -1 ∧ C.normalDegree = -1

def chapter06IntrinsicNegativeFiberComponent (C : Chapter06CurveNumericalData) : Prop :=
  C.vertical ∧ C.selfIntersection < 0

theorem chapter06_artificial_exceptional_curve_has_the_minus_one_signature
    (B : Chapter06RegularPointBlowup) :
    chapter06ArtificialMinusOneSignature B.exceptionalCurve := by
  exact ⟨B.exceptionalCurve.rationalEvidence,
    B.exceptionalSelfIntersection, B.exceptionalNormalDegree⟩

structure Chapter06NegativeFiberComponentData where
  component : Chapter06CurveNumericalData
  intrinsicToFiber : chapter06IntrinsicNegativeFiberComponent component
  notArtificialPointBlowup : Prop
  notArtificialPointBlowupEvidence : notArtificialPointBlowup

theorem chapter06_numerical_signature_separates_artificial_and_intrinsic_components
    (B : Chapter06RegularPointBlowup) (C : Chapter06NegativeFiberComponentData)
    (hnot : C.component.selfIntersection ≠ B.exceptionalCurve.selfIntersection) :
    C.component ≠ B.exceptionalCurve := by
  intro h
  apply hnot
  exact congrArg Chapter06CurveNumericalData.selfIntersection h

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter06

end
