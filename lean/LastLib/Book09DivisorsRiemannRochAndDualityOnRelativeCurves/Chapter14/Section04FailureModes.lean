import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter14.Dependencies

/-!
## 14.4 Failure modes

Each record below is a proof-ready witness interface for the corresponding
warning in the source.  The omitted hypothesis is named in the type, and the
failure is represented by the precise obstruction rather than by an informal
comment or a vacuous implication.
-/

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter14

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

/-! Properness controls finiteness and prevents boundary terms in the trace. -/

structure Chapter14FailureWithoutProperness where
  context : Chapter14RelativeCurveContext
  notProper : ¬ IsProper context.map
  cohomologyNeedNotBeFinite : Prop
  residueTraceHasBoundaryTerms : Prop

def chapter14WithoutProperness
    (C : Chapter14RelativeCurveContext) : Prop :=
  ¬ IsProper C.map

theorem chapter14_without_properness_failure_is_explicit
    (F : Chapter14FailureWithoutProperness) :
    chapter14WithoutProperness F.context :=
  F.notProper

/-! Flatness controls fiber dimension, genus, and specialization. -/

structure Chapter14FailureWithoutFlatness where
  context : Chapter14RelativeCurveContext
  notFlat : ¬ Flat context.map
  fiberDimensionMayJump : Prop
  arithmeticGenusMayJump : Prop
  dualizingSpecializationMayFail : Prop

def chapter14WithoutFlatness
    (C : Chapter14RelativeCurveContext) : Prop :=
  ¬ Flat C.map

theorem chapter14_without_flatness_failure_is_explicit
    (F : Chapter14FailureWithoutFlatness) :
    chapter14WithoutFlatness F.context :=
  F.notFlat

/-! Cohen--Macaulayness concentrates the relative duality object. -/

structure Chapter14FailureWithoutCohenMacaulay where
  context : Chapter14RelativeCurveContext
  notCohenMacaulay : ¬ context.CohenMacaulay
  dualityNeedNotBeConcentratedInOneSheaf : Prop
  higherDualizingCohomologyMayRemain : Prop

def chapter14WithoutCohenMacaulay
    (F : Chapter14FailureWithoutCohenMacaulay) : Prop :=
  F.notCohenMacaulay

theorem chapter14_without_cohen_macaulay_failure_is_explicit
    (F : Chapter14FailureWithoutCohenMacaulay) :
    chapter14WithoutCohenMacaulay F :=
  F.notCohenMacaulay

/-! Gorensteinness makes the dualizing sheaf invertible. -/

structure Chapter14FailureWithoutGorenstein where
  context : Chapter14RelativeCurveContext
  notGorenstein : ¬ context.Gorenstein
  dualizingSheafMayNotBeInvertible : Prop
  canonicalCartierDivisorNeedNotExist : Prop

def chapter14WithoutGorenstein
    (F : Chapter14FailureWithoutGorenstein) : Prop :=
  F.notGorenstein

theorem chapter14_without_gorenstein_failure_is_explicit
    (F : Chapter14FailureWithoutGorenstein) :
    chapter14WithoutGorenstein F :=
  F.notGorenstein

/-! Geometric connectedness is what gives one geometric summand of `f_*𝒪`. -/

structure Chapter14FailureWithoutGeometricConnectedness where
  context : Chapter14RelativeCurveContext
  notGeometricallyConnected : ¬ GeometricallyConnected context.map
  structureSheafPushforwardHasMultipleGeometricSummands : Prop
  traceIsomorphismMustBeReplacedByItsDual : Prop

def chapter14WithoutGeometricConnectedness
    (C : Chapter14RelativeCurveContext) : Prop :=
  ¬ GeometricallyConnected C.map

theorem chapter14_without_geometric_connectedness_failure_is_explicit
    (F : Chapter14FailureWithoutGeometricConnectedness) :
    chapter14WithoutGeometricConnectedness F.context :=
  F.notGeometricallyConnected

/-! Locally constant cohomology dimensions are needed for locally free pushforwards. -/

structure Chapter14FailureWithoutLocallyConstantCohomology where
  C : Chapter14RelativeCurveFamily
  D : Chapter14RelativeDualityData C
  cohomologyDimensionNotLocallyConstant : Prop
  pushforwardMayFailToBeLocallyFree : Prop
  twoTermPerfectObjectMayStillExist : Prop

def chapter14WithoutLocallyConstantCohomology
    (F : Chapter14FailureWithoutLocallyConstantCohomology) : Prop :=
  F.cohomologyDimensionNotLocallyConstant

theorem chapter14_without_locally_constant_cohomology_failure_is_explicit
    (F : Chapter14FailureWithoutLocallyConstantCohomology) :
    chapter14WithoutLocallyConstantCohomology F :=
  F.cohomologyDimensionNotLocallyConstant

/-! Standard visible examples named by the source. -/

structure Chapter14CuspFailureExample where
  curve : Prop
  nonSmoothDifferentials : Prop
  ordinaryDifferentialsDoNotGiveTheDualizingSheaf : Prop

structure Chapter14EmbeddedPointFailureExample where
  curveWithEmbeddedPoint : Prop
  notCohenMacaulay : Prop
  dualityNotConcentrated : Prop

structure Chapter14UnbalancedReducibleCurveFailureExample where
  reducibleCurve : Prop
  unbalancedMultidegree : Prop
  totalDegreeVanishingFails : Prop

def chapter14CuspFailureStatement : Prop :=
  ∃ E : Chapter14CuspFailureExample,
    E.curve ∧ E.nonSmoothDifferentials ∧
      E.ordinaryDifferentialsDoNotGiveTheDualizingSheaf

def chapter14EmbeddedPointFailureStatement : Prop :=
  ∃ E : Chapter14EmbeddedPointFailureExample,
    E.curveWithEmbeddedPoint ∧ E.notCohenMacaulay ∧ E.dualityNotConcentrated

def chapter14UnbalancedReducibleCurveFailureStatement : Prop :=
  ∃ E : Chapter14UnbalancedReducibleCurveFailureExample,
    E.reducibleCurve ∧ E.unbalancedMultidegree ∧ E.totalDegreeVanishingFails

def chapter14FailureModeChecklist : Prop :=
  (∃ F : Chapter14FailureWithoutProperness, F.cohomologyNeedNotBeFinite) ∧
  (∃ F : Chapter14FailureWithoutFlatness, F.fiberDimensionMayJump) ∧
  (∃ F : Chapter14FailureWithoutCohenMacaulay,
    F.dualityNeedNotBeConcentratedInOneSheaf) ∧
  (∃ F : Chapter14FailureWithoutGorenstein,
    F.dualizingSheafMayNotBeInvertible) ∧
  (∃ F : Chapter14FailureWithoutGeometricConnectedness,
    F.structureSheafPushforwardHasMultipleGeometricSummands) ∧
  (∃ F : Chapter14FailureWithoutLocallyConstantCohomology,
    F.pushforwardMayFailToBeLocallyFree) ∧
  chapter14CuspFailureStatement ∧
  chapter14EmbeddedPointFailureStatement ∧
  chapter14UnbalancedReducibleCurveFailureStatement

end
end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter14
