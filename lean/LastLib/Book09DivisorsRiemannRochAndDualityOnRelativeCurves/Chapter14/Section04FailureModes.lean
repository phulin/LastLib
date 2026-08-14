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
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter09

noncomputable section

universe u

/-! Properness controls finiteness and prevents boundary terms in the trace. -/

structure Chapter14FailureWithoutProperness where
  context : Chapter14RelativeCurveContext
  notProper : ¬ IsProper context.map
  coefficient : context.X.Modules
  globalH0 : chapter09H coefficient 0
  globalH0_not_finite : ¬ Finite (chapter09H coefficient 0)
  boundaryTerm : chapter09H coefficient 1
  boundaryTerm_ne_zero : boundaryTerm ≠ 0

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
  fiberDimension : context.S → ℕ
  fiberDimensionJump : ∃ s t, fiberDimension s ≠ fiberDimension t
  arithmeticGenus : context.S → ℕ
  arithmeticGenusJump : ∃ s t, arithmeticGenus s ≠ arithmeticGenus t
  dualizingBeforeSpecialization : context.S.Modules
  dualizingAfterSpecialization : context.S.Modules
  dualizingSpecializationFailure :
    ¬ Nonempty (dualizingBeforeSpecialization ≅ dualizingAfterSpecialization)

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
  notCohenMacaulay : ¬ chapter09CohenMacaulay context.X
  dualityWarning : Chapter09NonCohenMacaulayDualityWarning context.X

def chapter14WithoutCohenMacaulay
    (C : Chapter14RelativeCurveContext) : Prop :=
  ¬ chapter09CohenMacaulay C.X

theorem chapter14_without_cohen_macaulay_failure_is_explicit
    (F : Chapter14FailureWithoutCohenMacaulay) :
    chapter14WithoutCohenMacaulay F.context :=
  F.notCohenMacaulay

/-! Gorensteinness makes the dualizing sheaf invertible. -/

structure Chapter14FailureWithoutGorenstein where
  context : Chapter14RelativeCurveContext
  notGorenstein : ¬ chapter09GorensteinMorphism context.map
  dualizingSheaf : context.X.Modules
  dualizingSheaf_not_invertible : ¬ chapter09IsInvertible dualizingSheaf

def chapter14WithoutGorenstein
    (C : Chapter14RelativeCurveContext) : Prop :=
  ¬ chapter09GorensteinMorphism C.map

theorem chapter14_without_gorenstein_failure_is_explicit
    (F : Chapter14FailureWithoutGorenstein) :
    chapter14WithoutGorenstein F.context :=
  F.notGorenstein

/-! Geometric connectedness is what gives one geometric summand of `f_*𝒪`. -/

structure Chapter14FailureWithoutGeometricConnectedness where
  context : Chapter14RelativeCurveContext
  notGeometricallyConnected : ¬ GeometricallyConnected context.map
  structureSheafPushforward : context.S.Modules
  nontrivialIdempotent : Γ(context.S, ⊤)
  nontrivialIdempotent_squared : nontrivialIdempotent * nontrivialIdempotent =
    nontrivialIdempotent
  nontrivialIdempotent_ne_zero : nontrivialIdempotent ≠ 0
  nontrivialIdempotent_ne_one : nontrivialIdempotent ≠ 1

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
  coefficient : C.X.Modules
  h1Dimension : C.S → ℕ
  cohomologyDimensionNotLocallyConstant :
    ¬ chapter14LocallyConstant h1Dimension
  pushforward : C.S.Modules
  pushforward_not_locally_free : ¬ chapter04FiniteLocallyFree pushforward

def chapter14WithoutLocallyConstantCohomology
    (F : Chapter14FailureWithoutLocallyConstantCohomology) : Prop :=
  ¬ chapter14LocallyConstant F.h1Dimension

theorem chapter14_without_locally_constant_cohomology_failure_is_explicit
    (F : Chapter14FailureWithoutLocallyConstantCohomology) :
    chapter14WithoutLocallyConstantCohomology F :=
  F.cohomologyDimensionNotLocallyConstant

/-! Standard visible examples named by the source. -/

abbrev chapter14CuspAmbientRing (k : Type u) [Field k] :=
  MvPolynomial (Fin 2) k

def chapter14CuspEquationIdeal (k : Type u) [Field k] :
    Ideal (chapter14CuspAmbientRing k) :=
  Ideal.span ({
    MvPolynomial.X (1 : Fin 2) ^ 2 - MvPolynomial.X (0 : Fin 2) ^ 3
  } : Set (chapter14CuspAmbientRing k))

abbrev chapter14CuspRing (k : Type u) [Field k] :=
  chapter14CuspAmbientRing k ⧸ chapter14CuspEquationIdeal k

def chapter14CuspScheme (k : Type u) [Field k] : Scheme :=
  Spec (.of (chapter14CuspRing k))

structure Chapter14CuspFailureExample where
  coefficientField : Type u
  [field : Field coefficientField]
  curve : Scheme
  curve_eq_cusp : curve = chapter14CuspScheme coefficientField
  kahlerDifferentials : curve.Modules
  kahlerDifferentials_not_invertible : ¬ chapter09IsInvertible kahlerDifferentials
  dualizingSheaf : curve.Modules
  dualizingSheaf_invertible : chapter09IsInvertible dualizingSheaf
  ordinaryDifferentialsDoNotGiveTheDualizingSheaf :
    ¬ Nonempty (kahlerDifferentials ≅ dualizingSheaf)

structure Chapter14EmbeddedPointFailureExample where
  curve : Scheme
  embeddedPoint : Chapter09EmbeddedZeroDimensionalComponent curve
  notCohenMacaulay : ¬ chapter09CohenMacaulay curve
  dualityWarning : Chapter09NonCohenMacaulayDualityWarning curve

structure Chapter14UnbalancedReducibleCurveFailureExample where
  curve : Scheme
  components : Fin 2 → Scheme
  componentMap : ∀ i, components i ⟶ curve
  componentGenus : Fin 2 → ℕ
  multidegree : Fin 2 → ℤ
  totalDegree : ℤ
  totalDegree_eq_sum : totalDegree = multidegree 0 + multidegree 1
  totalDegree_positive : 0 < totalDegree
  componentAtCanonicalBound : ∃ i : Fin 2,
    multidegree i ≤ 2 * (componentGenus i : ℤ) - 2
  lineBundle : curve.Modules
  lineBundle_multidegree : Fin 2 → ℤ
  lineBundle_multidegree_eq : lineBundle_multidegree = multidegree
  nonzeroH1 : chapter09H lineBundle 1
  nonzeroH1_ne_zero : nonzeroH1 ≠ 0

def chapter14CuspFailureStatement : Prop :=
  ∃ E : Chapter14CuspFailureExample.{0},
    E.curve = @chapter14CuspScheme E.coefficientField E.field ∧
      (¬ chapter09IsInvertible E.kahlerDifferentials) ∧
        (¬ Nonempty (E.kahlerDifferentials ≅ E.dualizingSheaf))

def chapter14EmbeddedPointFailureStatement : Prop :=
  ∃ E : Chapter14EmbeddedPointFailureExample,
    (∃ x : E.curve,
      Nontrivial (E.embeddedPoint.carrier.presheaf.stalk x)) ∧
      ¬ chapter09CohenMacaulay E.curve

def chapter14UnbalancedReducibleCurveFailureStatement : Prop :=
  ∃ E : Chapter14UnbalancedReducibleCurveFailureExample,
    0 < E.totalDegree ∧
      (∃ i : Fin 2,
        E.multidegree i ≤ 2 * (E.componentGenus i : ℤ) - 2) ∧
      E.nonzeroH1 ≠ 0

def chapter14FailureModeChecklist : Prop :=
  (∃ F : Chapter14FailureWithoutProperness,
    ¬ Finite (chapter09H F.coefficient 0)) ∧
  (∃ F : Chapter14FailureWithoutFlatness,
    ∃ s t, F.fiberDimension s ≠ F.fiberDimension t) ∧
  (∃ F : Chapter14FailureWithoutCohenMacaulay,
    ¬ chapter09CohenMacaulay F.context.X) ∧
  (∃ F : Chapter14FailureWithoutGorenstein,
    ¬ chapter09IsInvertible F.dualizingSheaf) ∧
  (∃ F : Chapter14FailureWithoutGeometricConnectedness,
    F.nontrivialIdempotent ≠ 0 ∧ F.nontrivialIdempotent ≠ 1) ∧
  (∃ F : Chapter14FailureWithoutLocallyConstantCohomology,
    ¬ chapter04FiniteLocallyFree F.pushforward) ∧
  chapter14CuspFailureStatement ∧
  chapter14EmbeddedPointFailureStatement ∧
  chapter14UnbalancedReducibleCurveFailureStatement

end
end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter14
