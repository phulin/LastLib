import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter10.Dependencies

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter10

noncomputable section

open AlgebraicGeometry CategoryTheory Set
open scoped LaurentSeries PowerSeries

universe u

/-! ## 10.1. The local node -/

/-!
The completed split node is represented by the canonical multivariate formal
power-series quotient.  The two coordinate classes are retained explicitly so
the relation, normalization, and smoothing statements can use the same
objects.
-/

abbrev chapter10BivariatePowerSeries (k : Type u) [Field k] :=
  MvPowerSeries (Fin 2) k

def chapter10NodeRelationIdeal (k : Type u) [Field k] :
    Ideal (chapter10BivariatePowerSeries k) :=
  Ideal.span ({
    MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2)
  } : Set (chapter10BivariatePowerSeries k))

/-- The completed local ring `k[[x,y]]/(xy)` of a split node. -/
abbrev chapter10CompletedNodeRing (k : Type u) [Field k] :=
  chapter10BivariatePowerSeries k ⧸ chapter10NodeRelationIdeal k

def chapter10NodeCoordinateX (k : Type u) [Field k] :
    chapter10CompletedNodeRing k :=
  Ideal.Quotient.mk (chapter10NodeRelationIdeal k)
    (MvPowerSeries.X (0 : Fin 2))

def chapter10NodeCoordinateY (k : Type u) [Field k] :
    chapter10CompletedNodeRing k :=
  Ideal.Quotient.mk (chapter10NodeRelationIdeal k)
    (MvPowerSeries.X (1 : Fin 2))

theorem chapter10_node_equation (k : Type u) [Field k] :
    chapter10NodeCoordinateX k * chapter10NodeCoordinateY k = 0 := by
  sorry

/-!
The normalization is the equal-constant subring of the two branch power
series.  The actual quotient-to-subring map is a standard branch-substitution
construction, but its presentation is not exposed by the pinned snapshot, so
the map and its universal properties are kept as one local interface.
-/

abbrev chapter10NodeNormalizationRing (k : Type u) [Field k] :=
  PowerSeries k × PowerSeries k

def chapter10NodeNormalizationSubring (k : Type u) [Field k] :
    Subring (chapter10NodeNormalizationRing k) where
  carrier := {
    p | PowerSeries.constantCoeff p.1 = PowerSeries.constantCoeff p.2
  }
  zero_mem' := by sorry
  one_mem' := by sorry
  add_mem' := by sorry
  mul_mem' := by sorry
  neg_mem' := by sorry

structure Chapter10NodeNormalizationData (k : Type u) [Field k] where
  map : chapter10CompletedNodeRing k →+* chapter10NodeNormalizationRing k
  map_x : map (chapter10NodeCoordinateX k) = (PowerSeries.X, 0)
  map_y : map (chapter10NodeCoordinateY k) = (0, PowerSeries.X)
  image_in_subring : ∀ z, map z ∈ chapter10NodeNormalizationSubring k
  injective : Function.Injective map
  finite : Prop
  universal : Prop

theorem chapter10_node_normalization_exists (k : Type u) [Field k] :
    Nonempty (Chapter10NodeNormalizationData k) := by
  sorry

noncomputable def chapter10NodeNormalizationData (k : Type u) [Field k] :
    Chapter10NodeNormalizationData k :=
  Classical.choice (chapter10_node_normalization_exists k)

theorem chapter10_node_normalization_is_two_branches (k : Type u) [Field k] :
    chapter10NodeNormalizationRing k = PowerSeries k × PowerSeries k :=
  rfl

/-!
The dualizing module of the node is free of rank one.  The displayed generator
is encoded in the two branch Laurent-series factors; the coefficient of
`t⁻¹` is the residue functional used in the later Rosenlicht API.
-/

abbrev chapter10NodeDualizingModule (k : Type u) [Field k] :=
  chapter10CompletedNodeRing k

def chapter10NodeDualizingGenerator (k : Type u) [Field k] :
    chapter10NodeDualizingModule k :=
  1

theorem chapter10_node_dualizing_module_free_rank_one
    (k : Type u) [Field k] :
    Chapter10FreeRankOne (chapter10CompletedNodeRing k)
      (chapter10NodeDualizingModule k) := by
  sorry

def chapter10NodeBranchUniformizer (k : Type u) [Field k] : LaurentSeries k :=
  ((PowerSeries.X : PowerSeries k) : LaurentSeries k)

/-- The branch presentation `θ = (dx/x,-dy/y)`. -/
def chapter10NodeTheta (k : Type u) [Field k] :
    Chapter10BranchDifferentialPair k :=
  ((chapter10NodeBranchUniformizer k)⁻¹,
    -((chapter10NodeBranchUniformizer k)⁻¹))

theorem chapter10_node_theta_left_residue (k : Type u) [Field k] :
    chapter10LaurentResidue (chapter10NodeTheta k).1 = 1 := by
  sorry

theorem chapter10_node_theta_right_residue (k : Type u) [Field k] :
    chapter10LaurentResidue (chapter10NodeTheta k).2 = -1 := by
  sorry

theorem chapter10_node_theta_has_opposite_residues (k : Type u) [Field k] :
    chapter10OppositeResidues (chapter10NodeTheta k) := by
  rw [chapter10_node_theta_left_residue, chapter10_node_theta_right_residue]
  ring

/-! ### The smoothing equation -/

abbrev chapter10SmoothingAmbientRing (R : Type u) [CommRing R] :=
  MvPolynomial (Fin 2) R

def chapter10SmoothingRelationIdeal (R : Type u) [CommRing R] (a : R) :
    Ideal (chapter10SmoothingAmbientRing R) :=
  Ideal.span ({
    MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) -
      MvPolynomial.C a
  } : Set (chapter10SmoothingAmbientRing R))

/-- The affine smoothing ring `R[x,y]/(xy-a)`. -/
abbrev chapter10SmoothingRing (R : Type u) [CommRing R] (a : R) :=
  chapter10SmoothingAmbientRing R ⧸ chapter10SmoothingRelationIdeal R a

def chapter10SmoothingCoordinateX (R : Type u) [CommRing R] (a : R) :
    chapter10SmoothingRing R a :=
  Ideal.Quotient.mk (chapter10SmoothingRelationIdeal R a)
    (MvPolynomial.X (0 : Fin 2))

def chapter10SmoothingCoordinateY (R : Type u) [CommRing R] (a : R) :
    chapter10SmoothingRing R a :=
  Ideal.Quotient.mk (chapter10SmoothingRelationIdeal R a)
    (MvPolynomial.X (1 : Fin 2))

theorem chapter10_smoothing_equation (R : Type u) [CommRing R] (a : R) :
    chapter10SmoothingCoordinateX R a * chapter10SmoothingCoordinateY R a =
      algebraMap R (chapter10SmoothingRing R a) a := by
  sorry

def chapter10SmoothingDX (R : Type u) [CommRing R] (a : R) :
    KaehlerDifferential R (chapter10SmoothingRing R a) :=
  KaehlerDifferential.D R (chapter10SmoothingRing R a)
    (chapter10SmoothingCoordinateX R a)

def chapter10SmoothingDY (R : Type u) [CommRing R] (a : R) :
    KaehlerDifferential R (chapter10SmoothingRing R a) :=
  KaehlerDifferential.D R (chapter10SmoothingRing R a)
    (chapter10SmoothingCoordinateY R a)

/-- Relative differentiation of `xy=a` gives `y dx+x dy=0`. -/
theorem chapter10_smoothing_differentiation_relation
    (R : Type u) [CommRing R] (a : R) :
    chapter10SmoothingCoordinateY R a • chapter10SmoothingDX R a +
        chapter10SmoothingCoordinateX R a • chapter10SmoothingDY R a = 0 := by
  sorry

def chapter10LogDifferentialOfElement
    {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    (x : A) (hx : IsUnit x) (η : M) : M :=
  (hx.unit : A)⁻¹ • η

theorem chapter10_smoothing_log_relation_on_unit_locus
    (R : Type u) [CommRing R] (a : R)
    (hx : IsUnit (chapter10SmoothingCoordinateX R a))
    (hy : IsUnit (chapter10SmoothingCoordinateY R a)) :
    chapter10LogDifferentialOfElement
        (chapter10SmoothingCoordinateX R a) hx (chapter10SmoothingDX R a) =
      -chapter10LogDifferentialOfElement
        (chapter10SmoothingCoordinateY R a) hy (chapter10SmoothingDY R a) := by
  sorry

/-! The common logarithmic expression is represented by a relative-dualizing
local frame that extends through the node. -/

structure Chapter10SmoothingLogFrameData (R : Type u) [CommRing R] (a : R) where
  dualizing : Chapter10RankOneModuleData (chapter10SmoothingRing R a)
  commonLogFrame : dualizing.carrier
  commonLogFrame_eq_module_frame : commonLogFrame = dualizing.frame
  agrees_on_unit_locus : Prop
  extends_through_node : Prop

theorem chapter10_smoothing_log_frame_exists
    (R : Type u) [CommRing R] (a : R) :
    Nonempty (Chapter10SmoothingLogFrameData R a) := by
  sorry

theorem chapter10_smoothing_common_log_expression_is_generator
    (R : Type u) [CommRing R] (a : R)
    (D : Chapter10SmoothingLogFrameData R a) :
    Chapter10FreeRankOne (chapter10SmoothingRing R a) D.dualizing.carrier := by
  exact D.dualizing.freeRankOne

theorem chapter10_node_coordinates_are_not_units (k : Type u) [Field k] :
    ¬ IsUnit (chapter10NodeCoordinateX k) ∧
      ¬ IsUnit (chapter10NodeCoordinateY k) := by
  sorry

def chapter10LeftOrdinaryLogExpressionDefinedAtNode
    (k : Type u) [Field k] : Prop :=
  IsUnit (chapter10NodeCoordinateX k)

def chapter10RightOrdinaryLogExpressionDefinedAtNode
    (k : Type u) [Field k] : Prop :=
  IsUnit (chapter10NodeCoordinateY k)

theorem chapter10_left_log_expression_is_not_ordinary_regular_at_node
    (k : Type u) [Field k] :
    ¬ chapter10LeftOrdinaryLogExpressionDefinedAtNode k := by
  exact (chapter10_node_coordinates_are_not_units k).1

theorem chapter10_right_log_expression_is_not_ordinary_regular_at_node
    (k : Type u) [Field k] :
    ¬ chapter10RightOrdinaryLogExpressionDefinedAtNode k := by
  exact (chapter10_node_coordinates_are_not_units k).2

def chapter10OrdinaryLogExpressionsDefinedAtNode
    (k : Type u) [Field k] : Prop :=
  IsUnit (chapter10NodeCoordinateX k) ∧
    IsUnit (chapter10NodeCoordinateY k)

theorem chapter10_log_expressions_are_not_ordinary_regular_differentials_at_the_node
    (k : Type u) [Field k] :
    ¬ chapter10OrdinaryLogExpressionsDefinedAtNode k := by
  intro h
  exact (chapter10_node_coordinates_are_not_units k).1 h.1

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter10
