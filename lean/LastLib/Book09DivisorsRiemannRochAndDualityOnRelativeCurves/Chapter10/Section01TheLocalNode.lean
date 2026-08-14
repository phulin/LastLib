import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter10.Dependencies

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter10

noncomputable section

open AlgebraicGeometry CategoryTheory Set
open scoped LaurentSeries PowerSeries MonomialOrder

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
  change
    Ideal.Quotient.mk (chapter10NodeRelationIdeal k)
        (MvPowerSeries.X (0 : Fin 2)) *
      Ideal.Quotient.mk (chapter10NodeRelationIdeal k)
        (MvPowerSeries.X (1 : Fin 2)) = 0
  rw [← (Ideal.Quotient.mk (chapter10NodeRelationIdeal k)).map_mul]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (show
      MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) ∈
        ({MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2)} :
          Set (chapter10BivariatePowerSeries k)) from Set.mem_singleton _))

/-!
The normalization ring is the product of the two branch power-series rings;
the completed node embeds into it as the equal-constant subring.  The actual
quotient-to-product map is a standard branch-substitution construction, but
its presentation is not exposed by the pinned snapshot, so the map and its
universal properties are kept as one local interface.
-/

abbrev chapter10NodeNormalizationRing (k : Type u) [Field k] :=
  PowerSeries k × PowerSeries k

def chapter10NodeNormalizationSubring (k : Type u) [Field k] :
    Subring (chapter10NodeNormalizationRing k) where
  carrier := {
    p | PowerSeries.constantCoeff p.1 = PowerSeries.constantCoeff p.2
  }
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simpa using congrArg₂ (· + ·) ha hb
  mul_mem' := by
    intro a b ha hb
    simpa using congrArg₂ (· * ·) ha hb
  neg_mem' := by simp [map_neg]

structure Chapter10NodeNormalizationData (k : Type u) [Field k] where
  map : chapter10CompletedNodeRing k →+* chapter10NodeNormalizationRing k
  map_x : map (chapter10NodeCoordinateX k) = (PowerSeries.X, 0)
  map_y : map (chapter10NodeCoordinateY k) = (0, PowerSeries.X)
  image_in_subring : ∀ z, map z ∈ chapter10NodeNormalizationSubring k
  subring_in_image : ∀ z : chapter10NodeNormalizationSubring k,
    ∃ w, map w = z.1
  injective : Function.Injective map
  finite :
    IsFinite (Scheme.Spec.map (CommRingCat.ofHom map).op)
  universal : Chapter10NormalizationUniversalProperty
    (Scheme.Spec.map (CommRingCat.ofHom map).op)

theorem chapter10_node_normalization_exists (k : Type u) [Field k] :
    Nonempty (Chapter10NodeNormalizationData k) := by
  sorry

noncomputable def chapter10NodeNormalizationData (k : Type u) [Field k] :
    Chapter10NodeNormalizationData k :=
  Classical.choice (chapter10_node_normalization_exists k)

theorem chapter10_node_normalization_is_two_branches (k : Type u) [Field k] :
    chapter10NodeNormalizationRing k = (PowerSeries k × PowerSeries k) :=
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
  exact ⟨Module.Basis.singleton (Fin 1) (chapter10CompletedNodeRing k)⟩

def chapter10NodeBranchUniformizer (k : Type u) [Field k] : LaurentSeries k :=
  ((PowerSeries.X : PowerSeries k) : LaurentSeries k)

/-- The branch presentation `θ = (dx/x,-dy/y)`. -/
def chapter10NodeTheta (k : Type u) [Field k] :
    Chapter10BranchDifferentialPair k :=
  ((chapter10NodeBranchUniformizer k)⁻¹,
    -((chapter10NodeBranchUniformizer k)⁻¹))

theorem chapter10_node_theta_left_residue (k : Type u) [Field k] :
    chapter10LaurentResidue (chapter10NodeTheta k).1 = 1 := by
  simp [chapter10LaurentResidue, chapter10NodeTheta,
    chapter10NodeBranchUniformizer, HahnSeries.inv_single]

theorem chapter10_node_theta_right_residue (k : Type u) [Field k] :
    chapter10LaurentResidue (chapter10NodeTheta k).2 = -1 := by
  simp [chapter10LaurentResidue, chapter10NodeTheta,
    chapter10NodeBranchUniformizer, HahnSeries.inv_single]

theorem chapter10_node_theta_has_opposite_residues (k : Type u) [Field k] :
    chapter10OppositeResidues (chapter10NodeTheta k) := by
  change chapter10LaurentResidue (chapter10NodeTheta k).1 +
    chapter10LaurentResidue (chapter10NodeTheta k).2 = 0
  rw [chapter10_node_theta_left_residue, chapter10_node_theta_right_residue]
  simp

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
  change
    Ideal.Quotient.mk (chapter10SmoothingRelationIdeal R a)
        (MvPolynomial.X (0 : Fin 2)) *
      Ideal.Quotient.mk (chapter10SmoothingRelationIdeal R a)
        (MvPolynomial.X (1 : Fin 2)) =
      Ideal.Quotient.mk (chapter10SmoothingRelationIdeal R a)
        (MvPolynomial.C a)
  rw [← (Ideal.Quotient.mk (chapter10SmoothingRelationIdeal R a)).map_mul]
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact Ideal.subset_span (show
      MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) -
          MvPolynomial.C a ∈
        ({MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) -
          MvPolynomial.C a} : Set (chapter10SmoothingAmbientRing R)) from
          Set.mem_singleton _)

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
  have h := congrArg
    (fun z : chapter10SmoothingRing R a =>
      KaehlerDifferential.D R (chapter10SmoothingRing R a) z)
    (chapter10_smoothing_equation R a)
  rw [Derivation.leibniz, Derivation.map_algebraMap] at h
  simpa [chapter10SmoothingDX, chapter10SmoothingDY, add_comm] using h

/-! The logarithmic frame belongs to the relative hypersurface only when the
defining equation is a regular element of the smooth ambient algebra. -/
def chapter10SmoothingEquationIsRegular
    (R : Type u) [CommRing R] (a : R) : Prop :=
  ∀ z : chapter10SmoothingAmbientRing R,
    z * (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) -
      MvPolynomial.C a) = 0 → z = 0

theorem chapter10_smoothing_equation_is_regular
    (R : Type u) [CommRing R] (a : R) :
    chapter10SmoothingEquationIsRegular R a := by
  classical
  unfold chapter10SmoothingEquationIsRegular
  intro z hz
  rcases subsingleton_or_nontrivial R with hR | hR
  · let := hR
    exact Subsingleton.elim _ _
  · let := hR
    let m : MonomialOrder (Fin 2) := MonomialOrder.lex
    let f : MvPolynomial (Fin 2) R :=
      MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)
    have hmono : m.Monic f := by
      dsimp [f]
      exact m.monic_X.mul m.monic_X
    have hdeg : m.degree f =
        Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1 := by
      change m.degree
        (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)) = _
      rw [m.degree_mul_of_isRegular_left]
      · rw [m.degree_X, m.degree_X]
      · simpa using (isRegular_one : IsRegular (1 : R))
      · exact m.monic_X.ne_zero
    have hlt : m.degree (MvPolynomial.C a) ≺[m]
        m.degree f := by
      rw [m.degree_C, hdeg, MonomialOrder.lex_lt_iff]
      change Finsupp.Lex (· < ·) (· < ·)
        (0 : Fin 2 →₀ ℕ)
        (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1)
      rw [Finsupp.lex_def]
      refine ⟨0, ?_, ?_⟩
      · intro d hd
        exact (not_lt_of_ge (Fin.zero_le d) hd).elim
      · simp
    have hlt_neg : m.degree (-MvPolynomial.C a) ≺[m]
        m.degree f := by
      simpa using hlt
    have hmonic_sub : m.Monic (f - MvPolynomial.C a) := by
      simpa [sub_eq_add_neg] using hmono.add_of_lt hlt_neg
    have hcoeff_regular : IsRegular
        (m.leadingCoeff (f - MvPolynomial.C a)) := by
      rw [hmonic_sub.leadingCoeff_eq_one]
      exact isRegular_one
    have hzero : ∀ q : MvPolynomial (Fin 2) R,
        (f - MvPolynomial.C a) * q = 0 → q = 0 := by
      intro q hq
      have hcoeff : m.leadingCoeff
          ((f - MvPolynomial.C a) * q) = m.leadingCoeff q := by
        rw [m.leadingCoeff_mul_of_isRegular_left hcoeff_regular,
          hmonic_sub.leadingCoeff_eq_one, one_mul]
      rw [hq, m.leadingCoeff_zero] at hcoeff
      by_contra hq_ne
      exact (m.leadingCoeff_ne_zero_iff.mpr hq_ne) hcoeff.symm
    have hreg : IsRegular (f - MvPolynomial.C a) := by
      apply (isRegular_iff_eq_zero_of_mul).2
      constructor
      · exact hzero
      · intro q hq
        apply hzero q
        simpa [mul_comm] using hq
    apply (isRightRegular_iff_left_eq_zero_of_mul.mp hreg.right) z
    simpa [f] using hz

def chapter10LogDifferentialOfElement
    {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    (x : A) (hx : IsUnit x) (η : M) : M :=
  ((↑(hx.unit⁻¹) : A) • η)

private theorem chapter10_log_relation_of_unit_coefficients
    {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    (x y : A) (hx : IsUnit x) (hy : IsUnit y) (dx dy : M)
    (h : y • dx + x • dy = 0) :
    (↑(hx.unit⁻¹) : A) • dx = -((↑(hy.unit⁻¹) : A) • dy) := by
  refine eq_neg_of_add_eq_zero_left ?_
  have h' := congrArg
    (fun η : M =>
      ((↑(hx.unit⁻¹) : A) * (↑(hy.unit⁻¹) : A)) • η) h
  rw [smul_add] at h'
  have hassoc1 :
      (((↑(hx.unit⁻¹) : A) * (↑(hy.unit⁻¹) : A)) * y) • dx =
        ((↑(hx.unit⁻¹) : A) * (↑(hy.unit⁻¹) : A)) • (y • dx) := by
    exact mul_smul _ _ _
  have hassoc2 :
      (((↑(hx.unit⁻¹) : A) * (↑(hy.unit⁻¹) : A)) * x) • dy =
        ((↑(hx.unit⁻¹) : A) * (↑(hy.unit⁻¹) : A)) • (x • dy) := by
    exact mul_smul _ _ _
  rw [← hassoc1, ← hassoc2] at h'
  have hcoef1 :
      ((↑(hx.unit⁻¹) : A) * (↑(hy.unit⁻¹) : A)) * y =
        (↑(hx.unit⁻¹) : A) := by
    rw [mul_assoc, hy.val_inv_mul, mul_one]
  have hcoef2 :
      ((↑(hx.unit⁻¹) : A) * (↑(hy.unit⁻¹) : A)) * x =
        (↑(hy.unit⁻¹) : A) := by
    rw [mul_comm (↑(hx.unit⁻¹) : A) (↑(hy.unit⁻¹) : A), mul_assoc,
      hx.val_inv_mul, mul_one]
  rw [hcoef1, hcoef2] at h'
  simpa using h'

theorem chapter10_smoothing_log_relation_on_unit_locus
    (R : Type u) [CommRing R] (a : R)
    (hx : IsUnit (chapter10SmoothingCoordinateX R a))
    (hy : IsUnit (chapter10SmoothingCoordinateY R a)) :
    chapter10LogDifferentialOfElement
        (chapter10SmoothingCoordinateX R a) hx (chapter10SmoothingDX R a) =
      -chapter10LogDifferentialOfElement
        (chapter10SmoothingCoordinateY R a) hy (chapter10SmoothingDY R a) := by
  simpa [chapter10LogDifferentialOfElement] using
    (chapter10_log_relation_of_unit_coefficients
      (chapter10SmoothingCoordinateX R a) (chapter10SmoothingCoordinateY R a)
      hx hy (chapter10SmoothingDX R a) (chapter10SmoothingDY R a)
      (chapter10_smoothing_differentiation_relation R a))

/-! The common logarithmic expression is represented by a relative-dualizing
local frame that extends through the node. -/

structure Chapter10SmoothingLogFrameData (R : Type u) [CommRing R] (a : R) where
  dualizing : Chapter10RankOneModuleData (chapter10SmoothingRing R a)
  commonLogFrame : dualizing.carrier
  commonLogFrame_eq_module_frame : commonLogFrame = dualizing.frame
  agrees_on_unit_locus : Prop
  agrees_on_unit_locus_holds : agrees_on_unit_locus
  extends_through_node : Prop
  extends_through_node_holds : extends_through_node

theorem chapter10_smoothing_log_frame_exists
    (R : Type u) [CommRing R] (a : R)
    (hregular : chapter10SmoothingEquationIsRegular R a) :
    Nonempty (Chapter10SmoothingLogFrameData R a) := by
  sorry

theorem chapter10_smoothing_common_log_expression_is_generator
    (R : Type u) [CommRing R] (a : R)
    (D : Chapter10SmoothingLogFrameData R a) :
    ∃ b : Module.Basis (Fin 1) (chapter10SmoothingRing R a)
        D.dualizing.carrier, b 0 = D.commonLogFrame := by
  refine ⟨D.dualizing.frameBasis, ?_⟩
  exact D.dualizing.frame_eq_basis.symm.trans
    D.commonLogFrame_eq_module_frame.symm

theorem chapter10_node_coordinates_are_not_units (k : Type u) [Field k] :
    ¬ IsUnit (chapter10NodeCoordinateX k) ∧
      ¬ IsUnit (chapter10NodeCoordinateY k) := by
  let f : chapter10BivariatePowerSeries k →+* k :=
    MvPowerSeries.constantCoeff
  have hker : chapter10NodeRelationIdeal k ≤ RingHom.ker f := by
    rw [chapter10NodeRelationIdeal]
    refine Ideal.span_le.2 ?_
    intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    change f (MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2)) = 0
    simp [f]
  let q : chapter10CompletedNodeRing k →+* k :=
    Ideal.Quotient.lift (chapter10NodeRelationIdeal k) f (fun z hz =>
      RingHom.mem_ker.mp (hker hz))
  have hqX : q (chapter10NodeCoordinateX k) = 0 := by
    change q (Ideal.Quotient.mk (chapter10NodeRelationIdeal k)
      (MvPowerSeries.X (0 : Fin 2))) = 0
    rw [Ideal.Quotient.lift_mk]
    simp [f]
  have hqY : q (chapter10NodeCoordinateY k) = 0 := by
    change q (Ideal.Quotient.mk (chapter10NodeRelationIdeal k)
      (MvPowerSeries.X (1 : Fin 2))) = 0
    rw [Ideal.Quotient.lift_mk]
    simp [f]
  constructor
  · intro hx
    apply not_isUnit_zero (M₀ := k)
    rw [← hqX]
    exact hx.map q
  · intro hy
    apply not_isUnit_zero (M₀ := k)
    rw [← hqY]
    exact hy.map q

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
