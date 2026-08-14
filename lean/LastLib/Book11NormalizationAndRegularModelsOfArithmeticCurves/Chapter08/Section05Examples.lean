import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter08.Section04Termination
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter02.Section01AffineConstruction
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04.Section03NormalSurfacesNeedNotBeRegular
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Dependencies

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter08

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter02
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07
open scoped AlgebraicGeometry BigOperators

universe u v

/-! ## 8.5. Examples -/

/-! ### The arithmetic node `R[x,y]/(xy-πⁿ)` -/

def chapter08ArithmeticNodeEquation
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    MvPolynomial (Fin 2) R :=
  MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C (π ^ n)

def chapter08ArithmeticNodeRelationIdeal
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Ideal (MvPolynomial (Fin 2) R) :=
  Ideal.span ({chapter08ArithmeticNodeEquation R π n} :
    Set (MvPolynomial (Fin 2) R))

abbrev chapter08ArithmeticNodeRing
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :=
  MvPolynomial (Fin 2) R ⧸ chapter08ArithmeticNodeRelationIdeal R π n

def chapter08ArithmeticNodeScheme
    (R : Type u) [CommRing R] (π : R) (n : ℕ) : Scheme.{u} :=
  Spec (.of (chapter08ArithmeticNodeRing R π n))

def chapter08ArithmeticNodeCoordinate
    (R : Type u) [CommRing R] (π : R) (n : ℕ) (i : Fin 2) :
    chapter08ArithmeticNodeRing R π n :=
  Ideal.Quotient.mk (chapter08ArithmeticNodeRelationIdeal R π n)
    (MvPolynomial.X i)

theorem chapter08_arithmetic_node_equation
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    chapter08ArithmeticNodeCoordinate R π n 0 *
        chapter08ArithmeticNodeCoordinate R π n 1 =
      algebraMap R (chapter08ArithmeticNodeRing R π n) (π ^ n) := by
  sorry

def chapter08ArithmeticNodeBlowupIdeal
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Ideal (chapter08ArithmeticNodeRing R π n) :=
  Ideal.span ({chapter08ArithmeticNodeCoordinate R π n 0,
    algebraMap R (chapter08ArithmeticNodeRing R π n) π} :
    Set (chapter08ArithmeticNodeRing R π n))

theorem chapter08_arithmetic_node_blowup_ideal_is_the_x_pi_ideal
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    chapter08ArithmeticNodeBlowupIdeal R π n =
      Ideal.span ({chapter08ArithmeticNodeCoordinate R π n 0,
        algebraMap R (chapter08ArithmeticNodeRing R π n) π} :
        Set (chapter08ArithmeticNodeRing R π n)) := by
  rfl

def chapter08ArithmeticNodeXChartRelationIdeal
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Ideal (MvPolynomial (Fin 3) R) :=
  Ideal.span ({
    MvPolynomial.X 1 - MvPolynomial.X 0 ^ (n - 1) * MvPolynomial.X 2 ^ n,
    MvPolynomial.C π - MvPolynomial.X 0 * MvPolynomial.X 2} :
    Set (MvPolynomial (Fin 3) R))

abbrev chapter08ArithmeticNodeXChartRing
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :=
  MvPolynomial (Fin 3) R ⧸ chapter08ArithmeticNodeXChartRelationIdeal R π n

def chapter08ArithmeticNodeXChartCoordinate
    (R : Type u) [CommRing R] (π : R) (n : ℕ) (i : Fin 3) :
    chapter08ArithmeticNodeXChartRing R π n :=
  Ideal.Quotient.mk (chapter08ArithmeticNodeXChartRelationIdeal R π n)
    (MvPolynomial.X i)

def chapter08ArithmeticNodeXChartScheme
    (R : Type u) [CommRing R] (π : R) (n : ℕ) : Scheme.{u} :=
  Spec (.of (chapter08ArithmeticNodeXChartRing R π n))

theorem chapter08_arithmetic_node_x_chart_equations
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    chapter08ArithmeticNodeXChartCoordinate R π n 1 =
        chapter08ArithmeticNodeXChartCoordinate R π n 0 ^ (n - 1) *
          chapter08ArithmeticNodeXChartCoordinate R π n 2 ^ n ∧
      algebraMap R (chapter08ArithmeticNodeXChartRing R π n) π =
        chapter08ArithmeticNodeXChartCoordinate R π n 0 *
          chapter08ArithmeticNodeXChartCoordinate R π n 2 := by
  sorry

def chapter08ArithmeticNodePiChartRelationIdeal
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Ideal (MvPolynomial (Fin 3) R) :=
  Ideal.span ({MvPolynomial.X 1 * MvPolynomial.X 2 -
    MvPolynomial.X 0 ^ (n - 1)} : Set (MvPolynomial (Fin 3) R))

abbrev chapter08ArithmeticNodePiChartRing
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :=
  MvPolynomial (Fin 3) R ⧸ chapter08ArithmeticNodePiChartRelationIdeal R π n

def chapter08ArithmeticNodePiChartCoordinate
    (R : Type u) [CommRing R] (π : R) (n : ℕ) (i : Fin 3) :
    chapter08ArithmeticNodePiChartRing R π n :=
  Ideal.Quotient.mk (chapter08ArithmeticNodePiChartRelationIdeal R π n)
    (MvPolynomial.X i)

def chapter08ArithmeticNodePiChartX
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    chapter08ArithmeticNodePiChartRing R π n :=
  algebraMap R (chapter08ArithmeticNodePiChartRing R π n) π *
    chapter08ArithmeticNodePiChartCoordinate R π n 1

theorem chapter08_arithmetic_node_pi_chart_equations
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    chapter08ArithmeticNodePiChartX R π n =
        algebraMap R (chapter08ArithmeticNodePiChartRing R π n) π *
          chapter08ArithmeticNodePiChartCoordinate R π n 1 ∧
      chapter08ArithmeticNodePiChartCoordinate R π n 1 *
          chapter08ArithmeticNodePiChartCoordinate R π n 2 =
        chapter08ArithmeticNodePiChartCoordinate R π n 0 ^ (n - 1) := by
  sorry

def Chapter08ArithmeticNodeXChartRegular
    (R : Type u) [CommRing R] (π : R) (n : ℕ) : Prop :=
  Chapter04RegularScheme (chapter08ArithmeticNodeXChartScheme R π n)

def Chapter08ArithmeticNodePiChartRegular
    (R : Type u) [CommRing R] (π : R) (n : ℕ) : Prop :=
  Chapter04RegularScheme
    (Spec (.of (chapter08ArithmeticNodePiChartRing R π n)))

theorem chapter08_arithmetic_node_x_chart_is_regular
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (n : ℕ) (hn : 2 ≤ n) (hπ : Irreducible π) :
    Chapter08ArithmeticNodeXChartRegular R π n := by
  sorry

theorem chapter08_arithmetic_node_pi_chart_has_smaller_exponent
    (n : ℕ) (hn : 0 < n) : n - 1 < n := by
  omega

structure Chapter08ArithmeticNodeBlowupStep
    (R : Type u) [CommRing R] (π : R) (n : ℕ) where
  exponent_at_least_two : 2 ≤ n
  center : Ideal (chapter08ArithmeticNodeRing R π n)
  center_eq_x_pi : center = chapter08ArithmeticNodeBlowupIdeal R π n
  x_chart_equations : Prop
  x_chart_regular : Chapter08ArithmeticNodeXChartRegular R π n
  pi_chart_equations : Prop
  pi_chart_exponent : n - 1
  modification_is_iso_away_from_singular_point : Prop

theorem chapter08_arithmetic_node_blowup_step
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (n : ℕ) (hn : 2 ≤ n) (hπ : Irreducible π) :
    Nonempty (Chapter08ArithmeticNodeBlowupStep R π n) := by
  sorry

abbrev chapter08ArithmeticNodeTerminalRing
    (R : Type u) [CommRing R] (π : R) :=
  chapter04DvrNodeRing R π

def chapter08ArithmeticNodeTerminalCoordinate
    (R : Type u) [CommRing R] (π : R) (i : Fin 2) :
    chapter08ArithmeticNodeTerminalRing R π :=
  chapter04DvrNodeCoordinate R π i

theorem chapter08_arithmetic_node_terminal_equation
    (R : Type u) [CommRing R] (π : R) :
    chapter08ArithmeticNodeTerminalCoordinate R π 0 *
        chapter08ArithmeticNodeTerminalCoordinate R π 1 =
      algebraMap R (chapter08ArithmeticNodeTerminalRing R π) π := by
  exact chapter04_dvr_node_equation R π

def Chapter08ArithmeticNodeTerminalRegularity
    (R : Type u) [CommRing R] (π : R) : Prop :=
  ∃ hprime : (chapter04DvrNodeMaximalIdeal R π).IsPrime,
    Chapter04DvrNodeRegularAtNode R π hprime

theorem chapter08_arithmetic_node_terminal_model_is_regular
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π) :
    Chapter08ArithmeticNodeTerminalRegularity R π := by
  sorry

structure Chapter08ArithmeticNodeResolutionData
    (R : Type u) [CommRing R] (π : R) (n : ℕ) where
  steps : ℕ
  steps_eq : steps = n - 1
  exponent : Fin (steps + 1) → ℕ
  initial_exponent : exponent 0 = n
  terminal_exponent : exponent (Fin.last steps) = 1
  exponent_decreases : ∀ i : Fin steps,
    exponent i.castSucc - 1 = exponent i.succ
  each_step : Prop
  terminal_regular : Chapter08ArithmeticNodeTerminalRegularity R π

theorem chapter08_arithmetic_node_resolves_by_induction
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (n : ℕ) (hn : 2 ≤ n) (hπ : Irreducible π) :
    Nonempty (Chapter08ArithmeticNodeResolutionData R π n) := by
  sorry

structure Chapter08RationalCurveSignature (C : Scheme.{u}) where
  field : Type u
  [field_isField : Field field]
  projectiveLine_iso : Nonempty (C ≅ chapter04ProjectiveLine field)

structure Chapter08RationalCurveChain (X : Scheme.{u}) where
  components : Set (Scheme.{u})
  finite_components : components.Finite
  component_maps_to_X : ∀ C : Scheme.{u}, C ∈ components → C ⟶ X
  rational_components : ∀ C : Scheme.{u}, C ∈ components →
    Chapter08RationalCurveSignature C
  chain_intersection_graph : Prop

theorem chapter08_arithmetic_node_exceptional_locus_is_rational_chain
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (n : ℕ) (hn : 2 ≤ n) (hπ : Irreducible π) :
    Nonempty (Chapter08RationalCurveChain
      (chapter08ArithmeticNodeScheme R π n)) := by
  sorry

/-! ### The quadratic cone `xy = z²` -/

def chapter08QuadraticConeBlowupCenter (k : Type u) [CommRing k] :
    Ideal (chapter04QuadraticConeRing k) :=
  chapter04QuadraticConeOriginIdeal k

def chapter08QuadraticConeXChartTotalEquation
    (k : Type u) [CommRing k] : MvPolynomial (Fin 3) k :=
  MvPolynomial.X 0 ^ 2 *
    (MvPolynomial.X 1 - MvPolynomial.X 2 ^ 2)

def chapter08QuadraticConeXChartStrictRelationIdeal
    (k : Type u) [CommRing k] : Ideal (MvPolynomial (Fin 3) k) :=
  Ideal.span ({MvPolynomial.X 1 - MvPolynomial.X 2 ^ 2} :
    Set (MvPolynomial (Fin 3) k))

abbrev chapter08QuadraticConeXChartStrictTransformRing
    (k : Type u) [CommRing k] :=
  MvPolynomial (Fin 3) k ⧸ chapter08QuadraticConeXChartStrictRelationIdeal k

theorem chapter08_quadratic_cone_x_chart_total_equation
    (k : Type u) [CommRing k] :
    chapter08QuadraticConeXChartTotalEquation k =
      MvPolynomial.X 0 ^ 2 *
        (MvPolynomial.X 1 - MvPolynomial.X 2 ^ 2) := by
  rfl

theorem chapter08_quadratic_cone_x_chart_strict_equation
    (k : Type u) [CommRing k] :
    Ideal.Quotient.mk (chapter08QuadraticConeXChartStrictRelationIdeal k)
        (MvPolynomial.X 1) =
      Ideal.Quotient.mk (chapter08QuadraticConeXChartStrictRelationIdeal k)
        (MvPolynomial.X 2) ^ 2 := by
  sorry

def Chapter08QuadraticConeXChartStrictTransformSmooth
    (k : Type u) [Field k] : Prop :=
  Chapter04RegularScheme
    (Spec (.of (chapter08QuadraticConeXChartStrictTransformRing k)))

theorem chapter08_quadratic_cone_blowup_x_chart_is_smooth
    (k : Type u) [Field k] :
    Chapter08QuadraticConeXChartStrictTransformSmooth k := by
  sorry

theorem chapter08_quadratic_cone_blowup_resolves_in_one_step
    (k : Type u) [Field k] :
    Nonempty (Chapter04QuadraticConeResolutionData k) := by
  sorry

/-! ### The cusp and the arithmetic cusp surface -/

abbrev chapter08CuspSubalgebra (k : Type u) [CommRing k] :=
  chapter02CuspSubalgebra k

abbrev chapter08CuspNormalizationRing (k : Type u) [CommRing k] :=
  Polynomial k

def chapter08CuspNormalizationMap (k : Type u) [CommRing k] :
    chapter08CuspSubalgebra k →+* chapter08CuspNormalizationRing k :=
  chapter02CuspInclusion k

structure Chapter08CuspNormalizationData (k : Type u) [Field k] where
  map : chapter08CuspSubalgebra k →+* chapter08CuspNormalizationRing k
  map_eq_canonical : map = chapter08CuspNormalizationMap k
  integral : IsIntegralHom map
  normalization_is_polynomial_ring :
    chapter08CuspNormalizationRing k = Polynomial k
  target_is_integrallyClosed : IsIntegrallyClosed (chapter08CuspNormalizationRing k)
  normalized_affine_is_regular :
    Chapter04RegularScheme
      (Spec (.of (chapter08CuspNormalizationRing k)))

theorem chapter08_cusp_normalization_resolves_immediately
    (k : Type u) [Field k] :
    Nonempty (Chapter08CuspNormalizationData k) := by
  sorry

def chapter08ArithmeticCuspEquation
    (R : Type u) [CommRing R] (π : R) (m : ℕ) :
    MvPolynomial (Fin 2) R :=
  MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 ^ 3 - MvPolynomial.C (π ^ m)

def chapter08ArithmeticCuspRelationIdeal
    (R : Type u) [CommRing R] (π : R) (m : ℕ) :
    Ideal (MvPolynomial (Fin 2) R) :=
  Ideal.span ({chapter08ArithmeticCuspEquation R π m} :
    Set (MvPolynomial (Fin 2) R))

abbrev chapter08ArithmeticCuspRing
    (R : Type u) [CommRing R] (π : R) (m : ℕ) :=
  MvPolynomial (Fin 2) R ⧸ chapter08ArithmeticCuspRelationIdeal R π m

def chapter08ArithmeticCuspSurface
    (R : Type u) [CommRing R] (π : R) (m : ℕ) : Scheme.{u} :=
  Spec (.of (chapter08ArithmeticCuspRing R π m))

def chapter08ArithmeticCuspSingularPointIdeal
    (R : Type u) [CommRing R] (π : R) (m : ℕ) :
    Ideal (chapter08ArithmeticCuspRing R π m) :=
  Ideal.span ({
    Ideal.Quotient.mk (chapter08ArithmeticCuspRelationIdeal R π m)
      (MvPolynomial.X 0),
    Ideal.Quotient.mk (chapter08ArithmeticCuspRelationIdeal R π m)
      (MvPolynomial.X 1),
    algebraMap R (chapter08ArithmeticCuspRing R π m) π} :
    Set (chapter08ArithmeticCuspRing R π m))

def Chapter08ArithmeticCuspSurfaceCanRemainNormalSingular
    (R : Type u) [CommRing R] (π : R) (m : ℕ) : Prop :=
  IsDomain (chapter08ArithmeticCuspRing R π m) ∧
    IsIntegrallyClosed (chapter08ArithmeticCuspRing R π m) ∧
      ∃ hprime :
          (chapter08ArithmeticCuspSingularPointIdeal R π m).IsPrime,
        ¬ (letI := hprime
           IsRegularLocalRing
             (Localization.AtPrime
               (chapter08ArithmeticCuspSingularPointIdeal R π m)))

structure Chapter08ArithmeticCuspSingularExample where
  base : Type u
  [base_commRing : CommRing base]
  uniformizer : base
  exponent : ℕ
  exponent_positive : 0 < exponent
  normal_singular :
    Chapter08ArithmeticCuspSurfaceCanRemainNormalSingular
      base uniformizer exponent

theorem chapter08_arithmetic_cusp_surface_can_remain_normal_singular :
    Nonempty Chapter08ArithmeticCuspSingularExample := by
  sorry

structure Chapter08ArithmeticCuspBlowupChartData
    (R : Type u) [CommRing R] (π : R) (m : ℕ) where
  transformed_plane_curve : Prop
  transformed_vertical_exponent : ℕ
  vertical_exponent_changes : transformed_vertical_exponent ≠ m
  chart_equations : Prop

theorem chapter08_arithmetic_cusp_blowups_change_plane_curve_and_vertical_exponent
    (R : Type u) [CommRing R] (π : R) (m : ℕ) :
    Nonempty (Chapter08ArithmeticCuspBlowupChartData R π m) := by
  sorry

theorem chapter08_cusp_alternation_is_precluded_by_the_triple
    (a : ℕ → ℕ × ℕ × ℕ)
    (hdecrease : ∀ n, chapter08LexLess (a (n + 1)) (a n)) :
    False := by
  exact chapter08_no_infinite_strictly_decreasing_invariant a hdecrease

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter08
