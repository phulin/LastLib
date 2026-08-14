import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter15.Dependencies

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter15

noncomputable section

open AlgebraicGeometry CategoryTheory Set
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter11
open LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter05
open LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter06
open LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter07
open LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter08
open LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter09
open LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13
open LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter14
open LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter12
open scoped BigOperators

universe u v

/-! ## 15.3 Failure modes -/

/-! ### Blowup presentations and base change -/

theorem chapter15_affine_blowup_chart_is_a_localized_subalgebra
    (A : Type u) [CommRing A] (a b : A) :
    chapter15AffineBlowupChart A a b =
      Algebra.adjoin A
        ({LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.chapter07FirstRatio
            A a b} : Set (Localization.Away a)) := by
  exact LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.chapter07_two_generator_chart_is_subalgebra_of_localization
    A a b

theorem chapter15_affine_blowup_chart_need_not_be_a_free_polynomial_ring
    (A : Type u) [CommRing A] (a b : A)
    (hchart : chapter15AffineBlowupChartNeedNotBePolynomial A a b) :
    ¬ chapter15ChartIsFreePolynomialPresentation A
      (chapter15AffineBlowupChart A a b) := by
  exact hchart

theorem chapter15_some_blowup_chart_is_not_free_polynomial
    : chapter15ThereExistsANonPolynomialBlowupChart := by
  sorry

theorem chapter15_rees_algebra_need_not_be_the_symmetric_algebra
    (k : Type u) [Field k] :
    chapter15SymmetricToReesMayHaveKernel
      (LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter02.chapter02BivariateSquareIdeal k) := by
  exact LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter02.chapter02_bivariate_square_symmetric_to_rees_has_kernel k

theorem chapter15_flat_base_change_has_all_power_comparisons
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) [Module.Flat R S] :
    LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter03.Chapter03AllPowersBaseChangeComparison I := by
  exact LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter03.chapter03_flat_base_change_has_power_comparisons I

theorem chapter15_arbitrary_base_change_warning_is_the_negation_of_power_compatibility
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) :
    chapter15ArbitraryBaseChangeMayHavePowerTorsion I ↔
      ¬ LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter03.Chapter03AllPowersBaseChangeComparison I := by
  rfl

theorem chapter15_strict_transform_removes_exceptional_components
    {Z Y X : Scheme.{u}} {z : Z ⟶ X} {f : Y ⟶ X}
    (T : LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.Chapter07StrictTransformData z f) :
    ∀ E : LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.Chapter07ExceptionalDivisor f,
      ¬ E.divisor.support ⊆ Set.range T.inclusion := by
  exact LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.chapter07_strict_transform_removes_exceptional_components T

/-! ### Normality, regularity, and semistable reduction -/

theorem chapter15_normality_does_not_imply_regularity
    (k : Type u) [Field k] (hchar : ringChar k ≠ 2) :
    LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04.Chapter04QuadraticConeNormal k ∧
      LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04.Chapter04QuadraticConeOriginNeedsThreeGenerators k ∧
      LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04.Chapter04QuadraticConeOriginSingular k ∧
      LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04.Chapter04QuadraticConeOnlySingularAtOrigin k ∧
      LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04.Chapter04QuadraticConeOriginHasCodimensionTwo k := by
  exact LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04.chapter04_quadratic_cone_normal_not_regular k hchar

theorem chapter15_normalized_surface_can_remain_normal_singular :
    Nonempty
      LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter08.Chapter08ArithmeticCuspSingularExample := by
  exact LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter08.chapter08_arithmetic_cusp_surface_can_remain_normal_singular

theorem chapter15_curve_normalization_need_not_resolve_the_ambient_surface :
    Nonempty Chapter06CurveCuspNormalizationExample := by
  exact chapter06_curve_normalization_does_not_in_general_resolve_a_surface

theorem chapter15_regular_total_space_does_not_force_semistable_fiber :
    Nonempty Chapter06RegularNonSemistableModel := by
  exact chapter06_regular_total_space_does_not_imply_semistable_reduction

theorem chapter15_semistable_reduction_may_require_finite_base_extension :
    ∃ E : Chapter06RegularNonSemistableModel,
      Nonempty (Chapter06SemistableAfterBaseExtension E) := by
  exact chapter06_semistable_reduction_may_require_a_finite_base_extension

theorem chapter15_ramified_node_base_change_produces_thickness
    {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
    (B : Chapter06RamifiedNodeBaseChange R R') (x' y' : R')
    (hxy : x' * y' = algebraMap R R' B.uniformizer) :
    chapter06ThicknessEquation x' y' B.newUniformizer B.ramificationIndex := by
  exact chapter06_ramified_node_base_change_equation B x' y' hxy

theorem chapter15_ramified_node_base_change_is_singular
    {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
    (B : Chapter06RamifiedNodeBaseChange R R') :
    B.baseChangedSurfaceSingular := by
  exact chapter06_ramified_node_base_change_is_singular B

/-! ### Local lengths, normal bundles, and horizontal classes -/

theorem chapter15_common_component_has_infinite_local_length
    {A : Type u} [CommRing A] [IsRegularLocalRing A]
    (hA : Chapter07IsTwoDimensionalRegularLocalRing A)
    {C D : Chapter15LocalEffectiveCartierCurve A}
    (hcommon : ¬ Chapter07NoCommonCurveComponentAt C D) :
    chapter15LocalIntersectionLength C D = ⊤ := by
  exact chapter07_common_component_gives_infinite_length hA hcommon

theorem chapter15_vertical_self_intersection_is_a_normal_bundle_degree
    {X : Chapter08ArithmeticSurface} (C : Chapter08VerticalCurve X)
    [Chapter08CurveDegreeTheory C] :
    chapter08DivisorCurveIntersection C.asCartierDivisor C =
      chapter08Degree C (chapter08NormalBundle C) := by
  exact chapter08_vertical_curve_selfIntersection_eq_normal_degree C

theorem chapter15_horizontal_self_intersection_is_a_norm_line_bundle_class
    {X : Chapter08ArithmeticSurface}
    (H : Chapter08HorizontalCartierCurve X)
    [Chapter08FiniteFlatNormTheory H] :
    chapter08HorizontalSelfIntersectionClass H =
      chapter08FiniteFlatNorm H (chapter08HorizontalNormalBundle H) := by
  exact chapter08_horizontal_selfIntersection_class_is_norm_of_normal_bundle H

theorem chapter15_horizontal_self_intersection_number_requires_extra_degree_data
    {X : Chapter08ArithmeticSurface}
    (H : Chapter08HorizontalCartierCurve X)
    [Chapter08FiniteFlatNormTheory H]
    [Chapter08ProperBaseCurveDegreeTheory X] :
    chapter08HorizontalSelfIntersectionNumber H =
      Chapter08ProperBaseCurveDegreeTheory.degree
        (chapter08FiniteFlatNorm H (chapter08HorizontalNormalBundle H)) := by
  exact chapter08_horizontal_selfIntersection_number_eq_degree_of_norm H

theorem chapter15_horizontal_local_order_changes_by_a_principal_order
    {X : Chapter08ArithmeticSurface}
    (T : Chapter08DVRLocalOrderTheory X)
    (t₁ t₂ : Chapter08DVRLocalTrivialization X) :
    ∃ f : T.rationalFunctions,
      t₂.localOrder - t₁.localOrder = T.principalOrder f := by
  exact chapter08_dvr_local_order_changes_by_principal_divisor T t₁ t₂

theorem chapter15_principal_divisor_has_zero_vertical_intersection
    {X : Chapter08ArithmeticSurface}
    (f : Chapter08PrincipalDivisorData X)
    (C : Chapter08VerticalCurve X)
    [Chapter08CurveDegreeTheory C] :
    chapter08DivisorCurveIntersection f.divisor C = 0 := by
  exact chapter08_principal_divisor_intersection_with_vertical_curve_zero f C

def chapter15BaseUniformizerBoundaryWarning
    {X S : Scheme.{u}} (f : X ⟶ S) (s : S) (z : Chapter09ZeroCycle X) : Prop :=
  chapter09PositiveHorizontalBoundaryWarning f s z

theorem chapter15_base_uniformizer_boundary_has_nonzero_degree
    {X S : Scheme.{u}} (f : X ⟶ S) (s : S) (z : Chapter09ZeroCycle X)
    (h : chapter15BaseUniformizerBoundaryWarning f s z) :
    chapter09ZeroCycleDegree f z ≠ 0 := by
  exact chapter09_positive_horizontal_boundary_has_nonzero_degree f s z h

/-! ### Matrix kernels and rational corrections -/

theorem chapter15_unreduced_special_fiber_matrix_is_not_negative_definite
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)) :
    chapter13VerticalSelfIntersection T
        (chapter13RationalMultiplicityVector T) = 0 := by
  exact chapter13_unreduced_matrix_is_not_negative_definite T

theorem chapter15_connected_fiber_has_exactly_the_full_fiber_kernel
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (hconn : chapter13GraphConnected T) :
    chapter13RationalMatrixKernel T = chapter13MultiplicityLine T := by
  exact chapter13_rational_intersection_kernel_eq_multiplicity_line T hconn

theorem chapter15_integral_correction_can_fail
    (q : ℤ) (hq : 0 < q) (a : ℤ) (ha : ¬ q ∣ a) :
    ¬ ∃ v : Chapter14IntegralVector 2,
      chapter14MatrixVec (chapter14TwoComponentMatrix q) v =
        -chapter14TwoComponentVector a := by
  exact chapter14_two_component_no_integral_correction_of_not_dvd q hq a ha

/-! ### Numerical recognition of exceptional curves -/

theorem chapter15_minus_two_curve_is_not_a_point_blowup_signature
    {k : Type u} [Field k]
    (C : Chapter05CurveNumericalData k)
    (hC : C.selfIntersection = -2) :
    ¬ chapter05PointBlowupNumericalSignature C := by
  exact chapter05_minus_two_curve_is_not_a_point_blowup_signature C hC

theorem chapter15_positive_genus_curve_is_not_a_point_blowup_signature
    {k : Type u} [Field k]
    (C : Chapter05CurveNumericalData k)
    (hgenus : 0 < C.genus) :
    ¬ chapter05PointBlowupNumericalSignature C := by
  exact chapter05_positive_genus_curve_is_not_a_point_blowup_signature C hgenus

def chapter15PointBlowupRecognitionNeedsGeometry :=
  Chapter05RecognitionDataNeedsGeometry

theorem chapter15_numerical_exceptional_data_keeps_contraction_as_separate_input
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    [Chapter12IntersectionTheory X]
    (P : Chapter12RelativeLCIPresentation X)
    (K : Chapter12RelativeCanonicalDivisor P)
    (E : Chapter12Curve X)
    [Chapter12CurveEulerCharacteristicTheory E] 
    (D : Chapter12ExceptionalCurveRecognitionData P K E) :
    D.projectiveLineGeometry ∧ D.normalBundleGeometry ∧
      D.contractionToRegularSurface ∧ D.inversePointBlowup := by
  exact ⟨D.projectiveLineGeometry, D.normalBundleGeometry,
    D.contractionToRegularSurface, D.inversePointBlowup⟩

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter15
