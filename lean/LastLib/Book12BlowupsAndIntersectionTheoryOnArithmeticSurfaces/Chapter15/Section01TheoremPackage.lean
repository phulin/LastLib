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
open LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter10
open LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter11
open LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter12
open LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13
open LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter14
open scoped BigOperators

universe u v

/-! ## 15.1 The theorem package -/

/-! ### (1) The reusable blowup construction -/

theorem chapter15_blowup_relative_proj_presentation
    {X : Scheme.{u}} (I : Chapter15CoherentIdeal X)
    (_hI : chapter15NonzeroCoherentIdeal I) :
    chapter15BlowupIsRelativeProj (chapter15BlowupOfIdeal I) := by
  exact (chapter15BlowupOfIdeal I).rees_presentation

theorem chapter15_blowup_universal_for_invertibility
    {X : Scheme.{u}} {I : Chapter15CoherentIdeal X}
    (B : Chapter15Blowup I) :
    chapter15BlowupUniversalProperty B := by
  exact B.universal

theorem chapter15_blowup_is_local_on_target
    {X : Scheme.{u}} (I : Chapter15CoherentIdeal X)
    (B : Chapter15Blowup I) (U : X.Opens) :
    Nonempty
      (LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.Chapter07BlowupLocalityWitness
        I B U) := by
  exact LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.chapter07_blowup_is_local_on_target
    I B U

theorem chapter15_blowup_commutes_with_flat_base_change
    {X Y : Scheme.{u}} {I : Chapter15CoherentIdeal X}
    (B : Chapter15Blowup I) (f : Y ⟶ X) (hf : Flat f) :
    Nonempty
      (LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.Chapter07BlowupBaseChangeWitness
        B f) := by
  exact LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.chapter07_blowup_commutes_with_flat_base_change
    B f hf

theorem chapter15_blowup_is_projective
    {X : Scheme.{u}} {I : Chapter15CoherentIdeal X}
    (B : Chapter15Blowup I) :
    LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.Chapter07IsProjectiveMorphism
      B.projection := by
  exact LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.chapter07_blowup_is_projective B

/-! ### (2) Point blowups and the exceptional curve -/

theorem chapter15_point_blowup_preserves_regularity
    {X : Scheme.{u}} [Chapter05RegularNoetherianSurface X]
    (P : Chapter05RegularPoint X) :
    Chapter05RegularNoetherianSurface (chapter05PointBlowup P).carrier := by
  exact chapter05_blowup_is_regular P

theorem chapter15_exceptional_curve_is_projective_line
    {X : Scheme.{u}} [Chapter05RegularNoetherianSurface X]
    (P : Chapter05RegularPoint X) :
    Nonempty
      ((chapter05ExceptionalDivisor P).carrier ≅
        chapter05ProjectiveLine (X.residueField P.point)) := by
  exact chapter05_exceptional_divisor_is_projective_line P

theorem chapter15_exceptional_square_is_negative_residue_degree
    {X S : Scheme.{u}} [Chapter05RegularNoetherianSurface X]
    {f : X ⟶ S} [Chapter05ArithmeticSurface X S f]
    (p : Chapter05PointOverBase f)
    (B : Chapter05PointBlowupConstruction p.point)
    (E : Chapter05ExceptionalDivisor B)
    (N : Chapter05ExceptionalNormalData B E)
    [Chapter05CurveDegreeTheory E.carrier (S.residueField (f p.point.point))
      (chapter05ExceptionalBaseMap p B E)] :
    chapter05ExceptionalSelfIntersection p B E N =
      -(chapter05ResidueDegree p : ℤ) := by
  sorry

/-! ### (3) Total transforms, strict transforms, and squares -/

theorem chapter15_total_transform_is_strict_plus_exceptional
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (b : Chapter11PointBlowup p)
    (D : Chapter11Divisor X) :
    chapter11TotalTransform b D =
      chapter11StrictTransformDivisor b D +
        chapter11DivisorMultiplicity D p • chapter11ExceptionalDivisor b := by
  exact chapter11_total_transform_eq_strict_plus_exceptional b D

theorem chapter15_curve_total_transform_formula
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (b : Chapter11PointBlowup p)
    (D : Chapter11CartierCurve X)
    (hmem : chapter11PointLiesOnCurve D p) :
    chapter11TotalTransform b (chapter11CurveAsDivisor D) =
      chapter11StrictTransformDivisor b (chapter11CurveAsDivisor D) +
        (D.multiplicity p : ℤ) • chapter11ExceptionalDivisor b := by
  sorry

theorem chapter15_strict_transform_exceptional_intersection
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (b : Chapter11PointBlowup p)
    (P : Chapter11PointBlowupProjectionData b)
    (D : Chapter11CartierCurve X)
    (hmem : chapter11PointLiesOnCurve D p)
    (hscope : P.source.scope ∧ P.target.scope) :
    P.target.pairing
        (chapter11StrictTransformDivisor b (chapter11CurveAsDivisor D))
        (chapter11ExceptionalDivisor b) =
      (D.multiplicity p : ℤ) * chapter11ResidueDegree p := by
  sorry

theorem chapter15_strict_transform_self_intersection_formula
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (b : Chapter11PointBlowup p)
    (P : Chapter11PointBlowupProjectionData b)
    (D : Chapter11CartierCurve X)
    (hscope : P.source.scope ∧ P.target.scope) :
    P.target.pairing
        (chapter11StrictTransformDivisor b (chapter11CurveAsDivisor D))
        (chapter11StrictTransformDivisor b (chapter11CurveAsDivisor D)) =
      P.source.pairing (chapter11CurveAsDivisor D)
          (chapter11CurveAsDivisor D) -
        (D.multiplicity p : ℤ) * (D.multiplicity p : ℤ) *
          (chapter11ResidueDegree p : ℤ) := by
  exact chapter11_curve_strict_self_intersection_formula b P D hscope

/-! ### (4) Local lengths and global residue weighting -/

theorem chapter15_local_intersection_is_module_length
    {A : Type u} [CommRing A]
    (C D : Chapter15LocalEffectiveCartierCurve A) :
    chapter15LocalIntersectionLength C D =
      Module.length A (A ⧸ Chapter07IntersectionIdeal C D) := by
  exact chapter07_local_intersection_formula C D

theorem chapter15_proper_local_intersection_is_finite
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (C D : Chapter15LocalEffectiveCartierCurve A)
    (hproper : Chapter07ProperIntersectionAt C D) :
    chapter15LocalIntersectionLength C D ≠ ⊤ := by
  exact chapter07_local_intersection_multiplicity_ne_top C D hproper

theorem chapter15_fiberwise_intersection_is_residue_weighted
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
  sorry

theorem chapter15_divisor_curve_intersection_is_residue_weighted_local_sum
    {X : Chapter08ArithmeticSurface}
    [Chapter08LocalIntersectionTheory X]
    {D : Chapter08CartierDivisor X} {C : Chapter08VerticalCurve X}
    [Chapter08CurveDegreeTheory C]
    (I : Chapter08ProperDivisorCurveIntersectionWitness D C) :
    chapter08DivisorCurveIntersection D C =
      chapter08DivisorCurveLocalLengthSum I := by
  sorry

/-! ### (5) Vertical curves, common components, and bilinearity -/

theorem chapter15_vertical_intersection_is_restriction_degree
    {X : Chapter08ArithmeticSurface}
    (D : Chapter08CartierDivisor X) (C : Chapter08VerticalCurve X)
    [Chapter08CurveDegreeTheory C] :
    chapter08DivisorCurveIntersection D C =
      chapter08Degree C (chapter08DivisorLineBundleRestriction D C) := by
  sorry

theorem chapter15_vertical_intersection_handles_common_components
    {X : Chapter08ArithmeticSurface}
    (D : Chapter08CartierDivisor X) (C : Chapter08VerticalCurve X)
    [Chapter08CurveDegreeTheory C] :
    ∃ n : ℤ, chapter08DivisorCurveIntersection D C = n := by
  sorry

theorem chapter15_vertical_curve_intersection_is_symmetric
    {X : Chapter08ArithmeticSurface}
    (C E : Chapter08VerticalCurve X)
    [Chapter08CurveDegreeTheory C] [Chapter08CurveDegreeTheory E] :
    chapter08DivisorCurveIntersection C.asCartierDivisor E =
      chapter08DivisorCurveIntersection E.asCartierDivisor C := by
  sorry

theorem chapter15_vertical_divisor_pairing_is_symmetric
    {X : Chapter08ArithmeticSurface} {s : Chapter08BaseClosedPoint X}
    [∀ C : Chapter08VerticalCurve X, Chapter08CurveDegreeTheory C]
    (V W : Chapter08VerticalDivisor X s) :
    chapter08VerticalDivisorPairing V W =
      chapter08VerticalDivisorPairing W V := by
  sorry

theorem chapter15_vertical_divisor_pairing_additive_left
    {X : Chapter08ArithmeticSurface} {s : Chapter08BaseClosedPoint X}
    [∀ C : Chapter08VerticalCurve X, Chapter08CurveDegreeTheory C]
    (V V' W : Chapter08VerticalDivisor X s) :
    chapter08VerticalDivisorPairing (V + V') W =
      chapter08VerticalDivisorPairing V W +
        chapter08VerticalDivisorPairing V' W := by
  sorry

theorem chapter15_vertical_divisor_pairing_additive_right
    {X : Chapter08ArithmeticSurface} {s : Chapter08BaseClosedPoint X}
    [∀ C : Chapter08VerticalCurve X, Chapter08CurveDegreeTheory C]
    (V W W' : Chapter08VerticalDivisor X s) :
    chapter08VerticalDivisorPairing V (W + W') =
      chapter08VerticalDivisorPairing V W +
        chapter08VerticalDivisorPairing V W' := by
  sorry

/-! ### (6) Projection and finite-flat scaling -/

theorem chapter15_projection_formula
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (D : Chapter10CartierDivisor X)
    (C : Chapter10IntegralCurveOn Y)
    [Chapter10IntersectionTheory X] [Chapter10IntersectionTheory Y]
    (P : Chapter10ProjectionFormulaInput f D C) :
    chapter10IntersectionNumber P.pullback C =
      chapter10IntersectionNumberWithWeilDivisor D P.pushforward := by
  exact chapter10_theorem_10_1_projection_formula f D C P

theorem chapter15_finite_flat_pullback_intersections_scale_by_degree
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (D G : Chapter10CartierDivisor X)
    [Chapter10IntersectionTheory X] [Chapter10IntersectionTheory Y]
    (P : Chapter10FiniteFlatIntersectionData f D G) :
    chapter10IntersectionNumberWithWeilDivisor P.pullbackD P.pullbackG.divisor =
      (P.genericDegree : ℤ) *
        chapter10IntersectionNumberWithWeilDivisor D G.divisor := by
  exact chapter10_finite_flat_intersection_scales_by_degree f D G P

/-! ### (7) Canonical divisors and adjunction -/

theorem chapter15_relative_canonical_divisor_blowup_formula
    {X Y : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier] [Chapter11PicardTheory Y.carrier]
    [Chapter12IntersectionTheory X] [Chapter12IntersectionTheory Y]
    {s : Chapter12ClosedPoint X}
    (B : Chapter12PointBlowup X Y s)
    (P : Chapter12RelativeLCIPresentation X)
    (Q : Chapter12RelativeLCIPresentation Y)
    (K : Chapter12RelativeCanonicalDivisor P) :
    chapter12CanonicalBlowupFormula B K
      (chapter12CompatibleCanonicalDivisor B P Q K) := by
  exact chapter12_relative_canonical_divisor_blowup_formula B P Q K

theorem chapter15_vertical_cartier_curve_adjunction
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    [Chapter12IntersectionTheory X]
    {s : Chapter12ClosedPoint X}
    (P : Chapter12RelativeLCIPresentation X)
    (K : Chapter12RelativeCanonicalDivisor P)
    (C : Chapter12VerticalCurve X s)
    [Chapter11PicardTheory C.carrier]
    [Chapter12CurveEulerCharacteristicTheory C.toChapter12Curve]
    (N : Chapter12ConormalFactor C)
    (A : Chapter12VerticalAdjunctionData P C N) :
    2 * chapter12ArithmeticGenus C.toChapter12Curve - 2 =
      chapter12Intersection K.divisor C.toChapter12Curve +
        chapter12SelfIntersection C.toChapter12Curve := by
  exact chapter12_vertical_adjunction_formula_expanded P K C N A

theorem chapter15_horizontal_cartier_line_bundle_adjunction
    {X : Chapter12ArithmeticSurface}
    [Chapter11PicardTheory X.carrier]
    (P : Chapter12RelativeLCIPresentation X)
    (H : Chapter12RelativeEffectiveCartierDivisor X)
    [Chapter11PicardTheory H.carrier]
    (A : Chapter12RelativeAdjunctionData P H) :
    Nonempty (Chapter11LineBundleIso A.relativeDualizing
      (chapter12RelativeAdjunctionBundle P H)) := by
  sorry

/-! ### (8) The special-fiber matrix -/

theorem chapter15_component_matrix_is_negative_semidefinite
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (a : Fin T.r → ℚ) :
    chapter13VerticalSelfIntersection T a ≤ 0 := by
  exact chapter13_vertical_self_intersection_nonpositive T a

theorem chapter15_component_matrix_fiber_equation
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)) :
    chapter13FiberRelation T := by
  exact chapter13_fiber_relation T

theorem chapter15_component_matrix_kernel_is_the_fiber_line
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (hconn : chapter13GraphConnected T) :
    chapter13RationalMatrixKernel T = chapter13MultiplicityLine T := by
  exact chapter13_rational_intersection_kernel_eq_multiplicity_line T hconn

theorem chapter15_connected_fiber_certificate_gives_graph_connected
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    {T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)}
    (C : Chapter13ConnectedFibersCertificate T) :
    chapter13GraphConnected T := by
  exact chapter13_graph_connected_of_connected_fibers_certificate C

theorem chapter15_component_matrix_kernel_membership_iff
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (hconn : chapter13GraphConnected T) (a : Fin T.r → ℚ) :
    a ∈ chapter13RationalMatrixKernel T ↔
      ∃ c : ℚ, a = c • chapter13RationalMultiplicityVector T := by
  exact chapter13_rational_matrix_kernel_mem_iff_multiple_of_fiber T hconn a

theorem chapter15_component_matrix_is_negative_definite_modulo_fiber
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (hconn : chapter13GraphConnected T) :
    chapter13NegativeDefiniteModuloFiber T := by
  exact chapter13_pairing_negative_definite_on_fiber_quotient T hconn

/-! ### (9) Rational vertical corrections and corrected pairings -/

theorem chapter15_degree_zero_divisor_satisfies_component_compatibility
    {r : ℕ} {F : Chapter14FiberMatrix r}
    (D : Chapter14HorizontalDivisor F) :
    ∑ i, F.multiplicity i * D.componentIntersections i = 0 := by
  exact chapter14_equation_14_1 D

theorem chapter15_vertical_correction_exists
    {r : ℕ} (F : Chapter14FiberMatrix r)
    (hconnected : F.connected)
    (D : Chapter14HorizontalDivisor F) :
    Nonempty (Chapter14VerticalCorrection D) := by
  exact chapter14_vertical_correction_exists F hconnected D

theorem chapter15_vertical_correction_unique_modulo_fiber
    {r : ℕ} {F : Chapter14FiberMatrix r}
    {D : Chapter14HorizontalDivisor F}
    {v w : Chapter14RationalVerticalDivisor F}
    (hv : chapter14Balanced F
      (fun i => (D.componentIntersections i : ℚ)) v)
    (hw : chapter14Balanced F
      (fun i => (D.componentIntersections i : ℚ)) w) :
    chapter14RationallyEquivalentModuloFiber F v w := by
  exact chapter14_vertical_correction_unique_mod_fiber hv hw

theorem chapter15_component_energy_is_nonnegative
    {r : ℕ} (F : Chapter14FiberMatrix r)
    (v : Chapter14RationalVerticalDivisor F) :
    0 ≤ chapter14ComponentEnergy F v := by
  exact chapter14_component_energy_nonnegative F v

theorem chapter15_corrected_local_pairing_is_symmetric
    {r : ℕ} {F : Chapter14FiberMatrix r}
    (I : Chapter14LocalIntersectionData F)
    (D G : Chapter14HorizontalDivisor F)
    (hgeneric : I.genericDisjoint D G)
    (v w : Chapter14RationalVerticalDivisor F)
    (hv : chapter14Balanced F
      (fun i => (D.componentIntersections i : ℚ)) v)
    (hw : chapter14Balanced F
      (fun i => (G.componentIntersections i : ℚ)) w)
    (hgeneric' : I.genericDisjoint G D) :
    chapter14CorrectedLocalPairing I D G hgeneric v =
      chapter14CorrectedLocalPairing I G D hgeneric' w := by
  exact chapter14_corrected_local_pairing_symmetric
    I D G hgeneric v w hv hw hgeneric'

theorem chapter15_fully_corrected_pairing_is_symmetric
    {r : ℕ} {F : Chapter14FiberMatrix r}
    (I : Chapter14LocalIntersectionData F)
    (D G : Chapter14HorizontalDivisor F)
    (hgeneric : I.genericDisjoint D G)
    (v w : Chapter14RationalVerticalDivisor F)
    (hv : chapter14Balanced F
      (fun i => (D.componentIntersections i : ℚ)) v)
    (hw : chapter14Balanced F
      (fun i => (G.componentIntersections i : ℚ)) w)
    (hgeneric' : I.genericDisjoint G D) :
    chapter14FullyCorrectedLocalPairing I D G hgeneric v w =
      chapter14FullyCorrectedLocalPairing I G D hgeneric' w v := by
  exact chapter14_fully_corrected_pairing_is_symmetric
    I D G hgeneric v w hv hw hgeneric'

theorem chapter15_corrected_pairing_is_independent_of_corrections
    {r : ℕ} {F : Chapter14FiberMatrix r}
    (I : Chapter14LocalIntersectionData F)
    (D G : Chapter14HorizontalDivisor F)
    (hgeneric : I.genericDisjoint D G)
    {v v' w w' : Chapter14RationalVerticalDivisor F}
    (hv : chapter14Balanced F
      (fun i => (D.componentIntersections i : ℚ)) v)
    (hv' : chapter14Balanced F
      (fun i => (D.componentIntersections i : ℚ)) v')
    (hw : chapter14Balanced F
      (fun i => (G.componentIntersections i : ℚ)) w)
    (hw' : chapter14Balanced F
      (fun i => (G.componentIntersections i : ℚ)) w') :
    chapter14FullyCorrectedLocalPairing I D G hgeneric v w =
      chapter14FullyCorrectedLocalPairing I D G hgeneric v' w' := by
  exact chapter14_corrected_pairing_independent_of_both_corrections
    I D G hgeneric hv hv' hw hw'

/-! ### (10) Resolution and thickness calculations -/

theorem chapter15_resolution_by_supported_normalized_blowups
    {X : Scheme.{u}} (hX : Chapter06NormalExcellentSurface X) :
    Nonempty (Chapter15NormalizedBlowupResolution hX) := by
  sorry

theorem chapter15_resolution_centers_are_supported_on_the_singular_locus
    {X : Scheme.{u}} (hX : Chapter06NormalExcellentSurface X)
    (r : Chapter06SurfaceResolution hX) :
    r.center ⊆ chapter06SingularLocus hX := by
  exact chapter06_resolution_is_supported_on_singular_locus hX r

theorem chapter15_normalized_blowup_resolution_exists
    {X : Scheme.{u}} (hX : Chapter06NormalExcellentSurface X) :
    Nonempty (Chapter15NormalizedBlowupResolution hX) := by
  exact chapter15_resolution_by_supported_normalized_blowups hX

theorem chapter15_normalized_blowup_resolution_is_supported_on_the_singular_locus
    {X : Scheme.{u}} {hX : Chapter06NormalExcellentSurface X}
    (R : Chapter15NormalizedBlowupResolution hX) :
    chapter15NormalizedBlowupResolutionIsSupportedOnSingularLocus R := by
  exact R.resolution.centerSubsetSingular

theorem chapter15_thickness_blowup_reduces_the_exponent
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (T : Chapter06ThicknessLocalEquation R)
    (B : Chapter06ThicknessBlowupDescription T) :
    T.thickness - 1 < T.thickness := by
  exact chapter06_blowup_thickness_decreases T B

theorem chapter15_thickness_blowup_has_reduced_chart
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (T : Chapter06ThicknessLocalEquation R) :
    Nonempty (Chapter06ThicknessBlowupDescription T) := by
  exact chapter06_blowup_thickness_chart T

theorem chapter15_thickness_resolution_is_a_minus_two_chain
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (T : Chapter06ThicknessLocalEquation R)
    (hclosed : IsAlgClosed (IsLocalRing.ResidueField R)) :
    Nonempty (Chapter06ThicknessResolutionGraph T) := by
  sorry

theorem chapter15_thickness_chain_has_minus_two_exceptionals
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {T : Chapter06ThicknessLocalEquation R}
    (G : Chapter06ThicknessResolutionGraph T) (i : Fin (T.thickness - 1)) :
    (G.exceptionalCurves i).selfIntersection = -2 := by
  sorry

theorem chapter15_thickness_chain_matrix_is_the_negative_cartan_matrix
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {T : Chapter06ThicknessLocalEquation R}
    (G : Chapter06ThicknessResolutionGraph T) :
    G.intersectionMatrix = chapter06NegativeChainMatrix (T.thickness - 1) := by
  sorry

theorem chapter15_total_transform_transports_fiber_multiplicity
    {X Y : Scheme.{u}} {b : Y ⟶ X}
    (T : Chapter06FiberTotalTransformStep b) :
      T.exceptionalMultiplicity =
        chapter06FiberMultiplicitySum T.centerFiberData ∧
      T.uniformizerFiber.fiberOnY =
        chapter06PullbackFormalDivisor b T.uniformizerFiber.fiberOnX := by
  sorry

theorem chapter15_regular_surface_boundary_steps_are_a_separate_resolution_stage :
    ∃ (S X : Scheme.{u}) (f : X ⟶ S),
      Nonempty (Chapter06ArithmeticSurface f) ∧
        Chapter06EmbeddedBoundaryResolution (X := X) := by
  sorry

theorem chapter15_point_blowups_resolve_a_marked_normal_crossing_boundary
    {X : Scheme.{u}} (hX : Chapter06NormalExcellentSurface X)
    (U : Set X) (B : Chapter06NormalCrossingBoundary X)
    (hgood : Chapter06RegularNormalCrossingOpen hX U B) :
    ∃ r : Chapter06BoundaryResolution hX U B,
      chapter06CenterAvoidsOpen r.center U := by
  exact chapter06_resolution_can_avoid_a_regular_normal_crossing_open hX U B hgood

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter15
