import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter10.Section04FiniteMapsAndDegree
import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter11.Section02IntersectionsOfStrictTransforms
import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter14.Section03TheCorrectedLocalPairing

/-!
# Book 12, Chapter 14, §14.4: functoriality and base change
-/

noncomputable section

open scoped BigOperators

universe u v

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter14

open AlgebraicGeometry CategoryTheory
open LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter10
open LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter11

/-! ## Canonical Chapter 10--13 bridges -/

/-!
These small wrappers retain the canonical Chapter 10 inputs.  The Chapter 14
coefficient records can then consume the resulting projection/scaling facts
without making those formulas a second, disconnected source of data.
-/
structure Chapter14CanonicalProjectionFormulaData
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (D : Chapter10CartierDivisor X)
    (C : Chapter10IntegralCurveOn Y)
    [Chapter10IntersectionTheory X] [Chapter10IntersectionTheory Y] where
  projection : Chapter10ProjectionFormulaInput f D C

theorem chapter14_canonical_projection_formula
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (D : Chapter10CartierDivisor X)
    (C : Chapter10IntegralCurveOn Y)
    [Chapter10IntersectionTheory X] [Chapter10IntersectionTheory Y]
    (P : Chapter14CanonicalProjectionFormulaData f D C) :
    chapter10IntersectionNumber P.projection.pullback C =
      chapter10IntersectionNumberWithWeilDivisor D P.projection.pushforward := by
  sorry

structure Chapter14CanonicalFiniteFlatIntersectionData
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (D G : Chapter10CartierDivisor X)
    [Chapter10IntersectionTheory X] [Chapter10IntersectionTheory Y]
    [QuasiCompact f] where
  finiteFlat : Chapter10FiniteFlatIntersectionData f D G

theorem chapter14_canonical_finite_flat_intersection_scales
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (D G : Chapter10CartierDivisor X)
    [Chapter10IntersectionTheory X] [Chapter10IntersectionTheory Y]
    [QuasiCompact f]
    (P : Chapter14CanonicalFiniteFlatIntersectionData f D G) :
    chapter10IntersectionNumberWithWeilDivisor
        P.finiteFlat.pullbackD P.finiteFlat.pullbackG.divisor =
      (P.finiteFlat.genericDegree : ℤ) *
        chapter10IntersectionNumberWithWeilDivisor D G.divisor := by
  sorry

/-! ## Finite flat maps and projection -/

/- LOCAL_DEPENDENCY_GUESS: the preceding surface chapters supply the actual
pullback/pushforward operations on divisors.  This correspondence record
keeps their component, raw-intersection, and generic-degree compatibilities
explicit while reusing the component matrix from this chapter. -/
structure Chapter14FiniteFlatIntersectionCorrespondence
    {Y X : Type u} {S : Type v}
    (Ydata : Chapter14ArithmeticSurfaceData Y S)
    (Xdata : Chapter14ArithmeticSurfaceData X S)
    (f : Y → X)
    {r t : ℕ}
    (down : Chapter14FiberMatrix r)
    (up : Chapter14FiberMatrix t)
    (C : Chapter14ComponentCorrespondence down up)
    (Idown : Chapter14LocalIntersectionData down)
    (Iup : Chapter14LocalIntersectionData up) where
  surfaceMap : Chapter14FiniteFlatSurfaceMap Ydata Xdata f
  pullbackHorizontal : Chapter14HorizontalDivisor down →
    Chapter14HorizontalDivisor up
  pushforwardHorizontal : Chapter14HorizontalDivisor up →
    Chapter14HorizontalDivisor down
  pullbackVertical : Chapter14RationalVector r →
    Chapter14RationalVector t
  pullbackVertical_add : ∀ v w,
    pullbackVertical (v + w) = pullbackVertical v + pullbackVertical w
  pullbackVertical_smul : ∀ (a : ℚ) v,
    pullbackVertical (a • v) = a • pullbackVertical v
  pullback_vertical_matrix_compatibility :
    ∀ v, chapter14MatrixVec (chapter14FiberRationalMatrix up)
        (pullbackVertical v) =
      chapter14TransposeComponentVector C
        (chapter14MatrixVec (chapter14FiberRationalMatrix down) v)
  pullback_component_intersections :
    ∀ (D : Chapter14HorizontalDivisor down),
      (pullbackHorizontal D).componentIntersections =
      fun j => ∑ i, C.pushforward i j * D.componentIntersections i
  raw_projection_formula :
    ∀ (D : Chapter14HorizontalDivisor down)
      (H : Chapter14HorizontalDivisor up)
      (hup : Iup.genericDisjoint (pullbackHorizontal D) H)
      (hdown : Idown.genericDisjoint D (pushforwardHorizontal H)),
      Iup.rawIntersection (pullbackHorizontal D) H hup =
        Idown.rawIntersection D (pushforwardHorizontal H) hdown
  vertical_pullback_projection_formula :
    ∀ (v : Chapter14RationalVector r)
      (H : Chapter14HorizontalDivisor up),
      chapter14VerticalAgainstHorizontal (pullbackVertical v)
          H.componentIntersections =
        chapter14VerticalAgainstHorizontal v
          (pushforwardHorizontal H).componentIntersections
  raw_pullback_scaling :
    ∀ (D G : Chapter14HorizontalDivisor down)
      (hup : Iup.genericDisjoint
        (pullbackHorizontal D) (pullbackHorizontal G))
      (hdown : Idown.genericDisjoint D G),
      Iup.rawIntersection (pullbackHorizontal D) (pullbackHorizontal G) hup =
        (surfaceMap.generic_degree : ℤ) * Idown.rawIntersection D G hdown
  pullback_vertical_intersection_scaling :
    ∀ (v w : Chapter14RationalVector r),
      chapter14VerticalIntersection up
          (pullbackVertical v) (pullbackVertical w) =
        (surfaceMap.generic_degree : ℚ) *
          chapter14VerticalIntersection down v w
  pullback_generic_degree :
    ∀ (D : Chapter14HorizontalDivisor down),
      (pullbackHorizontal D).genericDegree =
      (surfaceMap.generic_degree : ℤ) * D.genericDegree
  pushforward_generic_degree :
    ∀ (H : Chapter14HorizontalDivisor up),
      (pushforwardHorizontal H).genericDegree = H.genericDegree
  pushforward_pullback_component_intersections :
    ∀ (D : Chapter14HorizontalDivisor down),
      (pushforwardHorizontal (pullbackHorizontal D)).componentIntersections =
      fun i => (surfaceMap.generic_degree : ℤ) * D.componentIntersections i

def chapter14PullbackCorrectionCoefficients
    {Y X : Type u} {S : Type v}
    {Ydata : Chapter14ArithmeticSurfaceData Y S}
    {Xdata : Chapter14ArithmeticSurfaceData X S}
    {f : Y → X}
    {r t : ℕ}
    {down : Chapter14FiberMatrix r}
    {up : Chapter14FiberMatrix t}
    {C : Chapter14ComponentCorrespondence down up}
    {Idown : Chapter14LocalIntersectionData down}
    {Iup : Chapter14LocalIntersectionData up}
    (_A : Chapter14FiniteFlatIntersectionCorrespondence
      Ydata Xdata f down up C Idown Iup)
    (v : Chapter14RationalVector r) : Chapter14RationalVector t :=
  _A.pullbackVertical v

/- The transpose of the pushforward matrix acts on component intersection
vectors; coefficients of a pulled-back vertical divisor use the separate
ramification-index map `pullbackVertical`. -/

theorem chapter14_pullback_component_vector_is_transpose_pushforward
    {Y X : Type u} {S : Type v}
    {Ydata : Chapter14ArithmeticSurfaceData Y S}
    {Xdata : Chapter14ArithmeticSurfaceData X S}
    {f : Y → X}
    {r t : ℕ}
    {down : Chapter14FiberMatrix r}
    {up : Chapter14FiberMatrix t}
    {C : Chapter14ComponentCorrespondence down up}
    {Idown : Chapter14LocalIntersectionData down}
    {Iup : Chapter14LocalIntersectionData up}
    (A : Chapter14FiniteFlatIntersectionCorrespondence
      Ydata Xdata f down up C Idown Iup)
    (D : Chapter14HorizontalDivisor down) :
    (A.pullbackHorizontal D).componentIntersections =
      fun j => ∑ i, C.pushforward i j * D.componentIntersections i := by
  exact A.pullback_component_intersections D

theorem chapter14_pullback_preserves_generic_degree_zero
    {Y X : Type u} {S : Type v}
    {Ydata : Chapter14ArithmeticSurfaceData Y S}
    {Xdata : Chapter14ArithmeticSurfaceData X S}
    {f : Y → X}
    {r t : ℕ}
    {down : Chapter14FiberMatrix r}
    {up : Chapter14FiberMatrix t}
    {C : Chapter14ComponentCorrespondence down up}
    {Idown : Chapter14LocalIntersectionData down}
    {Iup : Chapter14LocalIntersectionData up}
    (A : Chapter14FiniteFlatIntersectionCorrespondence
      Ydata Xdata f down up C Idown Iup)
    (D : Chapter14HorizontalDivisor down) :
    (A.pullbackHorizontal D).genericDegree = 0 := by
  rw [A.pullback_generic_degree, D.genericDegree_zero]
  simp

theorem chapter14_pushforward_preserves_generic_degree_zero
    {Y X : Type u} {S : Type v}
    {Ydata : Chapter14ArithmeticSurfaceData Y S}
    {Xdata : Chapter14ArithmeticSurfaceData X S}
    {f : Y → X}
    {r t : ℕ}
    {down : Chapter14FiberMatrix r}
    {up : Chapter14FiberMatrix t}
    {C : Chapter14ComponentCorrespondence down up}
    {Idown : Chapter14LocalIntersectionData down}
    {Iup : Chapter14LocalIntersectionData up}
    (A : Chapter14FiniteFlatIntersectionCorrespondence
      Ydata Xdata f down up C Idown Iup)
    (H : Chapter14HorizontalDivisor up) :
    (A.pushforwardHorizontal H).genericDegree = 0 ↔
      H.genericDegree = 0 := by
  rw [A.pushforward_generic_degree]

theorem chapter14_component_projection_formula
    {Y X : Type u} {S : Type v}
    {Ydata : Chapter14ArithmeticSurfaceData Y S}
    {Xdata : Chapter14ArithmeticSurfaceData X S}
    {f : Y → X}
    {r t : ℕ}
    {down : Chapter14FiberMatrix r}
    {up : Chapter14FiberMatrix t}
    {C : Chapter14ComponentCorrespondence down up}
    {Idown : Chapter14LocalIntersectionData down}
    {Iup : Chapter14LocalIntersectionData up}
    (A : Chapter14FiniteFlatIntersectionCorrespondence
      Ydata Xdata f down up C Idown Iup)
    (D : Chapter14HorizontalDivisor down)
    (c : Chapter14RationalVector t) :
    chapter14VerticalAgainstHorizontal c
        (A.pullbackHorizontal D).componentIntersections =
      chapter14VerticalAgainstHorizontal
        (chapter14PushforwardComponentVector C c)
        D.componentIntersections := by
  sorry

theorem chapter14_pullback_correction_is_balanced
    {Y X : Type u} {S : Type v}
    {Ydata : Chapter14ArithmeticSurfaceData Y S}
    {Xdata : Chapter14ArithmeticSurfaceData X S}
    {f : Y → X}
    {r t : ℕ}
    {down : Chapter14FiberMatrix r}
    {up : Chapter14FiberMatrix t}
    {C : Chapter14ComponentCorrespondence down up}
    {Idown : Chapter14LocalIntersectionData down}
    {Iup : Chapter14LocalIntersectionData up}
    (A : Chapter14FiniteFlatIntersectionCorrespondence
      Ydata Xdata f down up C Idown Iup)
    (D : Chapter14HorizontalDivisor down)
    (v : Chapter14RationalVector r)
    (hv : chapter14Balanced down
      (fun i => (D.componentIntersections i : ℚ)) v) :
    chapter14Balanced up
      (fun j => ((A.pullbackHorizontal D).componentIntersections j : ℚ))
      (chapter14PullbackCorrectionCoefficients A v) := by
  sorry

theorem chapter14_upstairs_correction_class_is_pullback_class
    {Y X : Type u} {S : Type v}
    {Ydata : Chapter14ArithmeticSurfaceData Y S}
    {Xdata : Chapter14ArithmeticSurfaceData X S}
    {f : Y → X}
    {r t : ℕ}
    {down : Chapter14FiberMatrix r}
    {up : Chapter14FiberMatrix t}
    {C : Chapter14ComponentCorrespondence down up}
    {Idown : Chapter14LocalIntersectionData down}
    {Iup : Chapter14LocalIntersectionData up}
    (A : Chapter14FiniteFlatIntersectionCorrespondence
      Ydata Xdata f down up C Idown Iup)
    (_hupconnected : up.connected)
    (D : Chapter14HorizontalDivisor down)
    (v : Chapter14RationalVector r)
    (hv : chapter14Balanced down
      (fun i => (D.componentIntersections i : ℚ)) v)
    (w : Chapter14RationalVector t)
    (hw : chapter14Balanced up
      (fun j => ((A.pullbackHorizontal D).componentIntersections j : ℚ)) w) :
    chapter14RationallyEquivalentModuloFiber up
      (chapter14PullbackCorrectionCoefficients A v) w := by
  exact chapter14_vertical_correction_unique_mod_fiber
    (chapter14_pullback_correction_is_balanced A D v hv) hw

theorem chapter14_corrected_pairing_projection_formula
    {Y X : Type u} {S : Type v}
    {Ydata : Chapter14ArithmeticSurfaceData Y S}
    {Xdata : Chapter14ArithmeticSurfaceData X S}
    {f : Y → X}
    {r t : ℕ}
    {down : Chapter14FiberMatrix r}
    {up : Chapter14FiberMatrix t}
    {C : Chapter14ComponentCorrespondence down up}
    {Idown : Chapter14LocalIntersectionData down}
    {Iup : Chapter14LocalIntersectionData up}
    (A : Chapter14FiniteFlatIntersectionCorrespondence
      Ydata Xdata f down up C Idown Iup)
    (D : Chapter14HorizontalDivisor down)
    (H : Chapter14HorizontalDivisor up)
    (hdown : Idown.genericDisjoint D (A.pushforwardHorizontal H))
    (hup : Iup.genericDisjoint (A.pullbackHorizontal D) H)
    (v : Chapter14RationalVector r)
    (hv : chapter14Balanced down
      (fun i => (D.componentIntersections i : ℚ)) v) :
    chapter14CorrectedLocalPairing Iup
        (A.pullbackHorizontal D) H hup
        (chapter14PullbackCorrectionCoefficients A v) =
      chapter14CorrectedLocalPairing Idown D
        (A.pushforwardHorizontal H) hdown v := by
  sorry

theorem chapter14_corrected_pairing_pullback_pullback_scales
    {Y X : Type u} {S : Type v}
    {Ydata : Chapter14ArithmeticSurfaceData Y S}
    {Xdata : Chapter14ArithmeticSurfaceData X S}
    {f : Y → X}
    {r t : ℕ}
    {down : Chapter14FiberMatrix r}
    {up : Chapter14FiberMatrix t}
    {C : Chapter14ComponentCorrespondence down up}
    {Idown : Chapter14LocalIntersectionData down}
    {Iup : Chapter14LocalIntersectionData up}
    (A : Chapter14FiniteFlatIntersectionCorrespondence
      Ydata Xdata f down up C Idown Iup)
    (hflat : A.surfaceMap.flat)
    (D G : Chapter14HorizontalDivisor down)
    (hdown : Idown.genericDisjoint D G)
    (hup : Iup.genericDisjoint
      (A.pullbackHorizontal D) (A.pullbackHorizontal G))
    (v w : Chapter14RationalVector r)
    (hv : chapter14Balanced down
      (fun i => (D.componentIntersections i : ℚ)) v)
    (hw : chapter14Balanced down
      (fun i => (G.componentIntersections i : ℚ)) w) :
    chapter14FullyCorrectedLocalPairing Iup
        (A.pullbackHorizontal D) (A.pullbackHorizontal G) hup
        (chapter14PullbackCorrectionCoefficients A v)
        (chapter14PullbackCorrectionCoefficients A w) =
      (A.surfaceMap.generic_degree : ℚ) *
        chapter14FullyCorrectedLocalPairing Idown D G hdown v w := by
  sorry

/-! ## Unramified and ramified base change -/

structure Chapter14ResidueDegreeWeightedSplit
    (A B : Type*) [Fintype A] [Fintype B] [DecidableEq A] where
  map : B → A
  downstairsWeight : A → ℕ
  upstairsWeight : B → ℕ
  total_weight : ∀ a,
    downstairsWeight a =
      ∑ b ∈ (Finset.univ : Finset B).filter (fun b => map b = a),
        upstairsWeight b

theorem chapter14_unramified_residue_weights_preserve_total_contribution
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    (S : Chapter14ResidueDegreeWeightedSplit A B)
    (φ : A → ℚ) :
    ∑ a, (S.downstairsWeight a : ℚ) * φ a =
      ∑ b, (S.upstairsWeight b : ℚ) * φ (S.map b) := by
  sorry

structure Chapter14BaseChangeCaution where
  residue_extension_unramified : Prop
  components_may_split : Prop
  closed_intersection_points_may_split : Prop
  residue_degree_weights_preserve_totals : Prop
  residue_extension_ramified : Prop
  fiber_multiplicities_may_change : Prop
  base_changed_total_space_may_be_singular : Prop
  normalization_required_before_matrix : Prop
  resolution_required_before_matrix : Prop
  common_regular_domination_available : Prop
  matrix_is_not_naive_graph_copy : Prop
  matrix_compared_by_pullback_pushforward_on_domination : Prop
  ramified_changes_multiplicities :
    residue_extension_ramified → fiber_multiplicities_may_change
  ramified_may_make_total_space_singular :
    residue_extension_ramified → base_changed_total_space_may_be_singular
  ramified_requires_normalization :
    residue_extension_ramified → normalization_required_before_matrix
  ramified_requires_resolution :
    residue_extension_ramified → resolution_required_before_matrix
  ramified_has_common_regular_domination :
    residue_extension_ramified → common_regular_domination_available
  ramified_is_not_naive_graph_copy :
    residue_extension_ramified → matrix_is_not_naive_graph_copy
  ramified_matrix_comparison :
    residue_extension_ramified →
      matrix_compared_by_pullback_pushforward_on_domination

theorem chapter14_ramified_base_change_requires_regularization
    (B : Chapter14BaseChangeCaution)
    (hramified : B.residue_extension_ramified) :
    B.normalization_required_before_matrix ∧
      B.resolution_required_before_matrix := by
  exact ⟨B.ramified_requires_normalization hramified,
    B.ramified_requires_resolution hramified⟩

theorem chapter14_ramified_base_change_can_change_matrix_data
    (B : Chapter14BaseChangeCaution)
    (hramified : B.residue_extension_ramified) :
    B.fiber_multiplicities_may_change ∧
      B.base_changed_total_space_may_be_singular ∧
      B.matrix_is_not_naive_graph_copy := by
  exact ⟨B.ramified_changes_multiplicities hramified,
    B.ramified_may_make_total_space_singular hramified,
    B.ramified_is_not_naive_graph_copy hramified⟩

theorem chapter14_regularized_base_change_is_compared_on_common_domination
    (B : Chapter14BaseChangeCaution)
    (hramified : B.residue_extension_ramified) :
    B.common_regular_domination_available := by
  exact B.ramified_has_common_regular_domination hramified

theorem chapter14_regularized_base_change_matrix_comparison
    (B : Chapter14BaseChangeCaution)
    (hramified : B.residue_extension_ramified) :
    B.matrix_compared_by_pullback_pushforward_on_domination := by
  exact B.ramified_matrix_comparison hramified

/-!
The qualitative caution is paired here with the canonical Chapter 10 local
extension and fiber-scaling records.  The exact uniformizer and total-fiber
identities are consequently read from those records rather than restated as
free Chapter 14 assumptions.
-/
structure Chapter14CanonicalBaseChangeCertificate
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    {R R' : Type u} [CommRing R] [CommRing R'] where
  localExtension : Chapter10FiniteDVRFiberData R R'
  fiberScaling : Chapter10DVRFiberDivisorScalingData f
  caution : Chapter14BaseChangeCaution

theorem chapter14_canonical_base_change_uniformizer_formula
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    {R R' : Type u} [CommRing R] [CommRing R']
    (B : Chapter14CanonicalBaseChangeCertificate (R := R) (R' := R') f) :
    B.localExtension.map B.localExtension.uniformizer =
      B.localExtension.unit *
        B.localExtension.uniformizer' ^ B.localExtension.ramificationIndex := by
  sorry

theorem chapter14_canonical_base_change_fiber_scaling_formula
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    {R R' : Type u} [CommRing R] [CommRing R']
    (B : Chapter14CanonicalBaseChangeCertificate (R := R) (R' := R') f) :
    B.fiberScaling.pulledBackBaseFiber.cycle =
      (B.fiberScaling.ramificationIndex : ℤ) •
        B.fiberScaling.totalFiberOnY.cycle := by
  sorry

/-! ## Point blowups and birational invariance -/

structure Chapter14BlowupDivisorExpression
    {t : ℕ} (F : Chapter14FiberMatrix t) where
  horizontalPart : Chapter14HorizontalDivisor F
  verticalPart : Chapter14RationalVector t

/- LOCAL_DEPENDENCY_GUESS: the preceding blowup chapter supplies strict and
total transforms, exceptional components, and their projection formulas.  The
record below is the exact coefficient-level interface consumed by the
correction calculation. -/
structure Chapter14PointBlowupData
    {r t : ℕ}
    (down : Chapter14FiberMatrix r)
    (up : Chapter14FiberMatrix t)
    (C : Chapter14ComponentCorrespondence down up)
    (Idown : Chapter14LocalIntersectionData down)
    (Iup : Chapter14LocalIntersectionData up) where
  is_point_blowup : Prop
  is_point_blowup_evidence : is_point_blowup
  new_component_count : t = r + 1
  strictTransform : Chapter14HorizontalDivisor down →
    Chapter14HorizontalDivisor up
  exceptional : Fin t
  exceptionalVector : Chapter14RationalVector t
  exceptionalVector_is_basis :
    ∀ j, exceptionalVector j = if j = exceptional then 1 else 0
  centerResidueDegree : ℕ
  centerResidueDegree_pos : 0 < centerResidueDegree
  multiplicityAtPoint : Chapter14HorizontalDivisor down → ℤ
  pullbackVertical : Chapter14RationalVector r → Chapter14RationalVector t
  pullback_vertical_pushforward_identity :
    ∀ v, chapter14PushforwardComponentVector C (pullbackVertical v) = v
  pullback_vertical_matrix_compatibility :
    ∀ v, chapter14MatrixVec (chapter14FiberRationalMatrix up)
        (pullbackVertical v) =
      chapter14TransposeComponentVector C
        (chapter14MatrixVec (chapter14FiberRationalMatrix down) v)
  strict_transform_component_intersections :
    ∀ (D : Chapter14HorizontalDivisor down) (j : Fin t),
      ((strictTransform D).componentIntersections j : ℚ) =
        (∑ i, (C.pushforward i j : ℚ) *
          (D.componentIntersections i : ℚ)) -
        (multiplicityAtPoint D : ℚ) *
          chapter14MatrixVec (chapter14FiberRationalMatrix up)
            exceptionalVector j
  exceptional_against_strict_transform :
    ∀ (D : Chapter14HorizontalDivisor down),
      chapter14DotProduct exceptionalVector
          (fun j => ((strictTransform D).componentIntersections j : ℚ)) =
        (multiplicityAtPoint D : ℚ) * (centerResidueDegree : ℚ)
  exceptional_self_intersection :
    chapter14VerticalIntersection up exceptionalVector exceptionalVector =
      -(centerResidueDegree : ℚ)
  total_pullback_orthogonal_to_exceptional :
    ∀ v, chapter14VerticalIntersection up
      (pullbackVertical v) exceptionalVector = 0
  raw_strict_transform_projection :
    ∀ (D G : Chapter14HorizontalDivisor down)
      (hup : Iup.genericDisjoint (strictTransform D) (strictTransform G))
      (hdown : Idown.genericDisjoint D G),
      Iup.rawIntersection (strictTransform D) (strictTransform G) hup =
        Idown.rawIntersection D G hdown -
          multiplicityAtPoint D * multiplicityAtPoint G *
            (centerResidueDegree : ℤ)

/-!
The coefficient-level point-blowup certificate is also available directly
from the canonical Chapter 11 blowup and projection records.  This bridge
keeps strict/total transforms, exceptional orthogonality, and the residue
degree tied to their geometric source.
-/
structure Chapter14CanonicalPointBlowupCertificate
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X} where
  blowup : Chapter11PointBlowup p
  projection : Chapter11PointBlowupProjectionData blowup

theorem chapter14_canonical_point_blowup_total_transform_formula
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (B : Chapter14CanonicalPointBlowupCertificate (p := p))
    (D : Chapter11Divisor X) :
    chapter11TotalTransform B.blowup D =
      chapter11StrictTransformDivisor B.blowup D +
        chapter11DivisorMultiplicity D p • chapter11ExceptionalDivisor B.blowup := by
  sorry

theorem chapter14_canonical_point_blowup_intersection_formula
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (B : Chapter14CanonicalPointBlowupCertificate (p := p))
    (D G : Chapter11Divisor X)
    (hscope : B.projection.source.scope ∧ B.projection.target.scope) :
    B.projection.target.pairing
        (chapter11StrictTransformDivisor B.blowup D)
        (chapter11StrictTransformDivisor B.blowup G) =
      B.projection.source.pairing D G -
        chapter11DivisorMultiplicity D p *
          chapter11DivisorMultiplicity G p *
            (chapter11ResidueDegree p : ℤ) := by
  sorry

theorem chapter14_canonical_point_blowup_exceptional_orthogonality
    {S : Chapter11ArithmeticBase}
    {X : Chapter11ArithmeticSurface S}
    {p : Chapter11SurfacePoint X}
    (B : Chapter14CanonicalPointBlowupCertificate (p := p))
    (D : Chapter11Divisor X)
    (hscope : B.projection.source.scope ∧ B.projection.target.scope) :
    B.projection.target.pairing
        (chapter11TotalTransform B.blowup D)
        (chapter11ExceptionalDivisor B.blowup) = 0 := by
  sorry

def chapter14PointBlowupPullbackOfHorizontal
    {r t : ℕ}
    {down : Chapter14FiberMatrix r}
    {up : Chapter14FiberMatrix t}
    {C : Chapter14ComponentCorrespondence down up}
    {Idown : Chapter14LocalIntersectionData down}
    {Iup : Chapter14LocalIntersectionData up}
    (B : Chapter14PointBlowupData down up C Idown Iup)
    (D : Chapter14HorizontalDivisor down) :
    Chapter14BlowupDivisorExpression up :=
  { horizontalPart := B.strictTransform D
    verticalPart :=
      (B.multiplicityAtPoint D : ℚ) • B.exceptionalVector }

def chapter14PointBlowupCorrectionOfStrictTransform
    {r t : ℕ}
    {down : Chapter14FiberMatrix r}
    {up : Chapter14FiberMatrix t}
    {C : Chapter14ComponentCorrespondence down up}
    {Idown : Chapter14LocalIntersectionData down}
    {Iup : Chapter14LocalIntersectionData up}
    (B : Chapter14PointBlowupData down up C Idown Iup)
    (D : Chapter14HorizontalDivisor down)
    (v : Chapter14RationalVector r) : Chapter14RationalVector t :=
  B.pullbackVertical v +
    (B.multiplicityAtPoint D : ℚ) • B.exceptionalVector

def chapter14PointBlowupPullbackOfCorrectedDivisor
    {r t : ℕ}
    {down : Chapter14FiberMatrix r}
    {up : Chapter14FiberMatrix t}
    {C : Chapter14ComponentCorrespondence down up}
    {Idown : Chapter14LocalIntersectionData down}
    {Iup : Chapter14LocalIntersectionData up}
    (B : Chapter14PointBlowupData down up C Idown Iup)
    (D : Chapter14HorizontalDivisor down)
    (v : Chapter14RationalVector r) :
    Chapter14BlowupDivisorExpression up :=
  { horizontalPart := B.strictTransform D
    verticalPart := chapter14PointBlowupCorrectionOfStrictTransform B D v }

theorem chapter14_point_blowup_total_pullback_formula
    {r t : ℕ}
    {down : Chapter14FiberMatrix r}
    {up : Chapter14FiberMatrix t}
    {C : Chapter14ComponentCorrespondence down up}
    {Idown : Chapter14LocalIntersectionData down}
    {Iup : Chapter14LocalIntersectionData up}
    (B : Chapter14PointBlowupData down up C Idown Iup)
    (D : Chapter14HorizontalDivisor down) :
    chapter14PointBlowupPullbackOfHorizontal B D =
      { horizontalPart := B.strictTransform D
        verticalPart :=
          (B.multiplicityAtPoint D : ℚ) • B.exceptionalVector } := by
  rfl

theorem chapter14_point_blowup_balanced_correction_formula
    {r t : ℕ}
    {down : Chapter14FiberMatrix r}
    {up : Chapter14FiberMatrix t}
    {C : Chapter14ComponentCorrespondence down up}
    {Idown : Chapter14LocalIntersectionData down}
    {Iup : Chapter14LocalIntersectionData up}
    (B : Chapter14PointBlowupData down up C Idown Iup)
    (D : Chapter14HorizontalDivisor down)
    (v : Chapter14RationalVector r)
    (hv : chapter14Balanced down
      (fun i => (D.componentIntersections i : ℚ)) v) :
    chapter14Balanced up
      (fun j => ((B.strictTransform D).componentIntersections j : ℚ))
      (chapter14PointBlowupCorrectionOfStrictTransform B D v) := by
  sorry

theorem chapter14_point_blowup_corrected_divisor_identity
    {r t : ℕ}
    {down : Chapter14FiberMatrix r}
    {up : Chapter14FiberMatrix t}
    {C : Chapter14ComponentCorrespondence down up}
    {Idown : Chapter14LocalIntersectionData down}
    {Iup : Chapter14LocalIntersectionData up}
    (B : Chapter14PointBlowupData down up C Idown Iup)
    (D : Chapter14HorizontalDivisor down)
    (v : Chapter14RationalVector r) :
    chapter14PointBlowupPullbackOfCorrectedDivisor B D v =
      { horizontalPart := B.strictTransform D
        verticalPart :=
          B.pullbackVertical v +
            (B.multiplicityAtPoint D : ℚ) • B.exceptionalVector } := by
  rfl

theorem chapter14_point_blowup_preserves_corrected_pairing
    {r t : ℕ}
    {down : Chapter14FiberMatrix r}
    {up : Chapter14FiberMatrix t}
    {C : Chapter14ComponentCorrespondence down up}
    {Idown : Chapter14LocalIntersectionData down}
    {Iup : Chapter14LocalIntersectionData up}
    (B : Chapter14PointBlowupData down up C Idown Iup)
    (D G : Chapter14HorizontalDivisor down)
    (hdown : Idown.genericDisjoint D G)
    (hup : Iup.genericDisjoint (B.strictTransform D) (B.strictTransform G))
    (v w : Chapter14RationalVector r)
    (hv : chapter14Balanced down
      (fun i => (D.componentIntersections i : ℚ)) v)
    (hw : chapter14Balanced down
      (fun i => (G.componentIntersections i : ℚ)) w) :
    chapter14FullyCorrectedLocalPairing Iup
        (B.strictTransform D) (B.strictTransform G) hup
        (chapter14PointBlowupCorrectionOfStrictTransform B D v)
        (chapter14PointBlowupCorrectionOfStrictTransform B G w) =
      chapter14FullyCorrectedLocalPairing Idown D G hdown v w := by
  sorry

theorem chapter14_point_blowup_preserves_corrected_pairing_of_strict_transforms
    {r t : ℕ}
    {down : Chapter14FiberMatrix r}
    {up : Chapter14FiberMatrix t}
    {C : Chapter14ComponentCorrespondence down up}
    {Idown : Chapter14LocalIntersectionData down}
    {Iup : Chapter14LocalIntersectionData up}
    (B : Chapter14PointBlowupData down up C Idown Iup)
    (D G : Chapter14HorizontalDivisor down)
    (hdown : Idown.genericDisjoint D G)
    (hup : Iup.genericDisjoint (B.strictTransform D) (B.strictTransform G))
    (v w : Chapter14RationalVector r)
    (hv : chapter14Balanced down
      (fun i => (D.componentIntersections i : ℚ)) v)
    (hw : chapter14Balanced down
      (fun i => (G.componentIntersections i : ℚ)) w) :
    chapter14CorrectedLocalPairing Iup
        (B.strictTransform D) (B.strictTransform G) hup
        (chapter14PointBlowupCorrectionOfStrictTransform B D v) =
      chapter14CorrectedLocalPairing Idown D G hdown v := by
  sorry

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter14
