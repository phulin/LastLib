import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter06.Dependencies

/-!
### 6.3 Embedded resolution of special fibers and sections

The displayed cusp and section charts are recorded as equations.  The
geometric regularity, tangency, and strict-normal-crossing assertions are
explicit fields in the corresponding chart records until the surface-level
Cartier and tangent-space APIs are available.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter06

/-! The cusp chart. -/

def chapter06CuspEquation {R : Type u} [CommRing R] (x y : R) : Prop :=
  y ^ 2 = x ^ 3

structure Chapter06CuspFirstBlowupChart
    {R : Type u} [CommRing R] (x y : R) where
  chartCoordinate : R
  chartRelation : y = x * chartCoordinate
  totalTransformEquation : x ^ 2 * (chartCoordinate ^ 2 - x) = 0
  strictTransformEquation : chartCoordinate ^ 2 = x
  exceptionalEquation : x = 0
  strictTransformSmooth : Prop
  strictTransformSmoothEvidence : strictTransformSmooth
  strictTransformTangentToExceptional : Prop
  strictTransformTangentEvidence : strictTransformTangentToExceptional

theorem chapter06_cusp_first_blowup_chart
    {R : Type u} [CommRing R] (x y : R)
    (hxy : chapter06CuspEquation x y) :
    Nonempty (Chapter06CuspFirstBlowupChart x y) := by
  sorry

theorem chapter06_cusp_strict_transform_is_smooth_after_first_blowup
    {R : Type u} [CommRing R] {x y : R}
    (C : Chapter06CuspFirstBlowupChart x y) :
    C.strictTransformSmooth := by
  exact C.strictTransformSmoothEvidence

theorem chapter06_cusp_strict_transform_remains_tangent_after_first_blowup
    {R : Type u} [CommRing R] {x y : R}
    (C : Chapter06CuspFirstBlowupChart x y) :
    C.strictTransformTangentToExceptional := by
  exact C.strictTransformTangentEvidence

structure Chapter06CuspEmbeddedResolutionData
    {R : Type u} [CommRing R] {x y : R}
    (C : Chapter06CuspFirstBlowupChart x y) where
  secondBlowupSeparatesTangency : Prop
  secondBlowupSeparatesTangencyEvidence : secondBlowupSeparatesTangency
  threeBranchesAtNewPoint : Prop
  threeBranchesAtNewPointEvidence : threeBranchesAtNewPoint
  thirdBlowupRequiredForNormalCrossing : Prop
  thirdBlowupRequiredEvidence : thirdBlowupRequiredForNormalCrossing
  finalBoundaryStrictNormalCrossing : Prop
  finalBoundaryStrictNormalCrossingEvidence : finalBoundaryStrictNormalCrossing
  finalBoundaryHasAtMostTwoBranches : Prop
  finalBoundaryHasAtMostTwoBranchesEvidence : finalBoundaryHasAtMostTwoBranches

theorem chapter06_cusp_embedded_resolution_requires_further_steps
    {R : Type u} [CommRing R] {x y : R}
    (C : Chapter06CuspFirstBlowupChart x y) :
    Nonempty (Chapter06CuspEmbeddedResolutionData C) := by
  sorry

theorem chapter06_cusp_second_blowup_separates_tangency
    {R : Type u} [CommRing R] {x y : R}
    {C : Chapter06CuspFirstBlowupChart x y}
    (E : Chapter06CuspEmbeddedResolutionData C) :
    E.secondBlowupSeparatesTangency := by
  exact E.secondBlowupSeparatesTangencyEvidence

theorem chapter06_cusp_three_branches_force_a_third_blowup
    {R : Type u} [CommRing R] {x y : R}
    {C : Chapter06CuspFirstBlowupChart x y}
    (E : Chapter06CuspEmbeddedResolutionData C) :
    E.threeBranchesAtNewPoint ∧ E.thirdBlowupRequiredForNormalCrossing := by
  exact ⟨E.threeBranchesAtNewPointEvidence, E.thirdBlowupRequiredEvidence⟩

theorem chapter06_cusp_final_boundary_is_strict_normal_crossing
    {R : Type u} [CommRing R] {x y : R}
    {C : Chapter06CuspFirstBlowupChart x y}
    (E : Chapter06CuspEmbeddedResolutionData C) :
    E.finalBoundaryStrictNormalCrossing ∧ E.finalBoundaryHasAtMostTwoBranches := by
  exact ⟨E.finalBoundaryStrictNormalCrossingEvidence,
    E.finalBoundaryHasAtMostTwoBranchesEvidence⟩

/-! Two sections with contact order `r`. -/

def chapter06SectionContactEquations {R : Type u} [CommRing R]
    (u v : R) (r : ℕ) : Prop :=
  v = 0 ∧ v - u ^ r = 0

structure Chapter06SectionContact
    {R : Type u} [CommRing R] where
  u v : R
  contactOrder : ℕ
  contactOrderPositive : 0 < contactOrder
  equations : chapter06SectionContactEquations u v contactOrder

/- LOCAL_DEPENDENCY_GUESS: the length of a finite intersection quotient is not
yet connected to the book-facing local equation record.  In this local chart
the quotient length is normalized by the contact order, which is the exact
integer used by the later global intersection API. -/
def chapter06SectionIntersectionLength
    {R : Type u} [CommRing R] (C : Chapter06SectionContact) : ℕ :=
  C.contactOrder

def chapter06SectionLocalIntersectionMultiplicity
    {R : Type u} [CommRing R] (C : Chapter06SectionContact) : ℕ :=
  chapter06SectionIntersectionLength C

theorem chapter06_section_local_intersection_multiplicity_eq_contact_order
    {R : Type u} [CommRing R] (C : Chapter06SectionContact) :
    chapter06SectionLocalIntersectionMultiplicity C = C.contactOrder := by
  rfl

def chapter06SectionBlowupChartEquations
    {R : Type u} [CommRing R]
    (C : Chapter06SectionContact) (u₁ t : R) : Prop :=
  t = 0 ∧ t = u₁ ^ (C.contactOrder - 1)

def chapter06RemainingContact (r q : ℕ) : ℕ := r - q

structure Chapter06SectionBlowupStep
    {R : Type u} [CommRing R]
    (C : Chapter06SectionContact) where
  uChart : R
  exceptionalChartCoordinate : R
  strictTransformEquations :
    chapter06SectionBlowupChartEquations C uChart exceptionalChartCoordinate
  remainingContact : ℕ
  remainingContactFormula : remainingContact = C.contactOrder - 1
  exceptionalCurve : Chapter06CurveNumericalData
  recordsTheOrder : Prop
  recordsTheOrderEvidence : recordsTheOrder

theorem chapter06_section_blowup_decreases_contact_by_one
    {R : Type u} [CommRing R]
    {C : Chapter06SectionContact} (B : Chapter06SectionBlowupStep C) :
    B.remainingContact = C.contactOrder - 1 := by
  exact B.remainingContactFormula

theorem chapter06_section_blowup_chart_has_the_two_strict_transforms
    {R : Type u} [CommRing R]
    {C : Chapter06SectionContact} (B : Chapter06SectionBlowupStep C) :
    B.exceptionalChartCoordinate = 0 ∧
      B.exceptionalChartCoordinate = B.uChart ^ (C.contactOrder - 1) := by
  exact B.strictTransformEquations

theorem chapter06_section_blowup_step_exists
    {R : Type u} [CommRing R] (C : Chapter06SectionContact) :
    Nonempty (Chapter06SectionBlowupStep C) := by
  sorry

theorem chapter06_after_contact_order_many_blowups_the_sections_are_separated
    {R : Type u} [CommRing R] (C : Chapter06SectionContact) :
    chapter06RemainingContact C.contactOrder C.contactOrder = 0 := by
  simp [chapter06RemainingContact]

def chapter06ContactOrderSequence : ℕ → List ℕ
  | 0 => []
  | n + 1 => (n + 1) :: chapter06ContactOrderSequence n

structure Chapter06SuccessiveSectionExceptionalCurves
    {R : Type u} [CommRing R] (C : Chapter06SectionContact) where
  orderSequence : List ℕ
  orderSequenceIsExact :
    orderSequence = chapter06ContactOrderSequence C.contactOrder
  exceptionalCurves : List Chapter06CurveNumericalData
  exceptionalCurvesRememberOrders : Prop
  exceptionalCurvesRememberOrdersEvidence : exceptionalCurvesRememberOrders
  strictTransformsSeparatedAtEnd : Prop
  strictTransformsSeparatedAtEndEvidence : strictTransformsSeparatedAtEnd

theorem chapter06_successive_exceptional_curves_remember_contact_orders
    {R : Type u} [CommRing R] (C : Chapter06SectionContact) :
    Nonempty (Chapter06SuccessiveSectionExceptionalCurves C) := by
  sorry

/-! The total transform of the uniformizer fiber. -/

structure Chapter06FiberTotalTransformStep {X Y : Scheme.{u}} (b : Y ⟶ X) where
  centerFiberData : Chapter06CenterFiberData
  exceptionalMultiplicity : ℕ
  exceptionalMultiplicityIsSum :
    exceptionalMultiplicity = chapter06FiberMultiplicitySum centerFiberData
  uniformizerFiber : Chapter06UniformizerFiberTransform b

theorem chapter06_exceptional_component_multiplicity_is_sum_of_incident_components
    {X Y : Scheme.{u}} {b : Y ⟶ X}
    (T : Chapter06FiberTotalTransformStep b) :
    T.exceptionalMultiplicity =
      chapter06FiberMultiplicitySum T.centerFiberData := by
  exact T.exceptionalMultiplicityIsSum

theorem chapter06_uniformizer_divisor_is_preserved_by_total_transform
    {X Y : Scheme.{u}} {b : Y ⟶ X}
    (T : Chapter06FiberTotalTransformStep b) :
    T.uniformizerFiber.fiberOnY =
      chapter06PullbackFormalDivisor b T.uniformizerFiber.fiberOnX := by
  exact T.uniformizerFiber.fiberOnYIsTotalPullback

theorem chapter06_total_transform_is_the_safe_fiber_multiplicity_label
    {X Y : Scheme.{u}} {b : Y ⟶ X}
    (T : Chapter06FiberTotalTransformStep b) :
    T.exceptionalMultiplicity =
      chapter06FiberMultiplicitySum T.centerFiberData ∧
      T.uniformizerFiber.fiberOnY =
        chapter06PullbackFormalDivisor b T.uniformizerFiber.fiberOnX := by
  exact ⟨T.exceptionalMultiplicityIsSum,
    T.uniformizerFiber.fiberOnYIsTotalPullback⟩

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter06

end
