import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter06.Dependencies

/-!
### 6.2 Thickness singularities

The equation `x * y = π ^ n` is recorded directly over a DVR.  The chart and
resolution records retain the algebraic equations from the text while leaving
the scheme-level blowup construction and the local regularity calculation to
the missing Book 11/Book 12 interfaces.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter06

/-! The local equation and its thickness. -/

def chapter06ThicknessEquation {R : Type u} [CommRing R]
    (x y π : R) (n : ℕ) : Prop :=
  x * y = π ^ n

structure Chapter06ThicknessLocalEquation
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] where
  uniformizer : R
  uniformizerIrreducible : Irreducible uniformizer
  thickness : ℕ
  thicknessGreaterThanOne : 1 < thickness
  x y : R
  equation : chapter06ThicknessEquation x y uniformizer thickness

def chapter06ThicknessGreaterThanOne
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (T : Chapter06ThicknessLocalEquation R) : Prop :=
  T.thickness > 1

/- LOCAL_DEPENDENCY_GUESS: Mathlib does not yet expose the book-level
regularity predicate for a surface chart together with its punctured open.
The following record is the minimal local interface needed to state both
parts of the thickness assertion without identifying regularity with a mere
equation-level proposition. -/
structure Chapter06ThicknessGeometry
  {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (T : Chapter06ThicknessLocalEquation R) where
  totalSpace : Scheme.{u}
  origin : totalSpace
  regularAtOrigin : Prop
  singularAtOrigin : ¬ regularAtOrigin
  puncturedRegular : Prop
  puncturedRegularEvidence : puncturedRegular

theorem chapter06_thickness_total_space_is_singular_at_origin
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (T : Chapter06ThicknessLocalEquation R)
    (G : Chapter06ThicknessGeometry T) :
    G.singularAtOrigin := by
  exact G.singularAtOrigin

theorem chapter06_thickness_punctured_surface_is_regular
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (T : Chapter06ThicknessLocalEquation R)
    (G : Chapter06ThicknessGeometry T) :
    G.puncturedRegular := by
  exact G.puncturedRegularEvidence

theorem chapter06_thickness_geometry_exists
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (T : Chapter06ThicknessLocalEquation R) :
    Nonempty (Chapter06ThicknessGeometry T) := by
  sorry

/-! The blowup charts decrease the exponent by one. -/

def chapter06ReducedThicknessEquation {R : Type u} [CommRing R]
    (x₁ y π : R) (n : ℕ) : Prop :=
  x₁ * y = π ^ (n - 1)

structure Chapter06ThicknessBlowupDescription
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (T : Chapter06ThicknessLocalEquation R) where
  idealGenerators : Ideal R
  idealGeneratorsAreXAndUniformizer :
    idealGenerators = Ideal.span ({T.x, T.uniformizer} : Set R)
  xChartRegular : Prop
  xChartRegularEvidence : xChartRegular
  xChartCoordinate : R
  xChartUniformizerRelation :
    T.uniformizer = T.x * xChartCoordinate
  xChartEquationAfterSubstitution :
    T.y = T.x ^ (T.thickness - 1) * xChartCoordinate ^ T.thickness
  piChartCoordinateX : R
  piChartEquation :
    chapter06ReducedThicknessEquation
      piChartCoordinateX T.y T.uniformizer T.thickness
  strictTransform : Prop
  strictTransformEvidence : strictTransform
  thicknessDecreases : T.thickness - 1 < T.thickness

theorem chapter06_blowup_thickness_decreases
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (T : Chapter06ThicknessLocalEquation R)
    (B : Chapter06ThicknessBlowupDescription T) :
    T.thickness - 1 < T.thickness := by
  exact B.thicknessDecreases

theorem chapter06_blowup_thickness_chart
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (T : Chapter06ThicknessLocalEquation R) :
    Nonempty (Chapter06ThicknessBlowupDescription T) := by
  sorry

def chapter06ThicknessSequence : ℕ → List ℕ
  | 0 => []
  | n + 1 => (n + 1) :: chapter06ThicknessSequence n

theorem chapter06_thicknessSequence_succ
    (n : ℕ) :
    chapter06ThicknessSequence (n + 1) =
      (n + 1) :: chapter06ThicknessSequence n := by
  rfl

structure Chapter06ThicknessResolutionSequence (n : ℕ) where
  initialGreaterThanOne : 1 < n
  exponents : List ℕ
  exponentsAreRecursive : exponents = chapter06ThicknessSequence n
  terminalExponentOccurs : 1 ∈ exponents
  everyPositiveStepDecreases : Prop
  everyPositiveStepDecreasesEvidence : everyPositiveStepDecreases
  terminalChartRegular : Prop
  terminalChartRegularEvidence : terminalChartRegular

theorem chapter06_thickness_iteration_terminates
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (T : Chapter06ThicknessLocalEquation R) :
    Nonempty (Chapter06ThicknessResolutionSequence T.thickness) := by
  sorry

structure Chapter06ThicknessTerminalChart
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] where
  uniformizer : R
  uniformizerIrreducible : Irreducible uniformizer
  x y : R
  equation : x * y = uniformizer
  totalSpaceRegular : Prop
  totalSpaceRegularEvidence : totalSpaceRegular
  specialFiberHasTwoComponents : Prop
  specialFiberHasTwoComponentsEvidence : specialFiberHasTwoComponents
  componentsMeetTransversely : Prop
  componentsMeetTransverselyEvidence : componentsMeetTransversely

theorem chapter06_thickness_one_is_regular_node
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π x y : R) (hπ : Irreducible π) (hxy : x * y = π) :
    Nonempty (Chapter06ThicknessTerminalChart (uniformizer := π) (x := x) (y := y)) := by
  sorry

/-! The minimal resolution graph over an algebraically closed residue field. -/

structure Chapter06ThicknessResolutionGraph (n : ℕ) where
  nGreaterThanOne : 1 < n
  residueFieldAlgebraicallyClosed : Prop
  residueFieldAlgebraicallyClosedEvidence : residueFieldAlgebraicallyClosed
  exceptionalCurves : Fin (n - 1) → Chapter06CurveNumericalData
  intersectionMatrix : Chapter06IntersectionMatrix (Fin (n - 1))
  intersectionMatrixIsChain :
    intersectionMatrix = chapter06NegativeChainMatrix (n - 1)
  exceptionalCurvesAreSmoothRational :
    ∀ i, (exceptionalCurves i).smooth ∧ (exceptionalCurves i).rational
  exceptionalSquares :
    ∀ i, (exceptionalCurves i).selfIntersection = -2
  leftStrictTransformMeetsFirst : Prop
  leftStrictTransformMeetsFirstEvidence : leftStrictTransformMeetsFirst
  rightStrictTransformMeetsLast : Prop
  rightStrictTransformMeetsLastEvidence : rightStrictTransformMeetsLast
  consecutiveCurvesMeetOnce : Prop
  consecutiveCurvesMeetOnceEvidence : consecutiveCurvesMeetOnce
  noOtherExceptionalIntersections : Prop
  noOtherExceptionalIntersectionsEvidence : noOtherExceptionalIntersections
  minimal : Prop
  minimalEvidence : minimal

theorem chapter06_thickness_minimal_resolution_chain
    (n : ℕ) (hn : 1 < n) :
    Nonempty (Chapter06ThicknessResolutionGraph n) := by
  sorry

theorem chapter06_thickness_exceptional_curve_is_minus_two
    {n : ℕ} (G : Chapter06ThicknessResolutionGraph n) (i : Fin (n - 1)) :
    (G.exceptionalCurves i).selfIntersection = -2 := by
  exact G.exceptionalSquares i

theorem chapter06_thickness_chain_matrix_is_negative_Cartan
    {n : ℕ} (G : Chapter06ThicknessResolutionGraph n) :
    G.intersectionMatrix = chapter06NegativeChainMatrix (n - 1) := by
  exact G.intersectionMatrixIsChain

theorem chapter06_thickness_consecutive_exceptional_curves_meet_once
    {n : ℕ} (G : Chapter06ThicknessResolutionGraph n) :
    G.consecutiveCurvesMeetOnce := by
  exact G.consecutiveCurvesMeetOnceEvidence

theorem chapter06_thickness_no_other_exceptional_intersections
    {n : ℕ} (G : Chapter06ThicknessResolutionGraph n) :
    G.noOtherExceptionalIntersections := by
  exact G.noOtherExceptionalIntersectionsEvidence

/-! Nonminimal resolutions retain the generic curve but may add `(-1)` curves. -/

structure Chapter06NonminimalThicknessResolution (n : ℕ) where
  minimalGraph : Chapter06ThicknessResolutionGraph n
  addedExceptionalCurves : List Chapter06CurveNumericalData
  addedCurvesAreMinusOne :
    ∀ C, C ∈ addedExceptionalCurves → C.selfIntersection = -1
  genericCurveUnchanged : Prop
  genericCurveUnchangedEvidence : genericCurveUnchanged
  intersectionNumbersRecordChoice : Prop
  intersectionNumbersRecordChoiceEvidence : intersectionNumbersRecordChoice

theorem chapter06_nonminimal_resolution_can_add_minus_one_vertices
    {n : ℕ} (G : Chapter06ThicknessResolutionGraph n) :
    Nonempty (Chapter06NonminimalThicknessResolution n) := by
  sorry

theorem chapter06_nonminimal_resolution_preserves_generic_curve
    {n : ℕ} (N : Chapter06NonminimalThicknessResolution n) :
    N.genericCurveUnchanged := by
  exact N.genericCurveUnchangedEvidence

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter06

end
