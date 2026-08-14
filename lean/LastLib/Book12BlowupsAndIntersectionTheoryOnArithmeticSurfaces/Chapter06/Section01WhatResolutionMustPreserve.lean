import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter06.Dependencies

/-!
### 6.1 What resolution must preserve

This file records the distinction between resolving the surface and resolving a
boundary on an already regular surface.  The resolution theorem itself is kept
as a proof-ready interface because the relevant excellent-surface theorem is
supplied by Book 11 rather than by the pinned Mathlib snapshot.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter06

/-! The resolution theorem of Book 11, in the exact form needed here. -/

theorem chapter06_resolution_theorem {X : Scheme.{u}}
    (hX : Chapter06NormalExcellentSurface X) :
    Nonempty (Chapter06SurfaceResolution hX) := by
  sorry

theorem chapter06_resolution_is_supported_on_singular_locus
    {X : Scheme.{u}} (hX : Chapter06NormalExcellentSurface X)
    (r : Chapter06SurfaceResolution hX) :
    r.center ⊆ chapter06SingularLocus hX := by
  exact r.centerSubsetSingular

theorem chapter06_resolution_target_is_regular
    {X : Scheme.{u}} (hX : Chapter06NormalExcellentSurface X)
    (r : Chapter06SurfaceResolution hX) :
    ∀ y, r.targetRegular.regularAt y := by
  exact r.targetRegular.everywhereRegular

/-! A vertical modification has no generic-fiber contribution.  The explicit
generic-fiber isomorphism is the missing restriction/base-change bridge in the
current pinned snapshot, so the result is stated as a local dependency guess
rather than smuggled in through a stronger surface record. -/

theorem chapter06_vertical_modification_preserves_generic_curve
    {S : Scheme.{u}} {X Y : Chapter06RelativeSurfaceModel S}
    (_b : Chapter06VerticalModification X Y) :
    Chapter06SameGenericCurve X Y := by
  exact _b.genericFiberPreserved

def chapter06CenterAvoidsOpen {X : Scheme.{u}}
    (center U : Set X) : Prop :=
  ∀ x, x ∈ center → x ∉ U

theorem chapter06_centerAvoidsOpen_iff_disjoint {X : Scheme.{u}}
    (center U : Set X) :
    chapter06CenterAvoidsOpen center U ↔ center ∩ U = ∅ := by
  constructor
  · intro h
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact (h x hx.1) hx.2
  · intro h x hxCenter hxOpen
    have : x ∈ center ∩ U := ⟨hxCenter, hxOpen⟩
    rw [h] at this
    simp at this

def Chapter06RegularNormalCrossingOpen {X : Scheme.{u}}
    (hX : Chapter06NormalExcellentSurface X)
    (U : Set X) (B : Chapter06NormalCrossingBoundary X) : Prop :=
  (∀ x, x ∈ U → hX.regularAt x) ∧
    B.support ⊆ U ∧
    B.smoothBranches ∧ B.atMostTwoBranches ∧ B.transverseBranches

structure Chapter06BoundaryResolution {X : Scheme.{u}}
    (hX : Chapter06NormalExcellentSurface X) (U : Set X)
    (B : Chapter06NormalCrossingBoundary X) where
  resolved : Scheme.{u}
  map : resolved ⟶ X
  projective : Prop
  projectiveEvidence : projective
  birational : Prop
  birationalEvidence : birational
  targetRegular : Chapter06RegularSurface resolved
  targetBoundary : Chapter06NormalCrossingBoundary resolved
  center : Set X
  centerSubsetSingularOrBoundary : center ⊆ chapter06SingularLocus hX ∪ B.support
  avoidsChosenOpen : chapter06CenterAvoidsOpen center U

theorem chapter06_resolution_can_avoid_a_regular_normal_crossing_open
    {X : Scheme.{u}} (hX : Chapter06NormalExcellentSurface X)
    (U : Set X) (B : Chapter06NormalCrossingBoundary X)
    (hgood : Chapter06RegularNormalCrossingOpen hX U B) :
    ∃ r : Chapter06BoundaryResolution hX U B,
      chapter06CenterAvoidsOpen r.center U := by
  sorry

theorem chapter06_embedded_resolution_is_a_distinct_task :
    Chapter06ResolutionPurpose.surfaceSingularities ≠
      Chapter06ResolutionPurpose.embeddedBoundary := by
  intro h
  cases h

/-! The second process starts after the total space is regular. -/

structure Chapter06EmbeddedBoundaryStep {X Y : Scheme.{u}} where
  map : Y ⟶ X
  sourceRegular : Chapter06RegularSurface X
  targetRegular : Chapter06RegularSurface Y
  boundaryBefore : Chapter06NormalCrossingBoundary X
  boundaryAfter : Chapter06NormalCrossingBoundary Y
  center : X
  centerIsClosedPoint : IsClosed ({center} : Set X)
  centerIsRegular : sourceRegular.regularAt center
  centerOnBoundary : center ∈ boundaryBefore.support
  projective : Prop
  projectiveEvidence : projective
  birational : Prop
  birationalEvidence : birational

def Chapter06EmbeddedBoundaryResolution {X : Scheme.{u}} : Prop :=
  ∃ (Y : Scheme.{u}),
    Nonempty (Chapter06EmbeddedBoundaryStep (X := X) (Y := Y))

theorem chapter06_regular_surface_may_need_embedded_boundary_steps :
    ∃ (S X : Scheme.{u}) (f : X ⟶ S),
      Nonempty (Chapter06ArithmeticSurface f) ∧
        Chapter06EmbeddedBoundaryResolution (X := X) := by
  sorry

/-! The multiplicity/branch/tangent ledger is intentionally independent of a
picture of the special fiber. -/

structure Chapter06LocalResolutionStep where
  invariants : Chapter06LocalStepInvariants
  centerFiberData : Chapter06CenterFiberData
  multiplicityTransportedByTotalTransform : Prop
  multiplicityTransportedEvidence : multiplicityTransportedByTotalTransform

/-! A terminal step is allowed: only a step whose ledger detects a remaining
boundary defect is required to carry the nonterminal marker. -/
structure Chapter06NonterminalLocalResolutionStep where
  step : Chapter06LocalResolutionStep
  requiresFurtherBlowup : Chapter06LocalStepNeedsNewCenter step.invariants

def chapter06LocalResolutionStepMultiplicity
    (s : Chapter06LocalResolutionStep) : ℕ :=
  chapter06ExceptionalFiberMultiplicity s.centerFiberData

theorem chapter06_nonterminal_local_step_requires_further_blowup
    (s : Chapter06NonterminalLocalResolutionStep) :
    Chapter06LocalStepNeedsNewCenter s.step.invariants := by
  exact s.requiresFurtherBlowup

theorem chapter06_local_step_exceptional_multiplicity_is_transport_sum
    (s : Chapter06LocalResolutionStep) :
    chapter06LocalResolutionStepMultiplicity s =
      chapter06FiberMultiplicitySum s.centerFiberData := by
  exact chapter06_exceptional_fiber_multiplicity_eq_sum s.centerFiberData

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter06

end
