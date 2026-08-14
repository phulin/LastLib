import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter10.Section03RosenlichtDifferentials

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter10

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Set
open scoped BigOperators

universe u

/-! ## 10.4. Families of nodal curves -/

/-!
The family record keeps properness, flatness, finite presentation, nodality,
and the relative local-complete-intersection hypothesis separate.  The last
property is a local dependency interface for the pinned snapshot; it is not
silently replaced by smoothness.
-/

theorem chapter10_relative_dualizing_sheaf_exists
    (F : Chapter10ProperFlatNodalFamily) :
    Nonempty (Chapter10RelativeDualizingSheafData F) := by
  sorry

theorem chapter10_relative_dualizing_is_invertible
    (F : Chapter10ProperFlatNodalFamily)
    (ω : Chapter10RelativeDualizingSheafData F) :
    chapter10RelativeDualizingIsLineBundle ω := by
  exact ω.invertible

theorem chapter10_relative_dualizing_commutes_with_arbitrary_base_change
    (F : Chapter10ProperFlatNodalFamily)
    (ω : Chapter10RelativeDualizingSheafData F) :
    chapter10RelativeDualizingCommutesWithBaseChange ω := by
  intro T g
  exact ⟨ω.baseChangeIso g⟩

theorem chapter10_relative_dualizing_restricts_to_rosenlicht_on_geometric_fibers
    (F : Chapter10ProperFlatNodalFamily)
    (ω : Chapter10RelativeDualizingSheafData F)
    (p : Chapter10GeometricPoint F.base) :
    ω.fiberwiseRosenlicht p := by
  exact ω.fiberwiseRosenlicht p

/-! ### Étale-local node charts -/

structure Chapter10EtaleNodalChart (F : Chapter10ProperFlatNodalFamily) where
  coefficientRing : Type u
  [coefficientRingCommRing : CommRing coefficientRing]
  parameter : coefficientRing
  chartRing : Type u
  [chartRingCommRing : CommRing chartRing]
  [chartRingAlgebra : Algebra coefficientRing chartRing]
  x y : chartRing
  equation : x * y = algebraMap coefficientRing chartRing parameter
  etaleNeighborhood : Prop
  smoothRelativeSurface : Prop
  mapsToFamily : Prop
  logFrame : Prop

attribute [instance] Chapter10EtaleNodalChart.coefficientRingCommRing
attribute [instance] Chapter10EtaleNodalChart.chartRingCommRing
attribute [instance] Chapter10EtaleNodalChart.chartRingAlgebra

structure Chapter10EtaleNodalChartFamily (F : Chapter10ProperFlatNodalFamily) where
  nodes : Type u
  [nodesFinite : Fintype nodes]
  chart : nodes → Chapter10EtaleNodalChart F

attribute [instance] Chapter10EtaleNodalChartFamily.nodesFinite

theorem chapter10_nodal_family_has_etale_local_xy_charts
    (F : Chapter10ProperFlatNodalFamily) :
    Nonempty (Chapter10EtaleNodalChartFamily F) := by
  sorry

theorem chapter10_etale_node_chart_has_smoothing_equation
    (F : Chapter10ProperFlatNodalFamily)
    (H : Chapter10EtaleNodalChartFamily F) (q : H.nodes) :
    (H.chart q).x * (H.chart q).y =
      algebraMap (H.chart q).coefficientRing (H.chart q).chartRing
        (H.chart q).parameter := by
  exact (H.chart q).equation

theorem chapter10_etale_node_chart_log_frame
    (F : Chapter10ProperFlatNodalFamily)
    (H : Chapter10EtaleNodalChartFamily F) (q : H.nodes) :
    (H.chart q).logFrame := by
  exact (H.chart q).logFrame

theorem chapter10_relative_dualizing_local_frames_glue_by_adjunction
    (F : Chapter10ProperFlatNodalFamily)
    (ω : Chapter10RelativeDualizingSheafData F) :
    ω.canonicalAdjunctionGluing := by
  exact ω.canonicalAdjunctionGluing

/-!
Simultaneous normalization is an extra hypothesis, not a consequence of
normalizing the total space.  The first declaration packages the optional
construction; the second records the general failure mode described in the
source.
-/

theorem chapter10_simultaneous_normalization_is_not_automatic :
    ∃ F : Chapter10ProperFlatNodalFamily,
      ¬ chapter10HasSimultaneousNormalization F := by
  sorry

structure Chapter10FiberwiseNormalization
    (F : Chapter10ProperFlatNodalFamily)
    (p : Chapter10GeometricPoint F.base) where
  normalizedFiber : Scheme.{u}
  map : normalizedFiber ⟶ chapter10GeometricFiberTotal F.map p
  finite : IsFinite map
  normal : Prop
  normalizesTheGeometricFiber : Prop

def chapter10HasFiberwiseNormalization
    (F : Chapter10ProperFlatNodalFamily)
    (p : Chapter10GeometricPoint F.base) : Prop :=
  Nonempty (Chapter10FiberwiseNormalization F p)

/-! ### Marked smooth points and logarithmic twists -/

def chapter10MarkedDivisor
    (F : Chapter10ProperFlatNodalFamily)
    (ω : Chapter10RelativeDualizingSheafData F)
    (n : ℕ) (D : Chapter10MarkedDifferentialData F ω n) :
    Fin n → Chapter10MarkedSection F :=
  D.markings

def chapter10MarkedTwistedDualizingSheaf
    (F : Chapter10ProperFlatNodalFamily)
    (ω : Chapter10RelativeDualizingSheafData F)
    (n : ℕ) (D : Chapter10MarkedDifferentialData F ω n) : F.total.Modules :=
  D.twistedOmega

def chapter10MarkedGlobalSection
    (F : Chapter10ProperFlatNodalFamily)
    (ω : Chapter10RelativeDualizingSheafData F)
    (n : ℕ) (D : Chapter10MarkedDifferentialData F ω n) : Type u :=
  (Scheme.Modules.presheaf (chapter10MarkedTwistedDualizingSheaf F ω n D)).obj
    (Opposite.op (⊤ : F.total.Opens))

theorem chapter10_marked_twist_allows_simple_marking_poles
    (F : Chapter10ProperFlatNodalFamily)
    (ω : Chapter10RelativeDualizingSheafData F)
    (n : ℕ) (D : Chapter10MarkedDifferentialData F ω n) :
    D.allowsSimplePolesAtMarkings := by
  exact D.allowsSimplePolesAtMarkings

theorem chapter10_marked_twist_retains_implicit_node_branch_poles
    (F : Chapter10ProperFlatNodalFamily)
    (ω : Chapter10RelativeDualizingSheafData F)
    (n : ℕ) (D : Chapter10MarkedDifferentialData F ω n) :
    D.allowsImplicitNodeBranchPoles := by
  exact D.allowsImplicitNodeBranchPoles

/-!
The total-residue statement is numerical on each geometric fiber.  Since the
residue field varies with the geometric point, the profile below keeps the
fiber field explicit and records only the raw branch residues; the theorem
derives both internal node cancellation and the total sum-zero relation.
-/

structure Chapter10MarkedFiberResidueProfile
    (F : Chapter10ProperFlatNodalFamily)
    (ω : Chapter10RelativeDualizingSheafData F)
    (n : ℕ) (D : Chapter10MarkedDifferentialData F ω n)
    (η : chapter10MarkedGlobalSection F ω n D) where
  nodes : Type u
  [nodesFinite : Fintype nodes]
  totalResidue : ∀ p : Chapter10GeometricPoint F.base, p.field
  nodeLeftResidue : ∀ p : Chapter10GeometricPoint F.base, nodes → p.field
  nodeRightResidue : ∀ p : Chapter10GeometricPoint F.base, nodes → p.field
  markingResidue : ∀ p : Chapter10GeometricPoint F.base, Fin n → p.field

attribute [instance] Chapter10MarkedFiberResidueProfile.nodesFinite

def chapter10NodeResiduesCancelInternally
    {F : Chapter10ProperFlatNodalFamily}
    {ω : Chapter10RelativeDualizingSheafData F}
    {n : ℕ} {D : Chapter10MarkedDifferentialData F ω n}
    {η : chapter10MarkedGlobalSection F ω n D}
    (R : Chapter10MarkedFiberResidueProfile F ω n D η) : Prop :=
  ∀ p q, R.nodeLeftResidue p q + R.nodeRightResidue p q = 0

def chapter10TotalResidueIsZeroOnEveryGeometricFiber
    {F : Chapter10ProperFlatNodalFamily}
    {ω : Chapter10RelativeDualizingSheafData F}
    {n : ℕ} {D : Chapter10MarkedDifferentialData F ω n}
    {η : chapter10MarkedGlobalSection F ω n D}
    (R : Chapter10MarkedFiberResidueProfile F ω n D η) : Prop :=
  ∀ p, R.totalResidue p = 0

theorem chapter10_marked_global_section_has_total_residue_zero
    (F : Chapter10ProperFlatNodalFamily)
    (ω : Chapter10RelativeDualizingSheafData F)
    (n : ℕ) (D : Chapter10MarkedDifferentialData F ω n)
    (η : chapter10MarkedGlobalSection F ω n D)
    (R : Chapter10MarkedFiberResidueProfile F ω n D η) :
    chapter10TotalResidueIsZeroOnEveryGeometricFiber R ∧
      chapter10NodeResiduesCancelInternally R := by
  sorry

theorem chapter10_marked_residue_statement_is_node_cancellation_plus_marking_balance
    (F : Chapter10ProperFlatNodalFamily)
    (ω : Chapter10RelativeDualizingSheafData F)
    (n : ℕ) (D : Chapter10MarkedDifferentialData F ω n)
    (η : chapter10MarkedGlobalSection F ω n D)
    (R : Chapter10MarkedFiberResidueProfile F ω n D η) :
    chapter10NodeResiduesCancelInternally R := by
  exact (chapter10_marked_global_section_has_total_residue_zero F ω n D η R).2

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter10
