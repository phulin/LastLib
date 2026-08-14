import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter15.Section02TheInfinitesimalAbelMap
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01.Section01TheAbsoluteAndRelativeSettings

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter15

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11

universe u v

/-!
### 15.3 A formal-immersion criterion

The formal-immersion certificate below keeps the completed local-ring map,
its direction, and surjectivity visible.  Cotangent and tangent certificates
are separate so the residue-field and finiteness assumptions of the converse
cannot disappear into a definition.

-/

/- The completed local-ring map and its linearizations are named constructions
   attached to the actual morphism.  The records below only retain their typed
   comparison and rank properties. -/
noncomputable def chapter15InducedCompletedLocalRingMap
    {Y Z : Scheme.{u}} (φ : Y ⟶ Z) (x : Y) (z : Z) :
    CommRingCat.of (chapter01CompletedLocalRing Z z) ⟶
      CommRingCat.of (chapter01CompletedLocalRing Y x) := by
  sorry

def Chapter15SameResidueField
    {Y Z : Scheme.{u}} (x : Y) (z : Z) : Prop :=
  Nonempty (Y.residueField x ≃+* Z.residueField z)

def Chapter15FormalImmersionFiniteness
    {Y Z : Scheme.{u}} (φ : Y ⟶ Z) : Prop :=
  LocallyOfFiniteType φ ∧ IsNoetherian Y ∧ IsNoetherian Z

noncomputable def chapter15CotangentTarget
    {k : Type u} [Field k]
    {Y Z : Scheme.{u}} (φ : Y ⟶ Z) (x : Y) (z : Z) : ModuleCat.{u, u} k := by
  sorry

noncomputable def chapter15CotangentSource
    {k : Type u} [Field k]
    {Y Z : Scheme.{u}} (φ : Y ⟶ Z) (x : Y) (z : Z) : ModuleCat.{u, u} k := by
  sorry

noncomputable def chapter15InducedCotangentMap
    {k : Type u} [Field k]
    {Y Z : Scheme.{u}} (φ : Y ⟶ Z) (x : Y) (z : Z) :
    chapter15CotangentTarget (k := k) φ x z ⟶
      chapter15CotangentSource (k := k) φ x z := by
  sorry

noncomputable def chapter15TangentSource
    {k : Type u} [Field k]
    {Y Z : Scheme.{u}} (φ : Y ⟶ Z) (x : Y) (z : Z) : ModuleCat.{u, u} k := by
  sorry

noncomputable def chapter15TangentTarget
    {k : Type u} [Field k]
    {Y Z : Scheme.{u}} (φ : Y ⟶ Z) (x : Y) (z : Z) : ModuleCat.{u, u} k := by
  sorry

noncomputable def chapter15InducedTangentMap
    {k : Type u} [Field k]
    {Y Z : Scheme.{u}} (φ : Y ⟶ Z) (x : Y) (z : Z) :
    chapter15TangentSource (k := k) φ x z ⟶
      chapter15TangentTarget (k := k) φ x z := by
  sorry

structure Chapter15CompletedLocalRingMap
    {Y Z : Scheme.{u}} (φ : Y ⟶ Z) (x : Y) (z : Z) where
  map : CommRingCat.of (chapter01CompletedLocalRing Z z) ⟶
    CommRingCat.of (chapter01CompletedLocalRing Y x)
  point_compatibility : φ x = z
  map_is_induced : map = chapter15InducedCompletedLocalRingMap φ x z
  surjective : Function.Surjective (chapter15InducedCompletedLocalRingMap φ x z).hom

def Chapter15FormalImmersionAt
    {Y Z : Scheme.{u}} (φ : Y ⟶ Z) (x : Y) (z : Z) : Prop :=
  Nonempty (Chapter15CompletedLocalRingMap φ x z)

theorem chapter15_formal_immersion_iff_completed_local_ring_surjective
    {Y Z : Scheme.{u}} (φ : Y ⟶ Z) (x : Y) (z : Z) :
    Chapter15FormalImmersionAt φ x z ↔
      Nonempty (Chapter15CompletedLocalRingMap φ x z) := by
  rfl

structure Chapter15CotangentMapData
    {k : Type u} [Field k]
    {Y Z : Scheme.{u}} (φ : Y ⟶ Z) (x : Y) (z : Z) where
  cotangentMap : chapter15CotangentTarget (k := k) φ x z ⟶
    chapter15CotangentSource (k := k) φ x z
  point_compatibility : φ x = z
  cotangentMap_is_induced :
    cotangentMap = chapter15InducedCotangentMap (k := k) φ x z
  surjective : Function.Surjective (chapter15InducedCotangentMap (k := k) φ x z).hom

structure Chapter15TangentMapData
    {k : Type u} [Field k]
    {Y Z : Scheme.{u}} (φ : Y ⟶ Z) (x : Y) (z : Z) where
  tangentMap : chapter15TangentSource (k := k) φ x z ⟶
    chapter15TangentTarget (k := k) φ x z
  point_compatibility : φ x = z
  tangentMap_is_induced :
    tangentMap = chapter15InducedTangentMap (k := k) φ x z
  injective : Function.Injective (chapter15InducedTangentMap (k := k) φ x z).hom

theorem chapter15_formal_immersion_implies_cotangent_surjective
    {k : Type u} [Field k]
    {Y Z : Scheme.{u}} (φ : Y ⟶ Z) (x : Y) (z : Z)
    (hformal : Chapter15FormalImmersionAt φ x z) :
    Nonempty (Chapter15CotangentMapData (k := k) φ x z) := by
  sorry

theorem chapter15_cotangent_surjective_implies_tangent_injective
    {k : Type u} [Field k]
    {Y Z : Scheme.{u}} (φ : Y ⟶ Z) (x : Y) (z : Z)
    (hcotangent : Nonempty (Chapter15CotangentMapData (k := k) φ x z)) :
    Nonempty (Chapter15TangentMapData (k := k) φ x z) := by
  sorry

theorem chapter15_formal_immersion_implies_tangent_injective
    {k : Type u} [Field k]
    {Y Z : Scheme.{u}} (φ : Y ⟶ Z) (x : Y) (z : Z)
    (hformal : Chapter15FormalImmersionAt φ x z) :
    Nonempty (Chapter15TangentMapData (k := k) φ x z) := by
  sorry

theorem chapter15_formal_immersion_of_cotangent_surjective
    {k : Type u} [Field k]
    {Y Z : Scheme.{u}} (φ : Y ⟶ Z) (x : Y) (z : Z)
    (hresidue : Chapter15SameResidueField x z)
    (hfinite : Chapter15FormalImmersionFiniteness φ)
    (hcotangent : Nonempty (Chapter15CotangentMapData (k := k) φ x z)) :
    Chapter15FormalImmersionAt φ x z := by
  sorry

theorem chapter15_formal_immersion_iff_tangent_injective
    {k : Type u} [Field k]
    {Y Z : Scheme.{u}} (φ : Y ⟶ Z) (x : Y) (z : Z)
    (hresidue : Chapter15SameResidueField x z)
    (hfinite : Chapter15FormalImmersionFiniteness φ) :
    Chapter15FormalImmersionAt φ x z ↔
      Nonempty (Chapter15TangentMapData (k := k) φ x z) := by
  sorry

structure Chapter15AbelMapAtDivisor
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d) where
  abelMapData : Chapter15AbelMapData C.curve d
  source_point : (symmetricPower C.curve d).carrier
  target_point : abelMapData.picard.representing.carrier
  map : (symmetricPower C.curve d).carrier ⟶
    abelMapData.picard.representing.carrier
  map_is_abel_map : map = abelMapData.abelMap.hom
  source_point_is_divisor :
    source_point = (divisorToSymmetricPoint C.curve
      (RelativeScheme.base (chapter15FieldBase k)) d D
      ).hom (IsLocalRing.closedPoint k)
  target_point_is_abel_image : target_point = map source_point
  point_compatibility : map source_point = target_point

structure Chapter15AbelFormalImmersionProfile
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d) where
  mapAtDivisor : Chapter15AbelMapAtDivisor C d D
  differential : chapter15NormalSections D ⟶ chapter15H1StructureSpace C
  differential_is_abel_boundary :
    differential = chapter15CartierConnectingMap C d D
  restrictionOfDifferentials :
    chapter15DifferentialModule C ⟶ chapter15RestrictedDifferentialModule C d D
  restriction_is_canonical :
    restrictionOfDifferentials = chapter15DifferentialRestrictionMap C d D
  residue_fields_agree :
    Chapter15SameResidueField mapAtDivisor.source_point mapAtDivisor.target_point
  finite_type_and_noetherian : Chapter15FormalImmersionFiniteness mapAtDivisor.map

theorem chapter15_abel_formal_immersion_iff_differential_injective
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d)
    (P : Chapter15AbelFormalImmersionProfile C d D)
    (hresidue :
      Chapter15SameResidueField P.mapAtDivisor.source_point
        P.mapAtDivisor.target_point)
    (hfinite : Chapter15FormalImmersionFiniteness P.mapAtDivisor.map) :
    Chapter15FormalImmersionAt
        P.mapAtDivisor.map P.mapAtDivisor.source_point P.mapAtDivisor.target_point ↔
      Function.Injective P.differential.hom ∧
        Function.Surjective P.restrictionOfDifferentials.hom := by
  sorry

theorem chapter15_formal_abel_immersion_forces_degree_le_genus
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d)
    (P : Chapter15AbelFormalImmersionProfile C d D)
    (hresidue :
      Chapter15SameResidueField P.mapAtDivisor.source_point
        P.mapAtDivisor.target_point)
    (hfinite : Chapter15FormalImmersionFiniteness P.mapAtDivisor.map) :
    Chapter15FormalImmersionAt
        P.mapAtDivisor.map P.mapAtDivisor.source_point P.mapAtDivisor.target_point →
      (d : ℤ) ≤ C.genus := by
  sorry

structure Chapter15DifferentialEvaluationData
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k)
    (p q : Chapter15RationalPointData C) where
  evaluation : chapter15DifferentialModule C ⟶ ModuleCat.of.{u, u} k (k × k)
  distinct_points : p.point ≠ q.point

def Chapter15DifferentialEvaluationSeparatesPoints
    {k : Type u} [Field k]
    {C : Chapter15ProperSmoothIntegralCurve k}
    {p q : Chapter15RationalPointData C}
    (E : Chapter15DifferentialEvaluationData C p q) : Prop :=
  Function.Surjective E.evaluation.hom

theorem chapter15_distinct_points_have_differential_evaluation
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k)
    (p q : Chapter15RationalPointData C) (hpq : p.point ≠ q.point) :
    Nonempty (Chapter15DifferentialEvaluationData C p q) := by
  sorry

structure Chapter15NodalDualizingData
    {k : Type u} [Field k] (X : Scheme.{u}) where
  nodal : chapter01NodalScheme X
  smoothLocus : Set X
  dualizing : Chapter15LineBundle X
  normalization : Scheme.{u}
  normalizationMap : normalization ⟶ X
  dualizing_restriction :
    (Scheme.Modules.pullback normalizationMap).obj dualizing.module ⟶
      chapter15StructureSheaf normalization
  normalization_differentials : normalization.Modules
  simple_pole_comparison :
    Nonempty (normalization_differentials ≅
      (Scheme.Modules.pullback normalizationMap).obj dualizing.module)
  residues : ModuleCat.{u, u} k
  opposite_branch_residues : Nonempty (residues ≅ residues)

structure Chapter15NodalAbelFormalImmersionData
  {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d) where
  dualizing : Chapter15NodalDualizingData (k := k) (Chapter15FiberCurve C)
  mapAtDivisor : Chapter15AbelMapAtDivisor C d D
  divisor_supported_on_smooth_locus :
    (D.divisor.ideal.support : Set (Chapter15FiberCurve C)) ⊆ dualizing.smoothLocus
  differential : chapter15NormalSections D ⟶ chapter15H1StructureSpace C
  differential_is_abel_boundary :
    differential = chapter15CartierConnectingMap C d D
  smooth_locus_restriction :
    chapter15DifferentialModule C ⟶ chapter15RestrictedDifferentialModule C d D
  restriction_is_dualizing :
    smooth_locus_restriction = chapter15DifferentialRestrictionMap C d D
  dualizing_map :
    (Scheme.Modules.pullback dualizing.normalizationMap).obj dualizing.dualizing.module ⟶
      chapter15StructureSheaf dualizing.normalization
  dualizing_map_is_canonical :
    dualizing_map = dualizing.dualizing_restriction
  residue_fields_agree :
    Chapter15SameResidueField mapAtDivisor.source_point mapAtDivisor.target_point
  finite_type_and_noetherian : Chapter15FormalImmersionFiniteness mapAtDivisor.map

theorem chapter15_nodal_formal_immersion_criterion
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d) :
    ∀ P : Chapter15NodalAbelFormalImmersionData C d D,
      Nonempty (P.dualizing.residues ≅ P.dualizing.residues) →
      Chapter15SameResidueField P.mapAtDivisor.source_point
        P.mapAtDivisor.target_point →
      Chapter15FormalImmersionFiniteness P.mapAtDivisor.map →
      Chapter15FormalImmersionAt
          P.mapAtDivisor.map P.mapAtDivisor.source_point P.mapAtDivisor.target_point ↔
        Function.Injective P.differential.hom ∧
          Function.Surjective P.smooth_locus_restriction.hom := by
  sorry

structure Chapter15NodalAbelFormalNeighborhoodComparison
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (A : Chapter15AbelMapData C.curve d)
    (D E : Chapter15FiberDivisor C d) where
  nodal_duality_hypotheses :
    Chapter15NodalDualizingData (k := k) (Chapter15FiberCurve C)
  source_point : A.picard.representing.carrier
  target_point : A.picard.representing.carrier
  source_point_is_abel_image :
    source_point = (chapter15AbelPoint C d A D).hom
      (IsLocalRing.closedPoint k)
  target_point_is_abel_image :
    target_point = (chapter15AbelPoint C d A E).hom
      (IsLocalRing.closedPoint k)
  equal_formal_neighborhoods : Nonempty
    (CommRingCat.of (chapter01CompletedLocalRing A.picard.representing.carrier source_point) ≅
      CommRingCat.of (chapter01CompletedLocalRing A.picard.representing.carrier target_point))

theorem chapter15_nodal_Abel_image_and_formal_neighborhood_comparison
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (A : Chapter15AbelMapData C.curve d)
    (D E : Chapter15FiberDivisor C d)
    (hdual : Chapter15NodalDualizingData (k := k) (Chapter15FiberCurve C))
    (equal_Abel_images :
      chapter15AbelPoint C d A D = chapter15AbelPoint C d A E) :
    Nonempty (Chapter15NodalAbelFormalNeighborhoodComparison C d A D E) := by
  sorry

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter15
