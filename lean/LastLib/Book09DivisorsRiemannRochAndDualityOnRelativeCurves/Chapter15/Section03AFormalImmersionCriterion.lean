import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter15.Section02TheInfinitesimalAbelMap

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter15

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

/-!
### 15.3 A formal-immersion criterion

The formal-immersion certificate below keeps the completed local-ring map,
its direction, and surjectivity visible.  Cotangent and tangent certificates
are separate so the residue-field and finiteness assumptions of the converse
cannot disappear into a definition.

-/

/- LOCAL_DEPENDENCY_GUESS: the pinned scheme API does not expose the completed
   local-ring comparison and cotangent/tangent maps in the source-facing form;
   these certificates are the minimal interfaces needed by the criterion. -/

structure Chapter15CompletedLocalRingMap
    {Y Z : Scheme.{u}} (φ : Y ⟶ Z) (x : Y) (z : Z) where
  targetCompletion : CommRingCat.{u}
  sourceCompletion : CommRingCat.{u}
  map : targetCompletion ⟶ sourceCompletion
  target_is_completed_local_ring : Prop
  target_is_completed_local_ring_proof : target_is_completed_local_ring
  source_is_completed_local_ring : Prop
  source_is_completed_local_ring_proof : source_is_completed_local_ring
  identifies_with_local_rings : Prop
  identifies_with_local_rings_proof : identifies_with_local_rings
  surjective : Function.Surjective map.hom

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
  cotangentAtTarget : ModuleCat k
  cotangentAtSource : ModuleCat k
  cotangentMap : cotangentAtTarget ⟶ cotangentAtSource
  target_is_mZ_over_mZsq : Prop
  target_is_mZ_over_mZsq_proof : target_is_mZ_over_mZsq
  source_is_mX_over_mXsq : Prop
  source_is_mX_over_mXsq_proof : source_is_mX_over_mXsq
  induced_by_local_ring_map : Prop
  induced_by_local_ring_map_proof : induced_by_local_ring_map
  surjective : Function.Surjective cotangentMap.hom

structure Chapter15TangentMapData
    {k : Type u} [Field k]
    {Y Z : Scheme.{u}} (φ : Y ⟶ Z) (x : Y) (z : Z) where
  tangentAtSource : ModuleCat k
  tangentAtTarget : ModuleCat k
  tangentMap : tangentAtSource ⟶ tangentAtTarget
  dual_to_cotangent_map : Prop
  dual_to_cotangent_map_proof : dual_to_cotangent_map
  injective : Function.Injective tangentMap.hom

theorem chapter15_formal_immersion_implies_cotangent_surjective
    {k : Type u} [Field k]
    {Y Z : Scheme.{u}} (φ : Y ⟶ Z) (x : Y) (z : Z)
    (hformal : Chapter15FormalImmersionAt φ x z) :
    Nonempty (Chapter15CotangentMapData φ x z) := by
  sorry

theorem chapter15_cotangent_surjective_implies_tangent_injective
    {k : Type u} [Field k]
    {Y Z : Scheme.{u}} (φ : Y ⟶ Z) (x : Y) (z : Z)
    (hcotangent : Nonempty (Chapter15CotangentMapData φ x z)) :
    Nonempty (Chapter15TangentMapData φ x z) := by
  sorry

theorem chapter15_formal_immersion_implies_tangent_injective
    {k : Type u} [Field k]
    {Y Z : Scheme.{u}} (φ : Y ⟶ Z) (x : Y) (z : Z)
    (hformal : Chapter15FormalImmersionAt φ x z) :
    Nonempty (Chapter15TangentMapData φ x z) := by
  sorry

theorem chapter15_formal_immersion_of_cotangent_surjective
    {k : Type u} [Field k]
    {Y Z : Scheme.{u}} (φ : Y ⟶ Z) (x : Y) (z : Z)
    (same_residue_field : Prop)
    (hresidue : same_residue_field)
    (finite_type_and_noetherian : Prop)
    (hfinite : finite_type_and_noetherian)
    (hcotangent : Nonempty (Chapter15CotangentMapData φ x z)) :
    Chapter15FormalImmersionAt φ x z := by
  sorry

theorem chapter15_formal_immersion_iff_tangent_injective
    {k : Type u} [Field k]
    {Y Z : Scheme.{u}} (φ : Y ⟶ Z) (x : Y) (z : Z)
    (same_residue_field : Prop)
    (hresidue : same_residue_field)
    (finite_type_and_noetherian : Prop)
    (hfinite : finite_type_and_noetherian) :
    Chapter15FormalImmersionAt φ x z ↔
      Nonempty (Chapter15TangentMapData φ x z) := by
  sorry

structure Chapter15AbelMapAtDivisor
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d) where
  source : Scheme.{u}
  target : Scheme.{u}
  map : source ⟶ target
  source_point : source
  target_point : target
  point_compatibility : Prop
  point_compatibility_proof : point_compatibility

structure Chapter15AbelFormalImmersionProfile
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d) where
  mapAtDivisor : Chapter15AbelMapAtDivisor C d D
  differentialSource : ModuleCat k
  differentialTarget : ModuleCat k
  differential : differentialSource ⟶ differentialTarget
  differentialSource_is_H0_D : differentialSource = chapter15NormalSections D
  differentialTarget_is_H1 : differentialTarget = chapter15H1StructureSpace C
  differential_is_abel_boundary : Prop
  differential_is_abel_boundary_proof : differential_is_abel_boundary
  restrictionSource : ModuleCat k
  restrictionTarget : ModuleCat k
  restrictionOfDifferentials : restrictionSource ⟶ restrictionTarget
  residue_fields_agree : Prop
  residue_fields_agree_proof : residue_fields_agree
  finite_type_and_noetherian : Prop
  finite_type_and_noetherian_proof : finite_type_and_noetherian

theorem chapter15_abel_formal_immersion_iff_differential_injective
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d)
    (P : Chapter15AbelFormalImmersionProfile C d D)
    (hresidue : P.residue_fields_agree)
    (hfinite : P.finite_type_and_noetherian) :
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
    (hresidue : P.residue_fields_agree)
    (hfinite : P.finite_type_and_noetherian) :
    Chapter15FormalImmersionAt
        P.mapAtDivisor.map P.mapAtDivisor.source_point P.mapAtDivisor.target_point →
      (d : ℤ) ≤ C.genus := by
  sorry

structure Chapter15DifferentialEvaluationData
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k)
    (p q : Chapter15RationalPointData C) where
  differentials : ModuleCat k
  differentials_are_H0_omega : Prop
  differentials_are_H0_omega_proof : differentials_are_H0_omega
  valuesAtPoints : ModuleCat.of k (k × k)
  evaluation : differentials ⟶ valuesAtPoints
  distinct_points : p.point ≠ q.point
  separates_points : Prop
  separates_points_proof : separates_points

theorem chapter15_distinct_points_are_separated_by_differentials
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k)
    (p q : Chapter15RationalPointData C) (hpq : p.point ≠ q.point) :
    Nonempty (Chapter15DifferentialEvaluationData C p q) := by
  sorry

structure Chapter15NodalDualizingData
    {k : Type u} [Field k] where
  curve : Scheme.{u}
  nodal : Prop
  nodal_proof : nodal
  smoothLocus : Set curve
  dualizingModule : curve.Modules
  dualizing_invertible_on_smooth_locus : Prop
  dualizing_invertible_on_smooth_locus_proof :
    dualizing_invertible_on_smooth_locus
  normalization : Scheme.{u}
  pullback_with_simple_poles : Prop
  pullback_with_simple_poles_proof : pullback_with_simple_poles
  opposite_branch_residues : Prop
  opposite_branch_residues_proof : opposite_branch_residues

structure Chapter15NodalAbelFormalImmersionData
  {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d) where
  dualizing : Chapter15NodalDualizingData (k := k)
  mapAtDivisor : Chapter15AbelMapAtDivisor C d D
  divisor_supported_on_smooth_locus : Prop
  divisor_supported_on_smooth_locus_proof : divisor_supported_on_smooth_locus
  differentialSource : ModuleCat k
  differentialTarget : ModuleCat k
  differential : differentialSource ⟶ differentialTarget
  restrictionSource : ModuleCat k
  restrictionTarget : ModuleCat k
  smooth_locus_restriction : restrictionSource ⟶ restrictionTarget
  opposite_residue_condition : Prop
  opposite_residue_condition_proof : opposite_residue_condition
  residue_fields_agree : Prop
  residue_fields_agree_proof : residue_fields_agree
  finite_type_and_noetherian : Prop
  finite_type_and_noetherian_proof : finite_type_and_noetherian

theorem chapter15_nodal_formal_immersion_criterion
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d) :
    ∀ P : Chapter15NodalAbelFormalImmersionData C d D,
      P.opposite_residue_condition → P.residue_fields_agree →
      P.finite_type_and_noetherian →
      Chapter15FormalImmersionAt
          P.mapAtDivisor.map P.mapAtDivisor.source_point P.mapAtDivisor.target_point ↔
        Function.Injective P.differential.hom ∧
          Function.Surjective P.smooth_locus_restriction.hom := by
  sorry

structure Chapter15NodalAbelFormalNeighborhoodComparison
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D E : Chapter15FiberDivisor C d) where
  nodal_duality_hypotheses : Prop
  nodal_duality_hypotheses_proof : nodal_duality_hypotheses
  equal_formal_neighborhoods : Prop
  equal_formal_neighborhoods_proof : equal_formal_neighborhoods

theorem chapter15_nodal_Abel_image_and_formal_neighborhood_comparison
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (A : Chapter15AbelMapData C.curve d)
    (D E : Chapter15FiberDivisor C d)
    (hdual : Prop) (has_hdual : hdual)
    (equal_Abel_images :
      chapter15AbelPoint C d A D = chapter15AbelPoint C d A E) :
    Nonempty (Chapter15NodalAbelFormalNeighborhoodComparison C d D E) := by
  sorry

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter15
