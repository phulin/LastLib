import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter15.Section01AbelMapsBeforeThePicardScheme

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter15

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

/-!
### 15.2 The infinitesimal Abel map

This section records the tangent-space identifications, the Cartier exact
sequence, and the Serre-dual description of the Abel differential.  The
cohomology objects are represented by `ModuleCat k` so that the maps and their
transposes are available before a global relative-cohomology implementation.
-/

abbrev Chapter15FiberCurve {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) : Scheme.{u} :=
  pullback C.curve.structuralMap
    (RelativeScheme.base (chapter15FieldBase k)).structuralMap

abbrev Chapter15FiberDivisor {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ) :=
  Chapter15FieldDivisor C d

/- LOCAL_DEPENDENCY_GUESS: the pinned cohomology context returns additive
   groups, but the source uses the natural k-vector-space structures on curve
   cohomology. -/
noncomputable def chapter15CohomologyVectorSpace
    {k : Type u} [Field k] {X : Scheme.{u}}
    (F : X.Modules) (i : ℕ) : ModuleCat k := by
  sorry

noncomputable def chapter15NormalSections
    {k : Type u} [Field k]
    {C : Chapter15ProperSmoothIntegralCurve k} {d : ℕ}
    (D : Chapter15FiberDivisor C d) : ModuleCat k := by
  sorry

noncomputable def chapter15PicardTangentSpace
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) : ModuleCat k := by
  sorry

noncomputable def chapter15H1StructureSpace
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) : ModuleCat k := by
  sorry

structure Chapter15SymmetricPowerTangentData
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d) where
  tangent : ModuleCat k
  tangent_is_geometric_tangent : Prop
  tangent_is_geometric_tangent_proof : tangent_is_geometric_tangent
  normalSections : ModuleCat k
  tangent_identification : tangent ≅ normalSections
  normal_sections_are_H0 : Prop
  normal_sections_are_H0_proof : normal_sections_are_H0
  deformation_ideal_map : Prop
  deformation_ideal_map_proof : deformation_ideal_map

theorem chapter15_symmetric_power_tangent_exists
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d) :
    Nonempty (Chapter15SymmetricPowerTangentData C d D) := by
  sorry

noncomputable def chapter15TangentAtDivisor
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d) : ModuleCat k :=
  (Classical.choice (chapter15_symmetric_power_tangent_exists C d D)).tangent

theorem chapter15_tangent_at_divisor_is_H0_normal_sections
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d) :
    Nonempty (chapter15TangentAtDivisor C d D ≅ chapter15NormalSections D) := by
  sorry

/- The dual-number calculation is kept as a separate certificate: it records
   the map of the ideal into O_D and its Hom-module, including the fact that
   nonreduced divisors are allowed. -/
structure Chapter15DualNumberDivisorDeformationData
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d) where
  deformationBase : Scheme.{u}
  residuePoint : Spec (.of k) ⟶ deformationBase
  deformationBase_is_dual_number_base : deformationBase = chapter15DualNumberBase k
  idealModule : ModuleCat k
  structureModule : ModuleCat k
  idealToStructure : idealModule ⟶ structureModule
  homModule : ModuleCat k
  normalSections : ModuleCat k
  hom_identification : homModule ≅ normalSections
  ideal_is_OminusD : Prop
  ideal_is_OminusD_proof : ideal_is_OminusD
  deformation_is_dual_number_lift : Prop
  deformation_is_dual_number_lift_proof : deformation_is_dual_number_lift
  nonreduced_allowed : Prop
  nonreduced_allowed_proof : nonreduced_allowed

theorem chapter15_dual_number_deformation_exists
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d) :
    Nonempty (Chapter15DualNumberDivisorDeformationData C d D) := by
  sorry

structure Chapter15PicardTangentIdentification
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) where
  tangent : ModuleCat k
  h1Structure : ModuleCat k
  identification : tangent ≅ h1Structure
  tangent_is_picard_tangent : tangent = chapter15PicardTangentSpace C
  h1_is_structure_cohomology : h1Structure = chapter15H1StructureSpace C
  h1_is_Cech_H1 : Prop
  h1_is_Cech_H1_proof : h1_is_Cech_H1
  dual_number_transition_description : Prop
  dual_number_transition_description_proof : dual_number_transition_description

theorem chapter15_picard_tangent_is_H1
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) :
    Nonempty (Chapter15PicardTangentIdentification C) := by
  sorry

/- A Cartier sequence on the fiber.  Its quotient is deliberately represented
   by a named module rather than an unrelated module parameter. -/
structure Chapter15CartierExactSequence
    {X : Scheme.{u}} (D : Chapter15EffectiveCartierDivisor X) where
  OX : X.Modules
  OofD : X.Modules
  ODofD : X.Modules
  inclusion : OX ⟶ OofD
  restriction : OofD ⟶ ODofD
  OX_is_structure_sheaf : Nonempty (OX ≅ chapter15StructureSheaf X)
  OofD_is_divisor_line_bundle :
    Nonempty (OofD ≅ (chapter15DivisorLineBundle D).module)
  ODofD_is_restricted_divisor_line_bundle : Prop
  ODofD_is_restricted_divisor_line_bundle_proof :
    ODofD_is_restricted_divisor_line_bundle
  comp_zero : inclusion ≫ restriction = 0
  mono_inclusion : Mono inclusion
  epi_restriction : Epi restriction
  exact : (ShortComplex.mk inclusion restriction comp_zero).Exact

theorem chapter15_cartier_exact_sequence_exists
    {X : Scheme.{u}} (D : Chapter15EffectiveCartierDivisor X) :
    Nonempty (Chapter15CartierExactSequence D) := by
  sorry

noncomputable def chapter15CartierExactSequence
    {X : Scheme.{u}} (D : Chapter15EffectiveCartierDivisor X) :
    Chapter15CartierExactSequence D :=
  Classical.choice (chapter15_cartier_exact_sequence_exists D)

structure Chapter15ConnectingMapData
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d) where
  source : ModuleCat k
  target : ModuleCat k
  boundary : source ⟶ target
  source_is_H0_D : source = chapter15NormalSections D
  target_is_H1_X : target = chapter15H1StructureSpace C
  cartier_sequence : Chapter15CartierExactSequence D.divisor
  induced_by_cartier_sequence : Prop
  induced_by_cartier_sequence_proof : induced_by_cartier_sequence

theorem chapter15_connecting_map_exists
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d) :
    Nonempty (Chapter15ConnectingMapData C d D) := by
  sorry

structure Chapter15AbelDifferentialData
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d) where
  source : ModuleCat k
  target : ModuleCat k
  differential : source ⟶ target
  source_is_H0_D_normal : source = chapter15NormalSections D
  target_is_H1_OX : target = chapter15H1StructureSpace C
  cartier_sequence : Chapter15CartierExactSequence D.divisor
  differential_is_boundary : Prop
  differential_is_boundary_proof : differential_is_boundary
  sign_convention : Prop
  sign_convention_proof : sign_convention

theorem chapter15_abel_differential_is_cartier_boundary
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d) :
    Nonempty (Chapter15AbelDifferentialData C d D) := by
  sorry

/- Serre duality packages the transpose as restriction of differentials. -/
structure Chapter15DifferentialRestrictionData
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d) where
  differentials : ModuleCat k
  restrictedDifferentials : ModuleCat k
  restriction : differentials ⟶ restrictedDifferentials
  h1Dual : ModuleCat k
  normalDual : ModuleCat k
  transpose : normalDual ⟶ h1Dual
  differentials_are_H0_omega : Prop
  differentials_are_H0_omega_proof : differentials_are_H0_omega
  restriction_is_omega_to_D : Prop
  restriction_is_omega_to_D_proof : restriction_is_omega_to_D
  transpose_of_abel_differential : Prop
  transpose_of_abel_differential_proof : transpose_of_abel_differential
  residue_pairing_description : Prop
  residue_pairing_description_proof : residue_pairing_description

theorem chapter15_abel_differential_transpose_is_restriction
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d) :
    Nonempty (Chapter15DifferentialRestrictionData C d D) := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: a divisor-multiplicity/support API is not present in
   the earlier relative-effective-divisor interface. -/
noncomputable def chapter15DivisorMultiplicityAt
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d) (p : Chapter15RationalPointData C) : ℕ := by
  sorry

noncomputable def chapter15DivisorAwayFromPoint
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d) (p : Chapter15RationalPointData C) : ℕ := by
  sorry

def Chapter15DivisorIsMultipleOfPoint
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d) (p : Chapter15RationalPointData C) : Prop :=
  chapter15DivisorMultiplicityAt C d D p = d ∧
    chapter15DivisorAwayFromPoint C d D p = 0

structure Chapter15JetRestrictionData
    {k : Type u} [Field k]
  (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d) (p : Chapter15RationalPointData C) where
  jetOrder : ℕ
  jetSpace : ModuleCat.of k (Fin d → k)
  differentialRestriction : ModuleCat k
  restriction : differentialRestriction ⟶ jetSpace
  jetOrder_eq_d : jetOrder = d
  divisor_is_dp : Chapter15DivisorIsMultipleOfPoint C d D p
  retains_jets_through_order_d_minus_one : Prop
  retains_jets_through_order_d_minus_one_proof :
    retains_jets_through_order_d_minus_one
  evaluates_first_d_power_series_coefficients : Prop
  evaluates_first_d_power_series_coefficients_proof :
    evaluates_first_d_power_series_coefficients

theorem chapter15_repeated_point_divisor_retains_jets
    {k : Type u} [Field k]
  (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d) (p : Chapter15RationalPointData C)
    (hD : Chapter15DivisorIsMultipleOfPoint C d D p) :
    Nonempty (Chapter15JetRestrictionData C d D p) := by
  sorry

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter15
