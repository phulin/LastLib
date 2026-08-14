import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter15.Section01AbelMapsBeforeThePicardScheme

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter15

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11

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

/- The additive cohomology object is the earlier canonical `chapter09HObject`;
   this wrapper supplies the scalar-enhanced module used by the infinitesimal
   maps. -/
noncomputable def chapter15CohomologyVectorSpace
    {k : Type u} [Field k] {X : Scheme.{u}}
    (F : X.Modules) (i : ℕ) : ModuleCat.{u, u} k := by
  sorry

noncomputable def chapter15NormalSheaf
    {k : Type u} [Field k]
    {C : Chapter15ProperSmoothIntegralCurve k} {d : ℕ}
    (D : Chapter15FiberDivisor C d) : D.divisor.subscheme.Modules :=
  (Scheme.Modules.pullback D.divisor.inclusion).obj
    (chapter15DivisorLineBundle D.divisor).module

noncomputable def chapter15NormalSections
    {k : Type u} [Field k]
    {C : Chapter15ProperSmoothIntegralCurve k} {d : ℕ}
    (D : Chapter15FiberDivisor C d) : ModuleCat.{u, u} k :=
  chapter15CohomologyVectorSpace (chapter15NormalSheaf D) 0

noncomputable def chapter15PicardTangentSpace
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) : ModuleCat.{u, u} k :=
  chapter15CohomologyVectorSpace
    (chapter15StructureSheaf C.curve.carrier) 1

noncomputable def chapter15H1StructureSpace
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) : ModuleCat.{u, u} k :=
  chapter15PicardTangentSpace C

noncomputable def chapter15IdealSheafModule
    {X : Scheme.{u}} (D : Chapter15EffectiveCartierDivisor X) :
    X.Modules := by
  sorry

noncomputable def chapter15IdealToStructureMap
    {X : Scheme.{u}} (D : Chapter15EffectiveCartierDivisor X) :
    chapter15IdealSheafModule D ⟶ chapter15StructureSheaf X := by
  sorry

noncomputable def chapter15DivisorInclusionMap
    {X : Scheme.{u}} (D : Chapter15EffectiveCartierDivisor X) :
    chapter15StructureSheaf X ⟶ (chapter15DivisorLineBundle D).module := by
  sorry

noncomputable def chapter15DivisorRestrictionModule
    {X : Scheme.{u}} (D : Chapter15EffectiveCartierDivisor X) : X.Modules := by
  sorry

noncomputable def chapter15DivisorRestrictionMap
    {X : Scheme.{u}} (D : Chapter15EffectiveCartierDivisor X) :
    (chapter15DivisorLineBundle D).module ⟶ chapter15DivisorRestrictionModule D := by
  sorry

noncomputable def chapter15CartierConnectingMap
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d) :
    chapter15NormalSections D ⟶ chapter15H1StructureSpace C := by
  sorry

noncomputable def chapter15DifferentialModule
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) : ModuleCat.{u, u} k := by
  sorry

noncomputable def chapter15RestrictedDifferentialModule
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d) : ModuleCat.{u, u} k := by
  sorry

noncomputable def chapter15DifferentialRestrictionMap
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d) :
    chapter15DifferentialModule C ⟶ chapter15RestrictedDifferentialModule C d D := by
  sorry

noncomputable def chapter15H1DualModule
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) : ModuleCat.{u, u} k := by
  sorry

noncomputable def chapter15NormalDualModule
    {k : Type u} [Field k]
    {C : Chapter15ProperSmoothIntegralCurve k} {d : ℕ}
    (D : Chapter15FiberDivisor C d) : ModuleCat.{u, u} k := by
  sorry

noncomputable def chapter15TransposeRestrictionMap
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d) :
    chapter15NormalDualModule D ⟶ chapter15H1DualModule C := by
  sorry

noncomputable def chapter15TangentAtDivisor
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d) : ModuleCat.{u, u} k :=
  chapter15NormalSections D

structure Chapter15SymmetricPowerTangentData
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d) where
  tangent_identification :
    chapter15TangentAtDivisor C d D ≅ chapter15NormalSections D
  deformation_ideal_map :
    chapter15IdealSheafModule D.divisor ⟶
      chapter15StructureSheaf (Chapter15FiberCurve C)
  deformation_ideal_map_is_canonical :
    deformation_ideal_map = chapter15IdealToStructureMap D.divisor

theorem chapter15_symmetric_power_tangent_exists
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d) :
    Nonempty (Chapter15SymmetricPowerTangentData C d D) := by
  sorry

theorem chapter15_tangent_at_divisor_is_H0_normal_sections
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d) :
    Nonempty (chapter15TangentAtDivisor C d D ≅ chapter15NormalSections D) := by
  sorry

/- The dual-number calculation uses the canonical dual-number base and the
   actual ideal-to-structure map attached to the divisor. -/
structure Chapter15DualNumberDivisorDeformationData
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d) where
  residuePoint : Spec (.of k) ⟶ chapter15DualNumberBase k
  idealToStructure :
    chapter15IdealSheafModule D.divisor ⟶
      chapter15StructureSheaf (Chapter15FiberCurve C)
  idealToStructure_is_canonical :
    idealToStructure = chapter15IdealToStructureMap D.divisor
  hom_identification : chapter15NormalSections D ≅ chapter15NormalSections D

theorem chapter15_dual_number_deformation_exists
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d) :
    Nonempty (Chapter15DualNumberDivisorDeformationData C d D) := by
  sorry

structure Chapter15PicardTangentIdentification
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) where
  identification : chapter15PicardTangentSpace C ≅ chapter15H1StructureSpace C
  h1_is_structure_cohomology :
    chapter15H1StructureSpace C =
      chapter15CohomologyVectorSpace (chapter15StructureSheaf C.curve.carrier) 1
  dual_number_transition : chapter15H1StructureSpace C ⟶
    chapter15H1StructureSpace C

theorem chapter15_picard_tangent_is_H1
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) :
    Nonempty (Chapter15PicardTangentIdentification C) := by
  sorry

/- A Cartier sequence on the divisor is expressed using the canonical structure
   sheaf, divisor line bundle, and restriction module. -/
structure Chapter15CartierExactSequence
    {X : Scheme.{u}} (D : Chapter15EffectiveCartierDivisor X) where
  inclusion : chapter15StructureSheaf X ⟶ (chapter15DivisorLineBundle D).module
  restriction : (chapter15DivisorLineBundle D).module ⟶
    chapter15DivisorRestrictionModule D
  inclusion_is_canonical : inclusion = chapter15DivisorInclusionMap D
  restriction_is_canonical : restriction = chapter15DivisorRestrictionMap D
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
  boundary : chapter15NormalSections D ⟶ chapter15H1StructureSpace C
  cartier_sequence : Chapter15CartierExactSequence D.divisor
  induced_by_cartier_sequence : boundary = chapter15CartierConnectingMap C d D

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
  differential : chapter15NormalSections D ⟶ chapter15H1StructureSpace C
  cartier_sequence : Chapter15CartierExactSequence D.divisor
  differential_is_boundary : differential = chapter15CartierConnectingMap C d D

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
  restriction : chapter15DifferentialModule C ⟶
    chapter15RestrictedDifferentialModule C d D
  restriction_is_omega_to_D : restriction = chapter15DifferentialRestrictionMap C d D
  transpose : chapter15NormalDualModule D ⟶ chapter15H1DualModule C
  transpose_of_abel_differential : transpose = chapter15TransposeRestrictionMap C d D

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

noncomputable def chapter15JetRestrictionMap
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d) (p : Chapter15RationalPointData C) :
    chapter15DifferentialModule C ⟶ ModuleCat.of.{u, u} k (Fin d → k) := by
  sorry

structure Chapter15JetRestrictionData
    {k : Type u} [Field k]
  (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d) (p : Chapter15RationalPointData C) where
  jetOrder : ℕ
  restriction : chapter15DifferentialModule C ⟶
    ModuleCat.of.{u, u} k (Fin d → k)
  jetOrder_eq_d : jetOrder = d
  divisor_is_dp : Chapter15DivisorIsMultipleOfPoint C d D p
  restriction_is_canonical : restriction = chapter15JetRestrictionMap C d D p

theorem chapter15_repeated_point_divisor_retains_jets
    {k : Type u} [Field k]
  (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d) (p : Chapter15RationalPointData C)
    (hD : Chapter15DivisorIsMultipleOfPoint C d D p) :
    Nonempty (Chapter15JetRestrictionData C d D p) := by
  sorry

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter15
