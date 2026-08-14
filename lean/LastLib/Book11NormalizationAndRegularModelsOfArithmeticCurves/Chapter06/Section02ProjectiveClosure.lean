import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter06.Dependencies

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter06

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry

universe u v

/-! ### 6.2 Projective closure -/

theorem chapter06_schematicClosure_factorization
    (D : Chapter06ClosureDatum C) :
    chapter06SchematicClosureToAmbient D ≫
        chapter06SchematicClosureEmbedding D =
      chapter06GenericEmbeddingIntoBaseAmbient D := by
  exact (chapter06GenericEmbeddingIntoBaseAmbient D).toImage_imageι

theorem chapter06_schematicClosure_is_smallest_closed_subscheme
    (D : Chapter06ClosureDatum C)
    {Z : Scheme.{u}}
    (i : Z ⟶ chapter02ProjectiveSpace (Spec (.of R)) D.dimension)
    [IsClosedImmersion i]
    (hcontains : chapter06ClosedSubschemeContains
      (chapter06GenericEmbeddingIntoBaseAmbient D) i) :
    ∃ h : chapter06SchematicClosure D ⟶ Z,
      h ≫ i = chapter06SchematicClosureEmbedding D := by
  sorry

theorem chapter06_affine_closure_coordinate_subring
    (R A : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing A] [Algebra R A] :
    Nonempty
      (chapter06SaturatedAffineRing R A ≃+*
      (chapter06GenericFiberRingMap R A).range) := by
  sorry

theorem chapter06_affine_closure_coordinate_injective
    (R A : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing A] [Algebra R A] :
    Function.Injective (chapter06SaturationGenericMap R A) := by
  exact RingHom.kerLift_injective _

noncomputable def chapter06SchematicClosureModel
    (D : Chapter06ClosureDatum C) : Chapter06Model R C :=
  { carrier := chapter06SchematicClosure D
    structureMap := chapter06SchematicClosureStructureMap D
    projective := by
      sorry
    proper := by
      sorry
    locallyOfFiniteType := by
      sorry
    flat := by
      sorry
    integral := by
      sorry
    genericFiber := by
      sorry }

theorem chapter06_schematicClosure_model_carrier
    (D : Chapter06ClosureDatum C) :
    (chapter06SchematicClosureModel D).carrier = chapter06SchematicClosure D :=
  rfl

theorem chapter06_schematicClosure_model_is_integral
    (D : Chapter06ClosureDatum C) :
    IsIntegral (chapter06SchematicClosureModel D).carrier :=
  (chapter06SchematicClosureModel D).integral

theorem chapter06_schematicClosure_model_is_flat
    (D : Chapter06ClosureDatum C) :
    Flat (chapter06SchematicClosureModel D).structureMap :=
  (chapter06SchematicClosureModel D).flat

theorem chapter06_schematicClosure_model_is_projective
    (D : Chapter06ClosureDatum C) :
    chapter04Projective (chapter06SchematicClosureModel D).structureMap :=
  (chapter06SchematicClosureModel D).projective

/-! Proposition 6.1 is exposed both as a bundled model and as its individual
scheme-theoretic properties. -/

theorem chapter06_proposition_6_1
    (D : Chapter06ClosureDatum C) :
    IsIntegral (chapter06SchematicClosure D) ∧
      Flat (chapter06SchematicClosureStructureMap D) ∧
      chapter04Projective (chapter06SchematicClosureStructureMap D) ∧
      Nonempty
        (Chapter06GenericFiberIdentification R C
          (chapter06SchematicClosureStructureMap D)) := by
  let X₀ := chapter06SchematicClosureModel D
  refine ⟨X₀.integral, X₀.flat, X₀.projective, ?_⟩
  exact ⟨X₀.genericFiber⟩

theorem chapter06_schematicClosure_topological_support
    (D : Chapter06ClosureDatum C) :
    ((chapter06SchematicClosureEmbedding D).range : Set
        (chapter02ProjectiveSpace (Spec (.of R)) D.dimension)) =
      closure (Set.range (chapter06GenericEmbeddingIntoBaseAmbient D)) := by
  sorry

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter06
