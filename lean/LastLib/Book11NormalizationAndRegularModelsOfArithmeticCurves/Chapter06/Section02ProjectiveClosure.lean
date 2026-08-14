import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter06.Dependencies

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter06

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open scoped AlgebraicGeometry

universe u v

/-! ### 6.2 Projective closure -/

theorem chapter06_schematicClosure_factorization
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {C : Chapter06SmoothProjectiveCurve R}
    {E : Chapter06ProjectiveEmbedding C}
    (D : Chapter06ClosureDatum C E) :
    chapter06SchematicClosureToAmbient D ≫
        chapter06SchematicClosureEmbedding D =
      chapter06GenericEmbeddingIntoBaseAmbient D := by
  exact (chapter06GenericEmbeddingIntoBaseAmbient D).toImage_imageι

theorem chapter06_schematicClosure_is_smallest_closed_subscheme
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {C : Chapter06SmoothProjectiveCurve R}
    {E : Chapter06ProjectiveEmbedding C}
    (D : Chapter06ClosureDatum C E)
    {Z : Scheme.{u}}
    (i : Z ⟶ chapter02ProjectiveSpace (Spec (.of R)) E.dimension)
    [IsClosedImmersion i]
    (hcontains : chapter06ClosedSubschemeContains
      (chapter06GenericEmbeddingIntoBaseAmbient D) i) :
    ∃ h : chapter06SchematicClosure D ⟶ Z,
      h ≫ i = chapter06SchematicClosureEmbedding D := by
  rcases hcontains with ⟨g, hg⟩
  have hker :
      i.ker ≤ (chapter06GenericEmbeddingIntoBaseAmbient D).ker := by
    rw [← hg]
    exact g.le_ker_comp i
  have hker' :
      i.ker ≤ (chapter06SchematicClosureEmbedding D).ker := by
    simpa [chapter06SchematicClosureEmbedding, chapter06SchematicClosure] using hker
  refine ⟨IsClosedImmersion.lift i (chapter06SchematicClosureEmbedding D) hker', ?_⟩
  exact IsClosedImmersion.lift_fac i (chapter06SchematicClosureEmbedding D) hker'

theorem chapter06_affine_closure_coordinate_subring
    (R A : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing A] [Algebra R A] :
    Nonempty
      (chapter06SaturatedAffineRing R A ≃+*
      (chapter06GenericFiberRingMap R A).range) := by
  exact ⟨RingHom.quotientKerEquivRange (chapter06GenericFiberRingMap R A)⟩

theorem chapter06_affine_closure_coordinate_injective
    (R A : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing A] [Algebra R A] :
    Function.Injective (chapter06SaturationGenericMap R A) := by
  exact RingHom.kerLift_injective _

noncomputable def chapter06SchematicClosureModel
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {C : Chapter06SmoothProjectiveCurve R}
    {E : Chapter06ProjectiveEmbedding C}
    (D : Chapter06ClosureDatum C E) : Chapter06ProjectiveModel R C :=
  { toChapter06ProperModel :=
      { toChapter06Model :=
          { carrier := chapter06SchematicClosure D
            structureMap := chapter06SchematicClosureStructureMap D
            locallyOfFiniteType := by
              sorry
            quasiCompact := by
              sorry
            flat := by
              sorry
            integral := by
              sorry
            genericFiber := by
              sorry }
        proper := by
          sorry }
    projective := by
      sorry }

theorem chapter06_schematicClosure_model_carrier
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {C : Chapter06SmoothProjectiveCurve R}
    {E : Chapter06ProjectiveEmbedding C}
    (D : Chapter06ClosureDatum C E) :
    (chapter06SchematicClosureModel D).carrier = chapter06SchematicClosure D :=
  rfl

theorem chapter06_schematicClosure_model_is_integral
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {C : Chapter06SmoothProjectiveCurve R}
    {E : Chapter06ProjectiveEmbedding C}
    (D : Chapter06ClosureDatum C E) :
    IsIntegral (chapter06SchematicClosureModel D).carrier :=
  (chapter06SchematicClosureModel D).integral

theorem chapter06_schematicClosure_model_is_flat
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {C : Chapter06SmoothProjectiveCurve R}
    {E : Chapter06ProjectiveEmbedding C}
    (D : Chapter06ClosureDatum C E) :
    Flat (chapter06SchematicClosureModel D).structureMap :=
  (chapter06SchematicClosureModel D).flat

theorem chapter06_schematicClosure_model_is_projective
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {C : Chapter06SmoothProjectiveCurve R}
    {E : Chapter06ProjectiveEmbedding C}
    (D : Chapter06ClosureDatum C E) :
    chapter04Projective (chapter06SchematicClosureModel D).structureMap :=
  (chapter06SchematicClosureModel D).projective

/-! Proposition 6.1 is exposed both as a bundled model and as its individual
scheme-theoretic properties. -/

theorem chapter06_proposition_6_1
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {C : Chapter06SmoothProjectiveCurve R}
    {E : Chapter06ProjectiveEmbedding C}
    (D : Chapter06ClosureDatum C E) :
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
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {C : Chapter06SmoothProjectiveCurve R}
    {E : Chapter06ProjectiveEmbedding C}
    (D : Chapter06ClosureDatum C E) :
    Set.range (chapter06SchematicClosureEmbedding D) =
      closure (Set.range (chapter06GenericEmbeddingIntoBaseAmbient D)) := by
  let : IsClosedImmersion E.map := E.closedImmersion
  let : QuasiCompact (chapter06GenericBaseMap R) := by infer_instance
  let : QuasiCompact (chapter06GenericEmbeddingIntoBaseAmbient D) := by
    change QuasiCompact
      (E.map ≫ D.genericAmbientIso.inv ≫
        pullback.fst
          (chapter02ProjectiveSpaceProjection (Spec (.of R)) E.dimension)
          (chapter06GenericBaseMap R))
    infer_instance
  change Set.range (chapter06GenericEmbeddingIntoBaseAmbient D).imageι =
    closure (Set.range (chapter06GenericEmbeddingIntoBaseAmbient D))
  rw [AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι,
    Scheme.Hom.support_ker]

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter06
