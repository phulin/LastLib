import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter06.Section04NormalizationOfTheClosure
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter06

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u v

/-! ### 6.5 Existence and uniqueness up to modification -/

abbrev chapter06ModelProduct
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {C : Chapter06SmoothProjectiveCurve R}
    (X Y : Chapter06ProperModel R C) : Scheme.{u} :=
  pullback X.structureMap Y.structureMap

abbrev chapter06ModelProductToX
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {C : Chapter06SmoothProjectiveCurve R}
    (X Y : Chapter06ProperModel R C) : chapter06ModelProduct X Y ⟶ X.carrier :=
  pullback.fst X.structureMap Y.structureMap

abbrev chapter06ModelProductToY
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {C : Chapter06SmoothProjectiveCurve R}
    (X Y : Chapter06ProperModel R C) : chapter06ModelProduct X Y ⟶ Y.carrier :=
  pullback.snd X.structureMap Y.structureMap

abbrev chapter06ModelProductToBase
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {C : Chapter06SmoothProjectiveCurve R}
    (X Y : Chapter06ProperModel R C) : chapter06ModelProduct X Y ⟶ Chapter06BaseScheme R :=
  chapter06ModelProductToX X Y ≫ X.structureMap

noncomputable def chapter06GenericDiagonalMap
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {C : Chapter06SmoothProjectiveCurve R}
    (X Y : Chapter06ProperModel R C) :
    C.carrier ⟶ chapter06ModelProduct X Y :=
  pullback.lift
    (X.genericFiber.iso.inv ≫
      pullback.fst X.structureMap (chapter06GenericBaseMap R))
    (Y.genericFiber.iso.inv ≫
      pullback.fst Y.structureMap (chapter06GenericBaseMap R)) (by
        simp only [Category.assoc, pullback.condition]
        rw [← X.genericFiber.over, ← Y.genericFiber.over]
        simp only [Category.assoc, Iso.inv_hom_id_assoc])

noncomputable def chapter06DiagonalClosure
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {C : Chapter06SmoothProjectiveCurve R}
    (X Y : Chapter06ProperModel R C) : Scheme.{u} :=
  (chapter06GenericDiagonalMap X Y).image

abbrev chapter06DiagonalClosureEmbedding
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {C : Chapter06SmoothProjectiveCurve R}
    (X Y : Chapter06ProperModel R C) :
    chapter06DiagonalClosure X Y ⟶ chapter06ModelProduct X Y :=
  (chapter06GenericDiagonalMap X Y).imageι

noncomputable def chapter06DiagonalClosureToProduct
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {C : Chapter06SmoothProjectiveCurve R}
    (X Y : Chapter06ProperModel R C) :
    C.carrier ⟶ chapter06DiagonalClosure X Y :=
  (chapter06GenericDiagonalMap X Y).toImage

abbrev chapter06DiagonalClosureToX
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {C : Chapter06SmoothProjectiveCurve R}
    (X Y : Chapter06ProperModel R C) :
    chapter06DiagonalClosure X Y ⟶ X.carrier :=
  chapter06DiagonalClosureEmbedding X Y ≫ chapter06ModelProductToX X Y

abbrev chapter06DiagonalClosureToY
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {C : Chapter06SmoothProjectiveCurve R}
    (X Y : Chapter06ProperModel R C) :
    chapter06DiagonalClosure X Y ⟶ Y.carrier :=
  chapter06DiagonalClosureEmbedding X Y ≫ chapter06ModelProductToY X Y

abbrev chapter06DiagonalClosureStructureMap
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {C : Chapter06SmoothProjectiveCurve R}
    (X Y : Chapter06ProperModel R C) :
    chapter06DiagonalClosure X Y ⟶ Chapter06BaseScheme R :=
  chapter06DiagonalClosureToX X Y ≫ X.structureMap

theorem chapter06_diagonalClosure_factorization
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {C : Chapter06SmoothProjectiveCurve R}
    (X Y : Chapter06ProperModel R C) :
    chapter06DiagonalClosureToProduct X Y ≫
        chapter06DiagonalClosureEmbedding X Y =
      chapter06GenericDiagonalMap X Y := by
  exact (chapter06GenericDiagonalMap X Y).toImage_imageι

theorem chapter06_model_product_is_proper
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {C : Chapter06SmoothProjectiveCurve R}
    (X Y : Chapter06ProperModel R C) :
    IsProper (chapter06ModelProductToBase X Y) := by
  infer_instance

theorem chapter06_diagonalClosure_is_proper
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {C : Chapter06SmoothProjectiveCurve R}
    (X Y : Chapter06ProperModel R C) :
    IsProper (chapter06DiagonalClosureStructureMap X Y) := by
  let : IsClosedImmersion (chapter06DiagonalClosureEmbedding X Y) := by
    change IsClosedImmersion (chapter06GenericDiagonalMap X Y).imageι
    infer_instance
  let : IsProper (chapter06ModelProductToBase X Y) :=
    chapter06_model_product_is_proper X Y
  have hmap :
      chapter06DiagonalClosureStructureMap X Y =
        chapter06DiagonalClosureEmbedding X Y ≫
          chapter06ModelProductToBase X Y := by
    simp [chapter06DiagonalClosureStructureMap, chapter06DiagonalClosureToX,
      chapter06ModelProductToBase, Category.assoc]
  rw [hmap]
  infer_instance

theorem chapter06_diagonalClosure_toY_over
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {C : Chapter06SmoothProjectiveCurve R}
    (X Y : Chapter06ProperModel R C) :
    chapter06DiagonalClosureToY X Y ≫ Y.structureMap =
      chapter06DiagonalClosureStructureMap X Y := by
  simp [chapter06DiagonalClosureStructureMap, chapter06DiagonalClosureToX,
    chapter06DiagonalClosureToY, pullback.condition, Category.assoc]

private theorem chapter06_toImage_is_schemeTheoreticallyDominant
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] :
    IsSchemeTheoreticallyDominant f.toImage := by
  refine ⟨?_⟩
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun U : Y.affineOpens ↦ ⟨f.imageι ⁻¹ᵁ U.1, U.2.preimage _⟩)
    (TopologicalSpace.IsOpenCover.comap (iSup_affineOpens_eq_top _) _) fun U ↦ ?_
  simp only [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
  rw [← RingHom.injective_iff_ker_eq_bot]
  exact f.toImage_app_injective U

theorem chapter06_diagonalClosure_projections_are_modifications
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {C : Chapter06SmoothProjectiveCurve R}
    (X Y : Chapter06ProperModel R C) :
    chapter06Modification (chapter06DiagonalClosureToX X Y) ∧
      chapter06Modification (chapter06DiagonalClosureToY X Y) := by
  sorry

theorem chapter06_diagonalClosure_is_integral
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {C : Chapter06SmoothProjectiveCurve R}
    (X Y : Chapter06ProperModel R C) :
    IsIntegral (chapter06DiagonalClosure X Y) := by
  let : IsProper (chapter06ModelProductToBase X Y) :=
    chapter06_model_product_is_proper X Y
  have hcomp :
      chapter06GenericDiagonalMap X Y ≫ chapter06ModelProductToBase X Y =
        C.structureMap ≫ chapter06GenericBaseMap R := by
    simp only [chapter06GenericDiagonalMap, chapter06ModelProductToBase, Category.assoc,
      pullback.lift_snd_assoc, pullback.condition]
    rw [← Y.genericFiber.over]
    simp
  let : QuasiCompact
      (chapter06GenericDiagonalMap X Y ≫ chapter06ModelProductToBase X Y) := by
    rw [hcomp]
    infer_instance
  let : QuasiCompact (chapter06GenericDiagonalMap X Y) := by
    exact QuasiCompact.of_comp (chapter06GenericDiagonalMap X Y)
      (chapter06ModelProductToBase X Y)
  let : IsSchemeTheoreticallyDominant
      (chapter06GenericDiagonalMap X Y).toImage :=
    chapter06_toImage_is_schemeTheoreticallyDominant
      (chapter06GenericDiagonalMap X Y)
  let : IsReduced (chapter06DiagonalClosure X Y) := by
    change IsReduced (chapter06GenericDiagonalMap X Y).image
    exact IsSchemeTheoreticallyDominant.isReduced
      (chapter06GenericDiagonalMap X Y).toImage
  have hirr : IrreducibleSpace (chapter06DiagonalClosure X Y) := by
    change IrreducibleSpace (chapter06GenericDiagonalMap X Y).image
    rw [irreducibleSpace_def]
    convert!
      ((IrreducibleSpace.isIrreducible_univ C.carrier).image _
        (chapter06GenericDiagonalMap X Y).toImage.continuous.continuousOn).closure
    simpa using (chapter06GenericDiagonalMap X Y).toImage.denseRange.closure_range.symm
  exact isIntegral_of_irreducibleSpace_of_isReduced _

instance chapter06DiagonalClosure_isIntegral_instance
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {C : Chapter06SmoothProjectiveCurve R}
    (X Y : Chapter06ProperModel R C) :
    IsIntegral (chapter06DiagonalClosure X Y) :=
  chapter06_diagonalClosure_is_integral X Y

theorem chapter06_diagonalClosure_generic_fiber_is_C
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {C : Chapter06SmoothProjectiveCurve R}
    (X Y : Chapter06ProperModel R C) :
    Nonempty (Chapter06GenericFiberIdentification R C
      (chapter06DiagonalClosureStructureMap X Y)) := by
  sorry

noncomputable def chapter06DiagonalNormalizationScheme
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {C : Chapter06SmoothProjectiveCurve R}
    (X Y : Chapter06ProperModel R C)
    (hZ₀ : IsIntegral (chapter06DiagonalClosure X Y))
    (hqc : QuasiCompact
      (chapter06GenericPointMap (chapter06DiagonalClosure X Y)))
    (hqs : QuasiSeparated
      (chapter06GenericPointMap (chapter06DiagonalClosure X Y))) : Scheme.{u} := by
  letI := hZ₀
  exact chapter06RelativeNormalization hqc hqs

noncomputable def chapter06DiagonalNormalizationMap
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {C : Chapter06SmoothProjectiveCurve R}
    (X Y : Chapter06ProperModel R C)
    (hZ₀ : IsIntegral (chapter06DiagonalClosure X Y))
    (hqc : QuasiCompact
      (chapter06GenericPointMap (chapter06DiagonalClosure X Y)))
    (hqs : QuasiSeparated
      (chapter06GenericPointMap (chapter06DiagonalClosure X Y))) :
    chapter06DiagonalNormalizationScheme X Y hZ₀ hqc hqs ⟶
      chapter06DiagonalClosure X Y := by
  letI := hZ₀
  exact chapter06RelativeNormalizationMap hqc hqs

theorem chapter06_diagonalClosure_normalization_is_finite
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    [Chapter06ExcellentDedekindBase R]
    (C : Chapter06SmoothProjectiveCurve R)
    (X Y : Chapter06ProperModel R C)
    [hZ₀ : IsIntegral (chapter06DiagonalClosure X Y)]
    (hqc : QuasiCompact
      (chapter06GenericPointMap (chapter06DiagonalClosure X Y)))
    (hqs : QuasiSeparated
      (chapter06GenericPointMap (chapter06DiagonalClosure X Y))) :
    IsFinite (chapter06RelativeNormalizationMap hqc hqs) := by
  let : IsClosedImmersion (chapter06DiagonalClosureEmbedding X Y) := by
    change IsClosedImmersion (chapter06GenericDiagonalMap X Y).imageι
    infer_instance
  let : QuasiCompact (chapter06ModelProductToBase X Y) := by
    infer_instance
  let : QuasiCompact (chapter06DiagonalClosureEmbedding X Y) := by
    infer_instance
  have hmap :
      chapter06DiagonalClosureStructureMap X Y =
        chapter06DiagonalClosureEmbedding X Y ≫
          chapter06ModelProductToBase X Y := by
    simp [chapter06DiagonalClosureStructureMap, chapter06DiagonalClosureToX,
      chapter06ModelProductToBase, Category.assoc]
  let : QuasiCompact (chapter06DiagonalClosureStructureMap X Y) := by
    rw [hmap]
    infer_instance
  let : IsProper (chapter06DiagonalClosureStructureMap X Y) :=
    chapter06_diagonalClosure_is_proper X Y
  let : LocallyOfFiniteType (chapter06DiagonalClosureStructureMap X Y) := by
    infer_instance
  exact chapter06_excellent_normalization_is_finite R
    (chapter06DiagonalClosure X Y)
    (chapter06DiagonalClosureStructureMap X Y) inferInstance hqc hqs

structure Chapter06CommonNormalDomination
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    (C : Chapter06SmoothProjectiveCurve R)
    (X Y : Chapter06ProperModel R C) where
  model : Chapter06NormalProperModel R C
  toDiagonal : model.carrier ⟶ chapter06DiagonalClosure X Y
  toDiagonal_over :
    toDiagonal ≫ chapter06DiagonalClosureStructureMap X Y = model.structureMap
  finite : IsFinite toDiagonal
  toX : model.carrier ⟶ X.carrier
  toY : model.carrier ⟶ Y.carrier
  factor_toX : toDiagonal ≫ chapter06DiagonalClosureToX X Y = toX
  factor_toY : toDiagonal ≫ chapter06DiagonalClosureToY X Y = toY
  diagonal_integral : IsIntegral (chapter06DiagonalClosure X Y)
  genericPoint_quasiCompact : QuasiCompact
    (chapter06GenericPointMap (chapter06DiagonalClosure X Y))
  genericPoint_quasiSeparated : QuasiSeparated
    (chapter06GenericPointMap (chapter06DiagonalClosure X Y))
  normalization_carrier_iso : model.carrier ≅
    chapter06DiagonalNormalizationScheme X Y diagonal_integral
      genericPoint_quasiCompact genericPoint_quasiSeparated
  normalization_map_compatibility :
    normalization_carrier_iso.hom ≫
        chapter06DiagonalNormalizationMap X Y diagonal_integral
          genericPoint_quasiCompact genericPoint_quasiSeparated =
      toDiagonal

theorem chapter06_common_normal_domination_exists
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    [Chapter06ExcellentDedekindBase R]
    (C : Chapter06SmoothProjectiveCurve R)
    (X Y : Chapter06ProperModel R C) :
    Nonempty (Chapter06CommonNormalDomination R C X Y) := by
  sorry

theorem chapter06_common_normal_domination_is_proper
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    [Chapter06ExcellentDedekindBase R]
    (C : Chapter06SmoothProjectiveCurve R)
    (X Y : Chapter06ProperModel R C)
    (Z : Chapter06CommonNormalDomination R C X Y) :
    IsProper Z.model.structureMap :=
  Z.model.proper

theorem chapter06_common_normal_domination_dominates_both
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    [Chapter06ExcellentDedekindBase R]
    (C : Chapter06SmoothProjectiveCurve R)
    (X Y : Chapter06ProperModel R C)
    (Z : Chapter06CommonNormalDomination R C X Y) :
    Z.toDiagonal ≫ chapter06DiagonalClosureToX X Y = Z.toX ∧
      Z.toDiagonal ≫ chapter06DiagonalClosureToY X Y = Z.toY :=
  ⟨Z.factor_toX, Z.factor_toY⟩

theorem chapter06_common_normal_domination_toX_over
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    [Chapter06ExcellentDedekindBase R]
    (C : Chapter06SmoothProjectiveCurve R)
    (X Y : Chapter06ProperModel R C)
    (Z : Chapter06CommonNormalDomination R C X Y) :
    Z.toX ≫ X.structureMap = Z.model.structureMap := by
  rw [← Z.factor_toX, Category.assoc, Z.toDiagonal_over]

theorem chapter06_common_normal_domination_toY_over
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    [Chapter06ExcellentDedekindBase R]
    (C : Chapter06SmoothProjectiveCurve R)
    (X Y : Chapter06ProperModel R C)
    (Z : Chapter06CommonNormalDomination R C X Y) :
    Z.toY ≫ Y.structureMap = Z.model.structureMap := by
  rw [← Z.factor_toY, Category.assoc,
    chapter06_diagonalClosure_toY_over X Y, Z.toDiagonal_over]

theorem chapter06_common_normal_domination_projections_are_modifications
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    [Chapter06ExcellentDedekindBase R]
    (C : Chapter06SmoothProjectiveCurve R)
    (X Y : Chapter06ProperModel R C)
    (Z : Chapter06CommonNormalDomination R C X Y) :
    chapter06Modification Z.toX ∧ chapter06Modification Z.toY := by
  sorry

theorem chapter06_proposition_6_3
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    [Chapter06ExcellentDedekindBase R]
    (C : Chapter06SmoothProjectiveCurve R)
    (X Y : Chapter06ProperModel R C) :
    IsProper (chapter06DiagonalClosureStructureMap X Y) ∧
      chapter06Modification (chapter06DiagonalClosureToX X Y) ∧
      chapter06Modification (chapter06DiagonalClosureToY X Y) ∧
      Nonempty (Chapter06CommonNormalDomination R C X Y) := by
  refine ⟨chapter06_diagonalClosure_is_proper X Y, ?_, ?_, ?_⟩
  · exact (chapter06_diagonalClosure_projections_are_modifications X Y).1
  · exact (chapter06_diagonalClosure_projections_are_modifications X Y).2
  · exact chapter06_common_normal_domination_exists R C X Y

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter06
