import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter06.Section04NormalizationOfTheClosure

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter06

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u v

/-! ### 6.5 Existence and uniqueness up to modification -/

abbrev chapter06ModelProduct
    (X Y : Chapter06Model R C) : Scheme.{u} :=
  pullback X.structureMap Y.structureMap

abbrev chapter06ModelProductToX
    (X Y : Chapter06Model R C) : chapter06ModelProduct X Y ⟶ X.carrier :=
  pullback.fst X.structureMap Y.structureMap

abbrev chapter06ModelProductToY
    (X Y : Chapter06Model R C) : chapter06ModelProduct X Y ⟶ Y.carrier :=
  pullback.snd X.structureMap Y.structureMap

abbrev chapter06ModelProductToBase
    (X Y : Chapter06Model R C) : chapter06ModelProduct X Y ⟶ Chapter06BaseScheme R :=
  chapter06ModelProductToX X Y ≫ X.structureMap

noncomputable def chapter06GenericDiagonalMap
    (X Y : Chapter06Model R C) :
    C.carrier ⟶ chapter06ModelProduct X Y :=
  pullback.lift
    (X.genericFiber.iso.inv ≫
      pullback.fst X.structureMap (chapter06GenericBaseMap R))
    (Y.genericFiber.iso.inv ≫
      pullback.fst Y.structureMap (chapter06GenericBaseMap R)) (by
      sorry)

noncomputable def chapter06DiagonalClosure
    (X Y : Chapter06Model R C) : Scheme.{u} :=
  (chapter06GenericDiagonalMap X Y).image

abbrev chapter06DiagonalClosureEmbedding
    (X Y : Chapter06Model R C) :
    chapter06DiagonalClosure X Y ⟶ chapter06ModelProduct X Y :=
  (chapter06GenericDiagonalMap X Y).imageι

noncomputable def chapter06DiagonalClosureToProduct
    (X Y : Chapter06Model R C) :
    C.carrier ⟶ chapter06DiagonalClosure X Y :=
  (chapter06GenericDiagonalMap X Y).toImage

abbrev chapter06DiagonalClosureToX
    (X Y : Chapter06Model R C) :
    chapter06DiagonalClosure X Y ⟶ X.carrier :=
  chapter06DiagonalClosureEmbedding X Y ≫ chapter06ModelProductToX X Y

abbrev chapter06DiagonalClosureToY
    (X Y : Chapter06Model R C) :
    chapter06DiagonalClosure X Y ⟶ Y.carrier :=
  chapter06DiagonalClosureEmbedding X Y ≫ chapter06ModelProductToY X Y

abbrev chapter06DiagonalClosureStructureMap
    (X Y : Chapter06Model R C) :
    chapter06DiagonalClosure X Y ⟶ Chapter06BaseScheme R :=
  chapter06DiagonalClosureToX X Y ≫ X.structureMap

theorem chapter06_diagonalClosure_factorization
    (X Y : Chapter06Model R C) :
    chapter06DiagonalClosureToProduct X Y ≫
        chapter06DiagonalClosureEmbedding X Y =
      chapter06GenericDiagonalMap X Y := by
  exact (chapter06GenericDiagonalMap X Y).toImage_imageι

theorem chapter06_model_product_is_proper
    (X Y : Chapter06Model R C) :
    IsProper (chapter06ModelProductToBase X Y) := by
  sorry

theorem chapter06_diagonalClosure_is_proper
    (X Y : Chapter06Model R C) :
    IsProper (chapter06DiagonalClosureStructureMap X Y) := by
  sorry

theorem chapter06_diagonalClosure_projections_are_modifications
    (X Y : Chapter06Model R C) :
    chapter06Modification (chapter06DiagonalClosureToX X Y) ∧
      chapter06Modification (chapter06DiagonalClosureToY X Y) := by
  sorry

theorem chapter06_diagonalClosure_is_integral
    (X Y : Chapter06Model R C) :
    IsIntegral (chapter06DiagonalClosure X Y) := by
  sorry

instance chapter06DiagonalClosure_isIntegral_instance
    (X Y : Chapter06Model R C) :
    IsIntegral (chapter06DiagonalClosure X Y) :=
  chapter06_diagonalClosure_is_integral X Y

theorem chapter06_diagonalClosure_generic_fiber_is_C
    (X Y : Chapter06Model R C) :
    Nonempty (Chapter06GenericFiberIdentification R C
      (chapter06DiagonalClosureStructureMap X Y)) := by
  sorry

noncomputable def chapter06DiagonalNormalizationScheme
    (X Y : Chapter06Model R C)
    (hZ₀ : IsIntegral (chapter06DiagonalClosure X Y))
    (hqc : QuasiCompact
      (chapter06GenericPointMap (chapter06DiagonalClosure X Y)))
    (hqs : QuasiSeparated
      (chapter06GenericPointMap (chapter06DiagonalClosure X Y))) : Scheme.{u} := by
  letI := hZ₀
  exact chapter06RelativeNormalization hqc hqs

noncomputable def chapter06DiagonalNormalizationMap
    (X Y : Chapter06Model R C)
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
    (X Y : Chapter06Model R C)
    [hZ₀ : IsIntegral (chapter06DiagonalClosure X Y)]
    (hqc : QuasiCompact
      (chapter06GenericPointMap (chapter06DiagonalClosure X Y)))
    (hqs : QuasiSeparated
      (chapter06GenericPointMap (chapter06DiagonalClosure X Y))) :
    IsFinite (chapter06RelativeNormalizationMap hqc hqs) := by
  letI : QuasiCompact (chapter06DiagonalClosureStructureMap X Y) := by
    sorry
  letI : QuasiSeparated (chapter06DiagonalClosureStructureMap X Y) := by
    sorry
  exact chapter06_excellent_normalization_is_finite R
    (chapter06DiagonalClosure X Y) (chapter06DiagonalClosureStructureMap X Y)
    (by sorry) hqc hqs

structure Chapter06CommonNormalDomination
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    (C : Chapter06SmoothProjectiveCurve R)
    (X Y : Chapter06Model R C) where
  model : Chapter06NormalModel R C
  toDiagonal : model.carrier ⟶ chapter06DiagonalClosure X Y
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
    (X Y : Chapter06Model R C) :
    Nonempty (Chapter06CommonNormalDomination R C X Y) := by
  sorry

theorem chapter06_common_normal_domination_is_proper
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    [Chapter06ExcellentDedekindBase R]
    (C : Chapter06SmoothProjectiveCurve R)
    (X Y : Chapter06Model R C)
    (Z : Chapter06CommonNormalDomination R C X Y) :
    IsProper Z.model.structureMap :=
  Z.model.proper

theorem chapter06_common_normal_domination_dominates_both
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    [Chapter06ExcellentDedekindBase R]
    (C : Chapter06SmoothProjectiveCurve R)
    (X Y : Chapter06Model R C)
    (Z : Chapter06CommonNormalDomination R C X Y) :
    Z.toDiagonal ≫ chapter06DiagonalClosureToX X Y = Z.toX ∧
      Z.toDiagonal ≫ chapter06DiagonalClosureToY X Y = Z.toY :=
  ⟨Z.factor_toX, Z.factor_toY⟩

theorem chapter06_proposition_6_3
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    [Chapter06ExcellentDedekindBase R]
    (C : Chapter06SmoothProjectiveCurve R)
    (X Y : Chapter06Model R C) :
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
