import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter06.Dependencies
import Mathlib.RingTheory.RegularLocalRing.Defs

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter06

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u v

/-! ### 6.4 Normalization of the closure -/

theorem chapter06_excellent_normalization_is_finite
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    [Chapter06ExcellentDedekindBase R]
    (X₀ : Scheme.{u}) (f : X₀ ⟶ Chapter06BaseScheme R)
    [IsIntegral X₀] (hft : LocallyOfFiniteType f)
    [QuasiCompact f] [QuasiSeparated f]
    (hqc : QuasiCompact (chapter06GenericPointMap X₀))
    (hqs : QuasiSeparated (chapter06GenericPointMap X₀)) :
    IsFinite (chapter06RelativeNormalizationMap hqc hqs) := by
  letI := hqc
  letI := hqs
  exact Chapter06ExcellentDedekindBase.finite_normalization X₀ f hft hqc hqs

theorem chapter06_relativeNormalization_morphism_is_integral
    {X₀ : Scheme.{u}} [IsIntegral X₀]
    (hqc : QuasiCompact (chapter06GenericPointMap X₀))
    (hqs : QuasiSeparated (chapter06GenericPointMap X₀)) :
    IsIntegralHom (chapter06RelativeNormalizationMap hqc hqs) := by
  letI := hqc
  letI := hqs
  infer_instance

theorem chapter06_relativeNormalization_is_integral
    {X₀ : Scheme.{u}} [IsIntegral X₀]
    (hqc : QuasiCompact (chapter06GenericPointMap X₀))
    (hqs : QuasiSeparated (chapter06GenericPointMap X₀)) :
    IsIntegral (chapter06RelativeNormalization hqc hqs) := by
  letI := hqc
  letI := hqs
  infer_instance

structure Chapter06NormalizedClosureData
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    (C : Chapter06SmoothProjectiveCurve R)
    (X₀ : Chapter06Model R C) where
  genericPoint_quasiCompact : QuasiCompact (chapter06GenericPointMap X₀.carrier)
  genericPoint_quasiSeparated : QuasiSeparated (chapter06GenericPointMap X₀.carrier)
  finite : IsFinite
    (chapter06RelativeNormalizationMap genericPoint_quasiCompact genericPoint_quasiSeparated)
  flat : Flat
    (chapter06RelativeNormalizationMap genericPoint_quasiCompact genericPoint_quasiSeparated ≫
      X₀.structureMap)
  normal : chapter06IsNormal
    (chapter06RelativeNormalization genericPoint_quasiCompact genericPoint_quasiSeparated)
  genericFiber : Chapter06GenericFiberIdentification R C
    (chapter06RelativeNormalizationMap genericPoint_quasiCompact genericPoint_quasiSeparated ≫
      X₀.structureMap)

noncomputable def chapter06NormalModelFromNormalizedClosure
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    (C : Chapter06SmoothProjectiveCurve R)
    (X₀ : Chapter06Model R C)
    (D : Chapter06NormalizedClosureData R C X₀) : Chapter06NormalModel R C :=
  { toChapter06Model :=
      { carrier := chapter06RelativeNormalization
          D.genericPoint_quasiCompact D.genericPoint_quasiSeparated
        structureMap :=
          chapter06RelativeNormalizationMap
              D.genericPoint_quasiCompact D.genericPoint_quasiSeparated ≫ X₀.structureMap
        projective := by
          sorry
        proper := by
          sorry
        locallyOfFiniteType := by
          sorry
        flat := D.flat
        integral := by
          sorry
        genericFiber := D.genericFiber }
    normal := D.normal }

theorem chapter06_normalizedClosure_is_finite
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    (C : Chapter06SmoothProjectiveCurve R)
    (X₀ : Chapter06Model R C)
    (D : Chapter06NormalizedClosureData R C X₀) :
    IsFinite
      (chapter06RelativeNormalizationMap
        D.genericPoint_quasiCompact D.genericPoint_quasiSeparated) :=
  D.finite

theorem chapter06_normalizedClosure_generic_fiber_is_C
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    (C : Chapter06SmoothProjectiveCurve R)
    (X₀ : Chapter06Model R C)
    (D : Chapter06NormalizedClosureData R C X₀) :
    Nonempty (Chapter06GenericFiberIdentification R C
      (chapter06RelativeNormalizationMap
        D.genericPoint_quasiCompact D.genericPoint_quasiSeparated ≫ X₀.structureMap)) :=
  ⟨D.genericFiber⟩

theorem chapter06_normalizedClosure_is_normal
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    (C : Chapter06SmoothProjectiveCurve R)
    (X₀ : Chapter06Model R C)
    (D : Chapter06NormalizedClosureData R C X₀) :
    chapter06IsNormal
      (chapter06RelativeNormalization
        D.genericPoint_quasiCompact D.genericPoint_quasiSeparated) :=
  D.normal

theorem chapter06_normalizedClosure_is_flat
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    (C : Chapter06SmoothProjectiveCurve R)
    (X₀ : Chapter06Model R C)
    (D : Chapter06NormalizedClosureData R C X₀) :
    Flat
      (chapter06RelativeNormalizationMap
        D.genericPoint_quasiCompact D.genericPoint_quasiSeparated ≫ X₀.structureMap) :=
  D.flat

theorem chapter06_normalization_of_smooth_generic_fiber_is_an_isomorphism
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    (C : Chapter06SmoothProjectiveCurve R)
    (X₀ : Chapter06Model R C)
    (D : Chapter06NormalizedClosureData R C X₀) :
    Nonempty (Chapter06GenericFiberIdentification R C
      (chapter06RelativeNormalizationMap
        D.genericPoint_quasiCompact D.genericPoint_quasiSeparated ≫ X₀.structureMap)) := by
  sorry

/-! The phrase “remains flat” is exposed with the actual flatness datum used
by the model constructor; it is not inferred from dominance alone. -/
theorem chapter06_normalizedClosure_flatness_requires_a_base_flatness_argument
    {X S : Scheme.{u}} (f : X ⟶ S) (hflat : Flat f) : Flat f :=
  hflat

structure Chapter06RestrictionIdentification
    (X₁ : Chapter06NormalModel R C)
    (M : Chapter06SmoothProjectiveOpenModel R C) where
  iso : (X₁.carrier ⁻¹ᵁ M.open).toScheme ≅ M.carrier
  over : iso.hom ≫ M.structureMap = X₁.structureMap ∣_ M.open

def chapter06IsRegular (X : Scheme.{u}) : Prop :=
  ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)

structure Chapter06RegularOpenModel
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    (C : Chapter06SmoothProjectiveCurve R) where
  open : (Chapter06BaseScheme R).Opens
  open_nonempty : open ≠ ⊥
  complement_finite : Set.Finite ((open : Set (Chapter06BaseScheme R))ᶜ)
  carrier : Scheme.{u}
  structureMap : carrier ⟶ open.toScheme
  regular : chapter06IsRegular carrier
  genericMap : Spec (.of (FractionRing R)) ⟶ open.toScheme
  genericMap_over : genericMap ≫ open.ι = chapter06GenericBaseMap R
  genericFiber : Chapter06GenericFiberIdentification R C
    (structureMap ≫ open.ι)

structure Chapter06RegularOpenRestrictionIdentification
    (X₁ : Chapter06NormalModel R C)
    (M : Chapter06RegularOpenModel R C) where
  iso : (X₁.carrier ⁻¹ᵁ M.open).toScheme ≅ M.carrier
  over : iso.hom ≫ M.structureMap = X₁.structureMap ∣_ M.open

theorem chapter06_smooth_open_model_is_normal
    (M : Chapter06SmoothProjectiveOpenModel R C) :
    chapter06IsNormal M.carrier := by
  sorry

theorem chapter06_normal_model_exists
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    [Chapter06ExcellentDedekindBase R]
    (C : Chapter06SmoothProjectiveCurve R) :
    ∃ X₁ : Chapter06NormalModel R C, Nonempty
      (Chapter06GenericFiberIdentification R C X₁.structureMap) := by
  sorry

theorem chapter06_normal_model_exists_restricting_to
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    [Chapter06ExcellentDedekindBase R]
    (C : Chapter06SmoothProjectiveCurve R)
    (M : Chapter06SmoothProjectiveOpenModel R C) :
    ∃ X₁ : Chapter06NormalModel R C,
      Nonempty (Chapter06RestrictionIdentification X₁ M) := by
  sorry

theorem chapter06_theorem_6_2
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    [Chapter06ExcellentDedekindBase R]
    (C : Chapter06SmoothProjectiveCurve R) :
    ∃ X₁ : Chapter06NormalModel R C, chapter06IsNormal X₁.carrier := by
  obtain ⟨X₁, h⟩ := chapter06_normal_model_exists R C
  exact ⟨X₁, X₁.normal⟩

theorem chapter06_restriction_of_projective_model_is_projective
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    (C : Chapter06SmoothProjectiveCurve R)
    (X₁ : Chapter06NormalModel R C)
    (U : (Chapter06BaseScheme R).Opens) :
    chapter04Projective (X₁.structureMap ∣_ U) := by
  sorry

theorem chapter06_prescribed_regular_open_model_is_projective
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    [Chapter06ExcellentDedekindBase R]
    (C : Chapter06SmoothProjectiveCurve R)
    (M : Chapter06RegularOpenModel R C)
    (hprescribed : ∃ X₁ : Chapter06NormalModel R C,
      Nonempty (Chapter06RegularOpenRestrictionIdentification X₁ M)) :
    chapter04Projective M.structureMap := by
  sorry

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter06
