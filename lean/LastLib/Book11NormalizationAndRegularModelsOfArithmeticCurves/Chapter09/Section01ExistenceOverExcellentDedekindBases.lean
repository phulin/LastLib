import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter09.Dependencies

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter09

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter03
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter03
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter08
open scoped AlgebraicGeometry

universe u v

/-! ## 9.1. Existence over excellent Dedekind bases -/

theorem chapter09_regular_model_theorem
    {S : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter09ExcellentDedekindBase S K)
    (C : Chapter09SmoothProjectiveCurve K) :
    Nonempty (Chapter09RegularProjectiveModel B C) := by
  sorry

theorem chapter09_theorem_9_1
    {S : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter09ExcellentDedekindBase S K)
    (C : Chapter09SmoothProjectiveCurve K) :
    Nonempty (Chapter09RegularProjectiveModel B C) ∧
      (∀ U : S.Opens, ∀ M : Chapter09RegularProjectiveOpenModel B C U,
        ∃ X : Chapter09RegularProjectiveModel B C,
          Nonempty (Chapter09ModelRestrictionIdentification X U M)) := by
  sorry

theorem chapter09_projective_closure_exists
    {S : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter09ExcellentDedekindBase S K)
    (C : Chapter09SmoothProjectiveCurve K) :
    Nonempty (Chapter01ProjectiveClosureData B.toChapter01DedekindBase C.structureMap) := by
  sorry

theorem chapter09_regular_model_theorem_has_arithmetic_surface_structure
    {S : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter09ExcellentDedekindBase S K)
    (C : Chapter09SmoothProjectiveCurve K)
    (X : Chapter09RegularProjectiveModel B C) :
    Chapter01ArithmeticSurface X.structureMap := by
  sorry

theorem chapter09_regular_model_is_regular_surface
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter09ExcellentDedekindBase S K}
    {C : Chapter09SmoothProjectiveCurve K}
    (X : Chapter09RegularProjectiveModel B C) :
    Chapter09RegularSurface X.carrier := by
  sorry

/- The resolution input is exposed in the same form as the preceding chapter's theorem, so a
   normalized closure can be passed to resolution without changing its good open. -/
theorem chapter09_resolution_of_normalized_surface
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hS : IsNoetherian S)
    (hf : chapter03QuasiProjective f)
    (hX : Chapter08ExcellentSurfaceInput X)
    (U : X.Opens)
    (hU : ∀ x : X, x ∈ U → IsRegularLocalRing (X.presheaf.stalk x)) :
    Nonempty (Chapter08ProjectiveResolutionData X U) :=
  chapter08_resolution_projective_over_noetherian_base f hS hf hX U hU

/-! A proper smooth curve over a field is already projective; the projective hypothesis in the
    main theorem is therefore a harmless choice of the standard model interface. -/

theorem chapter09_smooth_proper_curve_is_projective
    {K : Type u} [Field K]
    (C : Chapter09SmoothProperCurveOverField K) :
    Chapter01ProjectiveMorphism C.structureMap := by
  sorry

noncomputable def chapter09_projective_curve_of_smooth_proper
    {K : Type u} [Field K] (C : Chapter09SmoothProperCurveOverField K) :
    Chapter09SmoothProjectiveCurve K :=
  { toChapter09SmoothProperCurveOverField := C
    projective := chapter09_smooth_proper_curve_is_projective C }

theorem chapter09_projective_curve_of_smooth_proper_carrier
    {K : Type u} [Field K] (C : Chapter09SmoothProperCurveOverField K) :
    (chapter09_projective_curve_of_smooth_proper C).carrier = C.carrier :=
  rfl

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter09
