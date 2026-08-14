import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter08.Dependencies

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter08

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter03
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07
open scoped AlgebraicGeometry

universe u v

/-! ## 8.1. The resolution theorem in the required setting -/

theorem chapter08_resolutionModification_is_projective
    {Y X : Scheme.{u}} {f : Y ⟶ X}
    (h : Chapter08ResolutionModification f) :
    Chapter07IsProjectiveMorphism f := by
  sorry

theorem chapter08_resolutionModification_is_proper
    {Y X : Scheme.{u}} {f : Y ⟶ X}
    (h : Chapter08ResolutionModification f) :
    IsProper f := by
  sorry

theorem chapter08_resolutionModification_is_birational
    {Y X : Scheme.{u}} {f : Y ⟶ X}
    (h : Chapter08ResolutionModification f) :
    Chapter07Birational f := by
  sorry

/- The absolute statement is obtained by taking the prescribed regular open to be empty.  The
   result still records properness, birationality, regularity, and the finite blowup/normalization
   chain separately so later chapters can consume whichever interface they need. -/
theorem chapter08_resolution_of_excellent_noetherian_surface
    (X : Scheme.{u}) (hX : Chapter08ExcellentSurfaceInput X) :
    Nonempty (Chapter08ResolutionData X (⊥ : X.Opens)) := by
  sorry

theorem chapter08_resolution_relative_to_regular_open
    (X : Scheme.{u}) (hX : Chapter08ExcellentSurfaceInput X)
    (U : X.Opens)
    (hU : ∀ x : X, x ∈ U → IsRegularLocalRing (X.presheaf.stalk x)) :
    Nonempty (Chapter08ResolutionData X U) := by
  sorry

theorem chapter08_resolution_projective_over_noetherian_base
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hS : IsNoetherian S)
    (hf : chapter03QuasiProjective f)
    (hX : Chapter08ExcellentSurfaceInput X)
    (U : X.Opens)
    (hU : ∀ x : X, x ∈ U → IsRegularLocalRing (X.presheaf.stalk x)) :
    Nonempty (Chapter08ProjectiveResolutionData X U) := by
  sorry

theorem chapter08_resolution_exists_projective_absolute
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hS : IsNoetherian S)
    (hf : chapter03QuasiProjective f)
    (hX : Chapter08ExcellentSurfaceInput X) :
    Nonempty (Chapter08ProjectiveResolutionData X (⊥ : X.Opens)) := by
  sorry

/-! The arithmetic-surface bookkeeping used immediately after Theorem 8.1. -/

theorem chapter08_normal_arithmetic_surface_singular_locus_locally_finite_closed
    (M : Chapter08NormalArithmeticSurface) :
    Chapter08LocallyFiniteSet (chapter08ArithmeticSurfaceSingularLocus M) ∧
      Chapter08ClosedPointSet (chapter08ArithmeticSurfaceSingularLocus M) := by
  sorry

theorem chapter08_normal_arithmetic_surface_singular_locus_finite
    (M : Chapter08NormalArithmeticSurface)
    (hqc : IsCompact (Set.univ : Set M.surface.model)) :
    (chapter08ArithmeticSurfaceSingularLocus M).Finite := by
  sorry

def Chapter08FiniteClosedPointPreparation (M : Chapter08NormalArithmeticSurface) : Prop :=
  (chapter08ArithmeticSurfaceSingularLocus M).Finite ∧
    Chapter08ClosedPointSet (chapter08ArithmeticSurfaceSingularLocus M)

theorem chapter08_arithmetic_surface_centers_can_be_taken_successively_above_singular_points
    (M : Chapter08NormalArithmeticSurface)
    (hqc : IsCompact (Set.univ : Set M.surface.model)) :
    Nonempty (Chapter08ResolutionData M.surface.model (⊥ : M.surface.model.Opens)) ∧
      Chapter08FiniteClosedPointPreparation M := by
  sorry

/- The theorem is intentionally parameterized by a surface dimension bound and an excellence
   profile.  No declaration here asserts resolution in higher dimension or for nonexcellent
   schemes; those cases are outside this API. -/

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter08
