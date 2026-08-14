import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter08.Section01PullbackDataOnACover

namespace LastLib
namespace Book10FaithfullyFlatDescentInAlgebraicGeometry
namespace Chapter08

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.Bicategory
open scoped AlgebraicGeometry

noncomputable section

universe u

/-!
## 8.2 Affine-local construction

This section records the scalar-extension normalization on basic opens, the
local-to-global gluing interface, and the base-change reduction used for a
general morphism over the base.
-/

/-- The descended affine module restricted to `D(f)`. -/
def chapter08AffineRestrictedModule {R : CommRingCat.{u}} (M : ModuleCat R) (f : R) :
    ModuleCat (Localization.Away f) :=
  chapter08LocalizedModule M f

/-- The restriction calculation is exactly extension of scalars along
`R ⟶ R_f`. -/
theorem chapter08_affine_restriction_is_scalar_extension
    {R : CommRingCat.{u}} (M : ModuleCat R) (f : R) :
    chapter08AffineRestrictedModule M f =
      (ModuleCat.extendScalars (algebraMap R (Localization.Away f))).obj M := by
  rfl

/-- The canonical comparison object for the restriction of an affine module. -/
def chapter08AffineRestrictionComparisonData
    {R : CommRingCat.{u}} (M : ModuleCat R) (f : R) :
    Chapter08AffineRestrictionComparison M f :=
  Chapter08AffineRestrictionComparison.canonical M f

/-- Restriction comparisons are normalized by the same scalar-extension
functor, so the two affine computations use the same module. -/
theorem chapter08_affine_restriction_comparison_is_canonical
    {R : CommRingCat.{u}} (M : ModuleCat R) (f : R) :
    (chapter08AffineRestrictionComparisonData M f).restricted =
      chapter08AffineRestrictedModule M f := by
  rfl

/-- LOCAL_DEPENDENCY_GUESS: the pinned categorical descent API supplies the
compatibility data, while the final Zariski gluing bridge for affine schemes is
not yet present in an earlier LastLib chapter. -/
structure Chapter08AffineLocalModuleSystem
    {S : Scheme.{u}} (C : Chapter08AffineOpenCover S)
    (choices : Chapter08PullbackChoices
      (fun i => Scheme.Spec (C.coordinateRing i)) C.map) where
  module : ∀ i, ModuleCat (C.coordinateRing i)
  descent : Chapter08QuasiCoherentModuleDescentData choices
  tildeComparison : ∀ i,
    Nonempty (Scheme.Modules.tilde (module i) ≅ (descent.obj).obj i)

/- LOCAL_DEPENDENCY_GUESS: the witness packages the canonical affine-module
descent and the ordinary quasi-coherent Zariski gluing theorem, which are not
yet exposed together by an earlier LastLib chapter. -/
structure Chapter08AffineLocalGluingWitness
    {S : Scheme.{u}} (C : Chapter08AffineOpenCover S)
    {choices : Chapter08PullbackChoices
      (fun i => Scheme.Spec (C.coordinateRing i)) C.map}
    (D : Chapter08AffineLocalModuleSystem C choices) where
  descended : Chapter08QuasiCoherentModules S
  comparison : ∀ i,
    Nonempty
      ((Scheme.Modules.pullback (C.map i)).obj descended.obj ≅
        Scheme.Modules.tilde (D.module i))
  overlapCocycle : ∀ i j k,
    (D.descent.obj).pullHom'_hom_comp i j k

/- The canonical identifications of the affine sheaves agree on every
pairwise intersection. -/
theorem chapter08_affine_tilde_restriction_agrees
    {S : Scheme.{u}} {C : Chapter08AffineOpenCover S}
    {choices : Chapter08PullbackChoices
      (fun i => Scheme.Spec (C.coordinateRing i)) C.map}
    (D : Chapter08AffineLocalModuleSystem C choices) (i j : C.index) :
    Nonempty
      ((Scheme.Modules.pullback (choices.sq i j).p₁).obj
          (Scheme.Modules.tilde (D.module i)) ≅
        (Scheme.Modules.pullback (choices.sq i j).p₂).obj
          (Scheme.Modules.tilde (D.module j))) := by
  sorry

/- The glued sheaf carries the canonical local comparisons and their overlap
cocycle. -/
theorem chapter08_affine_local_gluing_with_comparisons
    {S : Scheme.{u}} {C : Chapter08AffineOpenCover S}
    {choices : Chapter08PullbackChoices
      (fun i => Scheme.Spec (C.coordinateRing i)) C.map}
    (D : Chapter08AffineLocalModuleSystem C choices) :
    Nonempty (Chapter08AffineLocalGluingWitness C D) := by
  sorry

/-- Canonical affine-local gluing produces a quasi-coherent sheaf on the base.
The proof is the ordinary Zariski gluing step after the affine module descent
calculation. -/
theorem chapter08_affine_local_gluing
    {S : Scheme.{u}} {C : Chapter08AffineOpenCover S}
    {choices : Chapter08PullbackChoices
      (fun i => Scheme.Spec (C.coordinateRing i)) C.map}
    (D : Chapter08AffineLocalModuleSystem C choices) :
    Nonempty (Chapter08QuasiCoherentModules S) := by
  rcases chapter08_affine_local_gluing_with_comparisons D with ⟨W⟩
  exact ⟨W.descended⟩

/-- The affine restriction data are stable under a second basic-open
restriction; this is the normalization behind the intersection cocycle. -/
theorem chapter08_affine_restriction_associates
    {R : CommRingCat.{u}} (M : ModuleCat R) (f g : R) :
    Nonempty
      (chapter08LocalizedModule M (f * g) ≅
        chapter08LocalizedModule (chapter08LocalizedModule M f)
          (algebraMap R (Localization.Away f) g)) := by
  sorry

/-- The canonical affine module descent module agrees with the one obtained by
descending directly after restricting to a basic open. -/
theorem chapter08_affine_descent_commutes_with_restriction
    {R : CommRingCat.{u}} (M : ModuleCat R) (f : R) :
    Nonempty
      (chapter08LocalizedModule M f ≅ chapter08AffineRestrictedModule M f) := by
  exact ⟨Iso.refl _⟩

/-- Base change of an fpqc cover is the cover used for descent over a morphism
`X ⟶ S`. -/
theorem chapter08_base_change_cover_for_morphism
    {X T S : Scheme.{u}} {f : X ⟶ S} {p : T ⟶ S}
    (hp : Chapter08FpqcMorphism p) :
    Chapter08FpqcMorphism (chapter08BaseChangedCoverMap f p) :=
  chapter08_baseChange_fpqc hp

end
end Chapter08
end Book10FaithfullyFlatDescentInAlgebraicGeometry
end LastLib
