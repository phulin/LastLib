import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Dependencies
import Mathlib.CategoryTheory.Limits.Shapes.Products

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/-! ## 4.1. The evaluation map and global generation -/

/-- Relative global generation is surjectivity of the adjunction evaluation map. -/
def chapter04GeneratedByRelativeGlobalSections
    {X S : Scheme.{u}} (f : X ⟶ S) (L : Chapter04LineBundle X) : Prop :=
  chapter04SheafSurjective (chapter04EvaluationMap f L.sheaf)

theorem chapter04_generated_iff_evaluation_is_sheaf_surjective
    {X S : Scheme.{u}} (f : X ⟶ S) (L : Chapter04LineBundle X) :
    chapter04GeneratedByRelativeGlobalSections f L ↔
      chapter04SheafSurjective (chapter04EvaluationMap f L.sheaf) :=
  Iff.rfl

theorem chapter04_generated_iff_evaluation_is_stalkwise_surjective
    {X S : Scheme.{u}} (f : X ⟶ S) (L : Chapter04LineBundle X) :
    chapter04GeneratedByRelativeGlobalSections f L ↔
      ∀ x : X, Function.Surjective
        ((TopCat.Presheaf.stalkFunctor Ab x).map
          (chapter04EvaluationMap f L.sheaf).mapPresheaf) := by
  exact chapter04SheafSurjective_iff_stalkwise (chapter04EvaluationMap f L.sheaf)

/- The twist and its generation predicate are defined in `Dependencies`
because the Serre interfaces reuse them. -/

theorem chapter04_twisted_generation_iff_evaluation_is_sheaf_surjective
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    (L : Chapter04LineBundle X) (n : ℕ) :
    chapter04TwistGeneratedByRelativeGlobalSections f F L n ↔
      chapter04SheafSurjective (chapter04EvaluationMap f (chapter04TwistedModule F L n)) :=
  Iff.rfl

theorem chapter04_finite_relative_generators_of_quasiCompact
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
    (L : Chapter04LineBundle X)
    (hL : chapter04GeneratedByRelativeGlobalSections f L) :
    chapter04LocallyFiniteRelativeGeneration f L := by
  sorry

/-! The standard projective line is the rank-two canonical projective space
from Chapter 2.  The following assertions expose the examples from the
source without replacing their target schemes by arbitrary data. -/

noncomputable def chapter04ProjectiveLineConstantSection
    (K : Type u) [Field K] :
    (chapter04ProjectiveLineTrivialLineBundle K).sheaf.sections :=
  SheafOfModules.unitHomEquiv (chapter04ProjectiveLineTrivialLineBundle K).sheaf (𝟙 _)

theorem chapter04_projective_line_trivial_constant_section_generates
    (K : Type u) [Field K] :
    Epi (((chapter04ProjectiveLineTrivialLineBundle K).sheaf.freeHomEquiv
      (I := ULift.{u} (Fin 1))).symm
      (fun _ : ULift.{u} (Fin 1) => chapter04ProjectiveLineConstantSection K)) := by
  let X := chapter04ProjectiveLine K
  let I := ULift.{u} (Fin 1)
  change Epi (((SheafOfModules.unit X.ringCatSheaf).freeHomEquiv
    (I := I)).symm
      (fun _ : I => (SheafOfModules.unitHomEquiv
        (SheafOfModules.unit X.ringCatSheaf)) (𝟙 _)))
  let e : SheafOfModules.free (R := X.ringCatSheaf) I ≅
      SheafOfModules.unit X.ringCatSheaf := by
    exact Limits.coproductUniqueIso (fun _ : I ↦ SheafOfModules.unit X.ringCatSheaf)
  have he : Epi e.hom := @IsIso.epi_of_iso _ _ _ _ e.hom e.isIso_hom
  have hEq :
      ((SheafOfModules.unit X.ringCatSheaf).freeHomEquiv
        (I := I)).symm
          (fun _ : I => (SheafOfModules.unitHomEquiv
            (SheafOfModules.unit X.ringCatSheaf)) (𝟙 _)) = e.hom := by
    apply (SheafOfModules.unit X.ringCatSheaf).freeHomEquiv.injective
    funext i
    simp only [Equiv.apply_symm_apply]
    change (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv (𝟙 _) =
      (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv
        (SheafOfModules.ιFree i ≫ e.hom)
    congr 1
    exact (Limits.ι_coproductUniqueIso_hom
      (fun _ : I => SheafOfModules.unit X.ringCatSheaf) i).symm
  rw [hEq]
  exact he

theorem chapter04_projective_line_trivial_is_generated
    (K : Type u) [Field K] :
    chapter04GeneratedByRelativeGlobalSections
      (chapter04ProjectiveLineStructureMap K)
      (chapter04ProjectiveLineTrivialLineBundle K) := by
  sorry

theorem chapter04_projective_line_example_exists
    (K : Type u) [Field K] :
    Nonempty (Chapter04ProjectiveLineExample K) := by
  sorry

noncomputable def chapter04ProjectiveLineExample
    (K : Type u) [Field K] : Chapter04ProjectiveLineExample K :=
  Classical.choice (chapter04_projective_line_example_exists K)

theorem chapter04_projective_line_constant_map_is_over
    (K : Type u) [Field K] :
      (chapter04ProjectiveLineExample K).constant_map ≫
        chapter04ProjectivePointStructureMap K =
      chapter04ProjectiveLineStructureMap K := by
  exact (chapter04ProjectiveLineExample K).constant_map_over

theorem chapter04_projective_line_constant_map_is_constant
    (K : Type u) [Field K] :
    chapter04UnderlyingConstant (chapter04ProjectiveLineExample K).constant_map := by
  exact (chapter04ProjectiveLineExample K).constant_map_is_constant

theorem chapter04_projective_line_tautological_basis_generates
    (K : Type u) [Field K] :
    Epi (((chapter04ProjectiveLineTautologicalLineBundle K).sheaf.freeHomEquiv
      (I := ULift.{u} (Fin 2))).symm
      (fun i : ULift.{u} (Fin 2) => chapter04ProjectiveLineTautologicalBasis K i.down)) := by
  let P := Chapter02.chapter02ProjectiveSpaceData
    (AlgebraicGeometry.Spec (.of K)) (Chapter02.Chapter02ProjectiveSpaceIndex 1)
  have hcoord := P.coordinateSections_spec
  have he : Epi P.coordinateComparison.hom :=
    @IsIso.epi_of_iso _ _ _ _ P.coordinateComparison.hom P.coordinateComparison.isIso_hom
  have hepi : Epi (P.coordinateComparison.hom ≫ P.bundle.universalQuotient) := by
    exact epi_comp' he P.bundle.universalQuotient_is_epi
  change Epi ((P.bundle.twistingLineBundle.carrier.freeHomEquiv).symm P.coordinateSections)
  rw [← hcoord]
  exact hepi

theorem chapter04_projective_line_tautological_identity_embedding
    (K : Type u) [Field K] :
    IsImmersion (𝟙 (chapter04ProjectiveLine K)) ∧
      Nonempty ((chapter04ProjectiveLineTautologicalLineBundle K).sheaf ≅
        (Scheme.Modules.pullback (𝟙 (chapter04ProjectiveLine K))).obj
          (chapter04ProjectiveLineTautologicalLineBundle K).sheaf) := by
  refine ⟨inferInstance, ?_⟩
  exact ⟨((Scheme.Modules.pullbackId (chapter04ProjectiveLine K)).app
    (chapter04ProjectiveLineTautologicalLineBundle K).sheaf).symm⟩

theorem chapter04_projective_line_tautological_is_veryAmple
    (K : Type u) [Field K] :
    chapter04VeryAmple
      (chapter04ProjectiveLineStructureMap K)
      (chapter04ProjectiveLineTautologicalLineBundle K) := by
  sorry

end
end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
