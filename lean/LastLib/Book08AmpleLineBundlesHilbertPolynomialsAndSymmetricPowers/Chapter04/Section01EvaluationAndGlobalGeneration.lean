import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Dependencies

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
  sorry

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
  sorry

theorem chapter04_projective_line_constant_map_is_constant
    (K : Type u) [Field K] :
    chapter04UnderlyingConstant (chapter04ProjectiveLineExample K).constant_map := by
  sorry

theorem chapter04_projective_line_tautological_basis_generates
    (K : Type u) [Field K] :
    Epi (((chapter04ProjectiveLineTautologicalLineBundle K).sheaf.freeHomEquiv
      (I := ULift.{u} (Fin 2))).symm
      (fun i : ULift.{u} (Fin 2) => chapter04ProjectiveLineTautologicalBasis K i.down)) := by
  sorry

theorem chapter04_projective_line_tautological_identity_embedding
    (K : Type u) [Field K] :
    IsImmersion (𝟙 (chapter04ProjectiveLine K)) ∧
      Nonempty ((chapter04ProjectiveLineTautologicalLineBundle K).sheaf ≅
        (Scheme.Modules.pullback (𝟙 (chapter04ProjectiveLine K))).obj
          (chapter04ProjectiveLineTautologicalLineBundle K).sheaf) := by
  sorry

theorem chapter04_projective_line_tautological_is_veryAmple
    (K : Type u) [Field K] :
    chapter04VeryAmple
      (chapter04ProjectiveLineStructureMap K)
      (chapter04ProjectiveLineTautologicalLineBundle K) := by
  sorry

end
end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
