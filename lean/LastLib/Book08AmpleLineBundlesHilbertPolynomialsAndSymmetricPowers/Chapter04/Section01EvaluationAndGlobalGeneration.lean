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

/- DEPENDENCY_GUESS: the standard `P¹` and its two named line bundles are not
yet exposed by the preceding Book 8 files or pinned Mathlib.  This compact
interface records the two source examples while leaving their identification
with the usual Proj construction to that earlier chapter. -/
structure Chapter04ProjectiveLineExample (K : Type u) [Field K] where
  projectiveLine : Scheme.{u}
  structureMap : projectiveLine ⟶ AlgebraicGeometry.Spec (.of K)
  trivial : Chapter04LineBundle projectiveLine
  tautological : Chapter04LineBundle projectiveLine
  constant_section : trivial.sheaf.val.sections
  constant_section_generates :
    Epi (trivial.sheaf.freeHomEquiv.symm (fun _ : PUnit => constant_section))
  trivial_not_veryAmple : ¬ chapter04VeryAmple structureMap trivial
  constant_map : projectiveLine ⟶ projectiveLine
  constant_map_over : constant_map ≫ structureMap = structureMap
  constant_map_is_constant :
    ∀ x y : projectiveLine, constant_map.base x = constant_map.base y
  basis : Fin 2 → tautological.sheaf.sections
  basis_generates :
    Epi (tautological.sheaf.freeHomEquiv.symm
      (fun i : ULift.{u} (Fin 2) => basis i.down))
  tautological_veryAmple : chapter04VeryAmple structureMap tautological
  basis_map : projectiveLine ⟶ projectiveLine
  basis_map_eq_identity : basis_map = 𝟙 projectiveLine

theorem chapter04_projective_line_constant_section_generates
    {K : Type u} [Field K] (P : Chapter04ProjectiveLineExample K) :
    Epi (P.trivial.sheaf.freeHomEquiv.symm
      (fun _ : PUnit => P.constant_section)) :=
  P.constant_section_generates

theorem chapter04_projective_line_constant_map_is_constant
    {K : Type u} [Field K] (P : Chapter04ProjectiveLineExample K) :
    ∀ x y : P.projectiveLine, P.constant_map.base x = P.constant_map.base y :=
  P.constant_map_is_constant

theorem chapter04_projective_line_trivial_not_veryAmple
    {K : Type u} [Field K] (P : Chapter04ProjectiveLineExample K) :
    ¬ chapter04VeryAmple P.structureMap P.trivial :=
  P.trivial_not_veryAmple

theorem chapter04_projective_line_tautological_is_veryAmple
    {K : Type u} [Field K] (P : Chapter04ProjectiveLineExample K) :
    chapter04VeryAmple P.structureMap P.tautological :=
  P.tautological_veryAmple

theorem chapter04_projective_line_tautological_basis_gives_identity
    {K : Type u} [Field K] (P : Chapter04ProjectiveLineExample K) :
    P.basis_map = 𝟙 P.projectiveLine :=
  P.basis_map_eq_identity

end
end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
