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
yet exposed by the preceding Book 8 files or pinned Mathlib.  This data record
keeps only the underlying objects needed by the examples; the generation,
separation, and identity assertions belong after a canonical `P¹` interface. -/
structure Chapter04ProjectiveLineExample (K : Type u) [Field K] where
  projectiveLine : Scheme.{u}
  structureMap : projectiveLine ⟶ AlgebraicGeometry.Spec (.of K)
  trivial : Chapter04LineBundle projectiveLine
  tautological : Chapter04LineBundle projectiveLine
  constant_section : trivial.sheaf.val.sections
  constant_map : projectiveLine ⟶ projectiveLine
  constant_map_over : constant_map ≫ structureMap = structureMap
  constant_map_is_constant : chapter04UnderlyingConstant constant_map
  basis : Fin 2 → tautological.sheaf.sections

end
end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
