import LastLib.Book06GlobalClassFieldTheory.Chapter02.Dependencies
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.Galois.IsGaloisGroup

namespace LastLib.Book06GlobalClassFieldTheory.Chapter02

noncomputable section

open scoped BigOperators Pointwise

universe u v w z

/-! ## 2.1. Decomposition groups from a chosen place -/

/-
The ambient finite group `G` is the Galois group of a finite Galois extension
`L/K`; the abstract place action in `Chapter02ChosenPlace` is the interface
shared by finite prime ideals and infinite places.
-/

/-- The selected upper place and its decomposition group. -/
abbrev chapter02ChosenDecompositionGroup
    {G : Type u} [Group G] {V : Type v} {W : Type w} [MulAction G W]
    (P : Chapter02ChosenPlace G V W) : Subgroup G :=
  chapter02DecompositionGroup P

theorem chapter02_decomposition_group_is_the_stabilizer
    {G : Type u} [Group G] {V : Type v} {W : Type w} [MulAction G W]
    (P : Chapter02ChosenPlace G V W) :
    chapter02ChosenDecompositionGroup P =
      MulAction.stabilizer G P.extensionPlace := by
  rfl

/-- The canonical local Galois identification, when supplied by the completion API. -/
def chapter02LocalDecompositionGroupEquiv
    {D H : Type*} [Group D] [Group H]
    (E : Chapter02CompletionGaloisIdentification D H) : D ≃* H :=
  E.equiv

theorem chapter02_decomposition_group_identifies_with_local_galois_group
    {D H : Type*} [Group D] [Group H]
    (E : Chapter02CompletionGaloisIdentification D H) :
    Nonempty (D ≃* H) := by
  exact ⟨chapter02LocalDecompositionGroupEquiv E⟩

/-
This is the canonical valuation-theoretic instance of the preceding abstract
completion bridge.  The extra `IsGaloisGroup` hypothesis is the explicit
interface for the induced completed action supplied by Book 2.
-/
theorem chapter02_decomposition_group_is_completion_galois_group
    {F E Γ : Type*} [Field F] [Field E] [Algebra F E]
    [LinearOrderedCommGroupWithZero Γ] [FiniteDimensional F E] [IsGalois F E]
    (v : Valuation F Γ) (w : Valuation E Γ)
    (hw : w.valuationSubring ∈
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05ValuationsAbove v)
    [Algebra (v.Completion) (w.Completion)]
    [FiniteDimensional (v.Completion) (w.Completion)]
    [MulSemiringAction
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
        F w.valuationSubring) (w.Completion)]
    [Finite
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
        F w.valuationSubring)]
    (hD : IsGaloisGroup
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
        F w.valuationSubring)
      (v.Completion) (w.Completion)) :
    Nonempty
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
        F w.valuationSubring ≃* Gal(w.Completion / v.Completion)) := by
  exact
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.decomposition_group_is_completion_galois_group
      v w hw hD

/-
At a finite place the residue action is the reduction datum from the shared
interface.  It is useful to expose the three maps separately before packaging
the exact sequence.
-/

/-- The reduction map on the selected decomposition group. -/
abbrev chapter02ResidueReduction
    {D k l : Type*} [Group D] [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l] [IsGalois k l]
    (R : Chapter02ResidueActionData D k l) : D →* Gal(l / k) :=
  R.reduction

/-- The inertia subgroup as the kernel of residue reduction. -/
theorem chapter02_inertia_is_reduction_kernel
    {D k l : Type*} [Group D] [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l] [IsGalois k l]
    (R : Chapter02ResidueActionData D k l) :
    R.inertia = (chapter02ResidueReduction R).ker := by
  exact R.kernel_eq_inertia.symm

/-- The finite-place decomposition/inertia sequence is exact and onto. -/
theorem chapter02_decomposition_inertia_exact
    {D k l : Type*} [Group D] [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l] [IsGalois k l]
    (R : Chapter02ResidueActionData D k l) :
    Function.MulExact R.inertia.subtype (chapter02ResidueReduction R) ∧
      Function.Surjective (chapter02ResidueReduction R) := by
  exact ⟨chapter02_residue_exact_sequence R, R.reduction_surjective⟩

/-!
The local reciprocity map first lands in `Dᵃᵇ`.  In the abelian case the
canonical equivalence `D ≃* Dᵃᵇ` turns it into the map whose image is `D`.
-/

/-- Local reciprocity in the abelian decomposition group. -/
def chapter02LocalArtinMapAtChosenPlace
    {G : Type u} [CommGroup G] {V : Type v} {W : Type w} [MulAction G W]
    {B E : Type*} [CommGroup B] [CommGroup E]
    (P : Chapter02ChosenPlace G V W)
    (R : Chapter02LocalReciprocityData B E (chapter02DecompositionGroup P)) :
    B →* G :=
  (chapter02DecompositionGroup P).subtype.comp (chapter02LocalArtinMap R)

theorem chapter02_local_artin_map_at_chosen_place_kernel
    {G : Type u} [CommGroup G] {V : Type v} {W : Type w} [MulAction G W]
    {B E : Type*} [CommGroup B] [CommGroup E]
    (P : Chapter02ChosenPlace G V W)
    (R : Chapter02LocalReciprocityData B E (chapter02DecompositionGroup P)) :
    (chapter02LocalArtinMapAtChosenPlace P R).ker = R.norm.range := by
  sorry

theorem chapter02_local_artin_map_at_chosen_place_range
    {G : Type u} [CommGroup G] {V : Type v} {W : Type w} [MulAction G W]
    {B E : Type*} [CommGroup B] [CommGroup E]
    (P : Chapter02ChosenPlace G V W)
    (R : Chapter02LocalReciprocityData B E (chapter02DecompositionGroup P)) :
    (chapter02LocalArtinMapAtChosenPlace P R).range =
      chapter02DecompositionGroup P := by
  sorry

theorem chapter02_local_artin_map_at_chosen_place_units
    {G : Type u} [CommGroup G] {V : Type v} {W : Type w} [MulAction G W]
    {B E : Type*} [CommGroup B] [CommGroup E]
    (P : Chapter02ChosenPlace G V W)
    (R : Chapter02LocalReciprocityData B E (chapter02DecompositionGroup P)) :
    ((chapter02LocalArtinMapAtChosenPlace P R).comp R.unitSubgroup.subtype).range =
      (R.inertia.map (chapter02DecompositionGroup P).subtype) := by
  sorry

/-
For a nonabelian Galois group the same construction has target `Gᵃᵇ`.  The
inclusion of the local decomposition group is the map induced by the chosen
place; changing the place changes it by conjugation before abelianization.
-/

/-- The abelianized local Artin map in the ambient Galois group. -/
def chapter02AbelianizedLocalArtinMapAtChosenPlace
    {G : Type u} [Group G] {V : Type v} {W : Type w} [MulAction G W]
    {B E : Type*} [CommGroup B] [CommGroup E]
    (P : Chapter02ChosenPlace G V W)
    (R : Chapter02LocalReciprocityData B E (chapter02DecompositionGroup P)) :
    B →* Abelianization G :=
  chapter02AbelianizedLocalArtinMap
    (chapter02DecompositionGroup P).subtype R

/-- A functorial comparison of local maps after changing the chosen place. -/
theorem chapter02_abelianized_local_artin_change_of_place
    {G D D' B E : Type*} [Group G] [Group D] [Group D']
    [CommGroup B] [CommGroup E]
    (ι : D →* G) (ι' : D' →* G)
    (e : D ≃* D')
    (R : Chapter02LocalReciprocityData B E D)
    (R' : Chapter02LocalReciprocityData B E D')
    (hι : (Abelianization.map ι').comp
        (Abelianization.map e.toMonoidHom) = Abelianization.map ι)
    (hR : R'.reciprocity =
      (Abelianization.map e.toMonoidHom).comp R.reciprocity) :
    chapter02AbelianizedLocalArtinMap ι' R' =
      chapter02AbelianizedLocalArtinMap ι R := by
  rw [chapter02AbelianizedLocalArtinMap, chapter02AbelianizedLocalArtinMap,
    hR, ← MonoidHom.comp_assoc, hι]

/-
The source's abelian-choice assertion is now available in the two forms used
later: decomposition/inertia subgroups are unchanged, while the nonabelian map
is compared only after abelianization.
-/

theorem chapter02_abelian_decomposition_group_choice_eq
    {G : Type u} [CommGroup G] {V : Type v} {W : Type w} [MulAction G W]
    (P : Chapter02ChosenPlace G V W) (τ : G) :
    chapter02ChosenDecompositionGroup (chapter02ConjugateChosenPlace P τ) =
      chapter02ChosenDecompositionGroup P := by
  exact chapter02_decompositionGroup_choice_independent_of_abelianity P τ

theorem chapter02_abelian_inertia_group_choice_eq
    {G : Type u} [CommGroup G] {V : Type v} {W : Type w} [MulAction G W]
    (P : Chapter02ChosenPlace G V W) (S : Chapter02InertiaSystem G W) (τ : G) :
    S.inertia (τ • P.extensionPlace) = S.inertia P.extensionPlace := by
  exact chapter02_inertia_choice_independent_of_abelianity P S τ

end

end LastLib.Book06GlobalClassFieldTheory.Chapter02
