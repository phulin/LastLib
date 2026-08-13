import LastLib.Book05LocalClassFieldTheory.Chapter11.Dependencies
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.Galois.Basic

namespace LastLib.Book05LocalClassFieldTheory.Chapter11

noncomputable section

open scoped Topology

/-! ## 11.2. Finite-order characters and cyclic extensions -/

theorem chapter11_character_kernel_open_finite_index
    {K A : Type*} [Field K] [CommGroup A] [Finite A]
    [TopologicalSpace Kˣ] [TopologicalSpace A] [DiscreteTopology A]
    (χ : Kˣ →ₜ* A) :
    IsOpen (chapter11CharacterKernel χ : Set Kˣ) ∧
      (chapter11CharacterKernel χ).FiniteIndex := by
  sorry

noncomputable def chapter11CharacterQuotientImageEquiv
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A]
    (χ : Kˣ →ₜ* A) :
    Kˣ ⧸ chapter11CharacterKernel χ ≃*
      MonoidHom.mrange χ.toMonoidHom :=
  QuotientGroup.quotientKerEquivRange χ.toMonoidHom

noncomputable def chapter11_character_quotient_equiv_image
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A]
    (χ : Kˣ →ₜ* A) :
    Kˣ ⧸ chapter11CharacterKernel χ ≃*
      MonoidHom.mrange χ.toMonoidHom :=
  chapter11CharacterQuotientImageEquiv χ

theorem chapter11_norm_group_membership_iff
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : Kˣ) :
    x ∈ chapter11NormGroup K L ↔
      ∃ y : Lˣ, chapter11NormHom K L y = x := by
  sorry

abbrev chapter11FiniteAbelianExtension
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] : Prop :=
  IsAbelianGalois K L

def chapter11CharacterCutsOutExtension
    {K L A : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A]
    (χ : Kˣ →ₜ* A) : Prop :=
  chapter11FiniteAbelianExtension K L ∧
    chapter11CharacterKernel χ = chapter11NormGroup K L

theorem chapter11_extension_norm_group_is_character_kernel
    {K L A : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A]
    (χ : Kˣ →ₜ* A)
    (hχ : chapter11CharacterCutsOutExtension (K := K) (L := L) χ) :
    chapter11NormGroup K L = chapter11CharacterKernel χ := by
  exact hχ.2.symm

theorem chapter11_finite_character_gives_cyclic_extension
    {K A : Type*} [Field K] [CommGroup A] [Finite A] [IsCyclic A]
    [TopologicalSpace Kˣ] [TopologicalSpace A] [DiscreteTopology A]
    (C : Chapter11ClassFieldExistenceData K)
    (χ : Kˣ →ₜ* A) :
    ∃ e : C.extension,
      C.normGroup e = chapter11CharacterKernel χ ∧
        C.degree e = Nat.card (Set.range χ) ∧ C.cyclic e := by
  sorry

theorem chapter11_finite_character_norm_index
    {K A : Type*} [Field K] [CommGroup A] [Finite A]
    [TopologicalSpace Kˣ] [TopologicalSpace A] [DiscreteTopology A]
    (C : Chapter11ClassFieldExistenceData K)
    (χ : Kˣ →ₜ* A) (e : C.extension)
    (he : C.normGroup e = chapter11CharacterKernel χ) :
    C.degree e = Nat.card (Set.range χ) := by
  sorry

theorem chapter11_cyclic_extension_embedding_gives_character
    {K L A : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [CommGroup A] [Finite A]
    [TopologicalSpace Kˣ] [TopologicalSpace A]
    [TopologicalSpace (Gal(L / K))] [DiscreteTopology (Gal(L / K))]
    [DiscreteTopology A]
    (hcyclic : IsCyclic (Gal(L / K)))
    (B : Chapter11FiniteArtinData K L)
    (ι : Gal(L / K) →* A) (hι : Function.Injective ι) :
    ∃ χ : Kˣ →ₜ* A,
      chapter11CharacterKernel χ = chapter11NormGroup K L ∧
        chapter11FiniteImage χ := by
  sorry

def chapter11FaithfulCharacterChoice
    {G A : Type*} [Group G] [CommGroup A] : Prop :=
  ∃ ι : G →* A, Function.Injective ι

theorem chapter11_extension_only_remembers_the_kernel
    {K L A : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A]
    (χ : Kˣ →ₜ* A)
    (hχ : chapter11CharacterCutsOutExtension (K := K) (L := L) χ) :
    chapter11CharacterKernel χ = chapter11NormGroup K L := by
  exact hχ.2

theorem chapter11_extension_kernel_invariant_under_character_choice
    {K L A : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A]
    (χ₁ χ₂ : Kˣ →ₜ* A)
    (hker : chapter11CharacterKernel χ₁ = chapter11CharacterKernel χ₂) :
    chapter11CharacterCutsOutExtension (K := K) (L := L) χ₁ ↔
      chapter11CharacterCutsOutExtension (K := K) (L := L) χ₂ := by
  rw [chapter11CharacterCutsOutExtension, chapter11CharacterCutsOutExtension,
    hker]

end
end LastLib.Book05LocalClassFieldTheory.Chapter11
