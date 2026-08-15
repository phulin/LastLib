import LastLib.Book05LocalClassFieldTheory.Chapter05.Core

namespace LastLib.Book05LocalClassFieldTheory.Chapter05

noncomputable section

/-!
### 5.1. Why abelianization appears
-/

theorem chapter05_hom_to_commGroup_factors_through_abelianization
    {G A : Type*} [Group G] [CommGroup A] (f : G →* A) :
    ∃ f_ab : chapter05Abelianization G →* A,
      f_ab.comp (chapter05AbelianizationMap G) = f := by
  refine ⟨Abelianization.lift f, ?_⟩
  ext g
  simp [chapter05AbelianizationMap]

@[instance_reducible]
def chapter05_abelianization_is_commutative
    (G : Type*) [Group G] : CommGroup (chapter05Abelianization G) := by
  infer_instance

theorem chapter05_maximal_abelian_fixed_field
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    IsGalois K (chapter05MaximalAbelianSubextension K L) := by
  exact chapter05_maximal_abelian_subextension_isGalois K L

theorem chapter05_maximal_abelian_subextension_is_abelian
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    ∀ σ τ : Gal(chapter05MaximalAbelianSubextension K L / K),
      σ * τ = τ * σ := by
  intro σ τ
  exact IsMulCommutative.is_comm.comm σ τ

/- The finite reciprocity target is named before the Tate argument; the
quotient equivalence itself is constructed after class formation. -/
abbrev chapter05FiniteReciprocityTarget
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :=
  chapter05Abelianization (Gal(L / K))

end

end LastLib.Book05LocalClassFieldTheory.Chapter05
