import LastLib.Book05LocalClassFieldTheory.Chapter09.Dependencies

namespace LastLib.Book05LocalClassFieldTheory.Chapter09

noncomputable section

/-!
## 9.1 Why directions are easy to reverse accidentally

The common separable closure is represented by `Ks`, and the two directions
of the crossed pair are kept visible in the names of the maps: field
inclusion goes from `Kˣ` to `Lˣ`, while restriction of automorphisms goes from
`Gal(Ks/L)` to `Gal(Ks/K)`.
-/

theorem chapter09_closure_over_base
    (K L Ks : Type*) [Field K] [Field L] [Field Ks]
    [Algebra K L] [Algebra K Ks] [Algebra L Ks]
    [IsScalarTower K L Ks] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (T : Chapter09FiniteSeparableExtension K L Ks) :
    IsSepClosure K Ks :=
  T.closure_over_base

theorem chapter09_closure_over_extension
    (K L Ks : Type*) [Field K] [Field L] [Field Ks]
    [Algebra K L] [Algebra K Ks] [Algebra L Ks]
    [IsScalarTower K L Ks] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (T : Chapter09FiniteSeparableExtension K L Ks) :
    IsSepClosure L Ks :=
  chapter09_isSepClosure_over_extension_of_base K L Ks T.closure_over_base

theorem chapter09_galoisSubgroup_mem_iff
    (K L Ks : Type*) [Field K] [Field L] [Field Ks]
    [Algebra K L] [Algebra K Ks] [Algebra L Ks]
    [IsScalarTower K L Ks] (σ : Gal(Ks / K)) :
    σ ∈ chapter09GaloisSubgroup K L Ks ↔
      ∃ τ : Gal(Ks / L), chapter09GaloisInclusion K L Ks τ = σ := by
  simp [chapter09GaloisSubgroup]

theorem chapter09_field_inclusion_injective
    (K L : Type*) [Field K] [Field L] [Algebra K L] :
    Function.Injective (chapter09FieldInclusionHom K L) := by
  exact Units.map_injective (algebraMap K L).injective

theorem chapter09_galoisInclusionAbelianization_apply
    (K L Ks : Type*) [Field K] [Field L] [Field Ks]
    [Algebra K L] [Algebra K Ks] [Algebra L Ks]
    [IsScalarTower K L Ks] (τ : Gal(Ks / L)) :
    chapter09GaloisInclusionAbelianization K L Ks (Abelianization.of τ) =
      Abelianization.of (chapter09GaloisInclusion K L Ks τ) := by
  rfl

end

end LastLib.Book05LocalClassFieldTheory.Chapter09
