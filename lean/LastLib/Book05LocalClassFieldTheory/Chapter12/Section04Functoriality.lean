import LastLib.Book05LocalClassFieldTheory.Chapter12.Core
import LastLib.Book05LocalClassFieldTheory.Chapter09.Section04TowersAndFiniteQuotientDiagrams

namespace LastLib.Book05LocalClassFieldTheory.Chapter12

noncomputable section

open LastLib.Book05LocalClassFieldTheory.Chapter09

/-! ## 12.4. Functoriality at a glance -/

/-- The canonical multiplicative inclusion induced by a field extension. -/
noncomputable def chapter12MultiplicativeInclusion
    (K L : Type*) [Field K] [Field L] [Algebra K L] : Kˣ →* Lˣ :=
  chapter09FieldInclusionHom K L

/-- The maps occurring in the two functoriality formulas. -/
structure Chapter12FunctorialityData
    (K L Ks : Type) [Field K] [Field L] [Field Ks]
    [Algebra K L] [Algebra K Ks] [Algebra L Ks]
    [IsScalarTower K L Ks] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] where
  finite_separable : Chapter09FiniteSeparableExtension K L Ks
  reciprocity : Chapter09ReciprocitySystem K L Ks finite_separable

/-- Norm pairs with inclusion of the corresponding Galois groups. -/
theorem chapter12_norm_corresponds_to_galois_inclusion
    (K L Ks : Type) [Field K] [Field L] [Field Ks]
    [Algebra K L] [Algebra K Ks] [Algebra L Ks]
    [IsScalarTower K L Ks] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (D : Chapter12FunctorialityData K L Ks) :
    D.reciprocity.recK.reciprocity.comp (chapter12MultiplicativeNormMap K L) =
      (chapter09GaloisInclusionAbelianization K L Ks).comp
        D.reciprocity.recL.reciprocity := by
  sorry

theorem chapter12_norm_corresponds_to_galois_inclusion_apply
    (K L Ks : Type) [Field K] [Field L] [Field Ks]
    [Algebra K L] [Algebra K Ks] [Algebra L Ks]
    [IsScalarTower K L Ks] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (D : Chapter12FunctorialityData K L Ks) (x : Lˣ) :
    D.reciprocity.recK.reciprocity (chapter12MultiplicativeNormMap K L x) =
      chapter09GaloisInclusionAbelianization K L Ks
        (D.reciprocity.recL.reciprocity x) := by
  have h := chapter12_norm_corresponds_to_galois_inclusion K L Ks D
  exact DFunLike.congr_fun h x

/-- Multiplicative inclusion pairs with Galois transfer. -/
theorem chapter12_multiplicative_inclusion_corresponds_to_transfer
    (K L Ks : Type) [Field K] [Field L] [Field Ks]
    [Algebra K L] [Algebra K Ks] [Algebra L Ks]
    [IsScalarTower K L Ks] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (D : Chapter12FunctorialityData K L Ks) :
    D.reciprocity.recL.reciprocity.comp (chapter12MultiplicativeInclusion K L) =
      (chapter09GaloisTransfer K L Ks D.finite_separable).comp
        D.reciprocity.recK.reciprocity := by
  sorry

theorem chapter12_multiplicative_inclusion_corresponds_to_transfer_apply
    (K L Ks : Type) [Field K] [Field L] [Field Ks]
    [Algebra K L] [Algebra K Ks] [Algebra L Ks]
    [IsScalarTower K L Ks] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (D : Chapter12FunctorialityData K L Ks) (a : Kˣ) :
    D.reciprocity.recL.reciprocity (chapter12MultiplicativeInclusion K L a) =
      chapter09GaloisTransfer K L Ks D.finite_separable
        (D.reciprocity.recK.reciprocity a) := by
  have h := chapter12_multiplicative_inclusion_corresponds_to_transfer K L Ks D
  exact DFunLike.congr_fun h a

theorem chapter12_norms_are_transitive
    (K L M : Type*) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M] [FiniteDimensional K L]
    [FiniteDimensional L M] [FiniteDimensional K M] :
    chapter12MultiplicativeNormMap K M =
      (chapter12MultiplicativeNormMap K L).comp
        (chapter12MultiplicativeNormMap L M) := by
  sorry

/-- Composition of transfer maps in a tower. -/
def chapter12TransferTowerComposition
    {G₁ G₂ G₃ : Type*} [Group G₁] [Group G₂] [Group G₃]
    (V₁₂ : G₁ →* G₂) (V₂₃ : G₂ →* G₃) : G₁ →* G₃ :=
  V₂₃.comp V₁₂

theorem chapter12_transfers_are_transitive
    {G₁ G₂ G₃ : Type*} [Group G₁] [Group G₂] [Group G₃]
    (V₁₂ : G₁ →* G₂) (V₂₃ : G₂ →* G₃) (g : G₁) :
    chapter12TransferTowerComposition V₁₂ V₂₃ g = V₂₃ (V₁₂ g) := by
  rfl

end

end LastLib.Book05LocalClassFieldTheory.Chapter12
