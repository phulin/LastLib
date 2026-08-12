import LastLib.Book05LocalClassFieldTheory.Chapter12.Core

namespace LastLib.Book05LocalClassFieldTheory.Chapter12

noncomputable section

/-! ## 12.4. Functoriality at a glance -/

/-- The canonical multiplicative inclusion induced by a field extension. -/
noncomputable def chapter12MultiplicativeInclusion
    (K L : Type*) [Field K] [Field L] [Algebra K L] : Kˣ →* Lˣ :=
  Units.map (algebraMap K L).toMonoidHom

/-- The maps occurring in the two functoriality formulas. -/
structure Chapter12FunctorialityData
    (K L G_K G_L : Type*) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L]
    [CommGroup G_K] [CommGroup G_L] where
  finite_separable : Algebra.IsSeparable K L
  recK : Kˣ →* G_K
  recL : Lˣ →* G_L
  galois_inclusion : G_L →* G_K
  transfer : G_K →* G_L

/-- Norm pairs with inclusion of the corresponding Galois groups. -/
-- DEPENDENCY_GUESS: The norm/restriction compatibility theorem is the
-- functorial finite-reciprocity result from the missing preceding chapters.
theorem chapter12_norm_corresponds_to_galois_inclusion
    {K L G_K G_L : Type*} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L]
    [CommGroup G_K] [CommGroup G_L]
    (P : Chapter12LocalFieldProfile K)
    (D : Chapter12FunctorialityData K L G_K G_L)
    (hseparable : Algebra.IsSeparable K L) :
    D.recK.comp (chapter12MultiplicativeNormMap K L) =
      D.galois_inclusion.comp D.recL := by
  sorry

theorem chapter12_norm_corresponds_to_galois_inclusion_apply
    {K L G_K G_L : Type*} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L]
    [CommGroup G_K] [CommGroup G_L]
    (P : Chapter12LocalFieldProfile K)
    (D : Chapter12FunctorialityData K L G_K G_L)
    (hseparable : Algebra.IsSeparable K L) (x : Lˣ) :
    D.recK (chapter12MultiplicativeNormMap K L x) =
      D.galois_inclusion (D.recL x) := by
  have h := chapter12_norm_corresponds_to_galois_inclusion P D hseparable
  simpa using congrArg (fun f : Lˣ →* G_K => f x) h

/-- Multiplicative inclusion pairs with Galois transfer. -/
theorem chapter12_multiplicative_inclusion_corresponds_to_transfer
    {K L G_K G_L : Type*} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L]
    [CommGroup G_K] [CommGroup G_L]
    (P : Chapter12LocalFieldProfile K)
    (D : Chapter12FunctorialityData K L G_K G_L)
    (hseparable : Algebra.IsSeparable K L) :
    D.recL.comp (chapter12MultiplicativeInclusion K L) =
      D.transfer.comp D.recK := by
  sorry

theorem chapter12_multiplicative_inclusion_corresponds_to_transfer_apply
    {K L G_K G_L : Type*} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L]
    [CommGroup G_K] [CommGroup G_L]
    (P : Chapter12LocalFieldProfile K)
    (D : Chapter12FunctorialityData K L G_K G_L)
    (hseparable : Algebra.IsSeparable K L) (a : Kˣ) :
    D.recL (chapter12MultiplicativeInclusion K L a) = D.transfer (D.recK a) := by
  have h := chapter12_multiplicative_inclusion_corresponds_to_transfer P D hseparable
  simpa using congrArg (fun f : Kˣ →* G_L => f a) h

/-- Composition of norm maps in a tower. -/
def chapter12NormTowerComposition
    {A B C : Type*} [Group A] [Group B] [Group C]
    (N_BC : B →* C) (N_AB : A →* B) : A →* C :=
  N_BC.comp N_AB

theorem chapter12_norms_are_transitive
    {A B C : Type*} [Group A] [Group B] [Group C]
    (N_BC : B →* C) (N_AB : A →* B) (x : A) :
    chapter12NormTowerComposition N_BC N_AB x = N_BC (N_AB x) := by
  rfl

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
