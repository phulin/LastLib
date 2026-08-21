import LastLib.Book05LocalClassFieldTheory.Chapter02.Section04NormGroupsAreOpenAndClosed

namespace LastLib.Book05LocalClassFieldTheory.Chapter02

noncomputable section

open Function Ideal IsLocalRing
open Filter Topology
open scoped BigOperators Pointwise Topology

/-! ## 2.5. The index question -/

abbrev Chapter02GaloisGroup
    (K L : Type*) [Field K] [Field L] [Algebra K L] :=
  L ≃ₐ[K] L

def chapter02MaximalAbelianIntermediateField
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] : IntermediateField K L :=
  IntermediateField.fixedField
    (commutator (Chapter02GaloisGroup K L))

def Chapter02GaloisNormIndexStatement
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Prop :=
  Nat.card (Kˣ ⧸ chapter02NormSubgroup K L) = Module.finrank K L

structure Chapter02LocalGaloisExtensionData
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] where
  vK : AddValuation K (WithTop ℤ)
  vL : AddValuation L (WithTop ℤ)
  base_local : Chapter02LocalField vK
  extension_local : Chapter02LocalField vL
  valuation_extension :
    vK.IsEquiv (AddValuation.comap (algebraMap K L) vL)

/- LOCAL_DEPENDENCY_GUESS: the finite local norm-index theorem is the later
   reciprocity input, recorded here so the chapter's index target is explicit. -/
theorem chapter02_galois_norm_index_eq_abelianization
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (d : Chapter02LocalGaloisExtensionData K L) :
    Nat.card (Kˣ ⧸ chapter02NormSubgroup K L) =
      Nat.card (Abelianization (Chapter02GaloisGroup K L)) := by
  sorry

theorem chapter02_galois_norm_index_eq_maximal_abelian_degree
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (d : Chapter02LocalGaloisExtensionData K L) :
    Nat.card (Kˣ ⧸ chapter02NormSubgroup K L) =
      Module.finrank K (chapter02MaximalAbelianIntermediateField K L) := by
  sorry

theorem chapter02_galois_abelianization_degree
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (habelian : ∀ σ τ : Chapter02GaloisGroup K L, σ * τ = τ * σ) :
    Nat.card (Abelianization (Chapter02GaloisGroup K L)) =
      Module.finrank K L := by
  sorry

theorem chapter02_galois_norm_index_eq_degree_of_abelian
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (d : Chapter02LocalGaloisExtensionData K L)
    (habelian : ∀ σ τ : Chapter02GaloisGroup K L, σ * τ = τ * σ) :
    Chapter02GaloisNormIndexStatement K L := by
  sorry

theorem chapter02_galois_degree_index_forces_abelian
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (d : Chapter02LocalGaloisExtensionData K L)
    (hindex : Chapter02GaloisNormIndexStatement K L) :
    ∀ σ τ : Chapter02GaloisGroup K L, σ * τ = τ * σ := by
  sorry

theorem chapter02_nonabelian_galois_degree_index_fails
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (d : Chapter02LocalGaloisExtensionData K L)
    (hnonabelian : ∃ σ τ : Chapter02GaloisGroup K L, σ * τ ≠ τ * σ) :
    ¬Chapter02GaloisNormIndexStatement K L := by
  sorry

/- The commutator-fixed-field construction is deliberately restricted to the
   Galois case.  A nonnormal finite separable extension has no canonical
   maximal abelian intermediate field inside it that can replace this object. -/
def Chapter02NonnormalExtension
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Prop :=
  Algebra.IsSeparable K L ∧ ¬IsGalois K L

end

end LastLib.Book05LocalClassFieldTheory.Chapter02
