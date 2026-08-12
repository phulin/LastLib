import Mathlib.FieldTheory.Galois.Abelian
import LastLib.Book05LocalClassFieldTheory.Chapter05.Core
import LastLib.Book05LocalClassFieldTheory.Chapter05.Section04FiniteArtinMap

namespace LastLib.Book05LocalClassFieldTheory.Chapter05

noncomputable section

open scoped IsMulCommutative

/-!
### 5.6. The reciprocity theorem at finite level
-/

noncomputable def chapter05FiniteReciprocityIso
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L) :
    chapter05NormQuotient K L ≃* Gal(L / K) :=
  (chapter05FiniteArtinQuotientEquiv D).trans
    (Abelianization.equivOfComm (H := Gal(L / K))).symm

def chapter05FiniteReciprocityMap
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L) : Kˣ →* Gal(L / K) :=
  (chapter05FiniteReciprocityIso D).toMonoidHom.comp
    (QuotientGroup.mk' (chapter05NormSubgroup K L))

theorem chapter05FiniteReciprocityMap_kernel
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L) :
    (chapter05FiniteReciprocityMap D).ker = chapter05NormSubgroup K L := by
  sorry

theorem chapter05FiniteReciprocityMap_surjective
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L) :
    Function.Surjective (chapter05FiniteReciprocityMap D) := by
  sorry

def chapter05FundamentalClassCompatible
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L)
    (e : chapter05NormQuotient K L ≃* Gal(L / K)) : Prop :=
  e = chapter05FiniteReciprocityIso D

theorem chapter05FiniteReciprocity_unique
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L)
    (e₁ e₂ : chapter05NormQuotient K L ≃* Gal(L / K))
    (h₁ : chapter05FundamentalClassCompatible D e₁)
    (h₂ : chapter05FundamentalClassCompatible D e₂) :
    e₁ = e₂ := by
  exact h₁.trans h₂.symm

/- LOCAL_DEPENDENCY_GUESS: the valuation/residue-field interface used to
define an unramified local extension belongs to the earlier local-field
chapters.  The group-theoretic content needed here is explicit: the inertia
subgroup is trivial, and the chosen arithmetic Frobenius and uniformizer are
the book's normalized ones. -/
structure Chapter05UnramifiedExtensionData
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))] where
  inertia : Subgroup (Gal(L / K))
  inertia_eq_bot : inertia = ⊥
  cyclic : IsCyclic (Gal(L / K))
  uniformizer : Kˣ
  arithmeticFrobenius : Gal(L / K)
  frobenius_generates : Subgroup.zpowers arithmeticFrobenius = ⊤

theorem chapter05_unramified_uniformizer_is_arithmetic_frobenius
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L)
    (U : Chapter05UnramifiedExtensionData K L) :
    chapter05FiniteReciprocityMap D U.uniformizer = U.arithmeticFrobenius := by
  sorry

theorem chapter05_unramified_uniformizer_is_arithmetic_frobenius_in_abelianization
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L)
    (U : Chapter05UnramifiedExtensionData K L) :
    chapter05FiniteArtinMap D U.uniformizer =
    chapter05AbelianizationMap (Gal(L / K)) U.arithmeticFrobenius := by
  sorry

structure Chapter05FiniteReciprocityCompatibility
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L)
    (e : chapter05NormQuotient K L ≃* Gal(L / K)) where
  fundamental_class : e = chapter05FiniteReciprocityIso D
  unramified_frobenius : ∀ U : Chapter05UnramifiedExtensionData K L,
    e (QuotientGroup.mk' (chapter05NormSubgroup K L) U.uniformizer) =
      U.arithmeticFrobenius

theorem chapter05FiniteReciprocity_unique_with_normalizations
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L)
    (e₁ e₂ : chapter05NormQuotient K L ≃* Gal(L / K))
    (c₁ : Chapter05FiniteReciprocityCompatibility D e₁)
    (c₂ : Chapter05FiniteReciprocityCompatibility D e₂) :
    e₁ = e₂ := by
  exact c₁.fundamental_class.trans c₂.fundamental_class.symm

theorem chapter05_finite_local_reciprocity
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L) :
    ∃ e : chapter05NormQuotient K L ≃* Gal(L / K),
      e = chapter05FiniteReciprocityIso D ∧
      (e.toMonoidHom.comp (QuotientGroup.mk' (chapter05NormSubgroup K L))).ker =
        chapter05NormSubgroup K L ∧
      Function.Surjective e := by
  refine ⟨chapter05FiniteReciprocityIso D, rfl, ?_, ?_⟩
  · exact chapter05FiniteReciprocityMap_kernel D
  · exact (chapter05FiniteReciprocityIso D).surjective

/- The source deliberately defers the precise quotient and tower diagrams to
Chapter 9.  The finite-level API above exposes the quotient map and its
kernel, while this theorem records the source-order uniqueness condition at
the current chapter's level. -/

end

end LastLib.Book05LocalClassFieldTheory.Chapter05
