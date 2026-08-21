import Mathlib.FieldTheory.Galois.Abelian
import LastLib.Book05LocalClassFieldTheory.Chapter04.Core
import LastLib.Book05LocalClassFieldTheory.Chapter05.Core
import LastLib.Book05LocalClassFieldTheory.Chapter05.Section04FiniteArtinMap

namespace LastLib.Book05LocalClassFieldTheory.Chapter05

noncomputable section

open scoped IsMulCommutative WithZero

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
  ext x
  simp [chapter05FiniteReciprocityMap]

theorem chapter05FiniteReciprocityMap_surjective
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L) :
    Function.Surjective (chapter05FiniteReciprocityMap D) := by
  intro y
  obtain ⟨z, rfl⟩ := (chapter05FiniteReciprocityIso D).surjective y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
    (chapter05NormSubgroup K L) z
  exact ⟨x, rfl⟩

/- The earlier chapter already packages the valued unramified extension,
   normalized uniformizer, and arithmetic Frobenius used by the source.
   Reuse that interface so this chapter does not introduce a second residue
   extension model. -/
abbrev Chapter05UnramifiedExtensionData
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :=
  LastLib.Book05LocalClassFieldTheory.Chapter04.Chapter04UnramifiedExtensionData K L

/- The quotient equivalence supplied by the class-formation data and the
   residue-field equivalence supplied by `U` are independent choices.  This
   bridge is the missing normalization datum: it identifies the canonical
   finite-Artin quotient map with the arithmetic Frobenius selected by `U`.
   Keeping it separate from `D` is important, since `D` is also used for
   ramified extensions, where no unramified Frobenius datum is present. -/
structure Chapter05FiniteReciprocityNormalization
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L)
    (U : Chapter05UnramifiedExtensionData K L) where
  quotient_uniformizer :
    chapter05FiniteArtinQuotientEquiv D
        (QuotientGroup.mk' (chapter05NormSubgroup K L) U.uniformizer) =
      chapter05AbelianizationMap (Gal(L / K)) U.arithmeticFrobenius

theorem chapter05FiniteReciprocityNormalization.artin_uniformizer
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L)
    (U : Chapter05UnramifiedExtensionData K L)
    (N : Chapter05FiniteReciprocityNormalization D U) :
    chapter05FiniteArtinMap D U.uniformizer =
      chapter05AbelianizationMap (Gal(L / K)) U.arithmeticFrobenius := by
  simpa [chapter05FiniteArtinMap] using N.quotient_uniformizer

theorem chapter05_unramified_uniformizer_is_arithmetic_frobenius_canonical_map
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L)
    (U : Chapter05UnramifiedExtensionData K L) :
    chapter05FiniteReciprocityMap D U.uniformizer = U.arithmeticFrobenius := by
  sorry

theorem chapter05_unramified_uniformizer_is_arithmetic_frobenius_canonical_artin
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L)
    (U : Chapter05UnramifiedExtensionData K L) :
    chapter05FiniteArtinMap D U.uniformizer =
      chapter05AbelianizationMap (Gal(L / K)) U.arithmeticFrobenius := by
  sorry

theorem chapter05_unramified_uniformizer_is_arithmetic_frobenius
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L)
    (U : Chapter05UnramifiedExtensionData K L)
    (N : Chapter05FiniteReciprocityNormalization D U) :
    chapter05FiniteReciprocityMap D U.uniformizer = U.arithmeticFrobenius := by
  exact chapter05_unramified_uniformizer_is_arithmetic_frobenius_canonical_map D U

theorem chapter05_unramified_uniformizer_is_arithmetic_frobenius_in_abelianization
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L)
    (U : Chapter05UnramifiedExtensionData K L)
    (N : Chapter05FiniteReciprocityNormalization D U) :
    chapter05FiniteArtinMap D U.uniformizer =
    chapter05AbelianizationMap (Gal(L / K)) U.arithmeticFrobenius := by
  exact chapter05_unramified_uniformizer_is_arithmetic_frobenius_canonical_artin D U

structure Chapter05FiniteReciprocityCompatibility
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
  (D : Chapter05LocalClassFormationData K L)
    (e : chapter05NormQuotient K L ≃* Gal(L / K)) where
  /- The finite reciprocity map is already the map obtained from the chosen
     fundamental class.  Compatibility is therefore equality of the induced
     maps on the norm quotient, rather than an uninformative placeholder
     proposition or the stronger definitional equality `e = ...`.  The
     arithmetic-Frobenius clause is kept in the fixed-level structure below:
     it needs an explicit bridge to the independently chosen residue data. -/
  fundamental_class_compatibility :
    e.toMonoidHom.comp (QuotientGroup.mk' (chapter05NormSubgroup K L)) =
      chapter05FiniteReciprocityMap D

structure Chapter05FiniteReciprocityCompatibilityAtUnramified
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L)
    (e : chapter05NormQuotient K L ≃* Gal(L / K))
    (U : Chapter05UnramifiedExtensionData K L) where
  base : Chapter05FiniteReciprocityCompatibility D e
  unramified_frobenius :
    e (QuotientGroup.mk' (chapter05NormSubgroup K L) U.uniformizer) =
      U.arithmeticFrobenius

theorem chapter05_finite_local_reciprocity
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L) :
    ∃! e : chapter05NormQuotient K L ≃* Gal(L / K),
      Chapter05FiniteReciprocityCompatibility D e := by
  sorry

theorem chapter05_finite_local_reciprocity_at_unramified
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L)
    (U : Chapter05UnramifiedExtensionData K L)
    (N : Chapter05FiniteReciprocityNormalization D U) :
    ∃! e : chapter05NormQuotient K L ≃* Gal(L / K),
      Chapter05FiniteReciprocityCompatibilityAtUnramified D e U := by
  sorry

theorem chapter05_finite_local_reciprocity_at_unramified_canonical
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L)
    (U : Chapter05UnramifiedExtensionData K L) :
    ∃! e : chapter05NormQuotient K L ≃* Gal(L / K),
      Chapter05FiniteReciprocityCompatibilityAtUnramified D e U := by
  sorry

/- The source deliberately defers the precise quotient and tower diagrams to
Chapter 9.  The finite-level API above exposes the canonical quotient map and
its kernel; the chain-level uniqueness comparison for arbitrary compatible
maps remains a separate dependency. -/

end

end LastLib.Book05LocalClassFieldTheory.Chapter05
