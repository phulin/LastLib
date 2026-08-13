import Mathlib.FieldTheory.Galois.Abelian
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.Section02FrobeniusInAnUnramifiedExtension
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Valuation.Extension
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
  sorry

theorem chapter05FiniteReciprocityMap_surjective
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L) :
    Function.Surjective (chapter05FiniteReciprocityMap D) := by
  sorry

/- The local-field input is carried by the earlier valuation and residue-field
interfaces.  In particular, the reduction equivalence is part of the data, so
the Frobenius used below cannot be an unrelated generator of an abstract
cyclic group. -/
structure Chapter05UnramifiedExtensionData
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))] where
  valuationK : Valuation K ℤᵐ⁰
  valuationL : Valuation L ℤᵐ⁰
  [valuationKDiscrete : Valuation.IsRankOneDiscrete valuationK]
  [valuationLDiscrete : Valuation.IsRankOneDiscrete valuationL]
  [valuationExtension : valuationK.HasExtension valuationL]
  uniformizer : Kˣ
  uniformizer_is_uniformizer :
    valuationK.IsUniformizer (uniformizer : K)
  residueBase : Type
  residueExtension : Type
  [residueBaseField : Field residueBase]
  [residueExtensionField : Field residueExtension]
  [residueFintype : Fintype residueBase]
  [residueFinite : Finite residueExtension]
  [residueAlgebra : Algebra residueBase residueExtension]
  [residueAlgebraic : Algebra.IsAlgebraic residueBase residueExtension]
  [residueFiniteDimensional : FiniteDimensional residueBase residueExtension]
  [residueGalois : IsGalois residueBase residueExtension]
  reduction :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.Chapter06UnramifiedGaloisReduction
      K L residueBase residueExtension

noncomputable def Chapter05UnramifiedExtensionData.arithmeticFrobenius
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (U : Chapter05UnramifiedExtensionData K L) : Gal(L / K) := by
  letI : Field U.residueBase := U.residueBaseField
  letI : Field U.residueExtension := U.residueExtensionField
  letI : Fintype U.residueBase := U.residueFintype
  letI : Finite U.residueExtension := U.residueFinite
  letI : Algebra U.residueBase U.residueExtension := U.residueAlgebra
  letI : Algebra.IsAlgebraic U.residueBase U.residueExtension := U.residueAlgebraic
  letI : FiniteDimensional U.residueBase U.residueExtension :=
    U.residueFiniteDimensional
  letI : IsGalois U.residueBase U.residueExtension := U.residueGalois
  exact
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.chapter06UnramifiedArithmeticFrobenius
    U.reduction

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
  /- The finite reciprocity map is already the map obtained from the chosen
     fundamental class.  Compatibility is therefore equality of the induced
     maps on the norm quotient, rather than an uninformative placeholder
     proposition or the stronger definitional equality `e = ...`. -/
  fundamental_class_compatibility :
    e.toMonoidHom.comp (QuotientGroup.mk' (chapter05NormSubgroup K L)) =
      chapter05FiniteReciprocityMap D
  unramified_frobenius : ∀ U : Chapter05UnramifiedExtensionData K L,
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

/- The source deliberately defers the precise quotient and tower diagrams to
Chapter 9.  The finite-level API above exposes the canonical quotient map and
its kernel; the chain-level uniqueness comparison for arbitrary compatible
maps remains a separate dependency. -/

end

end LastLib.Book05LocalClassFieldTheory.Chapter05
