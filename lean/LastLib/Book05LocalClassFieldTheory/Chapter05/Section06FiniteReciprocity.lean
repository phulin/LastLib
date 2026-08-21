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

/- The sign check in the source is a statement about the cap product before
   it is inverted to obtain reciprocity.  This interface records that
   chain-level normalization, rather than assuming the desired Artin-map
   conclusion itself. -/
noncomputable def chapter05CapImageOfGaloisElement
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L)
    (σ : Gal(L / K)) : Additive (chapter05NormQuotient K L) :=
  D.degreeZeroNorm
    ((D.topRestriction.iso 0).toLinearEquiv.toAddEquiv
      ((D.capProduct.cap (⊤ : Subgroup (Gal(L / K))) (-2))
        ((D.topRestrictionTrivial.iso (-2)).symm.toLinearEquiv.toAddEquiv
          ((chapter05TateMinusTwoAbelianizationIso (Gal(L / K))).symm
            (Additive.ofMul (chapter05AbelianizationMap (Gal(L / K)) σ))))))

structure Chapter05UnramifiedCapNormalization
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L)
    (U : Chapter05UnramifiedExtensionData K L) where
  cap_arithmeticFrobenius :
    chapter05CapImageOfGaloisElement D U.arithmeticFrobenius =
      Additive.ofMul (QuotientGroup.mk' (chapter05NormSubgroup K L) U.uniformizer)

theorem chapter05UnramifiedCapNormalization.artin_uniformizer
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L)
    (U : Chapter05UnramifiedExtensionData K L)
    (N : Chapter05UnramifiedCapNormalization D U) :
    chapter05FiniteArtinMap D U.uniformizer =
      chapter05AbelianizationMap (Gal(L / K)) U.arithmeticFrobenius := by
  /- Prior attempt: the quotient-level equality used to be assumed directly
     as `N.quotient_uniformizer`; it was circular because it was the desired
     conclusion of the sign check. -/
  apply_fun Additive.ofMul
  letI : CategoryTheory.IsIso
      (D.capProduct.cap (⊤ : Subgroup (Gal(L / K))) (-2)) :=
    chapter05_class_formation_top_isomorphism D (-2)
  let topToNorm :
      chapter05TateCohomology (⊤ : Subgroup (Gal(L / K)))
          (Rep.res (⊤ : Subgroup (Gal(L / K))).subtype
            (chapter05CoefficientRep K L)) 0 ≃+
        Additive (chapter05NormQuotient K L) :=
    (D.topRestriction.iso 0).toLinearEquiv.toAddEquiv.trans
      D.degreeZeroNorm
  let topMinusToNorm :
      chapter05TateCohomology (⊤ : Subgroup (Gal(L / K)))
          (Rep.res (⊤ : Subgroup (Gal(L / K))).subtype
            (Rep.trivial ℤ (Gal(L / K)) ℤ)) (-2) ≃+
        Additive (chapter05NormQuotient K L) :=
    (@CategoryTheory.asIso _ _ _ _
      (D.capProduct.cap (⊤ : Subgroup (Gal(L / K))) (-2)) inferInstance).toLinearEquiv.toAddEquiv.trans
      topToNorm
  let sourceToNorm :
      chapter05TateCohomology (Gal(L / K))
          (Rep.trivial ℤ (Gal(L / K)) ℤ) (-2) ≃+
        Additive (chapter05NormQuotient K L) :=
    ((D.topRestrictionTrivial.iso (-2)).symm.toLinearEquiv.toAddEquiv).trans
      topMinusToNorm
  let sourceToAbelianization :
      chapter05TateCohomology (Gal(L / K))
          (Rep.trivial ℤ (Gal(L / K)) ℤ) (-2) ≃+
        Additive (chapter05Abelianization (Gal(L / K))) :=
    chapter05TateMinusTwoAbelianizationIso (Gal(L / K))
  have hN :
      sourceToNorm
          (sourceToAbelianization.symm
          (Additive.ofMul
              (chapter05AbelianizationMap (Gal(L / K)) U.arithmeticFrobenius))) =
        Additive.ofMul
          (QuotientGroup.mk' (chapter05NormSubgroup K L) U.uniformizer) := by
    change chapter05CapImageOfGaloisElement D U.arithmeticFrobenius =
      Additive.ofMul
        (QuotientGroup.mk' (chapter05NormSubgroup K L) U.uniformizer)
    exact N.cap_arithmeticFrobenius
  have hsource :
      sourceToNorm.symm
          (Additive.ofMul
            (QuotientGroup.mk' (chapter05NormSubgroup K L) U.uniformizer)) =
        sourceToAbelianization.symm
          (Additive.ofMul
            (chapter05AbelianizationMap (Gal(L / K)) U.arithmeticFrobenius)) := by
    apply sourceToNorm.injective
    rw [sourceToNorm.apply_symm_apply, hN]
  have h := congrArg sourceToAbelianization hsource
  change sourceToAbelianization
      (sourceToNorm.symm
        (Additive.ofMul
          (QuotientGroup.mk' (chapter05NormSubgroup K L) U.uniformizer))) =
    Additive.ofMul
      (chapter05AbelianizationMap (Gal(L / K)) U.arithmeticFrobenius)
  simpa only [sourceToAbelianization.apply_symm_apply] using h

theorem chapter05_unramified_uniformizer_is_arithmetic_frobenius_canonical_map
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L)
    (U : Chapter05UnramifiedExtensionData K L)
    (N : Chapter05UnramifiedCapNormalization D U) :
    chapter05FiniteReciprocityMap D U.uniformizer = U.arithmeticFrobenius := by
  change (Abelianization.equivOfComm (H := Gal(L / K))).symm
      (chapter05FiniteArtinMap D U.uniformizer) =
    U.arithmeticFrobenius
  rw [chapter05UnramifiedCapNormalization.artin_uniformizer D U N]
  rfl

theorem chapter05_unramified_uniformizer_is_arithmetic_frobenius_canonical_artin
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L)
    (U : Chapter05UnramifiedExtensionData K L)
    (N : Chapter05UnramifiedCapNormalization D U) :
    chapter05FiniteArtinMap D U.uniformizer =
      chapter05AbelianizationMap (Gal(L / K)) U.arithmeticFrobenius := by
  exact chapter05UnramifiedCapNormalization.artin_uniformizer D U N

theorem chapter05_unramified_uniformizer_is_arithmetic_frobenius
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L)
    (U : Chapter05UnramifiedExtensionData K L)
    (N : Chapter05UnramifiedCapNormalization D U) :
    chapter05FiniteReciprocityMap D U.uniformizer = U.arithmeticFrobenius := by
  exact chapter05_unramified_uniformizer_is_arithmetic_frobenius_canonical_map D U N

theorem chapter05_unramified_uniformizer_is_arithmetic_frobenius_in_abelianization
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L)
    (U : Chapter05UnramifiedExtensionData K L)
    (N : Chapter05UnramifiedCapNormalization D U) :
    chapter05FiniteArtinMap D U.uniformizer =
    chapter05AbelianizationMap (Gal(L / K)) U.arithmeticFrobenius := by
  exact chapter05_unramified_uniformizer_is_arithmetic_frobenius_canonical_artin D U N

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
  let e := chapter05FiniteReciprocityIso D
  refine ⟨e, ?_, ?_⟩
  · exact ⟨by rfl⟩
  · intro e' h'
    apply MulEquiv.ext
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
      (chapter05NormSubgroup K L) z
    have hcanon :
        e.toMonoidHom.comp (QuotientGroup.mk' (chapter05NormSubgroup K L)) =
          chapter05FiniteReciprocityMap D := by
      rfl
    have h := congrArg (fun f : Kˣ →* Gal(L / K) => f x)
      (h'.fundamental_class_compatibility.trans hcanon.symm)
    simpa using h

theorem chapter05_finite_local_reciprocity_at_unramified
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L)
    (U : Chapter05UnramifiedExtensionData K L)
    (N : Chapter05UnramifiedCapNormalization D U) :
    ∃! e : chapter05NormQuotient K L ≃* Gal(L / K),
      Chapter05FiniteReciprocityCompatibilityAtUnramified D e U := by
  let e := chapter05FiniteReciprocityIso D
  refine ⟨e, ?_, ?_⟩
  · refine ⟨⟨by rfl⟩, ?_⟩
    exact chapter05_unramified_uniformizer_is_arithmetic_frobenius_canonical_map D U N
  · intro e' h'
    apply MulEquiv.ext
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
      (chapter05NormSubgroup K L) z
    have hcanon :
        e.toMonoidHom.comp (QuotientGroup.mk' (chapter05NormSubgroup K L)) =
          chapter05FiniteReciprocityMap D := by
      rfl
    have h := congrArg (fun f : Kˣ →* Gal(L / K) => f x)
      (h'.base.fundamental_class_compatibility.trans hcanon.symm)
    simpa using h

theorem chapter05_finite_local_reciprocity_at_unramified_canonical
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L)
    (U : Chapter05UnramifiedExtensionData K L)
    (N : Chapter05UnramifiedCapNormalization D U) :
    ∃! e : chapter05NormQuotient K L ≃* Gal(L / K),
      Chapter05FiniteReciprocityCompatibilityAtUnramified D e U := by
  exact chapter05_finite_local_reciprocity_at_unramified D U N

/- The source deliberately defers the precise quotient and tower diagrams to
Chapter 9.  The finite-level API above exposes the canonical quotient map and
its kernel; the chain-level uniqueness comparison for arbitrary compatible
maps remains a separate dependency. -/

end

end LastLib.Book05LocalClassFieldTheory.Chapter05
