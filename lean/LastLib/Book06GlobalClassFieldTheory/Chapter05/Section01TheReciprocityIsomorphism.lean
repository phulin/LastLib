import LastLib.Book06GlobalClassFieldTheory.Chapter05.Dependencies

namespace LastLib.Book06GlobalClassFieldTheory.Chapter05

noncomputable section

/-! ## 5.1. The reciprocity isomorphism -/

open scoped IsMulCommutative
open scoped BigOperators

universe uK uL uI uI' uC uC'

variable {K : Type uK} {L : Type uL}
variable {I_K : Type uI} {I_L : Type uI'} {C_K : Type uC} {C_L : Type uC'}
variable [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
variable [CommGroup I_K] [CommGroup I_L] [CommGroup C_K] [CommGroup C_L]
variable [FiniteDimensional K L]

/-- The cap-product form of finite global reciprocity. -/
noncomputable def chapter05_finite_global_reciprocity_cap_product
    [IsGalois K L]
    (X : Chapter05ClassFormationInput K L I_K I_L C_K C_L) :
    Abelianization (Gal(L / K)) ≃*
      C_K ⧸ chapter05InputNormSubgroup X :=
  chapter05InputCapProductEquiv X

/-- The canonical quotient projection followed by the inverse cap-product map. -/
theorem chapter05_finite_global_reciprocity_global_artin
    [IsGalois K L]
    (X : Chapter05ClassFormationInput K L I_K I_L C_K C_L) :
    chapter05InputGlobalArtin X =
      (chapter05InputCapProductEquiv X).symm.toMonoidHom.comp
        (chapter05InputClassNormQuotientMap X) := by
  rfl

/-- The degree-zero cap-product map has exactly the idelic norm subgroup as its kernel. -/
theorem chapter05_finite_global_reciprocity_kernel
    [IsGalois K L]
    (X : Chapter05ClassFormationInput K L I_K I_L C_K C_L) :
    (chapter05InputGlobalArtin X).ker = chapter05InputNormSubgroup X := by
  exact chapter05_input_global_artin_ker X

/-- Finite global reciprocity is surjective at the finite Galois level. -/
theorem chapter05_finite_global_reciprocity_surjective
    [IsGalois K L]
    (X : Chapter05ClassFormationInput K L I_K I_L C_K C_L) :
    Function.Surjective (chapter05InputGlobalArtin X) := by
  exact chapter05_input_global_artin_surjective X

/-- The norm quotient has the order of the abelianized Galois group. -/
theorem chapter05_finite_global_reciprocity_index
    [IsGalois K L]
    (X : Chapter05ClassFormationInput K L I_K I_L C_K C_L) :
    Nat.card (C_K ⧸ chapter05InputNormSubgroup X) =
      Nat.card (Abelianization (Gal(L / K))) := by
  exact chapter05_input_norm_quotient_card X

/-- Idelic norm limitation: the norm subgroup for a finite Galois level is
unchanged after replacing the level by the fixed field of the commutator
subgroup, once the two local quotient maps are identified. -/
theorem chapter05_idelic_norm_limitation
    {Q : Type*} [CommGroup Q]
    (D : Chapter05NormLimitationData C_K Q) :
    D.normSubgroupL = D.normSubgroupM := by
  exact chapter05_norm_limitation D

/-- For an abelian extension, the abelianized target can be identified with the
actual Galois group.  The local class-field-theory layer supplies this
identification without changing the arithmetic Frobenius convention. -/
noncomputable def chapter05_finite_global_reciprocity_abelian_equiv
    [IsAbelianGalois K L]
    (X : Chapter05ClassFormationInput K L I_K I_L C_K C_L) :
    (C_K ⧸ chapter05InputNormSubgroup X) ≃* Gal(L / K) :=
  (chapter05InputCapProductEquiv X).symm.trans
    (Abelianization.equivOfComm (H := Gal(L / K))).symm

noncomputable def chapter05_finite_global_reciprocity_abelian
    [IsAbelianGalois K L]
    (X : Chapter05ClassFormationInput K L I_K I_L C_K C_L) :
    (C_K ⧸ chapter05InputNormSubgroup X) ≃* Gal(L / K) :=
  chapter05_finite_global_reciprocity_abelian_equiv X

/-! The abelian specialization is also exposed as a map on the idele class
group itself, with the quotient projection made explicit. -/
noncomputable def chapter05_finite_global_reciprocity_abelian_artin
    [IsAbelianGalois K L]
    (X : Chapter05ClassFormationInput K L I_K I_L C_K C_L) :
    C_K →* Gal(L / K) :=
  (chapter05_finite_global_reciprocity_abelian X).toMonoidHom.comp
    (chapter05InputClassNormQuotientMap X)

theorem chapter05_finite_global_reciprocity_abelian_artin_kernel
    [IsAbelianGalois K L]
    (X : Chapter05ClassFormationInput K L I_K I_L C_K C_L) :
    (chapter05_finite_global_reciprocity_abelian_artin X).ker =
      chapter05InputNormSubgroup X := by
  rw [chapter05_finite_global_reciprocity_abelian_artin,
    MonoidHom.ker_comp_of_injective _ _
      (chapter05_finite_global_reciprocity_abelian X).injective,
    chapter05InputClassNormQuotientMap, QuotientGroup.ker_mk']

/-- In the abelian case the norm quotient has the degree of the extension. -/
theorem chapter05_finite_global_reciprocity_abelian_index
    [IsAbelianGalois K L]
    (X : Chapter05ClassFormationInput K L I_K I_L C_K C_L) :
    Nat.card (C_K ⧸ chapter05InputNormSubgroup X) = Module.finrank K L := by
  rw [chapter05_finite_global_reciprocity_index X]
  exact (Nat.card_congr
      (Abelianization.equivOfComm (H := Gal(L / K))).toEquiv.symm).trans
    (IsGalois.card_aut_eq_finrank K L)

/-- The local product identifies with the global Artin map once its class map
is the degree-zero cap-product map. -/
theorem chapter05_finite_global_artin_product
    {V : Type*} {U : V → Type*}
    [∀ v, CommGroup (U v)]
    [IsGalois K L]
    (X : Chapter05ClassFormationInput K L I_K I_L C_K C_L)
    (D : Chapter05LocalArtinFamily I_K C_K V U
      (Abelianization (Gal(L / K))))
    (hclass : D.classMap = X.classMapK)
    (hglobal : D.globalArtin = chapter05InputGlobalArtin X) :
    ∀ x : I_K, ∃ s : Finset V,
      (∀ v ∉ s, D.localArtin v (D.component v x) = 1) ∧
        chapter05InputGlobalArtin X (X.classMapK x) =
          ∏ v ∈ s, D.localArtin v (D.component v x) := by
  intro x
  obtain ⟨s, hs, hprod⟩ := D.finite_product x
  refine ⟨s, hs, ?_⟩
  rw [← hglobal, ← hclass]
  exact hprod

end

end LastLib.Book06GlobalClassFieldTheory.Chapter05
