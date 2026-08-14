import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Notation
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.NumberField.Basic

namespace LastLib.Book06GlobalClassFieldTheory.Chapter05

noncomputable section

open scoped BigOperators

/-!
Shared interfaces for finite global reciprocity.

The preceding adele and local class-field-theory chapters expose canonical
restricted-product, norm, and local reciprocity interfaces.  The structures
below are deliberately small comparison interfaces for those outputs: an
idele class group, an idele norm, local components, and the degree-zero
cap-product calculation.  They are not intended to replace the canonical
number-field constructions; the reconciliation bridge is recorded explicitly
where a canonical earlier interface is not yet multiplicatively identified.

DEPENDENCY_GUESS: `Chapter05ClassFormationInput` is the book-facing form of
the degree-zero specialization of the Chapter 4 class-formation lemma.  When
the earlier chapters are reconciled, its `classFormation` field should be
replaced by the canonical fundamental-class/cap-product interface.

DEPENDENCY_GUESS: `Chapter05LocalArtinFamily` is the bridge expected from the
local reciprocity and idele chapters.  In particular, `component` and
`classMap` should become the canonical restricted-product projections and
idele-class quotient map exposed there.
-/

universe uK uL uI uI' uC uC' uG uQ uV uU

/-- A bijective group homomorphism packaged as a multiplicative equivalence. -/
def chapter05MulEquivOfBijective
    {G : Type uG} {H : Type uQ} [Group G] [CommGroup H]
    (f : G →* H) (hf : Function.Bijective f) : G ≃* H where
  toFun := f
  invFun := (Equiv.ofBijective f hf).invFun
  left_inv := (Equiv.ofBijective f hf).left_inv
  right_inv := (Equiv.ofBijective f hf).right_inv
  map_mul' := f.map_mul

/-- The degree-zero cap-product interface supplied by a class formation. -/
structure Chapter05ClassFormationInterface
    (G : Type uG) (Q : Type uQ) [Group G] [CommGroup Q] where
  capProduct : Abelianization G →* Q
  capProduct_bijective : Function.Bijective capProduct

/-- An abstract presentation of the idele class quotient `I/Kˣ`. -/
def chapter05PrincipalIdeleSubgroup
    {K : Type uK} {I : Type uI} [Field K] [CommGroup I]
    (principal : Kˣ →* I) : Subgroup I :=
  Subgroup.map principal ⊤

abbrev chapter05IdeleClassGroup
    {K : Type uK} {I : Type uI} [Field K] [CommGroup I]
    (principal : Kˣ →* I) : Type uI :=
  I ⧸ chapter05PrincipalIdeleSubgroup principal

def chapter05IdeleClassMap
    {K : Type uK} {I : Type uI} [Field K] [CommGroup I]
    (principal : Kˣ →* I) : I →* chapter05IdeleClassGroup principal :=
  QuotientGroup.mk' (chapter05PrincipalIdeleSubgroup principal)

@[simp]
theorem chapter05_idele_class_map_principal
    {K : Type uK} {I : Type uI} [Field K] [CommGroup I]
    (principal : Kˣ →* I) (a : Kˣ) :
    chapter05IdeleClassMap principal (principal a) = 1 := by
  change QuotientGroup.mk' (chapter05PrincipalIdeleSubgroup principal) (principal a) = 1
  exact (QuotientGroup.eq_one_iff
    (N := chapter05PrincipalIdeleSubgroup principal) (principal a)).2
      ⟨a, by simp, rfl⟩

theorem chapter05_idele_class_eq_iff
    {K : Type uK} {I : Type uI} [Field K] [CommGroup I]
    (principal : Kˣ →* I) (x y : I) :
    chapter05IdeleClassMap principal x = chapter05IdeleClassMap principal y ↔
      x * y⁻¹ ∈ chapter05PrincipalIdeleSubgroup principal := by
  change QuotientGroup.mk' (chapter05PrincipalIdeleSubgroup principal) x =
    QuotientGroup.mk' (chapter05PrincipalIdeleSubgroup principal) y ↔ _
  rw [← QuotientGroup.eq_one_iff (N := chapter05PrincipalIdeleSubgroup principal)
    (x * y⁻¹)]
  simp only [QuotientGroup.mk'_apply]
  exact (mul_inv_eq_one :
    (QuotientGroup.mk' (chapter05PrincipalIdeleSubgroup principal) x) *
        (QuotientGroup.mk' (chapter05PrincipalIdeleSubgroup principal) y)⁻¹ = 1 ↔ _).symm

/-- The abstract norm and quotient maps used to compare two idele class groups. -/
structure Chapter05IdeleNormData
    (I_K : Type uI) (I_L : Type uI') (C_K : Type uC) (C_L : Type uC')
    [CommGroup I_K] [CommGroup I_L] [CommGroup C_K] [CommGroup C_L] where
  ideleNorm : I_L →* I_K
  classNorm : C_L →* C_K
  classMapK : I_K →* C_K
  classMapL : I_L →* C_L
  norm_class_commutes : classNorm.comp classMapL = classMapK.comp ideleNorm

def chapter05ClassNormSubgroup
    {I_K : Type uI} {I_L : Type uI'} {C_K : Type uC} {C_L : Type uC'}
    [CommGroup I_K] [CommGroup I_L] [CommGroup C_K] [CommGroup C_L]
    (N : Chapter05IdeleNormData I_K I_L C_K C_L) : Subgroup C_K :=
  Subgroup.map N.classNorm ⊤

def chapter05ClassNormQuotient
    {I_K : Type uI} {I_L : Type uI'} {C_K : Type uC} {C_L : Type uC'}
    [CommGroup I_K] [CommGroup I_L] [CommGroup C_K] [CommGroup C_L]
    (N : Chapter05IdeleNormData I_K I_L C_K C_L) : Type uC :=
  C_K ⧸ chapter05ClassNormSubgroup N

theorem chapter05_class_norm_mem_iff
    {I_K : Type uI} {I_L : Type uI'} {C_K : Type uC} {C_L : Type uC'}
    [CommGroup I_K] [CommGroup I_L] [CommGroup C_K] [CommGroup C_L]
    (N : Chapter05IdeleNormData I_K I_L C_K C_L) (c : C_K) :
    c ∈ chapter05ClassNormSubgroup N ↔ ∃ y : C_L, N.classNorm y = c := by
  rw [chapter05ClassNormSubgroup, Subgroup.mem_map]
  constructor
  · rintro ⟨y, _, hy⟩
    exact ⟨y, hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, trivial, hy⟩

theorem chapter05_norm_class_commutes
    {I_K : Type uI} {I_L : Type uI'} {C_K : Type uC} {C_L : Type uC'}
    [CommGroup I_K] [CommGroup I_L] [CommGroup C_K] [CommGroup C_L]
    (N : Chapter05IdeleNormData I_K I_L C_K C_L) (x : I_L) :
    N.classNorm (N.classMapL x) = N.classMapK (N.ideleNorm x) := by
  simpa [MonoidHom.comp_apply] using DFunLike.congr_fun N.norm_class_commutes x

/-- The finite-Galois data needed for the degree-zero global class formation. -/
structure Chapter05ClassFormationInput
    (K : Type uK) (L : Type uL)
    (I_K : Type uI) (I_L : Type uI') (C_K : Type uC) (C_L : Type uC')
    [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    [CommGroup I_K] [CommGroup I_L] [CommGroup C_K] [CommGroup C_L]
    [FiniteDimensional K L] [IsGalois K L] where
  ideleNorm : I_L →* I_K
  classNorm : C_L →* C_K
  classMapK : I_K →* C_K
  classMapL : I_L →* C_L
  norm_class_commutes : classNorm.comp classMapL = classMapK.comp ideleNorm
  classFormation :
    Chapter05ClassFormationInterface (Gal(L / K))
      (C_K ⧸ Subgroup.map classNorm ⊤)

def chapter05InputNormSubgroup
    {K : Type uK} {L : Type uL}
    {I_K : Type uI} {I_L : Type uI'} {C_K : Type uC} {C_L : Type uC'}
    [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    [CommGroup I_K] [CommGroup I_L] [CommGroup C_K] [CommGroup C_L]
    [FiniteDimensional K L] [IsGalois K L]
    (X : Chapter05ClassFormationInput K L I_K I_L C_K C_L) : Subgroup C_K :=
  Subgroup.map X.classNorm ⊤

def chapter05InputCapProductEquiv
    {K : Type uK} {L : Type uL}
    {I_K : Type uI} {I_L : Type uI'} {C_K : Type uC} {C_L : Type uC'}
    [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    [CommGroup I_K] [CommGroup I_L] [CommGroup C_K] [CommGroup C_L]
    [FiniteDimensional K L] [IsGalois K L]
    (X : Chapter05ClassFormationInput K L I_K I_L C_K C_L) :
    Abelianization (Gal(L / K)) ≃*
      C_K ⧸ chapter05InputNormSubgroup X := by
  exact chapter05MulEquivOfBijective X.classFormation.capProduct
    X.classFormation.capProduct_bijective

def chapter05InputClassNormQuotientMap
    {K : Type uK} {L : Type uL}
    {I_K : Type uI} {I_L : Type uI'} {C_K : Type uC} {C_L : Type uC'}
    [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    [CommGroup I_K] [CommGroup I_L] [CommGroup C_K] [CommGroup C_L]
    [FiniteDimensional K L] [IsGalois K L]
    (X : Chapter05ClassFormationInput K L I_K I_L C_K C_L) :
    C_K →* C_K ⧸ chapter05InputNormSubgroup X :=
  QuotientGroup.mk' (chapter05InputNormSubgroup X)

noncomputable def chapter05InputGlobalArtin
    {K : Type uK} {L : Type uL}
    {I_K : Type uI} {I_L : Type uI'} {C_K : Type uC} {C_L : Type uC'}
    [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    [CommGroup I_K] [CommGroup I_L] [CommGroup C_K] [CommGroup C_L]
    [FiniteDimensional K L] [IsGalois K L]
    (X : Chapter05ClassFormationInput K L I_K I_L C_K C_L) :
    C_K →* Abelianization (Gal(L / K)) :=
  (chapter05InputCapProductEquiv X).symm.toMonoidHom.comp
    (chapter05InputClassNormQuotientMap X)

noncomputable def chapter05InputIdeleArtin
    {K : Type uK} {L : Type uL}
    {I_K : Type uI} {I_L : Type uI'} {C_K : Type uC} {C_L : Type uC'}
    [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    [CommGroup I_K] [CommGroup I_L] [CommGroup C_K] [CommGroup C_L]
    [FiniteDimensional K L] [IsGalois K L]
    (X : Chapter05ClassFormationInput K L I_K I_L C_K C_L) :
    I_K →* Abelianization (Gal(L / K)) :=
  (chapter05InputGlobalArtin X).comp X.classMapK

theorem chapter05_input_global_artin_ker
    {K : Type uK} {L : Type uL}
    {I_K : Type uI} {I_L : Type uI'} {C_K : Type uC} {C_L : Type uC'}
    [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    [CommGroup I_K] [CommGroup I_L] [CommGroup C_K] [CommGroup C_L]
    [FiniteDimensional K L] [IsGalois K L]
    (X : Chapter05ClassFormationInput K L I_K I_L C_K C_L) :
    (chapter05InputGlobalArtin X).ker = chapter05InputNormSubgroup X := by
  rw [chapter05InputGlobalArtin,
    MonoidHom.ker_comp_of_injective _ _ (chapter05InputCapProductEquiv X).symm.injective,
    chapter05InputClassNormQuotientMap, QuotientGroup.ker_mk']

theorem chapter05_input_global_artin_surjective
    {K : Type uK} {L : Type uL}
    {I_K : Type uI} {I_L : Type uI'} {C_K : Type uC} {C_L : Type uC'}
    [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    [CommGroup I_K] [CommGroup I_L] [CommGroup C_K] [CommGroup C_L]
    [FiniteDimensional K L] [IsGalois K L]
    (X : Chapter05ClassFormationInput K L I_K I_L C_K C_L) :
    Function.Surjective (chapter05InputGlobalArtin X) := by
  exact (chapter05InputCapProductEquiv X).symm.surjective.comp
    (QuotientGroup.mk'_surjective _)

theorem chapter05_input_norm_quotient_card
    {K : Type uK} {L : Type uL}
    {I_K : Type uI} {I_L : Type uI'} {C_K : Type uC} {C_L : Type uC'}
    [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    [CommGroup I_K] [CommGroup I_L] [CommGroup C_K] [CommGroup C_L]
    [FiniteDimensional K L] [IsGalois K L]
    (X : Chapter05ClassFormationInput K L I_K I_L C_K C_L) :
    Nat.card (C_K ⧸ chapter05InputNormSubgroup X) =
      Nat.card (Abelianization (Gal(L / K))) := by
  exact Nat.card_congr (chapter05InputCapProductEquiv X).toEquiv.symm

/-
DEPENDENCY_GUESS: `Chapter05NormLimitationData` stands for the canonical
comparison between the level `L` and the commutator fixed field
`L^[G, G]`.  The two quotient maps, and their identification, should later
be supplied by the reconciled class-formation and local-compatibility
interfaces.
-/
/-- A norm-limitation comparison: the two levels have quotient maps into a
  common target, and the local comparison identifies those maps.  Equality of
  the two norm kernels is the resulting conclusion. -/
structure Chapter05NormLimitationData
    (C : Type uC) (Q : Type uQ) [CommGroup C] [CommGroup Q] where
  normSubgroupL : Subgroup C
  normSubgroupM : Subgroup C
  quotientL : C →* Q
  quotientM : C →* Q
  quotient_maps_agree : quotientL = quotientM
  quotientL_kernel : quotientL.ker = normSubgroupL
  quotientM_kernel : quotientM.ker = normSubgroupM

theorem chapter05_norm_limitation
    {C : Type uC} {Q : Type uQ} [CommGroup C] [CommGroup Q]
    (D : Chapter05NormLimitationData C Q) :
    D.normSubgroupL = D.normSubgroupM := by
  rw [← D.quotientL_kernel, ← D.quotientM_kernel, D.quotient_maps_agree]

/-- A local multiplicative group, its units, and its local Artin map. -/
structure Chapter05LocalArtinFamily
    (I : Type uI) (C : Type uC) (V : Type uV) (U : V → Type uU) (G : Type uG)
    [CommGroup I] [CommGroup C] [∀ v, CommGroup (U v)] [CommGroup G] where
  classMap : I →* C
  component : ∀ v, I →* U v
  localIdele : ∀ v, U v →* I
  localIdele_component : ∀ v u, component v (localIdele v u) = u
  localArtin : ∀ v, U v →* G
  decomposition : ∀ _v, Subgroup G
  inertia : ∀ _v, Subgroup G
  units : ∀ v, Subgroup (U v)
  decomposition_eq_range :
    ∀ v, Subgroup.map (localArtin v) ⊤ = decomposition v
  inertia_eq_units_range :
    ∀ v, Subgroup.map (localArtin v) (units v) = inertia v
  globalArtin : C →* G
  globalArtin_localIdele :
    ∀ v u, globalArtin (classMap (localIdele v u)) = localArtin v u
  ramification : Finset V
  local_units_killed_outside_ramification :
    ∀ {v}, v ∉ ramification → ∀ u, u ∈ units v → localArtin v u = 1
  finite_product :
    ∀ x : I, ∃ s : Finset V,
      (∀ v ∉ s, localArtin v (component v x) = 1) ∧
        globalArtin (classMap x) =
          ∏ v ∈ s, localArtin v (component v x)

theorem chapter05_local_artin_range_decomposition
    {I : Type uI} {C : Type uC} {V : Type uV} {U : V → Type uU} {G : Type uG}
    [CommGroup I] [CommGroup C] [∀ v, CommGroup (U v)] [CommGroup G]
    (D : Chapter05LocalArtinFamily I C V U G) (v : V) :
    Subgroup.map (D.localArtin v) ⊤ = D.decomposition v := by
  exact D.decomposition_eq_range v

theorem chapter05_local_artin_range_inertia
    {I : Type uI} {C : Type uC} {V : Type uV} {U : V → Type uU} {G : Type uG}
    [CommGroup I] [CommGroup C] [∀ v, CommGroup (U v)] [CommGroup G]
    (D : Chapter05LocalArtinFamily I C V U G) (v : V) :
    Subgroup.map (D.localArtin v) (D.units v) = D.inertia v := by
  exact D.inertia_eq_units_range v

theorem chapter05_local_artin_product_finite
    {I : Type uI} {C : Type uC} {V : Type uV} {U : V → Type uU} {G : Type uG}
    [CommGroup I] [CommGroup C] [∀ v, CommGroup (U v)] [CommGroup G]
    (D : Chapter05LocalArtinFamily I C V U G) (x : I) :
    ∃ s : Finset V,
      (∀ v ∉ s, D.localArtin v (D.component v x) = 1) ∧
        D.globalArtin (D.classMap x) =
          ∏ v ∈ s, D.localArtin v (D.component v x) := by
  exact D.finite_product x

theorem chapter05_local_units_killed_outside_ramification
    {I : Type uI} {C : Type uC} {V : Type uV} {U : V → Type uU} {G : Type uG}
    [CommGroup I] [CommGroup C] [∀ v, CommGroup (U v)] [CommGroup G]
    (D : Chapter05LocalArtinFamily I C V U G) {v : V}
    (hv : v ∉ D.ramification) (u : U v) (hu : u ∈ D.units v) :
    D.localArtin v u = 1 := by
  exact D.local_units_killed_outside_ramification hv u hu

theorem chapter05_global_artin_local_units_killed_outside_ramification
    {I : Type uI} {C : Type uC} {V : Type uV} {U : V → Type uU} {G : Type uG}
    [CommGroup I] [CommGroup C] [∀ v, CommGroup (U v)] [CommGroup G]
    (D : Chapter05LocalArtinFamily I C V U G) {v : V}
    (hv : v ∉ D.ramification) (u : U v) (hu : u ∈ D.units v) :
    D.globalArtin (D.classMap (D.localIdele v u)) = 1 := by
  rw [D.globalArtin_localIdele, D.local_units_killed_outside_ramification hv u hu]

/-- The unit filtration `U⁰ = Oᵥˣ`, `Uⁿ = 1 + 𝔭ᵥⁿ` abstracted from its local ring. -/
structure Chapter05UnitFiltration (U : Type uU) [CommGroup U] where
  units : Subgroup U
  level : ℕ → Subgroup U
  level_zero : level 0 = units
  descending : ∀ {m n : ℕ}, m ≤ n → level n ≤ level m

theorem chapter05_unit_filtration_descending
    {U : Type uU} [CommGroup U] (F : Chapter05UnitFiltration U)
    {m n : ℕ} (hmn : m ≤ n) : F.level n ≤ F.level m := by
  exact F.descending hmn

end

end LastLib.Book06GlobalClassFieldTheory.Chapter05
