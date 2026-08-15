import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import LastLib.Book06GlobalClassFieldTheory.Chapter03.Section03LocalNormTests

namespace LastLib.Book06GlobalClassFieldTheory.Chapter03

noncomputable section

open Filter Set
open scoped BigOperators RestrictedProduct IsMulCommutative

/-!
## 3.4. An index preview
-/

/-- The commutator subgroup of the finite Galois group. -/
def chapter03CommutatorSubgroup
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    Subgroup (Gal(L / K)) :=
  commutator (Gal(L / K))

/-- The maximal abelian subfield `L^[G,G]`. -/
abbrev Chapter03MaximalAbelianSubfield
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :=
  LastLib.Book06GlobalClassFieldTheory.Chapter01.globalMaximalAbelianSubextension K L

theorem chapter03_maximalAbelianSubfield_is_fixedField
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    Chapter03MaximalAbelianSubfield K L =
      IntermediateField.fixedField (chapter03CommutatorSubgroup (K := K) (L := L)) :=
  rfl

/-!
### The finite abelian quotient

The map in the next definition is the Artin map after quotienting by the norm subgroup.  The
bijectivity assertion is recorded as a proposition only; its proof belongs to the global
reciprocity/class-formation argument.  The quotient API is made explicit here so later chapters
can use the canonical map rather than restating it.
-/

noncomputable def chapter03ArtinQuotientMap
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (A : Chapter03ArtinReciprocityData N) :
    Chapter03ClassNormQuotient N →* Abelianization (Gal(L / K)) :=
  QuotientGroup.lift (chapter03NormClassSubgroup N) (chapter03ClassArtin A) (by
    exact chapter03_classNorm_range_le_artin_kernel A)

@[simp] theorem chapter03ArtinQuotientMap_mk
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (A : Chapter03ArtinReciprocityData N) (c : Chapter03ClassGroup S_K) :
    chapter03ArtinQuotientMap A
        (QuotientGroup.mk' (chapter03NormClassSubgroup N) c) =
      chapter03ClassArtin A c := by
  rfl

@[simp] theorem chapter03ClassNormQuotient_mk_eq_one_iff
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (c : Chapter03ClassGroup S_K) :
    QuotientGroup.mk' (chapter03NormClassSubgroup N) c = 1 ↔
      c ∈ chapter03NormClassSubgroup N := by
  exact QuotientGroup.eq_one_iff (N := chapter03NormClassSubgroup N) c

def chapter03ClassNormQuotientEquivGalois
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (A : Chapter03ArtinReciprocityData N) :
    Prop :=
  ∃ e : Chapter03ClassNormQuotient N ≃* Abelianization (Gal(L / K)),
    ∀ c : Chapter03ClassGroup S_K,
      e (QuotientGroup.mk' (chapter03NormClassSubgroup N) c) =
        chapter03ClassArtin A c

def chapter03_abelian_classNorm_index_preview
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative (Gal(L / K))]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) :
    Prop :=
  (chapter03NormClassSubgroup N).index = Module.finrank K L

def chapter03_abelian_classNorm_quotient_identified_with_galois
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative (Gal(L / K))]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (A : Chapter03ArtinReciprocityData N) :
    Prop :=
  chapter03ClassNormQuotientEquivGalois A

/-!
### The nonabelian norm-limitation statement

The tower datum is instantiated with `K ⊂ M ⊂ L`, where `M` is the fixed field of the
commutator subgroup.  This packages the two norm maps whose images are compared.
-/

def chapter03_nonabelian_norm_limitation
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {S_K : Chapter03FieldIdeleData K}
    {S_L : Chapter03FieldIdeleData L}
    {S_M : Chapter03FieldIdeleData (Chapter03MaximalAbelianSubfield K L)}
    (T : Chapter03NormTowerData S_K S_M S_L) :
    Prop :=
  chapter03NormClassSubgroup T.norm_L_over_K =
    chapter03NormClassSubgroup T.norm_M_over_K

def chapter03_nonabelian_classNorm_index_preview
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {S_K : Chapter03FieldIdeleData K}
    {S_L : Chapter03FieldIdeleData L}
    {S_M : Chapter03FieldIdeleData (Chapter03MaximalAbelianSubfield K L)}
    (T : Chapter03NormTowerData S_K S_M S_L) :
    Prop :=
  (chapter03NormClassSubgroup T.norm_L_over_K).index =
    Module.finrank K (Chapter03MaximalAbelianSubfield K L)

/-- The element-norm analogue of the idèle-class limitation equality.  The source explicitly
warns that this proposition is false in general, so it is exposed only as a proposition and not
as a theorem.  The valid local norm-limitation theorem belongs to the local-field chapters. -/
def chapter03ElementNormLimitationEquality
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {S_K : Chapter03FieldIdeleData K}
    {S_L : Chapter03FieldIdeleData L}
    {S_M : Chapter03FieldIdeleData (Chapter03MaximalAbelianSubfield K L)}
    (T : Chapter03NormTowerData S_K S_M S_L) : Prop :=
  chapter03ElementNormSubgroup T.norm_L_over_K =
    chapter03ElementNormSubgroup T.norm_M_over_K

end
end LastLib.Book06GlobalClassFieldTheory.Chapter03
