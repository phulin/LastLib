import LastLib.Book06GlobalClassFieldTheory.Chapter03.Section02OpenNormGroups

namespace LastLib.Book06GlobalClassFieldTheory.Chapter03

noncomputable section

open Filter Set
open scoped BigOperators RestrictedProduct

/-!
## 3.3. Local norm tests and the global kernel
-/

/-- The finite product of local factors above a fixed place. -/
abbrev Chapter03LocalNormFiber
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (v : Chapter03Place K) :=
  ∀ w : {w // w ∈ N.above v}, (S_L.localFactor w.1).carrier

/-- The product local norm at one place. -/
noncomputable def chapter03LocalNormAt
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (v : Chapter03Place K) :
    Chapter03LocalNormFiber N v →* (S_K.localFactor v).carrier where
  toFun z := ∏ w : {w // w ∈ N.above v}, N.localNorm v w.1 (z w)
  map_one' := by
    classical
    simp
  map_mul' x y := by
    classical
    simp [Finset.prod_mul_distrib]

theorem chapter03LocalNormAt_apply
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (v : Chapter03Place K)
    (z : Chapter03LocalNormFiber N v) :
    chapter03LocalNormAt N v z =
      ∏ w : {w // w ∈ N.above v}, N.localNorm v w.1 (z w) :=
  rfl

/-- Coordinatewise local solvability of the principal element `a` as an idèle norm. -/
def chapter03IsLocalElementNorm
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (a : Units K) : Prop :=
  ∀ v : Chapter03Place K,
    ∃ z : Chapter03LocalNormFiber N v,
      chapter03LocalNormAt N v z = S_K.embedding v a

/-- The global principal idèle is an idèle norm. -/
def chapter03IsIdeleElementNorm
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (a : Units K) : Prop :=
  ∃ y : Chapter03Ideles S_L,
    chapter03IdeleNorm N y = chapter03PrincipalIdeleHom S_K a

theorem chapter03_isIdeleElementNorm_iff_mem_ideleNormSubgroup
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (a : Units K) :
    chapter03IsIdeleElementNorm N a ↔
      chapter03PrincipalIdeleHom S_K a ∈ chapter03IdeleNormSubgroup N := by
  sorry

theorem chapter03_principal_idele_norm_iff_local
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (a : Units K) :
    chapter03IsIdeleElementNorm N a ↔ chapter03IsLocalElementNorm N a := by
  sorry

/-- The field norm on global units, as the multiplicative homomorphism used by principal
idèles. -/
noncomputable def chapter03ElementNorm
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (_N : Chapter03NormData S_K S_L) : Units L →* Units K :=
  Units.map (Algebra.norm K (S := L))

def chapter03ElementNormSubgroup
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) : Subgroup (Units K) :=
  (chapter03ElementNorm N).range

theorem chapter03_elementNorm_mem_iff
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (a : Units K) :
    a ∈ chapter03ElementNormSubgroup N ↔
      ∃ b : Units L, chapter03ElementNorm N b = a := by
  sorry

/- A class norm is intentionally a separate predicate from an element norm. -/
def chapter03IsClassNorm
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (c : Chapter03ClassGroup S_K) : Prop :=
  ∃ d : Chapter03ClassGroup S_L, chapter03ClassNorm N d = c

theorem chapter03_isClassNorm_iff_mem_normClassSubgroup
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (c : Chapter03ClassGroup S_K) :
    chapter03IsClassNorm N c ↔ c ∈ chapter03NormClassSubgroup N := by
  sorry

@[simp] theorem chapter03_principal_class_is_identity
    {K : Type*} [Field K] [NumberField K]
    {S_K : Chapter03FieldIdeleData K} (a : Units K) :
    (QuotientGroup.mk' (chapter03PrincipalSubgroup S_K)
      (chapter03PrincipalIdeleHom S_K a)) = 1 := by
  exact chapter03_class_of_principal S_K a

theorem chapter03_principal_class_is_classNorm
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (a : Units K) :
    chapter03IsClassNorm N
      (QuotientGroup.mk' (chapter03PrincipalSubgroup S_K)
        (chapter03PrincipalIdeleHom S_K a)) := by
  sorry

/-!
The theorem below records the local norm test for principal elements.  Its proof uses the
eventual unit-surjectivity in `Chapter03NormData` to patch local preimages into a restricted
product.  This is exactly where the element statement differs from the automatic principal
class statement above.
-/

theorem chapter03_principal_idele_is_norm_iff_local_test
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (a : Units K) :
    chapter03IsIdeleElementNorm N a ↔
      ∀ v : Chapter03Place K, ∃ z : Chapter03LocalNormFiber N v,
        chapter03LocalNormAt N v z = S_K.embedding v a := by
  exact chapter03_principal_idele_norm_iff_local N a

/-!
### Reciprocity and the one-sided global kernel inclusion
-/

theorem chapter03_local_reciprocity_kills_norm
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (A : Chapter03ArtinReciprocityData N) (v : Chapter03Place K)
    (w : Chapter03Place L) (hw : w ∈ N.above v)
    (x : (S_L.localFactor w).carrier) :
    A.localArtin v (N.localNorm v w x) = 1 := by
  exact A.local_norm_trivial v w hw x

theorem chapter03_artin_norm_idele
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative (Gal(L / K))]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (A : Chapter03ArtinReciprocityData N) (y : Chapter03Ideles S_L) :
    A.globalArtin (chapter03IdeleNorm N y) = 1 := by
  sorry

theorem chapter03_classNorm_range_le_artin_kernel
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative (Gal(L / K))]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (A : Chapter03ArtinReciprocityData N) :
    (chapter03ClassNorm N).range ≤ (chapter03ClassArtin A).ker := by
  sorry

/- The reverse inclusion is deliberately absent: it is the global norm theorem deferred to the
class-formation argument, and it cannot be proved by independent coordinatewise tests. -/

end
end LastLib.Book06GlobalClassFieldTheory.Chapter03
