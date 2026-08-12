import LastLib.Book06GlobalClassFieldTheory.Chapter03.Section01ConstructingTheGlobalNorm

namespace LastLib.Book06GlobalClassFieldTheory.Chapter03

noncomputable section

open Filter Set
open scoped BigOperators RestrictedProduct

/-!
## 3.2. Norm groups are open and have finite index

The local norm statements are kept separate from the global finiteness argument.  In
particular, the latter is formulated for the class group, not for the idèle group.
-/

/-- The local norm subgroup attached to a place of `K` and a place above it. -/
def chapter03LocalNormGroup
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (v : Chapter03Place K)
    (w : Chapter03Place L) : Subgroup (S_K.localFactor v).carrier :=
  MonoidHom.range (N.localNorm v w)

theorem chapter03_local_norm_group_open
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (v : Chapter03Place K)
    (w : Chapter03Place L) (hw : w ∈ N.above v) :
    IsOpen (chapter03LocalNormGroup N v w : Set (S_K.localFactor v).carrier) := by
  exact N.localNorm_range_isOpen v w hw

theorem chapter03_local_norm_on_units_surjective
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) {v : Chapter03Place K}
    (hv : S_K.finitePlace v) (hu : N.unramified v)
    (w : Chapter03Place L) (hw : w ∈ N.above v)
    (x : (S_K.localFactor v).carrier) (hx : x ∈ (S_K.localFactor v).unit) :
    ∃ y : (S_L.localFactor w).carrier,
      y ∈ (S_L.localFactor w).unit ∧ N.localNorm v w y = x := by
  exact N.localNorm_units_surjective hv hu w hw x hx

theorem chapter03_local_units_le_norm_group
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) {v : Chapter03Place K}
    (hv : S_K.finitePlace v) (hu : N.unramified v)
    (w : Chapter03Place L) (hw : w ∈ N.above v) :
    (S_K.localFactor v).unit ≤ chapter03LocalNormGroup N v w := by
  sorry

theorem chapter03_eventually_finite_unramified
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) :
    ∀ᶠ v in cofinite, S_K.finitePlace v ∧ N.unramified v :=
  N.eventually_finite_unramified

/-- The idèle norm subgroup in the base idèle group. -/
def chapter03IdeleNormSubgroup
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) : Subgroup (Chapter03Ideles S_K) :=
  (chapter03IdeleNorm N).range

theorem chapter03_mem_ideleNormSubgroup_iff
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (x : Chapter03Ideles S_K) :
    x ∈ chapter03IdeleNormSubgroup N ↔
      ∃ y : Chapter03Ideles S_L, chapter03IdeleNorm N y = x := by
  sorry

/- The following quotient is deliberately retained as an obstruction object.  The diagonal
principal-idèle contribution is not removed here, so no finite-index or Galois identification
is asserted for it. -/
abbrev Chapter03IdeleNormQuotient
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) :=
  Chapter03Ideles S_K ⧸ chapter03IdeleNormSubgroup N

theorem chapter03_ideleNorm_range_contains_basic_open
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) :
    ∃ U : OpenSubgroup (Chapter03Ideles S_K),
      (U : Subgroup (Chapter03Ideles S_K)) ≤ chapter03IdeleNormSubgroup N := by
  sorry

theorem chapter03_ideleNorm_range_isOpen
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) :
    IsOpen (chapter03IdeleNormSubgroup N : Set (Chapter03Ideles S_K)) := by
  sorry

/-- The image of the idèle norm after passing to idèle classes. -/
def chapter03NormClassSubgroup
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) : Subgroup (Chapter03ClassGroup S_K) :=
  (chapter03ClassNorm N).range

abbrev Chapter03ClassNormQuotient
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) :=
  Chapter03ClassGroup S_K ⧸ chapter03NormClassSubgroup N

theorem chapter03_classNorm_range_isOpen
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) :
    IsOpen (chapter03NormClassSubgroup N : Set (Chapter03ClassGroup S_K)) := by
  sorry

theorem chapter03_classNorm_range_isClosed
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) :
    IsClosed (chapter03NormClassSubgroup N : Set (Chapter03ClassGroup S_K)) := by
  sorry

/-!
### The module direction and the compact norm-one part

The next map is the descended normalized idèle-module map.  Its kernel is the book's
`C_K^1`; this isolates the compact factor used in the finite-index argument.
-/

/-- The positive-power map occurring on a real archimedean module coordinate. -/
def chapter03PositivePower (n : ℕ) : Chapter03PositiveReals →* Chapter03PositiveReals where
  toFun x := x ^ n
  map_one' := by simp
  map_mul' x y := by simp [mul_pow]

theorem chapter03_positivePower_surjective {n : ℕ} (hn : 0 < n) :
    Function.Surjective (chapter03PositivePower n) := by
  sorry

noncomputable def chapter03ClassModuleNorm
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (A : Chapter03AdelicModuleData N) :
    Chapter03ClassGroup S_K →* Chapter03PositiveReals :=
  QuotientGroup.lift (chapter03PrincipalSubgroup S_K) A.baseModuleNorm (by sorry)

@[simp] theorem chapter03ClassModuleNorm_mk
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (A : Chapter03AdelicModuleData N) (y : Chapter03Ideles S_K) :
    chapter03ClassModuleNorm A
        (QuotientGroup.mk' (chapter03PrincipalSubgroup S_K) y) = A.baseModuleNorm y := by
  sorry

def chapter03ClassModuleOneSubgroup
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (A : Chapter03AdelicModuleData N) : Subgroup (Chapter03ClassGroup S_K) :=
  (chapter03ClassModuleNorm A).ker

theorem chapter03_classModuleNorm_surjective
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (A : Chapter03AdelicModuleData N) :
    Function.Surjective (chapter03ClassModuleNorm A) := by
  sorry

theorem chapter03_classModuleOne_compact
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (A : Chapter03AdelicModuleData N) :
    IsCompact (chapter03ClassModuleOneSubgroup A : Set (Chapter03ClassGroup S_K)) := by
  sorry

theorem chapter03_classNorm_coset_has_module_one_representative
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (A : Chapter03AdelicModuleData N) (c : Chapter03ClassGroup S_K) :
    ∃ c₁ : Chapter03ClassGroup S_K, ∃ n : Chapter03ClassGroup S_K,
      c₁ ∈ chapter03ClassModuleOneSubgroup A ∧
        n ∈ chapter03NormClassSubgroup N ∧ c = c₁ * n := by
  sorry

theorem chapter03_classNormQuotient_compact
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (A : Chapter03AdelicModuleData N) :
    IsCompact (Set.univ : Set (Chapter03ClassNormQuotient N)) := by
  sorry

theorem chapter03_normClassSubgroup_finiteIndex
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (A : Chapter03AdelicModuleData N) :
    (chapter03NormClassSubgroup N).FiniteIndex := by
  sorry

theorem chapter03_classNormQuotient_finite
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (A : Chapter03AdelicModuleData N) :
    Finite (Chapter03ClassNormQuotient N) := by
  sorry

end
end LastLib.Book06GlobalClassFieldTheory.Chapter03
