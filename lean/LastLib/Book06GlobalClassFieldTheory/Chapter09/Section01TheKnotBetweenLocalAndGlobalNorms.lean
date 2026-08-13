import LastLib.Book06GlobalClassFieldTheory.Chapter09.Dependencies

namespace LastLib.Book06GlobalClassFieldTheory.Chapter09

noncomputable section

/-!
For a finite extension, the numerator of the knot is the pullback of the
idele-norm range along the diagonal embedding of `Kˣ`.
-/
def chapter09PrincipalNormSubgroup
    {K L I_K I_L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [CommGroup I_K] [CommGroup I_L]
    (D : Chapter09IdeleNormData K L I_K I_L) : Subgroup Kˣ :=
  Subgroup.comap D.principalK D.ideleNorm.range

def chapter09FieldNormSubgroup
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Subgroup Kˣ :=
  (chapter09FieldNormUnitHom K L).range

theorem chapter09_field_norm_le_principal_norm
    {K L I_K I_L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [CommGroup I_K] [CommGroup I_L]
    (D : Chapter09IdeleNormData K L I_K I_L) :
    chapter09FieldNormSubgroup K L ≤ chapter09PrincipalNormSubgroup D := by
  sorry

/-!
`K(L/K)` is the quotient of the local/global-norm intersection by the global
field norms.  `Subgroup.subgroupOf` makes the denominator a subgroup of the
ambient numerator, while the preceding theorem records the required
containment.
-/
abbrev chapter09KnotGroup
    {K L I_K I_L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [CommGroup I_K] [CommGroup I_L]
    (D : Chapter09IdeleNormData K L I_K I_L) : Type _ :=
  chapter09PrincipalNormSubgroup D ⧸
    (chapter09FieldNormSubgroup K L).subgroupOf (chapter09PrincipalNormSubgroup D)

theorem chapter09_mem_principalNormSubgroup_iff
    {K L I_K I_L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [CommGroup I_K] [CommGroup I_L]
    (D : Chapter09IdeleNormData K L I_K I_L) (x : Kˣ) :
    x ∈ chapter09PrincipalNormSubgroup D ↔
      ∃ y : I_L, D.ideleNorm y = D.principalK x := by
  sorry

theorem chapter09_mem_fieldNormSubgroup_iff
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : Kˣ) :
    x ∈ chapter09FieldNormSubgroup K L ↔
      ∃ y : Lˣ, chapter09FieldNormUnitHom K L y = x := by
  sorry

theorem chapter09_knot_trivial_iff
    {K L I_K I_L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [CommGroup I_K] [CommGroup I_L]
    (D : Chapter09IdeleNormData K L I_K I_L) :
    Subsingleton (chapter09KnotGroup D) ↔
      chapter09PrincipalNormSubgroup D = chapter09FieldNormSubgroup K L := by
  sorry

theorem chapter09_hasse_norm_principle_iff_knot_trivial
    {K L I_K I_L V : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [CommGroup I_K] [CommGroup I_L]
    {K_v A_v : V → Type*}
    [∀ v, Monoid (K_v v)] [∀ v, Monoid (A_v v)]
    (D : Chapter09IdeleNormData K L I_K I_L)
    (P : Chapter09LocalNormData K V K_v A_v)
    (hlocal : ∀ a, chapter09EverywhereLocalNorm P a ↔
      a ∈ chapter09PrincipalNormSubgroup D) :
    (∀ a, a ∈ chapter09FieldNormSubgroup K L ↔
      chapter09EverywhereLocalNorm P a) ↔
      Subsingleton (chapter09KnotGroup D) := by
  sorry

/-!
The class-group quotient in the displayed formula is represented by the
quotient of the idele group by the range of the diagonal principal map, and
the norm subgroup is the range of the induced class norm.
-/
abbrev chapter09IdeleClassGroupK
    {K L I_K I_L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [CommGroup I_K] [CommGroup I_L]
    (D : Chapter09IdeleNormData K L I_K I_L) : Type _ :=
  I_K ⧸ D.principalK.range

abbrev chapter09IdeleClassGroupL
    {K L I_K I_L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [CommGroup I_K] [CommGroup I_L]
    (D : Chapter09IdeleNormData K L I_K I_L) : Type _ :=
  I_L ⧸ D.principalL.range

def chapter09ClassNormMap
    {K L I_K I_L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [CommGroup I_K] [CommGroup I_L]
    (D : Chapter09IdeleNormData K L I_K I_L) :
    I_L →* chapter09IdeleClassGroupK D :=
  (QuotientGroup.mk' D.principalK.range).comp D.ideleNorm

def chapter09InducedClassNormMap
    {K L I_K I_L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [CommGroup I_K] [CommGroup I_L]
    (D : Chapter09IdeleNormData K L I_K I_L) :
    chapter09IdeleClassGroupL D →* chapter09IdeleClassGroupK D :=
  QuotientGroup.lift D.principalL.range (chapter09ClassNormMap D) (by
    sorry)

theorem chapter09_inducedClassNormMap_comp_quotient
    {K L I_K I_L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [CommGroup I_K] [CommGroup I_L]
    (D : Chapter09IdeleNormData K L I_K I_L) :
    (chapter09InducedClassNormMap D).comp
        (QuotientGroup.mk' D.principalL.range) =
      chapter09ClassNormMap D := by
  sorry

def chapter09ClassNormGroup
    {K L I_K I_L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [CommGroup I_K] [CommGroup I_L]
    (D : Chapter09IdeleNormData K L I_K I_L) :
    Subgroup (chapter09IdeleClassGroupK D) :=
  (chapter09ClassNormMap D).range

theorem chapter09_classNormGroup_eq_induced_range
    {K L I_K I_L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [CommGroup I_K] [CommGroup I_L]
    (D : Chapter09IdeleNormData K L I_K I_L) :
    chapter09ClassNormGroup D = (chapter09InducedClassNormMap D).range := by
  sorry

abbrev chapter09ClassNormQuotient
    {K L I_K I_L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [CommGroup I_K] [CommGroup I_L]
    (D : Chapter09IdeleNormData K L I_K I_L) : Type _ :=
  chapter09IdeleClassGroupK D ⧸ chapter09ClassNormGroup D

def chapter09ProductNormSubgroup
    {K L I_K I_L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [CommGroup I_K] [CommGroup I_L]
    (D : Chapter09IdeleNormData K L I_K I_L) : Subgroup I_K :=
  D.principalK.range ⊔ D.ideleNorm.range

abbrev chapter09ProductNormQuotient
    {K L I_K I_L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [CommGroup I_K] [CommGroup I_L]
    (D : Chapter09IdeleNormData K L I_K I_L) : Type _ :=
  I_K ⧸ chapter09ProductNormSubgroup D

theorem chapter09_class_norm_quotient_formula
    {K L I_K I_L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [CommGroup I_K] [CommGroup I_L]
    (D : Chapter09IdeleNormData K L I_K I_L) :
    Nonempty (chapter09ClassNormQuotient D ≃* chapter09ProductNormQuotient D) := by
  sorry

noncomputable def chapter09_class_norm_quotient_equiv_product_quotient
    {K L I_K I_L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [CommGroup I_K] [CommGroup I_L]
    (D : Chapter09IdeleNormData K L I_K I_L) :
    chapter09ClassNormQuotient D ≃*
      chapter09ProductNormQuotient D := by
  exact Classical.choice (chapter09_class_norm_quotient_formula D)

theorem chapter09_idele_class_exact_sequence
    {K L I_K I_L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [CommGroup I_K] [CommGroup I_L]
    (D : Chapter09IdeleNormData K L I_K I_L) :
    chapter09GroupExact D.principalL
      (QuotientGroup.mk' D.principalL.range) := by
  sorry

/-!
The intersection in the knot definition and the product in the class-group
formula are intentionally kept as different declarations.  No formal
manipulation identifying them is asserted here.
-/

end

end LastLib.Book06GlobalClassFieldTheory.Chapter09
