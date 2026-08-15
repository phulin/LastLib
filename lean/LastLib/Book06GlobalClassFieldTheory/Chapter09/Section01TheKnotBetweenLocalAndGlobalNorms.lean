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
  intro x hx
  rcases hx with ⟨y, hy⟩
  change D.principalK x ∈ D.ideleNorm.range
  rw [← hy]
  exact ⟨D.principalL y, congrArg (fun f => f y) D.norm_compatibility⟩

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
  rfl

theorem chapter09_mem_fieldNormSubgroup_iff
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : Kˣ) :
    x ∈ chapter09FieldNormSubgroup K L ↔
      ∃ y : Lˣ, chapter09FieldNormUnitHom K L y = x := by
  rfl

theorem chapter09_knot_trivial_iff
    {K L I_K I_L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [CommGroup I_K] [CommGroup I_L]
    (D : Chapter09IdeleNormData K L I_K I_L) :
    Subsingleton (chapter09KnotGroup D) ↔
      chapter09PrincipalNormSubgroup D = chapter09FieldNormSubgroup K L := by
  constructor
  · intro hs
    apply le_antisymm
    · intro x hx
      have hq : ((⟨x, hx⟩ : chapter09PrincipalNormSubgroup D) :
          chapter09KnotGroup D) = 1 := Subsingleton.elim _ _
      exact (QuotientGroup.eq_one_iff (⟨x, hx⟩ : chapter09PrincipalNormSubgroup D)).mp hq
    · exact chapter09_field_norm_le_principal_norm D
  · intro h
    have hq : ∀ q : chapter09KnotGroup D, q = 1 := by
      intro q
      refine QuotientGroup.induction_on q ?_
      intro x
      apply (QuotientGroup.eq_one_iff x).mpr
      change (x : Kˣ) ∈ chapter09FieldNormSubgroup K L
      rw [← h]
      exact x.property
    exact ⟨fun a b => (hq a).trans (hq b).symm⟩

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
  rw [chapter09_knot_trivial_iff D]
  constructor
  · intro h
    apply le_antisymm
    · intro a ha
      exact (h a).mpr ((hlocal a).mpr ha)
    · intro a ha
      exact (hlocal a).mp ((h a).mp ha)
  · intro heq a
    constructor
    · intro ha
      exact (hlocal a).mpr (by rw [heq]; exact ha)
    · intro ha
      exact heq ▸ (hlocal a).mp ha

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
    intro x hx
    rcases hx with ⟨y, rfl⟩
    change (QuotientGroup.mk' D.principalK.range)
      (D.ideleNorm (D.principalL y)) = 1
    have hnorm : D.ideleNorm (D.principalL y) =
        D.principalK (chapter09FieldNormUnitHom K L y) :=
      congrArg (fun f => f y) D.norm_compatibility
    rw [hnorm]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨chapter09FieldNormUnitHom K L y, rfl⟩)

theorem chapter09_inducedClassNormMap_comp_quotient
    {K L I_K I_L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [CommGroup I_K] [CommGroup I_L]
    (D : Chapter09IdeleNormData K L I_K I_L) :
    (chapter09InducedClassNormMap D).comp
      (QuotientGroup.mk' D.principalL.range) =
      chapter09ClassNormMap D := by
  have hN : D.principalL.range ≤ (chapter09ClassNormMap D).ker := by
    intro x hx
    rcases hx with ⟨y, rfl⟩
    change (QuotientGroup.mk' D.principalK.range)
      (D.ideleNorm (D.principalL y)) = 1
    have hnorm : D.ideleNorm (D.principalL y) =
        D.principalK (chapter09FieldNormUnitHom K L y) :=
      congrArg (fun f => f y) D.norm_compatibility
    rw [hnorm]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨chapter09FieldNormUnitHom K L y, rfl⟩
  apply MonoidHom.ext
  intro x
  change (QuotientGroup.lift D.principalL.range (chapter09ClassNormMap D) hN)
      ((QuotientGroup.mk' D.principalL.range) x) = chapter09ClassNormMap D x
  exact QuotientGroup.lift_mk' D.principalL.range hN x

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
  apply le_antisymm
  · rintro z ⟨x, rfl⟩
    refine ⟨(QuotientGroup.mk' D.principalL.range) x, ?_⟩
    exact congrArg (fun f => f x)
      (chapter09_inducedClassNormMap_comp_quotient D)
  · rintro z ⟨q, rfl⟩
    refine QuotientGroup.induction_on q ?_
    intro x
    refine ⟨x, ?_⟩
    exact (congrArg (fun f => f x)
      (chapter09_inducedClassNormMap_comp_quotient D)).symm

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
  have hR : Subgroup.map (QuotientGroup.mk' D.principalK.range)
      D.ideleNorm.range = chapter09ClassNormGroup D := by
    ext z
    constructor
    · intro hz
      rcases (Subgroup.mem_map.mp hz) with ⟨y, hy, hzy⟩
      rcases hy with ⟨w, rfl⟩
      change z ∈ (chapter09ClassNormMap D).range
      exact ⟨w, hzy⟩
    · intro hz
      change z ∈ (chapter09ClassNormMap D).range at hz
      rcases hz with ⟨w, hw⟩
      apply Subgroup.mem_map.mpr
      refine ⟨D.ideleNorm w, ⟨w, rfl⟩, ?_⟩
      exact hw
  have hmap : Subgroup.map (QuotientGroup.mk' D.principalK.range)
      (chapter09ProductNormSubgroup D) = chapter09ClassNormGroup D := by
    rw [chapter09ProductNormSubgroup, Subgroup.map_sup,
      QuotientGroup.map_mk'_self, bot_sup_eq, hR]
  have hle : D.principalK.range ≤ chapter09ProductNormSubgroup D := by
    exact le_sup_left
  have e := QuotientGroup.quotientQuotientEquivQuotient
    D.principalK.range (chapter09ProductNormSubgroup D) hle
  have e' : chapter09ClassNormQuotient D ≃*
      (chapter09IdeleClassGroupK D ⧸
        Subgroup.map (QuotientGroup.mk' D.principalK.range)
          (chapter09ProductNormSubgroup D)) :=
    QuotientGroup.quotientMulEquivOfEq hmap.symm
  exact ⟨e'.trans e⟩

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
  refine ⟨D.principalL_injective, QuotientGroup.mk'_surjective _, ?_⟩
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change (QuotientGroup.mk' D.principalL.range) (D.principalL y) = 1
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨y, rfl⟩
  · intro hx
    change (QuotientGroup.mk' D.principalL.range) x = 1 at hx
    exact (QuotientGroup.eq_one_iff x).mp hx

/-!
The intersection in the knot definition and the product in the class-group
formula are intentionally kept as different declarations.  No formal
manipulation identifying them is asserted here.
-/

end

end LastLib.Book06GlobalClassFieldTheory.Chapter09
