import LastLib.Book06GlobalClassFieldTheory.Chapter12.Dependencies

namespace LastLib.Book06GlobalClassFieldTheory.Chapter12

noncomputable section

open LastLib.Book06GlobalClassFieldTheory.Chapter04
open LastLib.Book06GlobalClassFieldTheory.Chapter05
open LastLib.Book06GlobalClassFieldTheory.Chapter09

/-! ## 12.4. Norms without ambiguity -/

def chapter12GlobalElementNormSubgroup
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L]
    [FiniteDimensional K L] : Subgroup Kˣ :=
  chapter09FieldNormSubgroup K L

def chapter12GlobalElementNorm
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L]
    [FiniteDimensional K L] (a : Kˣ) : Prop :=
  a ∈ chapter12GlobalElementNormSubgroup K L

def chapter12LocalElementNorm
    {K_v L_w : Type*} [CommGroup K_v] [CommGroup L_w]
    (localNorm : L_w →* K_v) (a : K_v) : Prop :=
  a ∈ localNorm.range

def chapter12IdeleNormSubgroup
    {I_K I_L : Type*} [CommGroup I_K] [CommGroup I_L]
    (ideleNorm : I_L →* I_K) : Subgroup I_K :=
  ideleNorm.range

def chapter12ClassNormSubgroupOfMap
    {C_K C_L : Type*} [CommGroup C_K] [CommGroup C_L]
    (classNorm : C_L →* C_K) : Subgroup C_K :=
  classNorm.range

theorem chapter12_idele_norm_mem_iff
    {I_K I_L : Type*} [CommGroup I_K] [CommGroup I_L]
    (ideleNorm : I_L →* I_K) (x : I_K) :
    x ∈ chapter12IdeleNormSubgroup ideleNorm ↔ ∃ y, ideleNorm y = x := by
  rfl

theorem chapter12_class_norm_of_map_mem_iff
    {C_K C_L : Type*} [CommGroup C_K] [CommGroup C_L]
    (classNorm : C_L →* C_K) (x : C_K) :
    x ∈ chapter12ClassNormSubgroupOfMap classNorm ↔ ∃ y, classNorm y = x := by
  rfl

theorem chapter12_local_element_norm_iff
    {K_v L_w : Type*} [CommGroup K_v] [CommGroup L_w]
    (localNorm : L_w →* K_v) (a : K_v) :
    chapter12LocalElementNorm localNorm a ↔ ∃ y, localNorm y = a := by
  rfl

structure Chapter12NamedNormLayers
    (I_K I_L C_K C_L K L K_v L_w : Type*)
    [CommGroup I_K] [CommGroup I_L] [CommGroup C_K] [CommGroup C_L]
    [Field K] [Field L] [Algebra K L] [NumberField K] [NumberField L]
    [FiniteDimensional K L]
    [CommGroup K_v] [CommGroup L_w] where
  ideleNorm : I_L →* I_K
  classNorm : C_L →* C_K
  localNorm : L_w →* K_v
  globalNorm : Lˣ →* Kˣ
  ideleNorm_subgroup : chapter12IdeleNormSubgroup ideleNorm = ideleNorm.range
  classNorm_subgroup : chapter12ClassNormSubgroupOfMap classNorm = classNorm.range
  localNorm_subgroup : chapter12LocalElementNorm localNorm =
    fun a => a ∈ localNorm.range
  globalNorm_subgroup :
    chapter12GlobalElementNormSubgroup K L = globalNorm.range

theorem chapter12_global_field_norm_is_local_norm_everywhere
    {K L V : Type*} [CommGroup K] [CommGroup L]
    {K_v L_w : V → Type*}
    [∀ v, CommGroup (K_v v)] [∀ v, CommGroup (L_w v)]
    (D : Chapter12LocalNormFamily K L V K_v L_w) (y : L) :
    ∀ v, chapter12LocalElementNorm (D.localNorm v)
      (D.baseEmbedding v (D.globalNorm y)) := by
  intro v
  refine ⟨D.localization v y, ?_⟩
  exact D.global_to_local v y

theorem chapter12_cyclic_element_norm_has_local_global_iff
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L] [FiniteDimensional K L]
    [IsGalois K L] [IsCyclic (Gal(L / K))]
    (P : Chapter09CyclicNormData K L) (a : Kˣ) :
    a ∈ chapter09FieldNormSubgroup K L ↔
      chapter09CyclicEverywhereLocalNorm P a := by
  exact chapter09_hasse_norm_theorem P a

/- The following is the precise noncyclic warning: the class-norm theorem
does not identify the principal-norm intersection with field norms. -/
theorem chapter12_biquadratic_local_norm_need_not_be_global
    {L : Type} {I_K I_L V : Type*} [Field L] [Algebra ℚ L]
    [NumberField L] [FiniteDimensional ℚ L] [IsGalois ℚ L]
    [CommGroup I_K] [CommGroup I_L]
    {K_v A_v : V → Type*}
    [∀ v, Monoid (K_v v)] [∀ v, Monoid (A_v v)]
    (E : Chapter09BiquadraticPresentation L)
    (R : Chapter09NormRealizationData ℚ L I_K I_L V K_v A_v)
    [Finite (chapter09KnotGroup R.idele)]
    (hknot : Nat.card (chapter09KnotGroup R.idele) = 2) :
    ∃ a : ℚˣ,
      chapter09EverywhereLocalNorm R.localNormData a ∧
        a ∉ chapter09FieldNormSubgroup ℚ L := by
  exact chapter09_biquadratic_exists_local_not_global_norm E R hknot

theorem chapter12_finite_abelian_class_norm_is_artin_kernel
    {K L I_K I_L C_K C_L : Type*}
    [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L]
    [CommGroup I_K] [CommGroup I_L] [CommGroup C_K] [CommGroup C_L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (X : Chapter05ClassFormationInput K L I_K I_L C_K C_L) :
    (chapter05InputGlobalArtin X).ker = chapter05InputNormSubgroup X := by
  exact chapter05_finite_global_reciprocity_kernel X

noncomputable def chapter12_finite_abelian_class_norm_quotient_is_galois_group
    {K L I_K I_L C_K C_L : Type*}
    [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L]
    [CommGroup I_K] [CommGroup I_L] [CommGroup C_K] [CommGroup C_L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (X : Chapter05ClassFormationInput K L I_K I_L C_K C_L) :
    (C_K ⧸ chapter05InputNormSubgroup X) ≃* Gal(L / K) := by
  exact chapter05_finite_global_reciprocity_abelian X

noncomputable def chapter12_class_norm_quotient_is_idele_product_quotient
    {K L I_K I_L : Type*} [Field K] [Field L] [Algebra K L]
    [CommGroup I_K] [CommGroup I_L]
    (D : Chapter09IdeleNormData K L I_K I_L) :
    chapter09ClassNormQuotient D ≃*
      chapter09ProductNormQuotient D := by
  exact chapter09_class_norm_quotient_equiv_product_quotient D

theorem chapter12_norm_on_idele_classes_matches_galois_inclusion
    {C_K C_L G_K G_L : Type*}
    [CommGroup C_K] [CommGroup C_L] [CommGroup G_K] [CommGroup G_L]
    (S : Chapter05NormInclusionArtinSquare C_K C_L G_K G_L) :
    S.artinK.comp S.norm = S.inclusion.comp S.artinL := by
  exact chapter05_norm_corresponds_to_galois_inclusion S

theorem chapter12_scalar_idele_inclusion_matches_transfer
    {C_K C_L G_K G_L : Type*}
    [CommGroup C_K] [CommGroup C_L] [CommGroup G_K] [CommGroup G_L]
    (S : Chapter05ArtinTransferSquare C_K C_L G_K G_L) :
    S.artinL.comp S.scalarInclusion = S.transfer.comp S.artinK := by
  exact chapter05_scalar_inclusion_corresponds_to_transfer S

theorem chapter12_quotient_fields_match_restriction
    {C G_L G_E : Type*} [CommGroup C] [CommGroup G_L] [CommGroup G_E]
    (S : Chapter05ArtinRestrictionSquare C G_L G_E) :
    S.restriction.comp S.artinL = S.artinE := by
  exact chapter05_artin_restriction_square S

theorem chapter12_brauer_restriction_multiplies_local_invariant
    {B₀ B₁ : Type*} [AddCommGroup B₀] [AddCommGroup B₁]
    (D : Chapter04LocalBrauerMapData B₀ B₁) (α : B₀) :
    D.inv₁ (D.res α) = D.degree • D.inv₀ α := by
  exact chapter04_local_invariant_restriction_formula D α

theorem chapter12_brauer_corestriction_preserves_local_invariant
    {B₀ B₁ : Type*} [AddCommGroup B₀] [AddCommGroup B₁]
    (D : Chapter04LocalBrauerMapData B₀ B₁) (β : B₁) :
    D.inv₀ (D.cor β) = D.inv₁ β := by
  exact chapter04_local_invariant_corestriction_formula D β

theorem chapter12_brauer_corestriction_sums_over_places
    {I : Type*} [Fintype I]
    (D : Chapter04FiniteEtaleBrauerData I) (β : ∀ i, D.branch i) :
    D.invBase (∑ i, D.cor i (β i)) =
      ∑ i, D.invBranch i (β i) := by
  exact chapter04_finite_etale_corestriction_sum_formula D β

theorem chapter12_brauer_restriction_sums_with_local_degrees
    {I : Type*} [Fintype I]
    (D : Chapter04FiniteEtaleBrauerData I) (α : D.base) :
    (∑ i, D.invBranch i (D.res i α)) =
      (∑ i, D.degree i) • D.invBase α := by
  exact chapter04_finite_etale_restriction_sum_formula D α

end

end LastLib.Book06GlobalClassFieldTheory.Chapter12
