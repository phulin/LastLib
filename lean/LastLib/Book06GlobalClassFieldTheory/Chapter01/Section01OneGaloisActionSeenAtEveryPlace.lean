import LastLib.Book06GlobalClassFieldTheory.Chapter01.Dependencies

namespace LastLib.Book06GlobalClassFieldTheory.Chapter01

open Set
open scoped BigOperators NumberField

noncomputable section

/-! ## 1.1. One Galois action seen at every place -/

theorem bookAdeleRing_as_infinite_finite_product
    {K : Type*} [Field K] [NumberField K] :
    BookAdeleRing K =
      (NumberField.InfiniteAdeleRing K ×
        IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) :=
  rfl

/- A basic open subgroup prescribes local open subgroups at finitely many
places and uses the finite-place unit subgroup elsewhere. -/
structure BasicIdeleOpenSubgroupData (K : Type*) [Field K] [NumberField K] where
  exceptional : Finset (BookPlace K)
  prescribed : ∀ v : BookPlace K, Subgroup (BookPlace.completion v)ˣ
  prescribed_open : ∀ v, IsOpen ((prescribed v : Set ((BookPlace.completion v)ˣ)))
  outside_finite_unit : ∀ v : FinitePlaceIndex K,
      Sum.inl v ∉ exceptional →
      (prescribed (Sum.inl v) : Set ((BookPlace.completion (Sum.inl v))ˣ)) =
        (bookFinitePlaceUnitSubgroup v : Set ((BookPlace.completion (Sum.inl v))ˣ))
  subgroup : Subgroup (I_K K)
  carrier_eq : (subgroup : Set (I_K K)) =
    {x | ∀ v : BookPlace K, bookIdeleUnitComponent x v ∈ prescribed v}
  subgroup_open : IsOpen (subgroup : Set (I_K K))

def basicIdeleOpenSubgroup {K : Type*} [Field K] [NumberField K]
    (D : BasicIdeleOpenSubgroupData K) : Subgroup (I_K K) :=
  D.subgroup

theorem basicIdeleOpenSubgroup_carrier {K : Type*} [Field K] [NumberField K]
    (D : BasicIdeleOpenSubgroupData K) :
    (basicIdeleOpenSubgroup D : Set (I_K K)) =
      {x | ∀ v : BookPlace K, bookIdeleUnitComponent x v ∈ D.prescribed v} :=
  D.carrier_eq

theorem basicIdeleOpenSubgroup_isOpen {K : Type*} [Field K] [NumberField K]
    (D : BasicIdeleOpenSubgroupData K) :
    IsOpen (basicIdeleOpenSubgroup D : Set (I_K K)) := by
  exact D.subgroup_open

/- The diagonal copy of `Kˣ` is discrete and closed in the ideles. -/
theorem principalIdele_discrete_closed {K : Type*} [Field K] [NumberField K] :
    DiscreteTopology (principalIdeleSubgroup K) ∧
      IsClosed (principalIdeleSubgroup K : Set (I_K K)) := by
  sorry

/- Passing to the quotient by the diagonal subgroup preserves the expected
locally compact Hausdorff structure. -/
theorem idelicClassGroup_locallyCompact_hausdorff
    {K : Type*} [Field K] [NumberField K] :
    LocallyCompactSpace (C_K K) ∧ T2Space (C_K K) := by
  sorry

theorem idelicClassGroup_not_compact
    {K : Type*} [Field K] [NumberField K] :
    ¬ IsCompact (Set.univ : Set (C_K K)) := by
  sorry

/- The idelic module, its norm-one subgroup, and its archimedean quotient. -/
theorem classModule_kernel_compact {K : Type*} [Field K] [NumberField K] :
    IsCompact (classModuleOneSubgroup K : Set (C_K K)) := by
  sorry

structure ClassModuleQuotientEquivalence
    (K : Type*) [Field K] [NumberField K] where
  equiv : (C_K K ⧸ classModuleOneSubgroup K) ≃* PositiveReal
  compatible : ∀ c : C_K K,
    equiv (QuotientGroup.mk' (classModuleOneSubgroup K) c) = classModule c

theorem classModule_quotient_positiveReal_equiv
    {K : Type*} [Field K] [NumberField K] :
    Nonempty (ClassModuleQuotientEquivalence K) := by
  sorry

theorem classModule_is_archimedean_size
    {K : Type*} [Field K] [NumberField K] (c : C_K K) :
    (classModule c : PositiveReal) = 1 ↔ c ∈ classModuleOneSubgroup K := by
  sorry

/-! ### The global and finite-level reciprocity interfaces -/

/- A global Artin map is a continuous homomorphism on the idelic class group. -/
abbrev GlobalArtinMap (K : Type*) [Field K] [NumberField K] :=
  ContinuousBookArtinMap K

def PrincipalIdeleProductRelation
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    (A : FiniteLevelArtinData K L) : Prop :=
  ∀ a : Kˣ, A.globalArtin (principalIdele a) = 1

def ArtinKernelIsClassNorm {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L]
    (A : FiniteLevelArtinData K L) (N : GlobalNormInterface K L) : Prop :=
  (classArtin A).ker = classNormGroup N

/- The quotient equivalence is required to be induced by the Artin map, not
 merely an unrelated abstract equivalence of the two groups. -/
structure FiniteLevelClassArtinQuotientEquivalence
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    (A : FiniteLevelArtinData K L) (N : GlobalNormInterface K L) where
  equiv : (C_K K ⧸ classNormGroup N) ≃*
    GroupAbelianization (Gal(L / K))
  compatible : ∀ c : C_K K,
    equiv (QuotientGroup.mk' (classNormGroup N) c) = classArtin A c

def EveryOpenFiniteIndexSubgroupIsAClassNorm
    (K : Type*) [Field K] [NumberField K] : Prop :=
  ∀ H : Subgroup (C_K K),
    IsOpen (H : Set (C_K K)) → H.FiniteIndex →
      Nonempty (ClassFieldNormRealization K H)

/- The finite-level statement keeps the local-product relation, the exact
kernel, and the quotient isomorphism as separate proof obligations. -/
theorem finiteLevel_classArtin_quotient_equiv
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    (A : FiniteLevelArtinData K L) (N : GlobalNormInterface K L)
    (hkernel : ArtinKernelIsClassNorm A N)
    (hsurjective : Function.Surjective (classArtin A)) :
    Nonempty (FiniteLevelClassArtinQuotientEquivalence A N) := by
  sorry

/- The class norm is the image of principal ideles times idelic norms. -/
theorem classNorm_is_principal_times_ideleNorm
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (N : GlobalNormInterface K L) :
    classNormGroup N =
      Subgroup.map (classQuotient (K := K))
        (principalTimesIdeleNormGroup N) :=
  classNormGroup_eq_principal_times_norm_quotient N

end
end LastLib.Book06GlobalClassFieldTheory.Chapter01
