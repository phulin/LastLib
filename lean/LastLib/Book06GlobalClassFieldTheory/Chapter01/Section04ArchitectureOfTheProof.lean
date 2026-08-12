import LastLib.Book06GlobalClassFieldTheory.Chapter01.Section03FourKindsOfNormAssertion

namespace LastLib.Book06GlobalClassFieldTheory.Chapter01

open Set
open scoped BigOperators NumberField

noncomputable section

universe uK uL

/-! ## 1.4. The architecture of the proof -/

/- The pinned Mathlib Brauer quotient does not yet expose the additive Brauer
group operations and invariant maps needed by this chapter.  This structure
is the smallest exact-sequence interface for the displayed global-to-local
invariant sequence. -/
structure BookBrauerInvariantSequence
    (K : Type uK) [Field K] [NumberField K] where
  localBrauer : BookPlace K → Type uK
  [localAddCommGroup : ∀ v, AddCommGroup (localBrauer v)]
  globalBrauer : Type uK
  [globalAddCommGroup : AddCommGroup globalBrauer]
  sequence :
    AdditiveShortExact globalBrauer (DirectSum (BookPlace K) localBrauer)
      RationalModuloIntegers

attribute [instance] BookBrauerInvariantSequence.localAddCommGroup
  BookBrauerInvariantSequence.globalAddCommGroup

/- LOCAL_DEPENDENCY_GUESS: this is the Brauer invariant exact sequence
`0 → Br(K) → ⊕ᵥ Br(Kᵥ) → ℚ/ℤ → 0`. -/
noncomputable def bookBrauerInvariantSequence
    (K : Type*) [Field K] [NumberField K] :
    BookBrauerInvariantSequence K := by
  sorry

def brauerGlobalToLocal
    {K : Type*} [Field K] [NumberField K]
    (S : BookBrauerInvariantSequence K) :
    S.globalBrauer →+ DirectSum (BookPlace K) S.localBrauer :=
  S.sequence.left

def brauerInvariantSum
    {K : Type*} [Field K] [NumberField K]
    (S : BookBrauerInvariantSequence K) :
    DirectSum (BookPlace K) S.localBrauer →+ RationalModuloIntegers :=
  S.sequence.right

theorem brauer_invariant_sequence_exact
    {K : Type*} [Field K] [NumberField K]
    (S : BookBrauerInvariantSequence K) :
    Function.Exact (brauerGlobalToLocal S) (brauerInvariantSum S) :=
  S.sequence.exact

theorem brauer_global_to_local_injective
    {K : Type*} [Field K] [NumberField K]
    (S : BookBrauerInvariantSequence K) :
    Function.Injective (brauerGlobalToLocal S) :=
  S.sequence.left_injective

theorem brauer_invariant_sum_surjective
    {K : Type*} [Field K] [NumberField K]
    (S : BookBrauerInvariantSequence K) :
    Function.Surjective (brauerInvariantSum S) :=
  S.sequence.right_surjective

/- The principal global relation is a zero sum in additive invariant notation,
equivalently a product-one relation in multiplicative local reciprocity. -/
def PrincipalLocalInvariantProductOne
    {K : Type*} [Field K] [NumberField K]
    (S : BookBrauerInvariantSequence K) (_b : S.globalBrauer) : Prop :=
  brauerInvariantSum S (brauerGlobalToLocal S _b) = 0

theorem principal_local_invariant_product_one
    {K : Type*} [Field K] [NumberField K]
    (S : BookBrauerInvariantSequence K) (b : S.globalBrauer) :
    PrincipalLocalInvariantProductOne S b := by
  sorry

/- A zero sum is not a pointwise vanishing assertion.  This generic predicate
keeps the distinction visible when individual local summands are introduced. -/
def SumZeroDoesNotMeanPointwiseZero
    {ι : Type*} (A : ι → Type*) [∀ i, AddCommGroup (A i)]
    {R : Type*} [AddCommGroup R]
    (sum : DirectSum ι A →+ R)
    (component : ∀ _i : ι, DirectSum ι A →+ R) : Prop :=
  ∃ x : DirectSum ι A, sum x = 0 ∧ ∃ i, component i x ≠ 0

/- The same global-to-local exact sequence is the input for the finite
Galois fundamental class. -/
structure FiniteGaloisFundamentalClassData
    (K : Type uK) (L : Type uL) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
  (N : GlobalNormInterface K L) where
  brauerSequence : BookBrauerInvariantSequence K
  cohomologyCoefficient : Type uL
  [cohomologyCoefficientCommGroup : CommGroup cohomologyCoefficient]
  coefficient_identification :
    Nonempty (cohomologyCoefficient ≃* BookIdeleClassGroup L)
  H2 : Type (max uK uL)
  [H2AddCommGroup : AddCommGroup H2]
  fundamentalClass : H2
  cap_equivalence :
    Nonempty (GroupAbelianization (Gal(L / K)) ≃*
      finiteClassArtinQuotient N)

/- LOCAL_DEPENDENCY_GUESS: the finite Galois class formation and its
restriction-compatible H² fundamental class are supplied at this boundary. -/
theorem finite_galois_fundamental_class_exists
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    (N : GlobalNormInterface K L) :
    Nonempty (FiniteGaloisFundamentalClassData K L N) := by
  sorry

theorem cap_fundamental_class_identifies_abelianization
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    (N : GlobalNormInterface K L)
    (D : FiniteGaloisFundamentalClassData K L N) :
    Nonempty (GroupAbelianization (Gal(L / K)) ≃*
      finiteClassArtinQuotient N) :=
  D.cap_equivalence

theorem abelian_group_abelianization_equiv
    {G : Type*} [CommGroup G] :
    Nonempty (GroupAbelianization G ≃* G) := by
  sorry

/- The finite local-global duality input uses the two Cartier coefficients
appearing in the source: the constant group Z/nZ and μₙ. -/
abbrev CartierConstantCoefficient (n : ℕ) := ZMod n

abbrev CartierRootCoefficient
    (K : Type*) [Field K] (n : ℕ) := rootsOfUnity n K

/- LOCAL_DEPENDENCY_GUESS: the exact finite local-global duality theorem is
not yet present in the pinned interfaces, so its coefficient pair and theorem
are bundled explicitly rather than replaced by an unrelated existence axiom. -/
structure FiniteCartierDualityData
    (K : Type uK) [Field K] [NumberField K] (n : ℕ) where
  n_pos : 0 < n
  constantCoefficient : Type
  [constantAddCommGroup : AddCommGroup constantCoefficient]
  constant_identification :
    Nonempty (constantCoefficient ≃+ CartierConstantCoefficient n)
  rootCoefficient : Type uK
  [rootCommGroup : CommGroup rootCoefficient]
  root_identification :
    Nonempty (rootCoefficient ≃* CartierRootCoefficient K n)
  local_global_duality : Prop

def HasFiniteCartierDualityForAllLevels
    (K : Type*) [Field K] [NumberField K] : Prop :=
  ∀ n : ℕ, 0 < n → Nonempty (FiniteCartierDualityData K n)

/- The duality theorem realizes open finite-index subgroups as class norms. -/
theorem every_open_finiteIndex_subgroup_realized_by_class_norm
    {K : Type*} [Field K] [NumberField K]
    (H : Subgroup (C_K K))
    (hopen : IsOpen (H : Set (C_K K))) [H.FiniteIndex]
    (hduality : HasFiniteCartierDualityForAllLevels K) :
    Nonempty (ClassFieldNormRealization K H) := by
  sorry

def ClassFieldExistenceViaFiniteCartierDuality
    (K : Type*) [Field K] [NumberField K] : Prop :=
  HasFiniteCartierDualityForAllLevels K →
    ∀ H : Subgroup (C_K K), IsOpen (H : Set (C_K K)) → H.FiniteIndex →
      Nonempty (ClassFieldNormRealization K H)

theorem class_field_existence_is_via_finite_duality
    {K : Type*} [Field K] [NumberField K]
    (hduality : HasFiniteCartierDualityForAllLevels K) :
    ClassFieldExistenceViaFiniteCartierDuality K := by
  sorry

end
end LastLib.Book06GlobalClassFieldTheory.Chapter01
