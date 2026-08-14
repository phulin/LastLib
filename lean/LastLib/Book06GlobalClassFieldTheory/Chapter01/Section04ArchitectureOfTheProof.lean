import LastLib.Book06GlobalClassFieldTheory.Chapter01.Dependencies
import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.Data.ZMod.QuotientGroup
import LastLib.Book05LocalClassFieldTheory.Chapter05.Section03ClassFormation

namespace LastLib.Book06GlobalClassFieldTheory.Chapter01

open Set
open scoped BigOperators NumberField
open LastLib.Book05LocalClassFieldTheory.Chapter05

noncomputable section

universe uK uL

local instance chapter01BookPlaceDecidableEq
    (K : Type*) [Field K] [NumberField K] : DecidableEq (BookPlace K) :=
  Classical.decEq _

local instance chapter01ClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-! ## 1.4. The architecture of the proof -/

/- Mathlib's canonical `BrauerGroup` is the carrier for the global and local
Brauer classes.  Its additive group operations are still pending upstream, so
the exact sequence is carried by an additive shadow together with explicit
restriction and invariant compatibility fields. -/
abbrev BookCanonicalBrauerGroup (F : Type uK) [Field F] :=
  BrauerGroup.{uK, uK} F

structure BookCanonicalBrauerContext
    (K : Type uK) [Field K] [NumberField K] where
  restriction : ∀ v : BookPlace K,
    BookCanonicalBrauerGroup K → BookCanonicalBrauerGroup (BookPlace.completion v)
  invariant : ∀ v : BookPlace K,
    BookCanonicalBrauerGroup (BookPlace.completion v) → RationalModuloIntegers

structure BookBrauerInvariantSequence
    (K : Type uK) [Field K] [NumberField K] where
  canonical : BookCanonicalBrauerContext K
  localBrauer : BookPlace K → Type uK
  [localAddCommGroup : ∀ v, AddCommGroup (localBrauer v)]
  globalBrauer : Type uK
  [globalAddCommGroup : AddCommGroup globalBrauer]
  sequence :
    AdditiveShortExact globalBrauer (DirectSum (BookPlace K) localBrauer)
      RationalModuloIntegers
  global_to_canonical : globalBrauer → BookCanonicalBrauerGroup K
  local_to_canonical : ∀ v,
    localBrauer v → BookCanonicalBrauerGroup (BookPlace.completion v)
  restriction_compatibility : ∀ (b : globalBrauer) (v : BookPlace K),
    local_to_canonical v (sequence.left b v) =
      canonical.restriction v (global_to_canonical b)
  invariant_sum_compatibility : ∀ x,
    sequence.right x =
      Finset.sum x.support (fun v =>
        canonical.invariant v (local_to_canonical v (x v)))
  global_to_canonical_bijective : Function.Bijective global_to_canonical
  local_to_canonical_bijective : ∀ v,
    Function.Bijective (local_to_canonical v)

attribute [instance] BookBrauerInvariantSequence.localAddCommGroup
  BookBrauerInvariantSequence.globalAddCommGroup

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

/- The global fundamental class has idele classes as its coefficient object.
The preceding local class-formation interface uses the units representation;
that representation is not a substitute for the Galois action on `C_L`.  The
action itself is kept as a boundary interface until the adelic Galois-action
API is available. -/
structure GlobalIdeleClassGaloisActionData
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] where
  action : MulAction (Gal(L / K)) (C_K L)

noncomputable def globalIdeleClassCoefficientRep
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (A : GlobalIdeleClassGaloisActionData K L) :
    Rep ℤ (Gal(L / K)) := by
  letI : MulAction (Gal(L / K)) (C_K L) := A.action
  exact Rep.ofMulAction ℤ (Gal(L / K)) (C_K L)

/- The same global-to-local exact sequence is the input for the finite
Galois fundamental class. -/
structure FiniteGaloisFundamentalClassData
    (K : Type) (L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))] where
  normData : GlobalNormInterface K L
  ideleClassAction : GlobalIdeleClassGaloisActionData K L
  brauerSequence : BookBrauerInvariantSequence K
  fundamentalClass : Chapter05FundamentalTwoClass
    (Gal(L / K)) (globalIdeleClassCoefficientRep ideleClassAction)
  capProduct : Chapter05CapProduct (Gal(L / K))
    (globalIdeleClassCoefficientRep ideleClassAction)
    fundamentalClass.value
  twoExtensionRepresentative :
    Chapter05TwoExtensionRepresentative (Gal(L / K))
      (globalIdeleClassCoefficientRep ideleClassAction) fundamentalClass.value capProduct
  classFormation : Chapter05TateNakayamaHypotheses
    (Gal(L / K)) (globalIdeleClassCoefficientRep ideleClassAction) fundamentalClass.value

/- LOCAL_DEPENDENCY_GUESS: the finite Galois class formation and its
restriction-compatible H² fundamental class are supplied at this boundary. -/
theorem finite_galois_fundamental_class_exists
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    : Nonempty (FiniteGaloisFundamentalClassData K L) := by
  sorry

theorem cap_fundamental_class_identifies_abelianization
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (D : FiniteGaloisFundamentalClassData K L) :
    Nonempty (GroupAbelianization (Gal(L / K)) ≃*
      finiteClassArtinQuotient D.normData) := by
  sorry

theorem abelian_group_abelianization_equiv
    {G : Type*} [CommGroup G] :
    Nonempty (GroupAbelianization G ≃* G) := by
  sorry

/- The finite local-global duality input is defined here, before the later
existence chapter that consumes it. The global term is the continuous
character group of the absolute Galois group, and the local term is the
restricted product of the corresponding local H¹ groups. -/
abbrev CartierConstantCoefficient (n : ℕ) :=
  ZMod n

abbrev CartierRootCoefficient
    (K : Type*) [Field K] (n : ℕ) := rootsOfUnity n K

def CartierContinuousCharacterSubgroup
    (G A : Type*) [Group G] [AddCommGroup A]
    [TopologicalSpace G] [TopologicalSpace A] [IsTopologicalAddGroup A] :
    Subgroup (G →* Multiplicative A) where
  carrier := {f | Continuous f}
  one_mem' := continuous_const
  mul_mem' := fun hf hg ↦ hf.mul hg
  inv_mem' := fun hf ↦ hf.inv

abbrev CartierContinuousACharacter
    (G A : Type*) [Group G] [AddCommGroup A]
    [TopologicalSpace G] [TopologicalSpace A] [IsTopologicalAddGroup A] :=
  Additive (↥(CartierContinuousCharacterSubgroup G A))

instance chapter01ZModTopologicalSpace (n : ℕ) :
    TopologicalSpace (CartierConstantCoefficient n) := ⊤

instance chapter01ZModIsTopologicalAddGroup (n : ℕ) :
    IsTopologicalAddGroup (CartierConstantCoefficient n) := by
  infer_instance

abbrev CartierGlobalH1
    (K : Type*) [Field K] [NumberField K] (n : ℕ) :=
  CartierContinuousACharacter (Field.absoluteGaloisGroup K)
    (CartierConstantCoefficient n)

abbrev CartierLocalH1At
    (K : Type*) [Field K] [NumberField K]
    (v : BookPlace K) (n : ℕ) :=
  CartierContinuousACharacter
    (Field.absoluteGaloisGroup (BookPlace.completion v))
    (CartierConstantCoefficient n)

def CartierRestrictedProductSubgroup
    (I : Type*) (H : I → Type*) [∀ i, AddCommGroup (H i)]
    (U : ∀ i, AddSubgroup (H i)) : AddSubgroup (∀ i, H i) where
  carrier := {x | {i | x i ∉ U i}.Finite}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    refine (hx.union hy).subset ?_
    intro i hi
    change x i ∉ U i ∨ y i ∉ U i
    by_cases hxi : x i ∉ U i
    · exact Or.inl hxi
    by_cases hyi : y i ∉ U i
    · exact Or.inr hyi
    · exfalso
      exact hi ((U i).add_mem (not_not.mp hxi) (not_not.mp hyi))
  neg_mem' := by
    intro x hx
    have hset : {i | -x i ∉ U i} = {i | x i ∉ U i} := by
      ext i
      simp
    simpa [hset] using hx

abbrev CartierRestrictedProduct
    (I : Type*) (H : I → Type*) [∀ i, AddCommGroup (H i)]
    (U : ∀ i, AddSubgroup (H i)) :=
  ↥(CartierRestrictedProductSubgroup I H U)

/- The restricted local product is parameterized by the unramified local
subgroups; this keeps the unit-tail condition visible instead of replacing it
by a full unrestricted product. -/
abbrev CartierLocalH1Product
    (K : Type*) [Field K] [NumberField K] (n : ℕ)
    (U : ∀ v : BookPlace K, AddSubgroup (CartierLocalH1At K v n)) :=
  CartierRestrictedProduct (BookPlace K) (fun v => CartierLocalH1At K v n) U

abbrev CartierKummerClassGroup (F : Type*) [Field F] (n : ℕ) :=
  Additive (Fˣ ⧸ (powMonoidHom n : Fˣ →* Fˣ).range)

def ExactAtMiddle
    {A B C : Type*} [AddZeroClass A] [AddZeroClass B] [AddZeroClass C]
    (f : A →+ B) (g : B →+ C) : Prop :=
  Set.range f = g ⁻¹' ({0} : Set C)

structure FiniteCartierDualityStatement
    (K : Type*) [Field K] [NumberField K] (n : ℕ) where
  n_pos : 0 < n
  unramified : ∀ v : BookPlace K, AddSubgroup (CartierLocalH1At K v n)
  localization : CartierGlobalH1 K n →+
    CartierLocalH1Product K n unramified
  obstruction : CartierLocalH1Product K n unramified →+
    (CartierKummerClassGroup K n →+ RationalModuloIntegers)
  localization_injective : Function.Injective localization
  exact_at_middle : ExactAtMiddle localization obstruction
  character_globalization : ∀ c,
    obstruction c = 0 → ∃ x, localization x = c

/- The coefficient realizations are no longer arbitrary carrier types: the
constant coefficient is `ZMod n`, the Cartier dual is the roots-of-unity
subgroup, and the dual H¹ term is the canonical Kummer class group. -/
structure FiniteCartierDualityData
    (K : Type uK) [Field K] [NumberField K] (n : ℕ) where
  n_pos : 0 < n
  duality : FiniteCartierDualityStatement K n

def HasFiniteCartierDualityForAllLevels
    (K : Type*) [Field K] [NumberField K] : Prop :=
  ∀ n : ℕ, 0 < n → Nonempty (FiniteCartierDualityData K n)

/- The duality theorem realizes open finite-index subgroups as class norms. -/
theorem every_open_finiteIndex_subgroup_realized_by_class_norm
    {K : Type*} [Field K] [NumberField K]
    (H : Subgroup (C_K K))
    (hopen : IsOpen (H : Set (C_K K))) (hindex : H.FiniteIndex)
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
