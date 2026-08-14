import LastLib.Book06GlobalClassFieldTheory.Chapter01.Dependencies
import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.FieldTheory.AlgebraicClosure
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

/- The source of the cap-product equivalence is the standard negative-degree
identification for the trivial coefficient module.  Exposing its exact type
here keeps the later idelic quotient equivalence from silently assuming an
unrelated abstract equivalence between the two endpoints. -/
noncomputable def trivialTateNegativeTwoAbelianizationEquiv
    (G : Type) [Group G] [Fintype G] :
    chapter05TateCohomology G (Rep.trivial ℤ G ℤ) (-2) ≃+
      Additive (GroupAbelianization G) := by
  sorry

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
  /- The local invariant normalizations used by the global sum: finite local
     Brauer groups identify with `Q/Z`, real ones have exactly their two
     torsion values, and complex ones are zero.  The canonical Brauer carrier
     is kept as a plain type because its additive structure is not yet exposed
     by the pinned Mathlib API. -/
  finite_invariant_bijective : ∀ v : FinitePlaceIndex K,
    Function.Bijective (invariant (Sum.inl v))
  real_invariant_range : ∀ v : InfinitePlaceIndex K,
    NumberField.InfinitePlace.IsReal v →
      Set.range (invariant (Sum.inr v)) =
        {x : RationalModuloIntegers | 2 • x = 0}
  complex_brauer_subsingleton : ∀ v : InfinitePlaceIndex K,
    NumberField.InfinitePlace.IsComplex v →
      ∀ b₁ b₂ : BookCanonicalBrauerGroup (BookPlace.completion (Sum.inr v)),
        b₁ = b₂
  complex_invariant_zero : ∀ v : InfinitePlaceIndex K,
    NumberField.InfinitePlace.IsComplex v →
      ∀ b, invariant (Sum.inr v) b = 0

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
  action : Representation ℤ (Gal(L / K)) (Additive (C_K L))

noncomputable def globalIdeleClassCoefficientRep
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (A : GlobalIdeleClassGaloisActionData K L) :
    Rep ℤ (Gal(L / K)) := by
  exact Rep.of A.action

/- The degree-zero Tate group is identified with the class norm quotient
separately from the cap-product theorem.  Keeping this bridge as its own
object prevents the reciprocity equivalence from being smuggled into the
fundamental-class data as an unrelated field. -/
structure GlobalIdeleClassDegreeZeroNormBridge
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (N : GlobalNormInterface K L)
    (A : GlobalIdeleClassGaloisActionData K L) where
  equiv :
    chapter05TateCohomology (Gal(L / K))
        (globalIdeleClassCoefficientRep A) 0 ≃+
      Additive (finiteClassArtinQuotient N)

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

/- The fixed-points modulo norm identification is a consequence of the
degree-zero calculation; it is deliberately not an input to the fundamental
class package. -/
theorem global_idele_class_degree_zero_norm_bridge_exists
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (D : FiniteGaloisFundamentalClassData K L) :
    Nonempty (GlobalIdeleClassDegreeZeroNormBridge K L
      D.normData D.ideleClassAction) := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the finite Galois class formation and its
restriction-compatible H² fundamental class are supplied at this boundary. -/
theorem finite_galois_fundamental_class_exists
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    : Nonempty (FiniteGaloisFundamentalClassData K L) := by
  sorry

/- The top-subgroup cap map must be transported back to the original Galois
   group before it can be compared with the degree-zero norm bridge. -/
structure GlobalCapProductDegreeZeroData
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (D : FiniteGaloisFundamentalClassData K L) where
  degreeZeroNormBridge :
    GlobalIdeleClassDegreeZeroNormBridge K L
      D.normData D.ideleClassAction
  topRestriction : Chapter05TopRestrictionTateIso (Gal(L / K))
    (globalIdeleClassCoefficientRep D.ideleClassAction)
  topRestrictionTrivial : Chapter05TopRestrictionTrivialTateIso (Gal(L / K))
  capEquiv :
    chapter05TateCohomology (Gal(L / K))
        (Rep.trivial ℤ (Gal(L / K)) ℤ) (-2) ≃+
      chapter05TateCohomology (Gal(L / K))
        (globalIdeleClassCoefficientRep D.ideleClassAction) 0
  capEquiv_is_cap :
    ∀ x : chapter05TateCohomology (Gal(L / K))
        (Rep.trivial ℤ (Gal(L / K)) ℤ) (-2),
      capEquiv x =
        (topRestriction.iso 0).hom
          (D.capProduct.cap (⊤ : Subgroup (Gal(L / K))) (-2)
            ((topRestrictionTrivial.iso (-2)).inv x))

theorem global_cap_product_degree_zero_data_exists
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (D : FiniteGaloisFundamentalClassData K L) :
    Nonempty (GlobalCapProductDegreeZeroData D) := by
  sorry

structure GlobalCapProductNormQuotientEquivalence
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (D : FiniteGaloisFundamentalClassData K L)
    (P : GlobalCapProductDegreeZeroData D) where
  equiv : Additive (GroupAbelianization (Gal(L / K))) ≃+
    Additive (finiteClassArtinQuotient D.normData)
  compatible :
    ∀ x : Additive (GroupAbelianization (Gal(L / K))),
      equiv x = P.degreeZeroNormBridge.equiv
        (P.capEquiv ((trivialTateNegativeTwoAbelianizationEquiv
          (Gal(L / K))).symm x))

theorem cap_fundamental_class_identifies_abelianization
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (D : FiniteGaloisFundamentalClassData K L)
    (P : GlobalCapProductDegreeZeroData D) :
    Nonempty (GlobalCapProductNormQuotientEquivalence D P) := by
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

/- The Cartier dual μₙ is geometric: using K-rational roots here would make
the interface silently assume μₙ ⊂ K. -/
abbrev CartierRootCoefficient
    (K : Type*) [Field K] (n : ℕ) := rootsOfUnity n (AlgebraicClosure K)

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

abbrev CartierNthPowerSubgroup (F : Type*) [Field F] (n : ℕ) : Subgroup Fˣ :=
  (powMonoidHom n : Fˣ →* Fˣ).range

abbrev CartierKummerClassGroup (F : Type*) [Field F] (n : ℕ) :=
  Additive (Fˣ ⧸ CartierNthPowerSubgroup F n)

def cartierKummerClassMk
    {F : Type*} [Field F] (n : ℕ) (x : Fˣ) : CartierKummerClassGroup F n :=
  Additive.ofMul (QuotientGroup.mk' (CartierNthPowerSubgroup F n) x)

noncomputable def cartierKummerRestriction
    {K F : Type*} [Field K] [Field F] (n : ℕ) (f : K →+* F) :
    CartierKummerClassGroup K n →+ CartierKummerClassGroup F n :=
  let q : Kˣ ⧸ CartierNthPowerSubgroup K n →*
      Fˣ ⧸ CartierNthPowerSubgroup F n :=
    QuotientGroup.map (CartierNthPowerSubgroup K n)
      (CartierNthPowerSubgroup F n) (Units.map f.toMonoidHom) (by
        intro x hx
        rcases hx with ⟨y, rfl⟩
        exact ⟨Units.map f.toMonoidHom y, by simp⟩)
  q.toAdditive

theorem cartierKummerRestriction_mk
    {K F : Type*} [Field K] [Field F] (n : ℕ) (f : K →+* F) (x : Kˣ) :
    cartierKummerRestriction n f (cartierKummerClassMk n x) =
      cartierKummerClassMk n (Units.map f.toMonoidHom x) := by
  sorry

abbrev CartierLocalKummerClassGroup
    (K : Type*) [Field K] [NumberField K]
    (v : BookPlace K) (n : ℕ) :=
  CartierKummerClassGroup (BookPlace.completion v) n

noncomputable def cartierKummerLocalization
    {K : Type*} [Field K] [NumberField K]
    (v : BookPlace K) (n : ℕ) :
    CartierKummerClassGroup K n →+
      CartierLocalKummerClassGroup K v n :=
  cartierKummerRestriction n (algebraMap K (BookPlace.completion v))

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
  localCupInvariant : ∀ v : BookPlace K,
    CartierLocalH1At K v n →+
      CartierLocalKummerClassGroup K v n →+ RationalModuloIntegers
  obstruction_is_local_sum :
    ∀ (c : CartierLocalH1Product K n unramified)
      (a : CartierKummerClassGroup K n),
      ∃ s : Finset (BookPlace K),
        (∀ v ∉ s,
          localCupInvariant v (c.1 v) (cartierKummerLocalization v n a) = 0) ∧
          obstruction c a = Finset.sum s
            (fun v =>
              localCupInvariant v (c.1 v) (cartierKummerLocalization v n a))
  localization_injective : Function.Injective localization
  exact_at_middle : ExactAtMiddle localization obstruction

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
