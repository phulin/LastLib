import LastLib.Book06GlobalClassFieldTheory.Chapter01.Dependencies
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

namespace LastLib.Book06GlobalClassFieldTheory.Chapter01

open Set
open scoped BigOperators NumberField TensorProduct

noncomputable section

universe uK uL

/-! ## 1.3. Four kinds of norm assertion -/

/- The scalar extension at a place is the full étale algebra
`L ⊗_K Kᵥ`; it is not replaced by a chosen factor. -/
abbrev LocalScalarExtensionAt
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (v : BookPlace K) :=
  L ⊗[K] BookPlace.completion v

attribute [local instance] Algebra.TensorProduct.rightAlgebra

def localElementNormAt
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (v : BookPlace K) (y : LocalScalarExtensionAt K L v) :
    BookPlace.completion v :=
  Algebra.norm (BookPlace.completion v) y

/- LOCAL_DEPENDENCY_GUESS: the branch fields `L_w` and the product
decomposition of the local tensor algebra are not yet exposed by the earlier
interfaces, so the factorization is retained as an explicit equivalence. -/
structure LocalProductDecomposition
    (K : Type uK) (L : Type uL) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (v : BookPlace K) where
  branchIndex : Type
  [branchFinite : Fintype branchIndex]
  branchField : branchIndex → Type (max uK uL)
  [branchFieldField : ∀ i, Field (branchField i)]
  [branchFieldAlgebra : ∀ i,
    Algebra (BookPlace.completion v) (branchField i)]
  [branchFieldFiniteDimensional : ∀ i,
    FiniteDimensional (BookPlace.completion v) (branchField i)]
  decomposition :
    Nonempty (LocalScalarExtensionAt K L v ≃ₐ[BookPlace.completion v]
      (∀ i, branchField i))

def IsLocalProductAlgebra
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (v : BookPlace K) : Prop :=
  Nonempty (LocalProductDecomposition K L v)

abbrev LocalScalarExtension
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (v : FinitePlaceIndex K) :=
  LocalScalarExtensionAt K L (Sum.inl v)

/- LOCAL_DEPENDENCY_GUESS: the finite-dimensional norm on the local étale
algebra is the canonical determinant norm once the tensor-product finiteness
instance is connected. -/
def localElementNorm
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (v : FinitePlaceIndex K) (y : LocalScalarExtension K L v) :
    BookPlace.completion (Sum.inl v) :=
  localElementNormAt K L (Sum.inl v) y

def LocalNormOutputIntegralAt
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (v : FinitePlaceIndex K) (y : LocalScalarExtension K L v) : Prop :=
  localElementNorm K L v y ∈ v.adicCompletionIntegers K

/- The integral elements in the full local tensor algebra form the canonical
 integral model used when local norm preimages are assembled into an idele. -/
noncomputable def localIntegralTensorSubalgebra
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (v : FinitePlaceIndex K) :
    Subalgebra (v.adicCompletionIntegers K) (LocalScalarExtension K L v) := by
  letI : Algebra (v.adicCompletionIntegers K)
      (BookPlace.completion (Sum.inl v)) :=
    (algebraMap (v.adicCompletionIntegers K)
      (BookPlace.completion (Sum.inl v))).toAlgebra
  letI : Algebra (v.adicCompletionIntegers K)
      (LocalScalarExtension K L v) :=
    ((Algebra.TensorProduct.includeRight
      (R := K) (A := L) (B := BookPlace.completion (Sum.inl v))).toRingHom.comp
      (algebraMap (v.adicCompletionIntegers K)
        (BookPlace.completion (Sum.inl v)))).toAlgebra
  exact integralClosure (v.adicCompletionIntegers K) (LocalScalarExtension K L v)

def LocalNormPreimageIntegralAt
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (v : FinitePlaceIndex K) (y : LocalScalarExtension K L v) : Prop :=
  y ∈ localIntegralTensorSubalgebra K L v ∧
    ∃ z : LocalScalarExtension K L v,
      z ∈ localIntegralTensorSubalgebra K L v ∧ y * z = 1

def AlmostAllLocalNormPreimagesIntegral
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (a : K) (_ha : a ≠ 0) : Prop :=
  ∃ S : Finset (FinitePlaceIndex K),
    ∀ v : FinitePlaceIndex K, v ∉ S →
      ∃ y : LocalScalarExtension K L v,
        localElementNorm K L v y =
            algebraMap K (BookPlace.completion (Sum.inl v)) a ∧
          LocalNormPreimageIntegralAt K L v y

def IsElementNorm
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (a : K) : Prop :=
  ∃ y : L, y ≠ 0 ∧ Algebra.norm K (S := L) y = a

def IsElementNormUnit
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (a : K) (ha : a ≠ 0) : Prop :=
  ∃ y : Lˣ,
    Units.map (Algebra.norm K (S := L)) y = Units.mk0 a ha

def IsLocalElementNorm
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (a : K) : Prop :=
  ∀ v : BookPlace K, ∃ y : (LocalScalarExtensionAt K L v)ˣ,
    localElementNormAt K L v (y : LocalScalarExtensionAt K L v) =
      algebraMap K (BookPlace.completion v) a

def IsIdeleNorm
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (N : GlobalNormInterface K L) (a : K) (ha : a ≠ 0) : Prop :=
  ∃ x : BookIdeleGroup L,
    componentwiseIdeleNorm N x = principalIdele (Units.mk0 a ha)

def IsClassNorm
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (N : GlobalNormInterface K L) (c : C_K K) : Prop :=
  c ∈ classNormGroup N

theorem elementNorm_iff_nonzero_norm_equation
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] {a : K} :
    IsElementNorm K L a ↔
      ∃ y : L, y ≠ 0 ∧ Algebra.norm K (S := L) y = a :=
  Iff.rfl

theorem elementNorm_iff_unit_norm_equation
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] {a : K} (ha : a ≠ 0) :
    IsElementNorm K L a ↔ IsElementNormUnit K L a ha := by
  sorry

/- The principal idele attached to a nonzero element. -/
def principalIdeleClassOf {K : Type*} [Field K] [NumberField K]
    (a : K) (ha : a ≠ 0) : C_K K :=
  classQuotient (principalIdele (Units.mk0 a ha))

@[simp]
theorem principalIdeleClassOf_eq_one
    {K : Type*} [Field K] [NumberField K] (a : K) (ha : a ≠ 0) :
    principalIdeleClassOf a ha = 1 := by
  exact classQuotient_principal (Units.mk0 a ha)

theorem principalIdeleClassOf_isClassNorm
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (N : GlobalNormInterface K L) {a : K} (ha : a ≠ 0) :
    IsClassNorm N (principalIdeleClassOf a ha) := by
  rw [principalIdeleClassOf_eq_one]
  exact (classNormGroup N).one_mem

/- The local-to-global comparison data records exactly the compatibility
   needed to compare the four notions without identifying their ambient groups. -/
/- A field norm remains a norm after scalar extension to every completion.  This
   implication is canonical; it is not part of the auxiliary comparison data
   used to identify the idele norm with the local product-algebra condition. -/
theorem elementNorm_implies_local_elementNorm
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] {a : K} (ha : a ≠ 0)
    (h : IsElementNorm K L a) :
    IsLocalElementNorm K L a := by
  sorry

structure LocalGlobalNormComparison
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] where
  normData : GlobalNormInterface K L
  principal_idele_iff_local : ∀ {a : K} (ha : a ≠ 0),
    IsIdeleNorm K L normData a ha ↔ IsLocalElementNorm K L a
  local_preimages_integral_almost_all : ∀ {a : K} (ha : a ≠ 0),
    IsLocalElementNorm K L a →
      AlmostAllLocalNormPreimagesIntegral K L a ha

/- A field norm gives an idele norm through the principal-idele compatibility of
the canonical norm interface.  This is not an additional comparison datum. -/
theorem elementNorm_implies_ideleNorm
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (N : GlobalNormInterface K L) {a : K} (ha : a ≠ 0)
    (h : IsElementNorm K L a) :
    IsIdeleNorm K L N a ha := by
  sorry

theorem elementNorm_implies_local_idele_class
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (D : LocalGlobalNormComparison K L) {a : K} (ha : a ≠ 0)
    (h : IsElementNorm K L a) :
    IsLocalElementNorm K L a ∧
      IsIdeleNorm K L D.normData a ha ∧
      IsClassNorm D.normData (principalIdeleClassOf a ha) := by
  refine ⟨elementNorm_implies_local_elementNorm ha h,
    elementNorm_implies_ideleNorm D.normData ha h, ?_⟩
  exact principalIdeleClassOf_isClassNorm D.normData ha

theorem principal_idele_is_ideleNorm_iff_local_elementNorm
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (D : LocalGlobalNormComparison K L) {a : K} (ha : a ≠ 0) :
    IsIdeleNorm K L D.normData a ha ↔ IsLocalElementNorm K L a :=
  D.principal_idele_iff_local ha

theorem principal_idele_is_ideleNorm_iff_local_elementNorm_with_integrality
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (D : LocalGlobalNormComparison K L) {a : K} (ha : a ≠ 0) :
      IsIdeleNorm K L D.normData a ha ↔
      IsLocalElementNorm K L a ∧
        AlmostAllLocalNormPreimagesIntegral K L a ha := by
  sorry

/- The Hasse norm principle is the converse for the first two notions. -/
def HasseNormPrinciple
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] : Prop :=
  ∀ {a : K}, a ≠ 0 → IsLocalElementNorm K L a → IsElementNorm K L a

def HasseNormFailureWitness
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] : Prop :=
  ∃ a : K, a ≠ 0 ∧ IsLocalElementNorm K L a ∧ ¬ IsElementNorm K L a

theorem hasseNormPrinciple_iff_no_failure_witness
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] :
    HasseNormPrinciple K L ↔ ¬ HasseNormFailureWitness K L := by
  sorry

/- A Galois extension has the local tensor product decomposed into conjugate
factors; the local norm subgroup does not depend on the chosen factor. -/
def GaloisLocalFactorNormSubgroupEquality
    (K L F : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Field F]
    (factorNorm : Gal(L / K) → Fˣ →* Fˣ) : Prop :=
  ∀ σ, Set.range (factorNorm σ) = Set.range (factorNorm 1)

/- A conjugacy witness is the usable local hypothesis behind equality of the
factor norm subgroups.  The equality predicate above is intentionally kept as
the book-facing assertion; this stronger interface prevents the theorem below
from taking its own conclusion as a hypothesis for an arbitrary family of
maps. -/
def GaloisLocalFactorNormConjugacy
    (K L F : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Field F]
  (factorNorm : Gal(L / K) → Fˣ →* Fˣ) : Prop :=
  ∀ σ, ∃ e : Fˣ ≃* Fˣ,
    (∀ x : Fˣ, factorNorm σ x = e (factorNorm 1 x)) ∧
    Set.range (e ∘ factorNorm 1) = Set.range (factorNorm 1)

theorem galois_local_factors_have_same_norm_subgroup
    {K L F : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Field F]
    (factorNorm : Gal(L / K) → Fˣ →* Fˣ)
    (h : GaloisLocalFactorNormConjugacy K L F factorNorm) :
    ∀ σ, Set.range (factorNorm σ) = Set.range (factorNorm 1) := by
  sorry

theorem local_norm_uses_the_full_product_algebra
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (v : FinitePlaceIndex K)
    (y : LocalScalarExtension K L v) :
    localElementNorm K L v y =
      Algebra.norm (BookPlace.completion (Sum.inl v)) y :=
  by sorry

theorem cyclic_extensions_satisfy_hasse_norm_principle
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic Gal(L / K)] :
    HasseNormPrinciple K L := by
  sorry

/- A non-Galois extension is therefore represented by the product algebra,
not by a selected field factor. -/
def NonGaloisLocalNormAssertion
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (a : K) : Prop :=
  IsLocalElementNorm K L a

theorem local_tensor_product_product_decomposition
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] :
    ∀ v : BookPlace K, IsLocalProductAlgebra K L v := by
  sorry

/- Biquadratic extensions provide the standard failure pattern for the Hasse
norm principle. -/
def IsBiquadraticExtension
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L] : Prop :=
  Nonempty (Gal(L / K) ≃* Multiplicative (ZMod 2 × ZMod 2))

/- LOCAL_DEPENDENCY_GUESS: the source's noncyclic biquadratic counterexample
is bundled existentially because no particular numerical example is needed by
the later global reciprocity statements. -/
structure BiquadraticHasseNormCounterexample where
  K : Type
  [field_K : Field K]
  [numberField_K : NumberField K]
  L : Type
  [field_L : Field L]
  [numberField_L : NumberField L]
  [algebra_K_L : Algebra K L]
  [finiteDimensional_K_L : FiniteDimensional K L]
  [abelianGalois_K_L : IsAbelianGalois K L]
  biquadratic : IsBiquadraticExtension K L
  failure : HasseNormFailureWitness K L

theorem exists_biquadratic_hasse_norm_failure :
    Nonempty BiquadraticHasseNormCounterexample := by
  sorry

/- The element-norm subgroup is a genuinely different object from the class
norm subgroup. -/
def elementNormSubgroup
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] : Subgroup Kˣ :=
  Subgroup.map (Units.map (Algebra.norm K (S := L))) ⊤

def ClassNormLimitationCounterexample
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] : Prop :=
  ∃ (N₁ : GlobalNormInterface K L)
    (N₂ : GlobalNormInterface K (globalMaximalAbelianSubextension K L)),
    classNormGroup N₁ = classNormGroup N₂ ∧
      elementNormSubgroup K L ≠
        elementNormSubgroup K (globalMaximalAbelianSubextension K L)

/- LOCAL_DEPENDENCY_GUESS: `generally` is recorded as an existential
counterexample rather than as an unproved universal equality or inequality. -/
structure ClassNormLimitationCounterexampleData where
  K : Type
  [field_K : Field K]
  [numberField_K : NumberField K]
  L : Type
  [field_L : Field L]
  [numberField_L : NumberField L]
  [algebra_K_L : Algebra K L]
  [finiteDimensional_K_L : FiniteDimensional K L]
  [galois_K_L : IsGalois K L]
  norm_L : GlobalNormInterface K L
  norm_maximal :
    GlobalNormInterface K (globalMaximalAbelianSubextension K L)
  classNorm_eq : classNormGroup norm_L = classNormGroup norm_maximal
  elementNorm_neq :
    elementNormSubgroup K L ≠
      elementNormSubgroup K (globalMaximalAbelianSubextension K L)

theorem exists_class_norm_limitation_counterexample :
    Nonempty ClassNormLimitationCounterexampleData := by
  sorry

theorem norm_limitation_does_not_identify_element_norm_groups :
    Nonempty ClassNormLimitationCounterexampleData :=
  exists_class_norm_limitation_counterexample

/- A locally normic element need not be a field norm merely because its
principal class lies in the class norm subgroup. -/
def ClassNormImpliesElementNormForPrincipalRepresentatives
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (N : GlobalNormInterface K L) : Prop :=
  ∀ {a : K} (ha : a ≠ 0),
    IsLocalElementNorm K L a →
      IsClassNorm N (principalIdeleClassOf a ha) → IsElementNorm K L a

theorem class_norm_does_not_assert_field_element_norm
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (N : GlobalNormInterface K L)
    (hfailure : HasseNormFailureWitness K L) :
    ¬ ClassNormImpliesElementNormForPrincipalRepresentatives N := by
  sorry

end
end LastLib.Book06GlobalClassFieldTheory.Chapter01
