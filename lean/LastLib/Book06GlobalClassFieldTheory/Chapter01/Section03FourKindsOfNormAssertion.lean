import LastLib.Book06GlobalClassFieldTheory.Chapter01.Section02ConventionsAtFiniteAndInfinitePlaces

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
  decomposition :
    Nonempty (LocalScalarExtensionAt K L v ≃+*
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

def AlmostAllLocalNormPreimagesIntegral
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (a : K) : Prop :=
  ∃ S : Finset (FinitePlaceIndex K),
    ∀ v : FinitePlaceIndex K, v ∉ S →
      ∃ y : LocalScalarExtension K L v,
        y ≠ 0 ∧
          localElementNorm K L v y =
            algebraMap K (BookPlace.completion (Sum.inl v)) a ∧
          LocalNormOutputIntegralAt K L v y

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
  ∀ v : BookPlace K, ∃ y : LocalScalarExtensionAt K L v,
    y ≠ 0 ∧ localElementNormAt K L v y =
      algebraMap K (BookPlace.completion v) a

def IsIdeleNorm
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (N : GlobalNormInterface K L) (a : K) (ha : a ≠ 0) : Prop :=
  ∃ x : BookIdeleGroup L,
    N.ideleNorm x = principalIdele (Units.mk0 a ha)

def IsClassNorm
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (N : GlobalNormInterface K L) (c : C_K K) : Prop :=
  c ∈ classNormGroup N

theorem elementNorm_iff_nonzero_norm_equation
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] {a : K} (_ha : a ≠ 0) :
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

/- The local-to-global comparison data records exactly the compatibility
needed to compare the four notions without identifying their ambient groups. -/
structure LocalGlobalNormComparison
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] where
  normData : GlobalNormInterface K L
  element_to_local : ∀ {a : K}, a ≠ 0 →
    IsElementNorm K L a → IsLocalElementNorm K L a
  element_to_idele : ∀ {a : K} (ha : a ≠ 0),
    IsElementNorm K L a → IsIdeleNorm K L normData a ha
  principal_idele_iff_local : ∀ {a : K} (ha : a ≠ 0),
    IsIdeleNorm K L normData a ha ↔ IsLocalElementNorm K L a
  local_preimages_integral_almost_all : ∀ {a : K} (_ha : a ≠ 0),
    IsLocalElementNorm K L a →
      AlmostAllLocalNormPreimagesIntegral K L a
  idele_to_class : ∀ {a : K} (ha : a ≠ 0),
    IsIdeleNorm K L normData a ha →
      IsClassNorm normData (principalIdeleClassOf a ha)

theorem elementNorm_implies_local_idele_class
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (D : LocalGlobalNormComparison K L) {a : K} (ha : a ≠ 0)
    (h : IsElementNorm K L a) :
    IsLocalElementNorm K L a ∧
      IsIdeleNorm K L D.normData a ha ∧
      IsClassNorm D.normData (principalIdeleClassOf a ha) := by
  refine ⟨D.element_to_local ha h, D.element_to_idele ha h, ?_⟩
  exact D.idele_to_class ha (D.element_to_idele ha h)

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
        AlmostAllLocalNormPreimagesIntegral K L a := by
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
    (factorNorm : Gal(L / K) → F → F) : Prop :=
  ∀ σ, Set.range (factorNorm σ) = Set.range (factorNorm 1)

theorem galois_local_factors_have_same_norm_subgroup
    {K L F : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Field F]
    (factorNorm : Gal(L / K) → F → F)
    (h : GaloisLocalFactorNormSubgroupEquality K L F factorNorm) :
    ∀ σ, Set.range (factorNorm σ) = Set.range (factorNorm 1) :=
  h

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

theorem biquadratic_extensions_can_fail_hasse_norm_principle
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    (hbiquadratic : IsBiquadraticExtension K L)
    (hfailure : ¬ HasseNormPrinciple K L) :
    HasseNormFailureWitness K L := by
  sorry

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
    (K L M : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L]
    [Field M] [NumberField M] [Algebra K M] [FiniteDimensional K M]
    [IsAbelianGalois K M] : Prop :=
  ∃ (N₁ : GlobalNormInterface K L) (N₂ : GlobalNormInterface K M),
    classNormGroup N₁ = classNormGroup N₂ ∧
      elementNormSubgroup K L ≠ elementNormSubgroup K M

theorem norm_limitation_does_not_identify_element_norm_groups
    {K L M : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L]
    [Field M] [NumberField M] [Algebra K M] [FiniteDimensional K M]
    [IsAbelianGalois K M]
    (h : ClassNormLimitationCounterexample K L M) :
    ∃ (N₁ : GlobalNormInterface K L) (N₂ : GlobalNormInterface K M),
      classNormGroup N₁ = classNormGroup N₂ ∧
        elementNormSubgroup K L ≠ elementNormSubgroup K M :=
  h

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
  [abelianGalois_K_L : IsAbelianGalois K L]
  M : Type
  [field_M : Field M]
  [numberField_M : NumberField M]
  [algebra_K_M : Algebra K M]
  [finiteDimensional_K_M : FiniteDimensional K M]
  [abelianGalois_K_M : IsAbelianGalois K M]
  counterexample : ClassNormLimitationCounterexample K L M

theorem exists_class_norm_limitation_counterexample :
    Nonempty ClassNormLimitationCounterexampleData := by
  sorry

/- A locally normic element need not be a field norm merely because its
principal class lies in the class norm subgroup. -/
def ClassNormImpliesElementNormForPrincipalRepresentatives
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (N : GlobalNormInterface K L) : Prop :=
  ∀ {a : K} (ha : a ≠ 0),
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
