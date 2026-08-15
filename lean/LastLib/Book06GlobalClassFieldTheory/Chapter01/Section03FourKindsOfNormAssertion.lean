import LastLib.Book06GlobalClassFieldTheory.Chapter01.Dependencies
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.LinearAlgebra.Charpoly.BaseChange

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
  constructor
  · rintro ⟨y, hy, hnorm⟩
    refine ⟨Units.mk0 y hy, ?_⟩
    apply Units.ext
    change Algebra.norm K y = a
    exact hnorm
  · rintro ⟨u, hu⟩
    refine ⟨(u : L), Units.ne_zero u, ?_⟩
    have h := congrArg Units.val hu
    simpa using h

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
  rcases h with ⟨x, hx, hnorm⟩
  have hx' : x ≠ 0 := by
    intro hx0
    apply ha
    rw [← hnorm, hx0]
    simp
  intro v
  let f : L →+* LocalScalarExtensionAt K L v :=
    Algebra.TensorProduct.includeLeftRingHom
  refine ⟨Units.map f (Units.mk0 x hx'), ?_⟩
  change Algebra.norm (BookPlace.completion v) (f x) =
    algebraMap K (BookPlace.completion v) a
  let e := Algebra.TensorProduct.commRight K (BookPlace.completion v) L
  have he : e.symm (f x) = Algebra.TensorProduct.includeRight x := by
    simp [e, f]
  calc
    Algebra.norm (BookPlace.completion v) (f x) =
        Algebra.norm (BookPlace.completion v) (e.symm (f x)) := by
      rw [← Algebra.norm_eq_of_algEquiv e (e.symm (f x))]
      simp
    _ = Algebra.norm (BookPlace.completion v)
          (Algebra.TensorProduct.includeRight x) := by rw [he]
    _ = LinearMap.det
          (Algebra.lmul (BookPlace.completion v)
            (BookPlace.completion v ⊗[K] L) (1 ⊗ₜ[K] x)) := rfl
    _ = LinearMap.det ((Algebra.lmul K L x).baseChange (BookPlace.completion v)) := by
      rw [Algebra.baseChange_lmul]
    _ = algebraMap K (BookPlace.completion v)
          (LinearMap.det (Algebra.lmul K L x)) := by
      exact LinearMap.det_baseChange (Algebra.lmul K L x)
    _ = algebraMap K (BookPlace.completion v) a := by
      rw [← hnorm, Algebra.norm_apply]

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
  rcases h with ⟨y, hy, hnorm⟩
  refine ⟨principalIdele (Units.mk0 y hy), ?_⟩
  rw [N.principal_compatibility_apply]
  congr 1
  apply Units.ext
  change Algebra.norm K y = a
  exact hnorm

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
  constructor
  · intro h
    have hlocal := (D.principal_idele_iff_local ha).mp h
    exact ⟨hlocal, D.local_preimages_integral_almost_all ha hlocal⟩
  · rintro ⟨hlocal, _hintegral⟩
    exact (D.principal_idele_iff_local ha).mpr hlocal

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
  constructor
  · intro hH hW
    rcases hW with ⟨a, ha, hlocal, hnot⟩
    exact hnot (hH ha hlocal)
  · intro hNo a ha hlocal
    by_contra hnot
    exact hNo ⟨a, ha, hlocal, hnot⟩

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
  intro σ
  rcases h σ with ⟨e, he, hrange⟩
  have hcomp : Set.range (factorNorm σ) = Set.range (e ∘ factorNorm 1) := by
    ext z
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      exact (he x).symm.trans hx
    · rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      exact (he x).trans hx
  exact hcomp.trans hrange

theorem local_norm_uses_the_full_product_algebra
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (v : FinitePlaceIndex K)
    (y : LocalScalarExtension K L v) :
    localElementNorm K L v y =
      Algebra.norm (BookPlace.completion (Sum.inl v)) y :=
  rfl

/- The global theorem is stated directly for the canonical tensor-product local
   norm predicate.  No arbitrary local/global comparison record is allowed to
   stand in for the cyclic Hasse norm theorem. -/
theorem global_cyclic_hasse_norm_theorem
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic Gal(L / K)] :
    HasseNormPrinciple K L := by
  sorry

theorem cyclic_extensions_satisfy_hasse_norm_principle
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic Gal(L / K)] :
    HasseNormPrinciple K L := by
  exact global_cyclic_hasse_norm_theorem

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
  intro v
  let : Module.FinitePresentation K L := Module.finitePresentation_of_finite K L
  let : Algebra.Etale K L :=
    { formallyEtale := Algebra.FormallyEtale.of_isSeparable K L
      finitePresentation := inferInstance }
  have hEtale : Algebra.Etale (BookPlace.completion v)
      (BookPlace.completion v ⊗[K] L) := inferInstance
  rcases (Algebra.Etale.iff_exists_algEquiv_prod
      (K := BookPlace.completion v)
      (A := BookPlace.completion v ⊗[K] L)).mp hEtale with
    ⟨I, hI, F, hF, hFA, e, hfinite⟩
  let : Fintype I := Fintype.ofFinite I
  let (i : I) : Field (F i) := hF i
  let (i : I) : Algebra (BookPlace.completion v) (F i) := hFA i
  let (i : I) : FiniteDimensional (BookPlace.completion v) (F i) :=
    hfinite i |>.1
  let eI := Fintype.equivFin I
  let F' : Fin (Fintype.card I) → Type _ := fun j => F (eI.symm j)
  let (j : Fin (Fintype.card I)) : Field (F' j) := hF (eI.symm j)
  let (j : Fin (Fintype.card I)) : Algebra (BookPlace.completion v) (F' j) :=
    hFA (eI.symm j)
  let (j : Fin (Fintype.card I)) :
      FiniteDimensional (BookPlace.completion v) (F' j) := hfinite (eI.symm j) |>.1
  exact ⟨{
    branchIndex := Fin (Fintype.card I)
    branchField := F'
    decomposition := ⟨(Algebra.TensorProduct.commRight K
      (BookPlace.completion v) L).symm.trans
        (e.trans (AlgEquiv.piCongrLeft' (BookPlace.completion v) F eI))⟩
  }⟩

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
  normData : GlobalNormInterface K L
  biquadratic : IsBiquadraticExtension K L
  failure : HasseNormFailureWitness K L

/- A concrete presentation is kept at the first point where the source uses a
   biquadratic counterexample.  The later local analysis can therefore refer to
   the displayed field without replacing it by an unspecified noncyclic
   extension. -/
structure RationalBiquadraticPresentation
    (L : Type) [Field L] [Algebra ℚ L] [NumberField L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L] where
  sqrt13 : L
  sqrt17 : L
  sqrt13_sq : sqrt13 ^ 2 = (13 : L)
  sqrt17_sq : sqrt17 ^ 2 = (17 : L)
  adjoin_eq_top :
    IntermediateField.adjoin ℚ ({sqrt13, sqrt17} : Set L) = ⊤
  galoisGroup_equiv :
    Gal(L / ℚ) ≃* Multiplicative (ZMod 2 × ZMod 2)

structure RationalBiquadraticHasseNormCounterexample where
  L : Type
  [field_L : Field L]
  [numberField_L : NumberField L]
  [algebra_L : Algebra ℚ L]
  [finiteDimensional_L : FiniteDimensional ℚ L]
  [abelianGalois_L : IsAbelianGalois ℚ L]
  [fintype_galois_L : Fintype (Gal(L / ℚ))]
  presentation : RationalBiquadraticPresentation L
  normData : GlobalNormInterface ℚ L
  failure : HasseNormFailureWitness ℚ L

attribute [instance] RationalBiquadraticHasseNormCounterexample.field_L
  RationalBiquadraticHasseNormCounterexample.numberField_L
  RationalBiquadraticHasseNormCounterexample.algebra_L
  RationalBiquadraticHasseNormCounterexample.finiteDimensional_L
  RationalBiquadraticHasseNormCounterexample.abelianGalois_L
  RationalBiquadraticHasseNormCounterexample.fintype_galois_L

theorem rational_biquadratic_hasse_norm_failure :
    Nonempty RationalBiquadraticHasseNormCounterexample := by
  sorry

theorem exists_biquadratic_hasse_norm_failure :
    Nonempty BiquadraticHasseNormCounterexample := by
  rcases rational_biquadratic_hasse_norm_failure with ⟨D⟩
  refine ⟨{
    K := ℚ
    L := D.L
    normData := D.normData
    biquadratic := ⟨D.presentation.galoisGroup_equiv⟩
    failure := D.failure }⟩

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
  ∃ D : GlobalClassNormLimitationData K L,
    classNormGroup D.norm_L = classNormGroup D.norm_maximal ∧
      ¬ IsAbelianGalois K L ∧
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
  [fintype_galois_K_L : Fintype (Gal(L / K))]
  nonabelian : ¬ IsAbelianGalois K L
  galoisGroup_equiv : Nonempty (Gal(L / K) ≃* Equiv.Perm (Fin 3))
  limitation : GlobalClassNormLimitationData K L
  elementNorm_neq :
    elementNormSubgroup K L ≠
      elementNormSubgroup K (globalMaximalAbelianSubextension K L)

attribute [instance] ClassNormLimitationCounterexampleData.field_K
  ClassNormLimitationCounterexampleData.numberField_K
  ClassNormLimitationCounterexampleData.field_L
  ClassNormLimitationCounterexampleData.numberField_L
  ClassNormLimitationCounterexampleData.algebra_K_L
  ClassNormLimitationCounterexampleData.finiteDimensional_K_L
  ClassNormLimitationCounterexampleData.galois_K_L
  ClassNormLimitationCounterexampleData.fintype_galois_K_L

theorem class_norm_limitation_counterexample_data_realizes
    (D : ClassNormLimitationCounterexampleData) :
    ClassNormLimitationCounterexample D.K D.L := by
  exact ⟨D.limitation, global_class_norm_limitation D.limitation,
    D.nonabelian, D.elementNorm_neq⟩

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
  intro hassertion
  rcases hfailure with ⟨a, ha, hlocal, hnot⟩
  apply hnot
  exact hassertion ha hlocal (principalIdeleClassOf_isClassNorm N ha)

end
end LastLib.Book06GlobalClassFieldTheory.Chapter01
