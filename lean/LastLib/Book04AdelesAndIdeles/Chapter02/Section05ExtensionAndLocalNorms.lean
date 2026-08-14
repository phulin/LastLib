import LastLib.Book04AdelesAndIdeles.Chapter02.Core

namespace LastLib.Book04AdelesAndIdeles.Chapter02

noncomputable section

open NumberField
open scoped BigOperators TensorProduct WithTop

/-! ## 2.5. Extension and local norms -/

/-- A branch completion product in the tensor-product form used by the book. -/
def Chapter02TensorCompletionBranchDecomposition
    (K L Kᵥ : Type*) [CommRing K] [CommRing L] [CommRing Kᵥ]
    [Algebra K L] [Algebra K Kᵥ]
    {ι : Type*} [Fintype ι] (Lω : ι → Type*)
    [∀ i, CommRing (Lω i)] : Prop :=
  Nonempty (L ⊗[K] Kᵥ ≃+* (∀ i, Lω i))

/-- A finite branch lies over a base finite place when its restriction is in the
same absolute-value class. -/
def Chapter02FinitePlaceLiesOver
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (v : Chapter02FinitePlace K) (w : Chapter02FinitePlace L) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ x : K, (v x) ^ c = w (algebraMap K L x)

/-- The precise `L ⊗_K Kᵥ ≅ ∏_{w|v} L_w` interface.  The finite branch index is
kept explicit because it is the object that the completed-product theorem
separates. -/
structure Chapter02FiniteLocalBranchDecomposition
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (v : Chapter02FinitePlace K) {ι : Type*} [Fintype ι]
    (w : ι → Chapter02FinitePlace L) where
  liesOver : ∀ i, Chapter02FinitePlaceLiesOver v (w i)
  distinct : Function.Injective w
  exhaustive : ∀ z : Chapter02FinitePlace L,
    Chapter02FinitePlaceLiesOver v z → ∃ i, w i = z
  decomposition : Nonempty
    (L ⊗[K] Chapter02FiniteCompletion v ≃+*
      (∀ i, Chapter02FiniteCompletion (w i)))

/-- The integral-completion branch used by the earlier CRT API. -/
abbrev Chapter02BranchCompletion
    (B : Type*) [CommRing B] (P : Ideal B) [P.IsPrime] : Type _ :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.branchCompletion B P

/-- A packaged branch decomposition, with its finite branch index and product
isomorphism available to later chapters. -/
structure Chapter02TensorCompletionBranchData
    (K L Kᵥ : Type*) [CommRing K] [CommRing L] [CommRing Kᵥ]
    [Algebra K L] [Algebra K Kᵥ]
    {ι : Type*} [Fintype ι] (Lω : ι → Type*)
    [∀ i, CommRing (Lω i)] where
  decomposition : Chapter02TensorCompletionBranchDecomposition K L Kᵥ Lω

/-- The completed-product theorem imported from the earlier completion chapter,
exposed in the branch notation used here. -/
theorem chapter02_completed_product_decomposition
    {A B : Type*} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [Algebra A B] [Algebra.IsIntegral A B]
    {g : ℕ} (m : Ideal A) (π : A) (P : Fin g → Ideal B) (e : Fin g → ℕ)
    [m.IsMaximal] [hprime : ∀ i, (P i).IsPrime]
    [hmax : ∀ i, (P i).IsMaximal]
    (huniformizer : m = Ideal.span {π})
    (hfinite : Module.Finite A B) (hfree : Module.Free A B)
    (hfactor : ∀ n : ℕ,
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.extendedPrincipalPowerIdeal
          A B π n = ⨅ i, P i ^ (n * e i))
    (he : ∀ i, 0 < e i)
    (hpair : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.pairwiseCoprimeIdeals P)
    (hP : ∀ i, (P i).LiesOver m)
    (hP_exhaustive :
      ∀ (q : Ideal B), q.IsPrime → q.LiesOver m → ∃ i, P i = q)
    (hP_distinct : Function.Injective P)
    [Algebra (AdicCompletion m A) (B ⊗[A] AdicCompletion m A)]
    [∀ i, Algebra A (Chapter02BranchCompletion B (P i))]
    [∀ i, Algebra (AdicCompletion m A) (Chapter02BranchCompletion B (P i))]
    [∀ i, IsScalarTower A B (Chapter02BranchCompletion B (P i))]
    [∀ i, IsScalarTower A (AdicCompletion m A)
      (Chapter02BranchCompletion B (P i))] :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.hasCompletedAlgebraProduct
      A B (AdicCompletion m A) (fun i => Chapter02BranchCompletion B (P i)) := by
  sorry

/-- The finite-precision version of branch separation. -/
theorem chapter02_finite_precision_branch_indexing
    {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    (I : Ideal R) (J : ι → Ideal R)
    (hcrt : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Chapter12CompatibleCRTSystem
      I J) :
    Nonempty (AdicCompletion I R ≃+* (∀ i, AdicCompletion (J i) R)) := by
  sorry

/-- The normalized absolute value attached to an additive valuation and a
residue-field cardinality. -/
noncomputable def Chapter02ValuationNormalizedValue
    {K : Type*} [Field K] (q : ℕ) (v : AddValuation K (WithTop ℤ)) (x : K) : ℝ :=
  by
    classical
    exact if hx : x = 0 then 0 else
      Real.rpow (q : ℝ)
        (-((WithTop.untopD (0 : ℤ) (v x) : ℤ) : ℝ))

/-- Data sufficient to turn the valuation norm formula into the book's literal
absolute-value identity. -/
structure Chapter02NormalizedLocalNormData
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] where
  abvK : AbsoluteValue K ℝ
  abvL : AbsoluteValue L ℝ
  vK : AddValuation K (WithTop ℤ)
  vL : AddValuation L (WithTop ℤ)
  qK : ℕ
  qL : ℕ
  f : ℕ
  qK_pos : 1 < qK
  qL_pos : 1 < qL
  residue_cardinality : qL = qK ^ f
  abvK_normalized : ∀ x, abvK x = Chapter02ValuationNormalizedValue qK vK x
  abvL_normalized : ∀ x, abvL x = Chapter02ValuationNormalizedValue qL vL x
  norm_valuation : ∀ y, y ≠ 0 →
    vK (Algebra.norm K y) = (f : WithTop ℤ) * vL y

/-- With the finite-branch valuation formula and the residue-cardinality
normalization, the local field norm has no extra correction exponent. -/
theorem chapter02_normalized_local_norm_identity
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (D : Chapter02NormalizedLocalNormData K L) (y : L) :
    D.abvK (Algebra.norm K y) = D.abvL y := by
  sorry

theorem chapter02_normalized_local_norm_identity_on_nonzero_elements
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (D : Chapter02NormalizedLocalNormData K L) {y : L} (_hy : y ≠ 0) :
    D.abvK (Algebra.norm K y) = D.abvL y := by
  exact chapter02_normalized_local_norm_identity D y

theorem chapter02_normalized_local_scalar_restriction
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (D : Chapter02NormalizedLocalNormData K L) (a : K) :
    D.abvL (algebraMap K L a) =
      D.abvK a ^ Module.finrank K L := by
  sorry

theorem chapter02_finite_branch_norm_formula_from_order_and_residue_degree
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (qK qL f : ℕ) (hq : qL = qK ^ f)
    (hord : ∀ y : L, y ≠ 0 →
      vK (Algebra.norm K y) = (f : WithTop ℤ) * vL y) {y : L} (hy : y ≠ 0) :
    Chapter02ValuationNormalizedValue qK vK (Algebra.norm K y) =
      Chapter02ValuationNormalizedValue qL vL y := by
  sorry

/-- The norm on a finite product algebra is the product of the component norms. -/
def Chapter02ProductAlgebraNorm
    (K : Type*) [Field K] {ι : Type*} [Fintype ι]
    (Lω : ι → Type*) [∀ i, Field (Lω i)]
    [∀ i, Algebra K (Lω i)] [∀ i, Module.Finite K (Lω i)]
    (x : ∀ i, Lω i) : K :=
  ∏ i, Algebra.norm K (x i)

theorem chapter02_product_algebra_norm_is_componentwise
    (K : Type*) [Field K] {ι : Type*} [Fintype ι]
    (Lω : ι → Type*) [∀ i, Field (Lω i)]
    [∀ i, Algebra K (Lω i)] [∀ i, Module.Finite K (Lω i)]
    (x : ∀ i, Lω i) :
    Chapter02ProductAlgebraNorm K Lω x = ∏ i, Algebra.norm K (x i) := by
  rfl

theorem chapter02_product_algebra_norm_absolute_value_is_componentwise
    (K : Type*) [Field K] {ι : Type*} [Fintype ι]
    (Lω : ι → Type*) [∀ i, Field (Lω i)]
    [∀ i, Algebra K (Lω i)] [∀ i, Module.Finite K (Lω i)]
    (abvK : AbsoluteValue K ℝ)
    (abvω : ∀ i, AbsoluteValue (Lω i) ℝ)
    (hω : ∀ i y, abvK (Algebra.norm K y) = abvω i y)
    (x : ∀ i, Lω i) :
    abvK (Chapter02ProductAlgebraNorm K Lω x) = ∏ i, abvω i (x i) := by
  sorry

theorem chapter02_local_norms_are_compatible_with_the_product_formula
    (K : Type*) [Field K] {ι : Type*} [Fintype ι]
    (Lω : ι → Type*) [∀ i, Field (Lω i)]
    [∀ i, Algebra K (Lω i)] [∀ i, Module.Finite K (Lω i)]
    (abvK : AbsoluteValue K ℝ) (abvω : ∀ i, AbsoluteValue (Lω i) ℝ)
    (hω : ∀ i y, abvK (Algebra.norm K y) = abvω i y) (x : ∀ i, Lω i) :
    abvK (Chapter02ProductAlgebraNorm K Lω x) = ∏ i, abvω i (x i) := by
  exact chapter02_product_algebra_norm_absolute_value_is_componentwise
    K Lω abvK abvω hω x

end

end LastLib.Book04AdelesAndIdeles.Chapter02
