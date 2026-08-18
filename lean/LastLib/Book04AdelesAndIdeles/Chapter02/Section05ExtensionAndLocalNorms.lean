import LastLib.Book04AdelesAndIdeles.Chapter02.Core
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Section01SeparatingBranchesByCompletion
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Section02TheCompletedProductTheorem
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.Section04TheValuationOfANorm
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Valuation.ValuationSubring

namespace LastLib.Book04AdelesAndIdeles.Chapter02

noncomputable section

open NumberField
open scoped BigOperators TensorProduct WithTop

/-! ## 2.5. Extension and local norms -/

/-- A branch completion product in the tensor-product form used by the book. -/
def Chapter02TensorCompletionBranchDecomposition
    (K L Kᵥ : Type*) [CommRing K] [CommRing L] [CommRing Kᵥ]
    [Algebra K L] [Algebra K Kᵥ]
    [Algebra Kᵥ (L ⊗[K] Kᵥ)]
    {ι : Type*} [Fintype ι] (Lω : ι → Type*)
    [∀ i, CommRing (Lω i)] [∀ i, Algebra Kᵥ (Lω i)] : Prop :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.hasCompletedAlgebraProduct
    K L Kᵥ Lω

/- The same branch-indexing interface is needed at archimedean places; the
finite version below is not a substitute because the completions and the
place relation are different APIs. -/
structure Chapter02InfiniteLocalBranchDecomposition
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (v : Chapter02InfinitePlace K) {ι : Type*} [Fintype ι]
    (w : ι → Chapter02InfinitePlace L) where
  liesOver : ∀ i, (w i).LiesOver v
  distinct : Function.Injective w
  exhaustive : ∀ z : Chapter02InfinitePlace L,
    z.LiesOver v → ∃ i, w i = z
  [tensorAlgebra : Algebra v.Completion (L ⊗[K] v.Completion)]
  [branchAlgebra : ∀ i, Algebra v.Completion (w i).Completion]
  decomposition : Nonempty
    (L ⊗[K] v.Completion ≃ₐ[v.Completion]
      (∀ i, (w i).Completion))

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
  [tensorAlgebra : Algebra (Chapter02FiniteCompletion v)
      (L ⊗[K] Chapter02FiniteCompletion v)]
  [branchAlgebra : ∀ i, Algebra (Chapter02FiniteCompletion v)
      (Chapter02FiniteCompletion (w i))]
  decomposition : Nonempty
    (L ⊗[K] Chapter02FiniteCompletion v ≃ₐ[Chapter02FiniteCompletion v]
      (∀ i, Chapter02FiniteCompletion (w i)))

/-- A packaged existential witness for the finite-place completed product. -/
structure Chapter02FiniteLocalBranchDecompositionWitness
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (v : Chapter02FinitePlace K) where
  index : Type*
  [index_fintype : Fintype index]
  branches : index → Chapter02FinitePlace L
  decomposition : Chapter02FiniteLocalBranchDecomposition v branches

theorem chapter02_finite_local_branch_decomposition_exists
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (v : Chapter02FinitePlace K) :
    Nonempty (Chapter02FiniteLocalBranchDecompositionWitness (K := K) (L := L) v) := by
  sorry

/-- A packaged existential witness for the infinite-place completed product. -/
structure Chapter02InfiniteLocalBranchDecompositionWitness
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (v : Chapter02InfinitePlace K) where
  index : Type*
  [index_fintype : Fintype index]
  branches : index → Chapter02InfinitePlace L
  decomposition : Chapter02InfiniteLocalBranchDecomposition v branches

theorem chapter02_infinite_local_branch_decomposition_exists
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (v : Chapter02InfinitePlace K) :
    Nonempty (Chapter02InfiniteLocalBranchDecompositionWitness (K := K) (L := L) v) := by
  sorry

/-- The integral-completion branch used by the earlier CRT API. -/
abbrev Chapter02BranchCompletion
    (B : Type*) [CommRing B] (P : Ideal B) [P.IsPrime] : Type _ :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.branchCompletion B P

/-- A packaged branch decomposition, with its finite branch index and product
isomorphism available to later chapters. -/
structure Chapter02TensorCompletionBranchData
    (K L Kᵥ : Type*) [CommRing K] [CommRing L] [CommRing Kᵥ]
    [Algebra K L] [Algebra K Kᵥ]
    [Algebra Kᵥ (L ⊗[K] Kᵥ)]
    {ι : Type*} [Fintype ι] (Lω : ι → Type*)
    [∀ i, CommRing (Lω i)] [∀ i, Algebra Kᵥ (Lω i)] where
  decomposition : Chapter02TensorCompletionBranchDecomposition K L Kᵥ Lω

/-- The completed-product theorem imported from the earlier completion chapter,
exposed in the branch notation used here. -/
theorem chapter02_completed_product_decomposition
    {A B : Type*} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsIntegrallyClosed B] [Algebra A B]
    [Algebra.IsIntegral A B]
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
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.completed_product_decomposition
    m π P e huniformizer hfinite hfree hfactor he hpair hP hP_exhaustive hP_distinct

/-- The finite-precision version of branch separation. -/
theorem chapter02_finite_precision_branch_indexing
    {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    (I : Ideal R) (J : ι → Ideal R)
    (hcrt : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Chapter12CompatibleCRTSystem
      I J) :
    Nonempty (AdicCompletion I R ≃+* (∀ i, AdicCompletion (J i) R)) := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.completion_product_of_finite_precision_crt
    I J hcrt

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
  by_cases hy : y = 0
  · subst y
    simp [D.abvK_normalized, D.abvL_normalized,
      Chapter02ValuationNormalizedValue]
  have hnorm : Algebra.norm K y ≠ 0 := Algebra.norm_ne_zero_iff.mpr hy
  rw [D.abvK_normalized, D.abvL_normalized]
  simp [Chapter02ValuationNormalizedValue, hnorm, hy]
  rw [D.norm_valuation y hy, WithTop.untopD_zero_mul]
  rw [D.residue_cardinality]
  rw [Nat.cast_pow]
  push_cast
  rw [← Real.rpow_natCast, ← Real.rpow_mul
    (by positivity : (0 : ℝ) ≤ (D.qK : ℝ))]
  congr 2
  have hf : WithTop.untopD (0 : ℤ) (D.f : WithTop ℤ) = (D.f : ℤ) := rfl
  rw [hf]
  push_cast
  ring

theorem chapter02_normalized_local_norm_identity_on_nonzero_elements
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (D : Chapter02NormalizedLocalNormData K L) {y : L} (_hy : y ≠ 0) :
    D.abvK (Algebra.norm K y) = D.abvL y := by
  exact chapter02_normalized_local_norm_identity D y

theorem chapter02_complex_over_real_normalized_local_norm_identity (z : ℂ) :
    |Algebra.norm ℝ z| = ‖z‖ ^ 2 := by
  calc
    |Algebra.norm ℝ z| = |Complex.normSq z| := by rw [Algebra.norm_complex_apply]
    _ = Complex.normSq z := abs_of_nonneg (Complex.normSq_nonneg z)
    _ = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq z

theorem chapter02_normalized_local_scalar_restriction
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (D : Chapter02NormalizedLocalNormData K L) (a : K) :
    D.abvL (algebraMap K L a) =
      D.abvK a ^ Module.finrank K L := by
  calc
    D.abvL (algebraMap K L a) =
        D.abvK (Algebra.norm K (algebraMap K L a)) :=
      (chapter02_normalized_local_norm_identity D (algebraMap K L a)).symm
    _ = D.abvK (a ^ Module.finrank K L) := by
      rw [Algebra.norm_algebraMap]
    _ = D.abvK a ^ Module.finrank K L := by
      rw [map_pow]

theorem chapter02_finite_branch_norm_formula_from_order_and_residue_degree
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (qK qL f : ℕ) (hq : qL = qK ^ f)
    (hord : ∀ y : L, y ≠ 0 →
      vK (Algebra.norm K y) = (f : WithTop ℤ) * vL y) {y : L} (hy : y ≠ 0) :
    Chapter02ValuationNormalizedValue qK vK (Algebra.norm K y) =
      Chapter02ValuationNormalizedValue qL vL y := by
  have hnorm : Algebra.norm K y ≠ 0 := Algebra.norm_ne_zero_iff.mpr hy
  simp [Chapter02ValuationNormalizedValue, hnorm, hy]
  rw [hord y hy, WithTop.untopD_zero_mul, hq, Nat.cast_pow]
  rw [← Real.rpow_natCast, ← Real.rpow_mul
    (by positivity : (0 : ℝ) ≤ (qK : ℝ))]
  congr 2
  have hf : WithTop.untopD (0 : ℤ) (f : WithTop ℤ) = (f : ℤ) := rfl
  rw [hf]
  push_cast
  ring

private theorem chapter02_algebra_norm_prod
    {K : Type u_1} {A : Type u_2} {B : Type u_3}
    [Field K] [Ring A] [Ring B]
    [Algebra K A] [Algebra K B]
    [Module.Finite K A] [Module.Finite K B]
    (a : A) (b : B) :
    Algebra.norm K (a, b) = Algebra.norm K a * Algebra.norm K b := by
  change LinearMap.det (Algebra.lmul K (A × B) (a, b)) =
    Algebra.norm K a * Algebra.norm K b
  rw [show Algebra.lmul K (A × B) (a, b) =
      LinearMap.prodMap (Algebra.lmul K A a) (Algebra.lmul K B b) by
    ext z <;> rfl]
  rw [LinearMap.det_prodMap]
  rfl

private def chapter02_fin_succ_pi_algEquiv
    {K : Type u_1} [Field K] {n : ℕ}
    {M : Fin (n + 1) → Type u_2} [∀ i, Field (M i)]
    [∀ i, Algebra K (M i)] :
    (∀ i, M i) ≃ₐ[K] (M 0 × ∀ j : Fin n, M j.succ) := by
  let f : (∀ i, M i) →ₐ[K] (M 0 × ∀ j : Fin n, M j.succ) :=
    { toFun := fun x => (x 0, fun j => x j.succ)
      map_one' := by
        ext i <;> rfl
      map_mul' := by
        intro x y
        ext i <;> rfl
      map_zero' := by
        ext i <;> rfl
      map_add' := by
        intro x y
        ext i <;> rfl
      commutes' := by
        intro r
        ext i <;> rfl }
  apply AlgEquiv.ofBijective f
  constructor
  · intro x y hxy
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact congrArg Prod.fst hxy
    · exact congrFun (congrArg Prod.snd hxy) j
  · intro z
    refine ⟨fun i => Fin.cases z.1 (fun j => z.2 j) i, ?_⟩
    apply Prod.ext
    · rfl
    · funext j
      rfl

private theorem chapter02_product_algebra_norm_fin
    {K : Type u_1} [Field K] (n : ℕ)
    {M : Fin n → Type u_2} [∀ i, Field (M i)]
    [∀ i, Algebra K (M i)] [∀ i, Module.Finite K (M i)]
    (x : ∀ i, M i) :
    Algebra.norm K x = ∏ i, Algebra.norm K (x i) := by
  induction n with
  | zero =>
      have hx : x = 1 := Subsingleton.elim _ _
      rw [hx]
      simp
  | succ n ih =>
      let e := chapter02_fin_succ_pi_algEquiv (K := K) (M := M)
      have he : Algebra.norm K (e x) = Algebra.norm K x :=
        Algebra.norm_eq_of_algEquiv e x
      rw [← he]
      change Algebra.norm K (x 0, fun j : Fin n => x (Fin.succ j)) = _
      have hprod := chapter02_algebra_norm_prod (K := K) (A := M 0)
        (B := ∀ j : Fin n, M (Fin.succ j)) (x 0)
        (fun j : Fin n => x (Fin.succ j))
      rw [hprod]
      rw [ih (M := fun j : Fin n => M (Fin.succ j))
        (x := fun j : Fin n => x (Fin.succ j))]
      simp [e, Fin.prod_univ_succ]

private def chapter02_pi_reindex_algEquiv
    {K : Type u_1} [Field K] {ι : Type u_2} {n : ℕ}
    {M : ι → Type u_3} [∀ i, Field (M i)]
    [∀ i, Algebra K (M i)] (e : ι ≃ Fin n) :
    (∀ i, M i) ≃ₐ[K] (∀ j, M (e.symm j)) := by
  let p : (∀ j : Fin n, M (e.symm j)) ≃ (∀ i : ι, M i) :=
    Equiv.piCongr e.symm (fun j => Equiv.refl (M (e.symm j)))
  let f : (∀ i, M i) →ₐ[K] (∀ j, M (e.symm j)) :=
    { toFun := p.symm
      map_one' := by
        ext j
        simp [p]
      map_mul' := by
        intro x y
        ext j
        simp [p]
      map_zero' := by
        ext j
        simp [p]
      map_add' := by
        intro x y
        ext j
        simp [p]
      commutes' := by
        intro r
        ext j
        simp [p] }
  exact AlgEquiv.ofBijective f p.symm.bijective

/-- The norm on a finite product algebra is the product of the component norms. -/
def Chapter02ProductAlgebraNorm
    (K : Type*) [Field K] {ι : Type*} [Fintype ι]
    (Lω : ι → Type*) [∀ i, Field (Lω i)]
    [∀ i, Algebra K (Lω i)] [∀ i, Module.Finite K (Lω i)]
    (x : ∀ i, Lω i) : K :=
  Algebra.norm K x

theorem chapter02_product_algebra_norm_is_componentwise
    (K : Type*) [Field K] {ι : Type*} [Fintype ι]
    (Lω : ι → Type*) [∀ i, Field (Lω i)]
    [∀ i, Algebra K (Lω i)] [∀ i, Module.Finite K (Lω i)]
    (x : ∀ i, Lω i) :
    Chapter02ProductAlgebraNorm K Lω x = ∏ i, Algebra.norm K (x i) := by
  classical
  change Algebra.norm K x = _
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let E := chapter02_pi_reindex_algEquiv (K := K) (M := Lω) e
  have he : Algebra.norm K (E x) = Algebra.norm K x :=
    Algebra.norm_eq_of_algEquiv E x
  have hfin : Algebra.norm K (E x) =
      ∏ j : Fin (Fintype.card ι), Algebra.norm K ((E x) j) :=
    chapter02_product_algebra_norm_fin (K := K) (n := Fintype.card ι)
      (M := fun j => Lω (e.symm j)) (E x)
  rw [← he, hfin]
  have hprod :
      (∏ j : Fin (Fintype.card ι), Algebra.norm K (x (e.symm j))) =
        ∏ i : ι, Algebra.norm K (x i) := by
    exact Fintype.prod_equiv e.symm
      (fun j : Fin (Fintype.card ι) => Algebra.norm K (x (e.symm j)))
      (fun i : ι => Algebra.norm K (x i)) (fun _ => rfl)
  simpa [E, chapter02_pi_reindex_algEquiv] using hprod

theorem chapter02_product_algebra_norm_absolute_value_is_componentwise
    (K : Type*) [Field K] {ι : Type*} [Fintype ι]
    (Lω : ι → Type*) [∀ i, Field (Lω i)]
    [∀ i, Algebra K (Lω i)] [∀ i, Module.Finite K (Lω i)]
    (abvK : AbsoluteValue K ℝ)
    (abvω : ∀ i, AbsoluteValue (Lω i) ℝ)
    (hω : ∀ i y, abvK (Algebra.norm K y) = abvω i y)
    (x : ∀ i, Lω i) :
    abvK (Chapter02ProductAlgebraNorm K Lω x) = ∏ i, abvω i (x i) := by
  rw [chapter02_product_algebra_norm_is_componentwise]
  simp_rw [map_prod, hω]

end

end LastLib.Book04AdelesAndIdeles.Chapter02
