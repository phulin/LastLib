import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Topology.Algebra.RestrictedProduct.Units
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.Topology.Algebra.Constructions

namespace LastLib.Book04AdelesAndIdeles.Chapter15

noncomputable section

open Set Filter
open NumberField
open scoped BigOperators RestrictedProduct

/-!
## Shared interfaces for Chapter 15

Mathlib has the restricted-product topology and the finite/full adele rings, but it
does not package the book's idele module, ray-class character API, or the matrix
restricted product.  The definitions below keep the book-facing notation close to
those canonical objects.  In particular, the local groups are genuine Mathlib
general-linear groups and the finite tails are genuine restricted products.
-/

/-! ### Places, local factors, and adelic groups -/

abbrev Chapter15FinitePlace (R : Type*) [CommRing R] :=
  IsDedekindDomain.HeightOneSpectrum R

abbrev Chapter15Place (R K : Type*) [CommRing R] [Field K] :=
  Sum (NumberField.InfinitePlace K) (Chapter15FinitePlace R)

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- The completion attached to a finite or infinite place. -/
def chapter15LocalRing (p : Chapter15Place R K) : Type _ :=
  match p with
  | Sum.inl v => v.Completion
  | Sum.inr v => v.adicCompletion K

instance chapter15LocalRingCommRing (p : Chapter15Place R K) :
    CommRing (chapter15LocalRing p) := by
  cases p with
  | inl v =>
      change CommRing (v.Completion)
      infer_instance
  | inr v =>
      change CommRing (v.adicCompletion K)
      infer_instance

instance chapter15LocalRingTopologicalSpace (p : Chapter15Place R K) :
    TopologicalSpace (chapter15LocalRing p) := by
  cases p with
  | inl v =>
      change TopologicalSpace v.Completion
      infer_instance
  | inr v =>
      change TopologicalSpace (v.adicCompletion K)
      infer_instance

/-- The distinguished integral subset at a place; it is unrestricted at infinity. -/
def chapter15LocalIntegerSet (p : Chapter15Place R K) : Set (chapter15LocalRing p) :=
  match p with
  | Sum.inl _ => Set.univ
  | Sum.inr v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))

/-- The finite local integral model inside the field-valued general-linear group. -/
def chapter15FiniteMatrixIntegralSubgroup (n : ℕ) (v : Chapter15FinitePlace R) :
    Subgroup (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K)) :=
  (Matrix.GeneralLinearGroup.map
      (v.adicCompletionIntegers K).subtype).range

/-- The finite local integral model inside the multiplicative group of the field. -/
def chapter15FiniteUnitIntegralSubgroup (v : Chapter15FinitePlace R) :
    Subgroup ((v.adicCompletion K)ˣ) :=
  (Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom).range

/-- The local matrix integral subgroup, with no condition at an infinite place. -/
def chapter15LocalMatrixIntegralSubgroup (n : ℕ) (p : Chapter15Place R K) :
    Subgroup (Matrix.GeneralLinearGroup (Fin n) (chapter15LocalRing p)) := by
  cases p with
  | inl v =>
      change Subgroup (Matrix.GeneralLinearGroup (Fin n) v.Completion)
      exact ⊤
  | inr v =>
      change Subgroup (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K))
      exact chapter15FiniteMatrixIntegralSubgroup (R := R) (K := K) n v

/-- The local unit integral subgroup, with no condition at an infinite place. -/
def chapter15LocalUnitIntegralSubgroup (p : Chapter15Place R K) :
    Subgroup ((chapter15LocalRing p)ˣ) := by
  cases p with
  | inl v =>
      change Subgroup ((v.Completion)ˣ)
      exact ⊤
  | inr v =>
      change Subgroup ((v.adicCompletion K)ˣ)
      exact chapter15FiniteUnitIntegralSubgroup (R := R) (K := K) v

/-- Matrix groups at the infinite places. -/
abbrev Chapter15ArchimedeanMatrixGroup (n : ℕ) (K : Type*) [Field K] :=
  (v : NumberField.InfinitePlace K) →
    Matrix.GeneralLinearGroup (Fin n) v.Completion

/-- The finite adelic matrix group, with the standard integral tail. -/
abbrev Chapter15FiniteMatrixGroup (n : ℕ) (R K : Type*) [CommRing R]
    [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] :=
  Πʳ v : Chapter15FinitePlace R,
    [Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K),
      chapter15FiniteMatrixIntegralSubgroup (R := R) (K := K) n v]

noncomputable instance (priority := 2000) chapter15FiniteMatrixGroup_topologicalSpace
    (n : ℕ) : TopologicalSpace (Chapter15FiniteMatrixGroup n R K) :=
  RestrictedProduct.topologicalSpace
    (fun v : Chapter15FinitePlace R =>
      Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K))
    (fun v =>
      (chapter15FiniteMatrixIntegralSubgroup (R := R) (K := K) n v : Set _))
    Filter.cofinite

/-- The full matrix group as its infinite component times its finite restricted product. -/
abbrev Chapter15AdelicMatrixGroup (n : ℕ) (R K : Type*) [CommRing R]
    [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] :=
  Chapter15ArchimedeanMatrixGroup n K × Chapter15FiniteMatrixGroup n R K

/-- The literal all-place restricted product appearing in the book's definition. -/
abbrev Chapter15RestrictedAdelicMatrixGroup (n : ℕ) (R K : Type*) [CommRing R]
    [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] :=
  Πʳ p : Chapter15Place R K,
    [Matrix.GeneralLinearGroup (Fin n) (chapter15LocalRing p),
      chapter15LocalMatrixIntegralSubgroup n p]

/-- Unit groups at the infinite places. -/
abbrev Chapter15ArchimedeanIdeleGroup (K : Type*) [Field K] :=
  (v : NumberField.InfinitePlace K) → (v.Completion)ˣ

/-- The finite idele group as a restricted product of local multiplicative groups. -/
abbrev Chapter15FiniteIdeleGroup (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] :=
  Πʳ v : Chapter15FinitePlace R,
    [(v.adicCompletion K)ˣ,
      chapter15FiniteUnitIntegralSubgroup (R := R) (K := K) v]

noncomputable instance (priority := 2000) chapter15FiniteIdeleGroup_topologicalSpace :
    TopologicalSpace (Chapter15FiniteIdeleGroup R K) :=
  RestrictedProduct.topologicalSpace
    (fun v : Chapter15FinitePlace R => (v.adicCompletion K)ˣ)
    (fun v =>
      (chapter15FiniteUnitIntegralSubgroup (R := R) (K := K) v : Set _))
    Filter.cofinite

/-- The finite standard integral idele level. -/
def chapter15StandardFiniteIdeleLevel :
    Subgroup (Chapter15FiniteIdeleGroup R K) where
  carrier := {g | ∀ v : Chapter15FinitePlace R,
    g v ∈ chapter15FiniteUnitIntegralSubgroup v}
  one_mem' := by
    intro v
    exact (chapter15FiniteUnitIntegralSubgroup v).one_mem
  mul_mem' := by
    intro g h hg hh v
    exact (chapter15FiniteUnitIntegralSubgroup v).mul_mem (hg v) (hh v)
  inv_mem' := by
    intro g hg v
    exact (chapter15FiniteUnitIntegralSubgroup v).inv_mem (hg v)

/-! ### Shared finite matrix levels -/

/-- A finite adelic matrix level together with its local factor description. -/
structure Chapter15FiniteMatrixLevel (n : ℕ) where
  localSubgroup : ∀ v : Chapter15FinitePlace R,
    Subgroup (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K))
  subgroup : Subgroup (Chapter15FiniteMatrixGroup n R K)
  mem_iff : ∀ g, g ∈ subgroup ↔
    ∀ v : Chapter15FinitePlace R, g v ∈ localSubgroup v
  isCompact : IsCompact (subgroup : Set (Chapter15FiniteMatrixGroup n R K))
  isOpen : IsOpen (subgroup : Set (Chapter15FiniteMatrixGroup n R K))
  standard_outside_finite : ∃ S : Finset (Chapter15FinitePlace R),
    ∀ v ∉ S, localSubgroup v = chapter15FiniteMatrixIntegralSubgroup n v

theorem chapter15FiniteMatrixLevel_mem_iff
    (n : ℕ) (L : Chapter15FiniteMatrixLevel (R := R) (K := K) n)
    (g : Chapter15FiniteMatrixGroup n R K) :
    g ∈ L.subgroup ↔ ∀ v, g v ∈ L.localSubgroup v :=
  L.mem_iff g

/-- The idele group, equipped with the graph/restricted-product topology. -/
abbrev Chapter15IdeleGroup (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] :=
  Chapter15ArchimedeanIdeleGroup K × Chapter15FiniteIdeleGroup R K

/-- The literal all-place restricted product version of the idele group. -/
abbrev Chapter15RestrictedIdeleGroup (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] :=
  Πʳ p : Chapter15Place R K,
    [(chapter15LocalRing p)ˣ, chapter15LocalUnitIntegralSubgroup p]

/-! ### Shared quotient and finite-level interfaces -/

/-- Equality of two representatives in a left/right double quotient. -/
def chapter15DoubleCosetRel {G : Type*} [Group G]
    (H K : Subgroup G) (x y : G) : Prop :=
  ∃ h ∈ H, ∃ k ∈ K, h * x * k = y

def chapter15DoubleCosetSetoid {G : Type*} [Group G]
    (H K : Subgroup G) : Setoid G where
  r := chapter15DoubleCosetRel H K
  iseqv := by
    constructor
    · intro x
      exact ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
    · intro x y ⟨h, hh, k, hk, heq⟩
      refine ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, ?_⟩
      calc
        h⁻¹ * y * k⁻¹ = h⁻¹ * (h * x * k) * k⁻¹ := by rw [← heq]
        _ = h⁻¹ * (h * (x * (k * k⁻¹))) := by simp only [mul_assoc]
        _ = x := by simp
    · intro x y z ⟨h₁, hh₁, k₁, hk₁, hxy⟩ ⟨h₂, hh₂, k₂, hk₂, hyz⟩
      refine ⟨h₂ * h₁, H.mul_mem hh₂ hh₁, k₁ * k₂, K.mul_mem hk₁ hk₂, ?_⟩
      rw [← hyz, ← hxy]
      simp only [mul_assoc]

/-- The type `H \ G / K`. -/
abbrev Chapter15DoubleQuotient {G : Type*} [Group G]
    (H K : Subgroup G) :=
  Quotient (chapter15DoubleCosetSetoid H K)

/-- The canonical representative map into a double quotient. -/
def chapter15DoubleQuotientMk {G : Type*} [Group G]
    (H K : Subgroup G) (g : G) :
    Chapter15DoubleQuotient H K := Quotient.mk (chapter15DoubleCosetSetoid H K) g

theorem chapter15DoubleQuotient_mk_eq_iff {G : Type*} [Group G]
    (H K : Subgroup G) (x y : G) :
    chapter15DoubleQuotientMk H K x = chapter15DoubleQuotientMk H K y ↔
      chapter15DoubleCosetRel H K x y := by
  exact Quotient.eq

theorem chapter15DoubleQuotient_mk_eq_of_left_right {G : Type*} [Group G]
    (H K : Subgroup G) {x y : G} (h : G) (hh : h ∈ H) (k : G) (hk : k ∈ K)
    (heq : h * x * k = y) :
    chapter15DoubleQuotientMk H K x = chapter15DoubleQuotientMk H K y := by
  exact (chapter15DoubleQuotient_mk_eq_iff H K _ _).2 ⟨h, hh, k, hk, heq⟩

/-- The canonical full adele ring from pinned Mathlib. -/
abbrev Chapter15AdeleRing (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] :=
  NumberField.AdeleRing R K

/-- The units of the full adele ring; this has the induced unit topology. -/
abbrev Chapter15AdeleUnitGroup (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] :=
  (Chapter15AdeleRing R K)ˣ

/-! ### Restricted-product identifications -/

/- LOCAL_DEPENDENCY_GUESS: the source uses the standard decomposition of an
all-place restricted product into its finite restricted factor and its finite
archimedean factor.  Pinned Mathlib provides both restricted products and the
number-field finiteness of the infinite places, but not this book-facing
equivalence as a named declaration. -/
def chapter15_restricted_matrix_group_equiv_product
    (n : ℕ) [NumberField K] :
    Chapter15RestrictedAdelicMatrixGroup n R K ≃ₜ*
      Chapter15AdelicMatrixGroup n R K := by
  have hinr : Tendsto (Sum.inr : Chapter15FinitePlace R → Chapter15Place R K)
      Filter.cofinite Filter.cofinite :=
    Function.Injective.tendsto_cofinite (fun a b h => Sum.inr.inj h)
  have hφ :
      ∀ᶠ v : Chapter15FinitePlace R in Filter.cofinite,
        MapsTo (fun z :
            Matrix.GeneralLinearGroup (Fin n) (chapter15LocalRing (Sum.inr v)) => z)
          (chapter15LocalMatrixIntegralSubgroup (R := R) (K := K) n (Sum.inr v) :
            Set (Matrix.GeneralLinearGroup (Fin n) (chapter15LocalRing (Sum.inr v))))
          (chapter15FiniteMatrixIntegralSubgroup (R := R) (K := K) n v :
            Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K))) := by
    filter_upwards [] with v
    intro z hz
    change z ∈ (chapter15FiniteMatrixIntegralSubgroup (R := R) (K := K) n v :
      Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K))) at hz
    exact hz
  let m :
      Chapter15RestrictedAdelicMatrixGroup n R K →
        Chapter15FiniteMatrixGroup n R K :=
    RestrictedProduct.mapAlong
      (R₁ := fun p : Chapter15Place R K =>
        Matrix.GeneralLinearGroup (Fin n) (chapter15LocalRing p))
      (R₂ := fun v : Chapter15FinitePlace R =>
        Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K))
      (A₁ := fun p =>
        (chapter15LocalMatrixIntegralSubgroup (R := R) (K := K) n p :
          Set (Matrix.GeneralLinearGroup (Fin n) (chapter15LocalRing p))))
      (A₂ := fun v =>
        (chapter15FiniteMatrixIntegralSubgroup (R := R) (K := K) n v :
          Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K))))
      (f := Sum.inr) hinr (fun v z => z) hφ
  have hm : Continuous m := by
    exact RestrictedProduct.mapAlong_continuous
      (R₁ := fun p : Chapter15Place R K =>
        Matrix.GeneralLinearGroup (Fin n) (chapter15LocalRing p))
      (R₂ := fun v : Chapter15FinitePlace R =>
        Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K))
      (A₁ := fun p =>
        (chapter15LocalMatrixIntegralSubgroup (R := R) (K := K) n p :
          Set (Matrix.GeneralLinearGroup (Fin n) (chapter15LocalRing p))))
      (A₂ := fun v =>
        (chapter15FiniteMatrixIntegralSubgroup (R := R) (K := K) n v :
          Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K))))
      (f := Sum.inr) hinr (fun v z => z) hφ
      (fun _ => continuous_id)
  have harch : Continuous
      (fun x : Chapter15RestrictedAdelicMatrixGroup n R K =>
        fun v : NumberField.InfinitePlace K => x (Sum.inl v)) := by
    apply continuous_pi
    intro v
    change Continuous
      (fun x : Chapter15RestrictedAdelicMatrixGroup n R K => x (Sum.inl v))
    exact RestrictedProduct.continuous_eval
      (R := fun p : Chapter15Place R K =>
        Matrix.GeneralLinearGroup (Fin n) (chapter15LocalRing p))
      (A := fun p =>
        (chapter15LocalMatrixIntegralSubgroup (R := R) (K := K) n p :
          Set (Matrix.GeneralLinearGroup (Fin n) (chapter15LocalRing p))))
      (𝓕 := Filter.cofinite) (Sum.inl v)
  have hto : Continuous
      (fun x : Chapter15RestrictedAdelicMatrixGroup n R K =>
        ((fun v : NumberField.InfinitePlace K => x (Sum.inl v)), m x)) :=
    harch.prodMk hm
  have hlocal :
      ∀ v : Chapter15FinitePlace R,
        (chapter15FiniteMatrixIntegralSubgroup (R := R) (K := K) n v :
          Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K))) =
          {g : Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K) |
            ∀ i j, g i j ∈ v.adicCompletionIntegers K ∧
              (g⁻¹) i j ∈ v.adicCompletionIntegers K} := by
    intro v
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      intro i j
      constructor
      · exact (x i j).property
      · exact (x⁻¹ i j).property
    · intro hg
      let A : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers K) :=
        fun i j => ⟨g i j, (hg i j).1⟩
      let B : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers K) :=
        fun i j => ⟨(g⁻¹) i j, (hg i j).2⟩
      have hA :
          A.map (v.adicCompletionIntegers K).subtype =
            (g : Matrix (Fin n) (Fin n) (v.adicCompletion K)) := by
        ext i j
        rfl
      have hB :
          B.map (v.adicCompletionIntegers K).subtype =
            ((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K)) :
              Matrix (Fin n) (Fin n) (v.adicCompletion K)) := by
        ext i j
        rfl
      let x : Matrix.GeneralLinearGroup (Fin n) (v.adicCompletionIntegers K) :=
        { val := A
          inv := B
          val_inv := by
            apply Matrix.ext
            intro i j
            apply Subtype.ext
            change ((A * B).map (v.adicCompletionIntegers K).subtype) i j =
              ((1 : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers K)).map
                (v.adicCompletionIntegers K).subtype) i j
            rw [Matrix.map_mul,
              Matrix.map_one _ (map_zero _) (map_one _), hA, hB]
            exact congrArg (fun M : Matrix (Fin n) (Fin n) (v.adicCompletion K) => M i j)
              g.val_inv
          inv_val := by
            apply Matrix.ext
            intro i j
            apply Subtype.ext
            change ((B * A).map (v.adicCompletionIntegers K).subtype) i j =
              ((1 : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers K)).map
                (v.adicCompletionIntegers K).subtype) i j
            rw [Matrix.map_mul,
              Matrix.map_one _ (map_zero _) (map_one _), hB, hA]
            exact congrArg (fun M : Matrix (Fin n) (Fin n) (v.adicCompletion K) => M i j)
              g.inv_val }
      refine ⟨x, ?_⟩
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      rfl
  let g : Chapter15AdelicMatrixGroup n R K →
      Chapter15RestrictedAdelicMatrixGroup n R K :=
    fun x =>
      ⟨(fun p =>
        match p with
        | Sum.inl v => x.1 v
        | Sum.inr v => x.2 v),
        by
          rw [Filter.eventually_cofinite]
          have hbad : Set.Finite
              {v : Chapter15FinitePlace R |
                ¬ x.2 v ∈
                  (chapter15FiniteMatrixIntegralSubgroup (R := R) (K := K) n v :
                    Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K)))} :=
            Filter.eventually_cofinite.mp x.2.2
          show Set.Finite
            {p : Chapter15Place R K |
              ¬ (match p with
                | Sum.inl v => x.1 v
                | Sum.inr v => x.2 v) ∈
                  (chapter15LocalMatrixIntegralSubgroup (R := R) (K := K) n p :
                    Set (Matrix.GeneralLinearGroup (Fin n) (chapter15LocalRing p)))}
          refine Set.Finite.subset
            (hbad.image (Sum.inr : Chapter15FinitePlace R → Chapter15Place R K)) ?_
          intro p hp
          cases p with
          | inl v =>
              exfalso
              apply hp
              change x.1 v ∈
                (⊤ : Subgroup (Matrix.GeneralLinearGroup (Fin n) v.Completion))
              exact trivial
          | inr v =>
              exact ⟨v, hp, rfl⟩⟩
  have hfiniteOpen :
      ∀ v : Chapter15FinitePlace R,
        IsOpen (chapter15FiniteMatrixIntegralSubgroup (R := R) (K := K) n v :
          Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K))) := by
    intro v
    rw [hlocal v]
    have hopen : IsOpen
        (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
      Valued.isOpen_valuationSubring _
    have hset :
        {g : Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K) |
            ∀ i j, g i j ∈ v.adicCompletionIntegers K ∧
              (g⁻¹) i j ∈ v.adicCompletionIntegers K} =
          ⋂ i : Fin n, ⋂ j : Fin n,
            {g : Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K) |
              g i j ∈ v.adicCompletionIntegers K ∧
                (g⁻¹) i j ∈ v.adicCompletionIntegers K} := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rw [hset]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    have hcval : Continuous
        (fun z : Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K) => z i j) :=
      (continuous_apply j).comp
        (Matrix.GeneralLinearGroup.continuous_apply
          (fun z : Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K) => z)
          continuous_id i)
    have hcinv : Continuous
        (fun z : Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K) => z⁻¹ i j) :=
      (continuous_apply j).comp
        (Matrix.GeneralLinearGroup.continuous_apply
          (fun z : Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K) => z⁻¹)
          continuous_inv i)
    exact (hopen.preimage hcval).inter (hopen.preimage hcinv)
  have hginv : Continuous g := by
    rw [RestrictedProduct.continuous_dom_prod_left
      (R := fun v : Chapter15FinitePlace R =>
        Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K))
      (A := fun v =>
        (chapter15FiniteMatrixIntegralSubgroup (R := R) (K := K) n v :
          Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K)))) hfiniteOpen]
    intro S hS
    let T : Set (Chapter15Place R K) :=
      Set.range Sum.inl ∪ Sum.inr '' S
    have hT : Filter.cofinite ≤ Filter.principal T := by
      apply Filter.le_principal_iff.mpr
      apply Filter.mem_cofinite.mpr
      have hSc : Sᶜ.Finite :=
        Filter.mem_cofinite.mp (Filter.le_principal_iff.mp hS)
      refine (hSc.image
        (Sum.inr : Chapter15FinitePlace R → Chapter15Place R K)).subset ?_
      intro p hp
      cases p with
      | inl v =>
          exact (hp (Or.inl ⟨v, rfl⟩)).elim
      | inr v =>
          refine ⟨v, ?_, rfl⟩
          intro hv
          exact hp (Or.inr ⟨v, hv, rfl⟩)
    let gS :
        Chapter15ArchimedeanMatrixGroup n K ×
            (Πʳ v : Chapter15FinitePlace R,
              [Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K),
                chapter15FiniteMatrixIntegralSubgroup (R := R) (K := K) n v]_[Filter.principal S]) →
          (Πʳ p : Chapter15Place R K,
            [Matrix.GeneralLinearGroup (Fin n) (chapter15LocalRing p),
              chapter15LocalMatrixIntegralSubgroup (R := R) (K := K) n p]_[Filter.principal T]) :=
      fun x =>
        ⟨(fun p =>
          match p with
          | Sum.inl v => x.1 v
          | Sum.inr v => x.2 v),
          by
            intro p hp
            cases p with
            | inl v =>
                change x.1 v ∈
                  (⊤ : Subgroup (Matrix.GeneralLinearGroup (Fin n) v.Completion))
                exact trivial
            | inr v =>
                have hvS : v ∈ S := by
                  simpa [T] using hp
                have hx :
                    ∀ w : Chapter15FinitePlace R, w ∈ S →
                      x.2 w ∈
                        (chapter15FiniteMatrixIntegralSubgroup (R := R) (K := K) n w :
                          Set (Matrix.GeneralLinearGroup (Fin n) (w.adicCompletion K))) :=
                  Filter.eventually_principal.mp x.2.2
                exact hx v hvS⟩
    have hgS : Continuous gS := by
      apply RestrictedProduct.continuous_rng_of_principal.mpr
      apply continuous_pi
      intro p
      cases p with
      | inl v =>
          change Continuous
            (fun x : Chapter15ArchimedeanMatrixGroup n K ×
              (Πʳ v : Chapter15FinitePlace R,
                [Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K),
                  chapter15FiniteMatrixIntegralSubgroup (R := R) (K := K) n v]_[Filter.principal S]) =>
              x.1 v)
          exact (continuous_apply v).comp continuous_fst
      | inr v =>
          change Continuous
            (fun x : Chapter15ArchimedeanMatrixGroup n K ×
              (Πʳ v : Chapter15FinitePlace R,
                [Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K),
                  chapter15FiniteMatrixIntegralSubgroup (R := R) (K := K) n v]_[Filter.principal S]) =>
              x.2 v)
          exact
            (RestrictedProduct.continuous_eval
              (R := fun v : Chapter15FinitePlace R =>
                Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K))
              (A := fun v =>
                (chapter15FiniteMatrixIntegralSubgroup (R := R) (K := K) n v :
                  Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K))))
              (𝓕 := Filter.principal S) v).comp continuous_snd
    let iS :
        (Πʳ v : Chapter15FinitePlace R,
          [Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K),
            chapter15FiniteMatrixIntegralSubgroup (R := R) (K := K) n v]_[Filter.principal S]) →
          Chapter15FiniteMatrixGroup n R K :=
      RestrictedProduct.inclusion
        (R := fun v : Chapter15FinitePlace R =>
          Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K))
        (A := fun v =>
          (chapter15FiniteMatrixIntegralSubgroup (R := R) (K := K) n v :
            Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K)))) hS
    let iT :
        (Πʳ p : Chapter15Place R K,
          [Matrix.GeneralLinearGroup (Fin n) (chapter15LocalRing p),
            chapter15LocalMatrixIntegralSubgroup (R := R) (K := K) n p]_[Filter.principal T]) →
          Chapter15RestrictedAdelicMatrixGroup n R K :=
      RestrictedProduct.inclusion
        (R := fun p : Chapter15Place R K =>
          Matrix.GeneralLinearGroup (Fin n) (chapter15LocalRing p))
        (A := fun p =>
          (chapter15LocalMatrixIntegralSubgroup (R := R) (K := K) n p :
            Set (Matrix.GeneralLinearGroup (Fin n) (chapter15LocalRing p)))) hT
    have hcomp : g ∘ (Prod.map id iS) = iT ∘ gS := by
      funext x
      apply Subtype.ext
      funext p
      cases p <;> rfl
    rw [hcomp]
    exact (RestrictedProduct.continuous_inclusion hT).comp hgS
  let e : Chapter15RestrictedAdelicMatrixGroup n R K ≃*
      Chapter15AdelicMatrixGroup n R K :=
    { toFun := fun x =>
        ((fun v : NumberField.InfinitePlace K => x (Sum.inl v)), m x)
      invFun := g
      left_inv := by
        intro x
        apply Subtype.ext
        funext p
        cases p <;> rfl
      right_inv := by
        intro x
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          funext v
          rfl
      map_mul' := by
        intro x y
        apply Prod.ext
        · funext v
          rfl
        · apply Subtype.ext
          funext v
          rfl }
  refine { __ := e, continuous_toFun := ?_, continuous_invFun := ?_ }
  · change Continuous (fun x : Chapter15RestrictedAdelicMatrixGroup n R K =>
      ((fun v : NumberField.InfinitePlace K => x (Sum.inl v)), m x))
    exact hto
  · change Continuous g
    exact hginv

def chapter15_restricted_idele_group_equiv_product
    [NumberField K] :
    Chapter15RestrictedIdeleGroup R K ≃ₜ*
      Chapter15IdeleGroup R K := by
  have hinr : Tendsto (Sum.inr : Chapter15FinitePlace R → Chapter15Place R K)
      Filter.cofinite Filter.cofinite :=
    Function.Injective.tendsto_cofinite (fun a b h => Sum.inr.inj h)
  let hφ :
      ∀ᶠ v : Chapter15FinitePlace R in Filter.cofinite,
        MapsTo (fun z : (chapter15LocalRing (Sum.inr v))ˣ => z)
          (chapter15LocalUnitIntegralSubgroup (R := R) (K := K) (Sum.inr v) :
            Set ((chapter15LocalRing (Sum.inr v))ˣ))
          (chapter15FiniteUnitIntegralSubgroup (R := R) (K := K) v :
            Set ((v.adicCompletion K)ˣ)) := by
    filter_upwards [] with v
    intro z hz
    change z ∈ (chapter15FiniteUnitIntegralSubgroup (R := R) (K := K) v :
      Set ((v.adicCompletion K)ˣ)) at hz
    exact hz
  let m :
      Chapter15RestrictedIdeleGroup R K → Chapter15FiniteIdeleGroup R K :=
    RestrictedProduct.mapAlong
      (R₁ := fun p : Chapter15Place R K => (chapter15LocalRing p)ˣ)
      (R₂ := fun v : Chapter15FinitePlace R => (v.adicCompletion K)ˣ)
      (A₁ := fun p =>
        (chapter15LocalUnitIntegralSubgroup (R := R) (K := K) p :
          Set ((chapter15LocalRing p)ˣ)))
      (A₂ := fun v =>
        (chapter15FiniteUnitIntegralSubgroup (R := R) (K := K) v :
          Set ((v.adicCompletion K)ˣ)))
      (f := Sum.inr) hinr (fun v z => z) hφ
  have hm : Continuous m := by
    exact RestrictedProduct.mapAlong_continuous
      (R₁ := fun p : Chapter15Place R K => (chapter15LocalRing p)ˣ)
      (R₂ := fun v : Chapter15FinitePlace R => (v.adicCompletion K)ˣ)
      (A₁ := fun p =>
        (chapter15LocalUnitIntegralSubgroup (R := R) (K := K) p :
          Set ((chapter15LocalRing p)ˣ)))
      (A₂ := fun v =>
        (chapter15FiniteUnitIntegralSubgroup (R := R) (K := K) v :
          Set ((v.adicCompletion K)ˣ)))
      (f := Sum.inr) hinr (fun v z => z) hφ
      (fun _ => continuous_id)
  have harch : Continuous
      (fun x : Chapter15RestrictedIdeleGroup R K =>
        fun v : NumberField.InfinitePlace K => x (Sum.inl v)) := by
    apply continuous_pi
    intro v
    change Continuous (fun x : Chapter15RestrictedIdeleGroup R K => x (Sum.inl v))
    exact RestrictedProduct.continuous_eval
      (R := fun p : Chapter15Place R K => (chapter15LocalRing p)ˣ)
      (A := fun p =>
        (chapter15LocalUnitIntegralSubgroup (R := R) (K := K) p :
          Set ((chapter15LocalRing p)ˣ)))
      (𝓕 := Filter.cofinite) (Sum.inl v)
  have hto : Continuous
      (fun x : Chapter15RestrictedIdeleGroup R K =>
        ((fun v : NumberField.InfinitePlace K => x (Sum.inl v)), m x)) :=
    harch.prodMk hm
  let g : Chapter15IdeleGroup R K → Chapter15RestrictedIdeleGroup R K :=
    fun x =>
      ⟨(fun p =>
        match p with
        | Sum.inl v => x.1 v
        | Sum.inr v => x.2 v),
        by
          rw [Filter.eventually_cofinite]
          have hbad : Set.Finite
              {v : Chapter15FinitePlace R |
                ¬ x.2 v ∈
                  (chapter15FiniteUnitIntegralSubgroup (R := R) (K := K) v :
                    Set ((v.adicCompletion K)ˣ))} :=
            Filter.eventually_cofinite.mp x.2.2
          show Set.Finite
            {p : Chapter15Place R K |
              ¬ (match p with
                | Sum.inl v => x.1 v
                | Sum.inr v => x.2 v) ∈
                  (chapter15LocalUnitIntegralSubgroup (R := R) (K := K) p :
                    Set ((chapter15LocalRing p)ˣ))}
          refine Set.Finite.subset
            (hbad.image (Sum.inr : Chapter15FinitePlace R → Chapter15Place R K)) ?_
          intro p hp
          cases p with
          | inl v =>
              exfalso
              apply hp
              change x.1 v ∈ (⊤ : Subgroup ((v.Completion)ˣ))
              exact trivial
          | inr v =>
              exact ⟨v, hp, rfl⟩⟩
  have hfiniteOpen :
      ∀ v : Chapter15FinitePlace R,
        IsOpen (chapter15FiniteUnitIntegralSubgroup (R := R) (K := K) v :
          Set ((v.adicCompletion K)ˣ)) := by
    intro v
    have hlocal :
        chapter15FiniteUnitIntegralSubgroup (R := R) (K := K) v =
          (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
      apply Subgroup.ext
      intro u
      constructor
      · rintro ⟨x, rfl⟩
        exact Submonoid.mem_units_of_val_mem_inv_val_mem _ x.1.2 x.2.2
      · intro hu
        rcases hu with ⟨hu, huinv⟩
        let x : (v.adicCompletionIntegers K)ˣ :=
          { val := ⟨(u : v.adicCompletion K), hu⟩
            inv := ⟨((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K), huinv⟩
            val_inv := by apply Subtype.ext; exact u.val_inv
            inv_val := by apply Subtype.ext; exact u.inv_val }
        exact ⟨x, by apply Units.ext; rfl⟩
    rw [hlocal]
    have hopen : IsOpen
        (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
      Valued.isOpen_valuationSubring _
    exact (hopen.preimage Units.continuous_val).inter
      (hopen.preimage Units.continuous_coe_inv)
  have hginv : Continuous g := by
    rw [RestrictedProduct.continuous_dom_prod_left
      (R := fun v : Chapter15FinitePlace R => (v.adicCompletion K)ˣ)
      (A := fun v =>
        (chapter15FiniteUnitIntegralSubgroup (R := R) (K := K) v :
          Set ((v.adicCompletion K)ˣ))) hfiniteOpen]
    intro S hS
    let T : Set (Chapter15Place R K) :=
      Set.range Sum.inl ∪ Sum.inr '' S
    have hT : Filter.cofinite ≤ Filter.principal T := by
      apply Filter.le_principal_iff.mpr
      apply Filter.mem_cofinite.mpr
      have hSc : Sᶜ.Finite :=
        Filter.mem_cofinite.mp (Filter.le_principal_iff.mp hS)
      refine (hSc.image
        (Sum.inr : Chapter15FinitePlace R → Chapter15Place R K)).subset ?_
      intro p hp
      cases p with
      | inl v =>
          exact (hp (Or.inl ⟨v, rfl⟩)).elim
      | inr v =>
          refine ⟨v, ?_, rfl⟩
          intro hv
          exact hp (Or.inr ⟨v, hv, rfl⟩)
    let gS :
        Chapter15ArchimedeanIdeleGroup K ×
            (Πʳ v : Chapter15FinitePlace R,
              [(v.adicCompletion K)ˣ,
                chapter15FiniteUnitIntegralSubgroup (R := R) (K := K) v]_[Filter.principal S]) →
          (Πʳ p : Chapter15Place R K,
            [(chapter15LocalRing p)ˣ,
              chapter15LocalUnitIntegralSubgroup (R := R) (K := K) p]_[Filter.principal T]) :=
      fun x =>
        ⟨(fun p =>
          match p with
          | Sum.inl v => x.1 v
          | Sum.inr v => x.2 v),
          by
            intro p hp
            cases p with
            | inl v =>
                change x.1 v ∈ (⊤ : Subgroup ((v.Completion)ˣ))
                exact trivial
            | inr v =>
                have hvS : v ∈ S := by
                  simpa [T] using hp
                have hx :
                    ∀ w : Chapter15FinitePlace R, w ∈ S →
                      x.2 w ∈
                        (chapter15FiniteUnitIntegralSubgroup (R := R) (K := K) w :
                          Set ((w.adicCompletion K)ˣ)) :=
                  Filter.eventually_principal.mp x.2.2
                exact hx v hvS⟩
    have hgS : Continuous gS := by
      apply RestrictedProduct.continuous_rng_of_principal.mpr
      apply continuous_pi
      intro p
      cases p with
      | inl v =>
          change Continuous
            (fun x : Chapter15ArchimedeanIdeleGroup K ×
              (Πʳ v : Chapter15FinitePlace R,
                [(v.adicCompletion K)ˣ,
                  chapter15FiniteUnitIntegralSubgroup (R := R) (K := K) v]_[Filter.principal S]) =>
              x.1 v)
          exact (continuous_apply v).comp continuous_fst
      | inr v =>
          change Continuous
            (fun x : Chapter15ArchimedeanIdeleGroup K ×
              (Πʳ v : Chapter15FinitePlace R,
                [(v.adicCompletion K)ˣ,
                  chapter15FiniteUnitIntegralSubgroup (R := R) (K := K) v]_[Filter.principal S]) =>
              x.2 v)
          exact
            (RestrictedProduct.continuous_eval
              (R := fun v : Chapter15FinitePlace R => (v.adicCompletion K)ˣ)
              (A := fun v =>
                (chapter15FiniteUnitIntegralSubgroup (R := R) (K := K) v :
                  Set ((v.adicCompletion K)ˣ)))
              (𝓕 := Filter.principal S) v).comp continuous_snd
    let iS :
        (Πʳ v : Chapter15FinitePlace R,
          [(v.adicCompletion K)ˣ,
            chapter15FiniteUnitIntegralSubgroup (R := R) (K := K) v]_[Filter.principal S]) →
          Chapter15FiniteIdeleGroup R K :=
      RestrictedProduct.inclusion
        (R := fun v : Chapter15FinitePlace R => (v.adicCompletion K)ˣ)
        (A := fun v =>
          (chapter15FiniteUnitIntegralSubgroup (R := R) (K := K) v :
            Set ((v.adicCompletion K)ˣ))) hS
    let iT :
        (Πʳ p : Chapter15Place R K,
          [(chapter15LocalRing p)ˣ,
            chapter15LocalUnitIntegralSubgroup (R := R) (K := K) p]_[Filter.principal T]) →
          Chapter15RestrictedIdeleGroup R K :=
      RestrictedProduct.inclusion
        (R := fun p : Chapter15Place R K => (chapter15LocalRing p)ˣ)
        (A := fun p =>
          (chapter15LocalUnitIntegralSubgroup (R := R) (K := K) p :
            Set ((chapter15LocalRing p)ˣ))) hT
    have hcomp : g ∘ (Prod.map id iS) = iT ∘ gS := by
      funext x
      apply Subtype.ext
      funext p
      cases p <;> rfl
    rw [hcomp]
    exact (RestrictedProduct.continuous_inclusion hT).comp hgS
  let e : Chapter15RestrictedIdeleGroup R K ≃* Chapter15IdeleGroup R K :=
    { toFun := fun x =>
        ((fun v : NumberField.InfinitePlace K => x (Sum.inl v)), m x)
      invFun := g
      left_inv := by
        intro x
        apply Subtype.ext
        funext p
        cases p <;> rfl
      right_inv := by
        intro x
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          funext v
          rfl
      map_mul' := by
        intro x y
        apply Prod.ext
        · funext v
          rfl
        · apply Subtype.ext
          funext v
          rfl }
  refine { __ := e, continuous_toFun := ?_, continuous_invFun := ?_ }
  · change Continuous (fun x : Chapter15RestrictedIdeleGroup R K =>
      ((fun v : NumberField.InfinitePlace K => x (Sum.inl v)), m x))
    exact hto
  · change Continuous g
    exact hginv

/- The finite-idele part is the canonical unit restricted product supplied by Mathlib. -/
def chapter15_finite_idele_group_equiv_finite_adele_units :
    Chapter15FiniteIdeleGroup R K ≃*
      (IsDedekindDomain.FiniteAdeleRing R K)ˣ := by
  have h : ∀ v : Chapter15FinitePlace R,
      chapter15FiniteUnitIntegralSubgroup (R := R) (K := K) v =
        (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
    intro v
    apply Subgroup.ext
    intro u
    constructor
    · rintro ⟨x, rfl⟩
      exact Submonoid.mem_units_of_val_mem_inv_val_mem _ x.1.2 x.2.2
    · intro hu
      rcases hu with ⟨hu, huinv⟩
      let x : (v.adicCompletionIntegers K)ˣ :=
        { val := ⟨(u : v.adicCompletion K), hu⟩
          inv := ⟨((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K), huinv⟩
          val_inv := by apply Subtype.ext; exact u.val_inv
          inv_val := by apply Subtype.ext; exact u.inv_val }
      exact ⟨x, by apply Units.ext; rfl⟩
  have hset : ∀ v : Chapter15FinitePlace R,
      (chapter15FiniteUnitIntegralSubgroup (R := R) (K := K) v :
        Set ((v.adicCompletion K)ˣ)) =
        ((Submonoid.ofClass (v.adicCompletionIntegers K)).units :
          Set ((v.adicCompletion K)ˣ)) := by
    intro v
    rw [h v]
  let f :
      (Πʳ v : Chapter15FinitePlace R, [(v.adicCompletion K)ˣ,
        chapter15FiniteUnitIntegralSubgroup (R := R) (K := K) v]) ≃*
      (Πʳ v : Chapter15FinitePlace R, [(v.adicCompletion K)ˣ,
        (Submonoid.ofClass (v.adicCompletionIntegers K)).units]) :=
    { toFun := fun x =>
        ⟨x.1, by
          filter_upwards [x.2] with v hv
          rw [hset v] at hv
          exact hv⟩
      invFun := fun x =>
        ⟨x.1, by
          filter_upwards [x.2] with v hv
          rw [← hset v] at hv
          exact hv⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl
      map_mul' := fun x y => Subtype.ext rfl }
  let e := RestrictedProduct.unitsEquiv
    (fun v : Chapter15FinitePlace R => v.adicCompletion K)
    (B := fun v => v.adicCompletionIntegers K) (𝓕 := Filter.cofinite)
  exact f.trans e.symm

/- The underlying multiplicative groups agree with units of the full adele
ring; the topology on the graph model is kept separate. -/
def chapter15_idele_group_equiv_full_adele_units
    [NumberField K] :
    Chapter15IdeleGroup R K ≃* Chapter15AdeleUnitGroup R K := by
  change (Chapter15ArchimedeanIdeleGroup K × Chapter15FiniteIdeleGroup R K) ≃*
    (NumberField.InfiniteAdeleRing K × IsDedekindDomain.FiniteAdeleRing R K)ˣ
  let hf :
      Chapter15FiniteIdeleGroup R K ≃*
        (IsDedekindDomain.FiniteAdeleRing R K)ˣ :=
    chapter15_finite_idele_group_equiv_finite_adele_units (R := R) (K := K)
  let h :
      (NumberField.InfiniteAdeleRing K × IsDedekindDomain.FiniteAdeleRing R K)ˣ ≃*
        (Chapter15ArchimedeanIdeleGroup K × Chapter15FiniteIdeleGroup R K) :=
    (MulEquiv.prodUnits.trans
      (MulEquiv.prodCongr (MulEquiv.piUnits) hf.symm))
  exact h.symm

/- The graph/restricted-product topology is deliberately kept separate from
the induced topology on the unit group of the adele ring.  The book's unit
group identification is algebraic; the graph description above is what makes
the idele topology a topological-group topology. -/

/-! ### Generic predicates used by later sections -/

/-- A family of local assertions holds almost everywhere at finite places. -/
def chapter15AlmostEverywhereFinite (P : Chapter15FinitePlace R → Prop) : Prop :=
  ∀ᶠ v : Chapter15FinitePlace R in Filter.cofinite, P v

/-- The matrix-entry formulation of the restricted tail. -/
def chapter15MatrixEntriesIntegralAlmostEverywhere
    (g : Chapter15FiniteMatrixGroup n R K) : Prop :=
  ∀ᶠ v : Chapter15FinitePlace R in Filter.cofinite,
    ∀ i j : Fin n, g v i j ∈ v.adicCompletionIntegers K

/-- The same predicate for the inverse matrix. -/
def chapter15InverseMatrixEntriesIntegralAlmostEverywhere
    (g : Chapter15FiniteMatrixGroup n R K) : Prop :=
  ∀ᶠ v : Chapter15FinitePlace R in Filter.cofinite,
    ∀ i j : Fin n, (g⁻¹) v i j ∈ v.adicCompletionIntegers K

/-- A book-facing full lattice in `K^n`. -/
abbrev Chapter15VectorSpace (n : ℕ) (K : Type*) := Fin n → K

/-- A fractional ideal over the chosen fraction field, using Mathlib's canonical type. -/
abbrev Chapter15FractionalIdeal (R K : Type*) [CommRing R] [Field K]
    [Algebra R K] := FractionalIdeal (nonZeroDivisors R) K

end

end LastLib.Book04AdelesAndIdeles.Chapter15
