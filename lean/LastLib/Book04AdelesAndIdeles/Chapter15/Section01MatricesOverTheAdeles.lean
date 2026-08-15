import LastLib.Book04AdelesAndIdeles.Chapter15.Dependencies
import LastLib.Book04AdelesAndIdeles.Chapter07.Dependencies
import Mathlib.LinearAlgebra.Matrix.Unique

namespace LastLib.Book04AdelesAndIdeles.Chapter15

noncomputable section

open Set Filter NumberField
open scoped RestrictedProduct

/-! ## 15.1. Matrices over the adeles -/

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- The book-facing `GLₙ(𝔸_K)`, written as the infinite product times the finite restricted product. -/
abbrev Chapter15GLnAdeles (n : ℕ) (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] :=
  Chapter15AdelicMatrixGroup n R K

/-! ### Shared finite-level interface -/

/-- The full-level subgroup attached to a finite level `K_f`. -/
def chapter15GlobalLevelSubgroup (n : ℕ)
    (Kf : Subgroup (Chapter15FiniteMatrixGroup n R K)) :
    Subgroup (Chapter15GLnAdeles n R K) where
  carrier := {g | g.1 = 1 ∧ g.2 ∈ Kf}
  one_mem' := by
    exact ⟨rfl, Kf.one_mem⟩
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    exact ⟨by simp [hg1, hh1], Kf.mul_mem hg2 hh2⟩
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    exact ⟨by simp [hg1], Kf.inv_mem hg2⟩

theorem chapter15_global_level_subgroup_mem_iff
    (n : ℕ) (Kf : Subgroup (Chapter15FiniteMatrixGroup n R K))
    (g : Chapter15GLnAdeles n R K) :
    g ∈ chapter15GlobalLevelSubgroup n Kf ↔ g.1 = 1 ∧ g.2 ∈ Kf :=
  Iff.rfl

/-- An arbitrary all-place tuple of local invertible matrices satisfies the adelic tail condition. -/
def chapter15RawMatrixIsAdelic (n : ℕ)
    (g : (p : Chapter15Place R K) →
      Matrix.GeneralLinearGroup (Fin n) (chapter15LocalRing p)) : Prop :=
  ∀ᶠ p : Chapter15Place R K in Filter.cofinite,
    g p ∈ chapter15LocalMatrixIntegralSubgroup n p

/-- The matrix analogue of the graph-tail condition: both a tuple and its inverse have integral
entries almost everywhere at finite places. -/
def chapter15RawMatrixEntriesAreAdelic (n : ℕ)
    (g : (p : Chapter15Place R K) →
      Matrix.GeneralLinearGroup (Fin n) (chapter15LocalRing p)) : Prop :=
  (∀ᶠ v : Chapter15FinitePlace R in Filter.cofinite,
      ∀ i j : Fin n, g (Sum.inr v) i j ∈ v.adicCompletionIntegers K) ∧
    (∀ᶠ v : Chapter15FinitePlace R in Filter.cofinite,
      ∀ i j : Fin n, (g (Sum.inr v))⁻¹ i j ∈ v.adicCompletionIntegers K)

theorem chapter15_finite_integral_matrix_mem_entries_and_inverse_iff
    (n : ℕ) (v : Chapter15FinitePlace R)
    (g : Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K)) :
    g ∈ chapter15FiniteMatrixIntegralSubgroup (R := R) (K := K) n v ↔
      ∀ i j : Fin n, g i j ∈ v.adicCompletionIntegers K ∧
        (g⁻¹) i j ∈ v.adicCompletionIntegers K := by
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

theorem chapter15_raw_matrix_is_adelic_iff_entries_and_inverse_adelic
    (n : ℕ) [NumberField K]
    (g : (p : Chapter15Place R K) →
      Matrix.GeneralLinearGroup (Fin n) (chapter15LocalRing p)) :
    chapter15RawMatrixIsAdelic n g ↔ chapter15RawMatrixEntriesAreAdelic n g := by
  let hinr : Tendsto (Sum.inr : Chapter15FinitePlace R → Chapter15Place R K)
      Filter.cofinite Filter.cofinite :=
    Function.Injective.tendsto_cofinite (fun a b h => Sum.inr.inj h)
  constructor
  · intro h
    change ∀ᶠ p : Chapter15Place R K in Filter.cofinite,
      g p ∈ (chapter15LocalMatrixIntegralSubgroup (R := R) (K := K) n p :
        Set (Matrix.GeneralLinearGroup (Fin n) (chapter15LocalRing p))) at h
    have hfin :
        ∀ᶠ v : Chapter15FinitePlace R in Filter.cofinite,
          g (Sum.inr v) ∈
            (chapter15FiniteMatrixIntegralSubgroup (R := R) (K := K) n v :
              Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K))) :=
      hinr.eventually h
    have hboth :
        ∀ᶠ v : Chapter15FinitePlace R in Filter.cofinite,
          ∀ i j : Fin n,
            g (Sum.inr v) i j ∈ v.adicCompletionIntegers K ∧
              (g (Sum.inr v))⁻¹ i j ∈ v.adicCompletionIntegers K :=
      hfin.mono fun v hv =>
        (chapter15_finite_integral_matrix_mem_entries_and_inverse_iff
          (R := R) (K := K) n v (g (Sum.inr v))).mp hv
    refine ⟨?_, ?_⟩
    · filter_upwards [hboth] with v hv
      intro i j
      exact (hv i j).1
    · filter_upwards [hboth] with v hv
      intro i j
      exact (hv i j).2
  · rintro ⟨hentries, hinverse⟩
    change ∀ᶠ p : Chapter15Place R K in Filter.cofinite,
      g p ∈ (chapter15LocalMatrixIntegralSubgroup (R := R) (K := K) n p :
        Set (Matrix.GeneralLinearGroup (Fin n) (chapter15LocalRing p)))
    have hfin :
        ∀ᶠ v : Chapter15FinitePlace R in Filter.cofinite,
          g (Sum.inr v) ∈
            (chapter15FiniteMatrixIntegralSubgroup (R := R) (K := K) n v :
              Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K))) := by
      filter_upwards [hentries, hinverse] with v hv hvi
      apply
        (chapter15_finite_integral_matrix_mem_entries_and_inverse_iff
          (R := R) (K := K) n v (g (Sum.inr v))).mpr
      intro i j
      exact ⟨hv i j, hvi i j⟩
    rw [Filter.eventually_cofinite]
    have hbad : Set.Finite
        {v : Chapter15FinitePlace R |
          ¬ g (Sum.inr v) ∈
            (chapter15FiniteMatrixIntegralSubgroup (R := R) (K := K) n v :
              Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K)))} :=
      Filter.eventually_cofinite.mp hfin
    have hinl : Set.Finite (Set.range (Sum.inl : NumberField.InfinitePlace K →
        Chapter15Place R K)) :=
      Set.toFinite _
    refine Set.Finite.subset ((hbad.image
      (Sum.inr : Chapter15FinitePlace R → Chapter15Place R K)).union hinl) ?_
    intro p hp
    cases p with
    | inl v =>
        exact Or.inr ⟨v, rfl⟩
    | inr v =>
        exact Or.inl ⟨v, hp, rfl⟩

theorem chapter15_restricted_matrix_group_tail
    (n : ℕ) [NumberField K]
    (g : Chapter15RestrictedAdelicMatrixGroup n R K) :
    chapter15RawMatrixEntriesAreAdelic n (fun p => g p) := by
  exact
    (chapter15_raw_matrix_is_adelic_iff_entries_and_inverse_adelic
      (R := R) (K := K) n (fun p => g p)).mp g.2

/-! ### The local integral model -/

theorem chapter15_finite_integral_matrix_mem_iff
    (n : ℕ) (_hn : 0 < n) (v : Chapter15FinitePlace R)
    (g : Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K)) :
    g ∈ chapter15FiniteMatrixIntegralSubgroup n v ↔
      (∀ i j : Fin n, g i j ∈ v.adicCompletionIntegers K) ∧
      ∃ u : (v.adicCompletionIntegers K)ˣ,
        Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom u =
          Matrix.GeneralLinearGroup.det g := by
  let : Nonempty (Fin n) := ⟨⟨0, _hn⟩⟩
  constructor
  · rintro ⟨x, rfl⟩
    constructor
    · intro i j
      exact (x i j).property
    · refine ⟨Matrix.GeneralLinearGroup.det x, ?_⟩
      exact (Matrix.GeneralLinearGroup.map_det
        (v.adicCompletionIntegers K).subtype x).symm
  · rintro ⟨hentries, ⟨u, hu⟩⟩
    let A : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers K) :=
      fun i j => ⟨g i j, hentries i j⟩
    have hA :
        A.map (v.adicCompletionIntegers K).subtype =
          (g : Matrix (Fin n) (Fin n) (v.adicCompletion K)) := by
      ext i j
      rfl
    have huval :
        (v.adicCompletionIntegers K).subtype (u : v.adicCompletionIntegers K) =
          Matrix.det (g : Matrix (Fin n) (Fin n) (v.adicCompletion K)) := by
      have huv := congrArg
        (fun z : (v.adicCompletion K)ˣ => (z : v.adicCompletion K)) hu
      change (v.adicCompletionIntegers K).subtype (u : v.adicCompletionIntegers K) =
        Matrix.det (g : Matrix (Fin n) (Fin n) (v.adicCompletion K)) at huv
      exact huv
    have hdet_eq :
        Matrix.det A = (u : v.adicCompletionIntegers K) := by
      apply Subtype.ext
      calc
        (v.adicCompletionIntegers K).subtype (Matrix.det A) =
            Matrix.det (A.map (v.adicCompletionIntegers K).subtype) :=
          RingHom.map_det (v.adicCompletionIntegers K).subtype A
        _ = Matrix.det (g : Matrix (Fin n) (Fin n) (v.adicCompletion K)) := by
          rw [hA]
        _ = (v.adicCompletionIntegers K).subtype (u : v.adicCompletionIntegers K) :=
          huval.symm
    have hunit : IsUnit (Matrix.det A) := by
      rw [hdet_eq]
      exact u.isUnit
    let x : Matrix.GeneralLinearGroup (Fin n) (v.adicCompletionIntegers K) :=
      Matrix.GeneralLinearGroup.mk'' A hunit
    refine ⟨x, ?_⟩
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rfl

theorem chapter15_finite_integral_matrix_group_is_closed
    (n : ℕ) (v : Chapter15FinitePlace R) :
    IsClosed
      (chapter15FiniteMatrixIntegralSubgroup (R := R) (K := K) n v :
        Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K))) := by
  have hmem :
      (chapter15FiniteMatrixIntegralSubgroup (R := R) (K := K) n v :
        Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K))) =
        {g : Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K) |
          ∀ i j, g i j ∈ v.adicCompletionIntegers K ∧
            (g⁻¹) i j ∈ v.adicCompletionIntegers K} := by
    ext g
    exact
      (chapter15_finite_integral_matrix_mem_entries_and_inverse_iff
        (R := R) (K := K) n v g)
  rw [hmem]
  have hclosed :
      IsClosed (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    Valued.isClosed_valuationSubring _
  have hset :
      {g : Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K) |
          ∀ i j, g i j ∈ v.adicCompletionIntegers K ∧
            (g⁻¹) i j ∈ v.adicCompletionIntegers K} =
        ⋂ i : Fin n, ⋂ j : Fin n,
          {g : Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K) |
            g i j ∈ v.adicCompletionIntegers K ∧
              (g⁻¹) i j ∈ v.adicCompletionIntegers K} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  rw [hset]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
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
  exact (hclosed.preimage hcval).inter (hclosed.preimage hcinv)

theorem chapter15_finite_integral_matrix_group_is_compact
    (n : ℕ) {L : Type*} [Field L] [NumberField L]
    (v : Chapter15FinitePlace (𝓞 L)) :
    IsCompact
      (chapter15FiniteMatrixIntegralSubgroup (R := 𝓞 L) (K := L) n v :
        Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion L))) := by
  have hO : IsCompact (v.adicCompletionIntegers L : Set (v.adicCompletion L)) :=
    Chapter07.chapter07_finite_local_integer_isCompact (𝓞 L) L v
  have hOs : IsCompact (Set.univ : Set (v.adicCompletionIntegers L)) :=
    isCompact_iff_isCompact_univ.mp hO
  have heq :
      (Set.matrix (Set.univ : Set (v.adicCompletionIntegers L)) :
        Set (Matrix (Fin n) (Fin n) (v.adicCompletionIntegers L))) =
        Set.univ := by
    ext M
    simp [Set.mem_matrix]
  have hM : IsCompact
      (Set.univ : Set (Matrix (Fin n) (Fin n) (v.adicCompletionIntegers L))) := by
    rw [← heq]
    exact hOs.matrix
  have heqU :
      ((⊤ : Submonoid (Matrix (Fin n) (Fin n) (v.adicCompletionIntegers L))).units :
        Set (Matrix (Fin n) (Fin n) (v.adicCompletionIntegers L))ˣ) =
        Set.univ := by
    ext u
    simp
  have hU :
      IsCompact (Set.univ : Set (Matrix (Fin n) (Fin n) (v.adicCompletionIntegers L))ˣ) := by
    rw [← heqU]
    exact Submonoid.units_isCompact hM
  let f : Matrix.GeneralLinearGroup (Fin n) (v.adicCompletionIntegers L) →
      Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion L) :=
    Matrix.GeneralLinearGroup.map (v.adicCompletionIntegers L).subtype
  have hf : Continuous f := by
    exact
      (continuous_subtype_val :
        Continuous ((↑) : v.adicCompletionIntegers L → v.adicCompletion L)).generalLinearGroup_map
  have hrange : IsCompact (Set.range f) := by
    rw [← Set.image_univ]
    exact hU.image hf
  simpa [chapter15FiniteMatrixIntegralSubgroup] using hrange

theorem chapter15_finite_integral_matrix_group_is_open
    (n : ℕ) (v : Chapter15FinitePlace R) :
    IsOpen
      (chapter15FiniteMatrixIntegralSubgroup (R := R) (K := K) n v :
        Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K))) := by
  have hmem : (chapter15FiniteMatrixIntegralSubgroup (R := R) (K := K) n v :
      Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K))) =
      {g : Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K) |
        ∀ i j, g i j ∈ v.adicCompletionIntegers K ∧
          (g⁻¹) i j ∈ v.adicCompletionIntegers K} := by
    ext g
    exact
      (chapter15_finite_integral_matrix_mem_entries_and_inverse_iff
        (R := R) (K := K) n v g)
  rw [hmem]
  have hopen :
      IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    Valued.isOpen_valuationSubring _
  have hset :
      {g : Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K) |
          ∀ i j, g i j ∈ v.adicCompletionIntegers K ∧
            (g⁻¹) i j ∈ v.adicCompletionIntegers K} =
        ⋂ i : Fin n, ⋂ j : Fin n,
          {g : Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K) |
            g i j ∈ v.adicCompletionIntegers K ∧
              (g⁻¹) i j ∈ v.adicCompletionIntegers K} := by
    ext g
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

/-! ### The standard finite compact open subgroup -/

/-- `GLₙ(\widehat{𝓞}_K)`: the subgroup integral at every finite place. -/
def chapter15StandardFiniteMatrixLevel (n : ℕ) :
    Subgroup (Chapter15FiniteMatrixGroup n R K) where
  carrier := {g | ∀ v : Chapter15FinitePlace R,
    g v ∈ chapter15FiniteMatrixIntegralSubgroup n v}
  one_mem' := by
    intro v
    exact (chapter15FiniteMatrixIntegralSubgroup n v).one_mem
  mul_mem' := by
    intro g h hg hh v
    exact (chapter15FiniteMatrixIntegralSubgroup n v).mul_mem (hg v) (hh v)
  inv_mem' := by
    intro g hg v
    exact (chapter15FiniteMatrixIntegralSubgroup n v).inv_mem (hg v)

theorem chapter15_standard_finite_matrix_level_mem_iff
    (n : ℕ) (g : Chapter15FiniteMatrixGroup n R K) :
    g ∈ chapter15StandardFiniteMatrixLevel n ↔
      ∀ v : Chapter15FinitePlace R,
        g v ∈ chapter15FiniteMatrixIntegralSubgroup n v :=
  Iff.rfl

theorem chapter15_standard_finite_matrix_level_is_compact
    (n : ℕ) {L : Type*} [Field L] [NumberField L] :
    IsCompact
      (chapter15StandardFiniteMatrixLevel (R := 𝓞 L) (K := L) n :
        Set (Chapter15FiniteMatrixGroup n (𝓞 L) L)) := by
  let A :
      (v : Chapter15FinitePlace (𝓞 L)) →
        Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion L)) :=
    fun v => (chapter15FiniteMatrixIntegralSubgroup (R := 𝓞 L) (K := L) n v :
      Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion L)))
  have hAcompact : ∀ v, IsCompact (A v) := fun v =>
    chapter15_finite_integral_matrix_group_is_compact n v
  have hAopen : ∀ v, IsOpen (A v) := fun v =>
    chapter15_finite_integral_matrix_group_is_open n v
  have hprod' : IsCompact
      {x : ∀ v, A v | ∀ v, x v ∈ (Set.univ : Set (A v))} :=
    isCompact_pi_infinite (fun v =>
      isCompact_iff_isCompact_univ.mp (hAcompact v))
  have hprod : IsCompact (Set.univ : Set (∀ v, A v)) := by
    convert hprod' using 1
    ext x
    simp
  have hrange :
      IsCompact
        (Set.range
          (RestrictedProduct.structureMap
            (fun v : Chapter15FinitePlace (𝓞 L) =>
              Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion L)) A cofinite)) := by
    rw [← Set.image_univ]
    exact hprod.image
      (RestrictedProduct.isOpenEmbedding_structureMap hAopen).continuous
  have heq :
      Set.range
          (RestrictedProduct.structureMap
            (fun v : Chapter15FinitePlace (𝓞 L) =>
              Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion L)) A cofinite) =
        (chapter15StandardFiniteMatrixLevel (R := 𝓞 L) (K := L) n :
          Set (Chapter15FiniteMatrixGroup n (𝓞 L) L)) := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      intro v
      exact (x v).property
    · intro hg
      apply RestrictedProduct.exists_structureMap_eq_of_forall
      intro v
      exact hg v
  rw [← heq]
  exact hrange

theorem chapter15_standard_finite_matrix_level_is_open
    (n : ℕ) :
    IsOpen
      (chapter15StandardFiniteMatrixLevel (R := R) (K := K) n :
        Set (Chapter15FiniteMatrixGroup n R K)) := by
  let A :
      (v : Chapter15FinitePlace R) →
        Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K)) :=
    fun v => (chapter15FiniteMatrixIntegralSubgroup (R := R) (K := K) n v :
      Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K)))
  have hAopen : ∀ v, IsOpen (A v) := fun v =>
    chapter15_finite_integral_matrix_group_is_open n v
  have hrange :
      IsOpen
        (Set.range
          (RestrictedProduct.structureMap
            (fun v : Chapter15FinitePlace R =>
              Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K)) A cofinite)) :=
    (RestrictedProduct.isOpenEmbedding_structureMap hAopen).isOpen_range
  have heq :
      Set.range
          (RestrictedProduct.structureMap
            (fun v : Chapter15FinitePlace R =>
              Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K)) A cofinite) =
        (chapter15StandardFiniteMatrixLevel (R := R) (K := K) n :
          Set (Chapter15FiniteMatrixGroup n R K)) := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      intro v
      exact (x v).property
    · intro hg
      apply RestrictedProduct.exists_structureMap_eq_of_forall
      intro v
      exact hg v
  rw [← heq]
  exact hrange

/-! ### Local compactness and rank one -/

theorem chapter15_adelic_matrix_group_is_locally_compact
    (n : ℕ) {L : Type*} [Field L] [NumberField L] :
    LocallyCompactSpace (Chapter15GLnAdeles n (𝓞 L) L) := by
  have harch : ∀ v : NumberField.InfinitePlace L,
      LocallyCompactSpace
        (Matrix.GeneralLinearGroup (Fin n) v.Completion) := by
    intro v
    let : LocallyCompactSpace
        (Matrix (Fin n) (Fin n) v.Completion) :=
      Pi.locallyCompactSpace_of_finite
    let : T1Space
        (Matrix (Fin n) (Fin n) v.Completion) := by
      infer_instance
    exact
      (inferInstance :
        LocallyCompactSpace
          (Matrix (Fin n) (Fin n) v.Completion)ˣ)
  have hfiniteLocal : ∀ v : Chapter15FinitePlace (𝓞 L),
      LocallyCompactSpace
        (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion L)) := by
    intro v
    have hcompact : IsCompact
        (v.adicCompletionIntegers L : Set (v.adicCompletion L)) :=
      Chapter07.chapter07_finite_local_integer_isCompact (𝓞 L) L v
    have hopen : IsOpen
        (v.adicCompletionIntegers L : Set (v.adicCompletion L)) :=
      Valued.isOpen_valuationSubring _
    let : LocallyCompactSpace (v.adicCompletion L) :=
      hcompact.locallyCompactSpace_of_mem_nhds_of_addGroup
        (hopen.mem_nhds (show (0 : v.adicCompletion L) ∈
          (v.adicCompletionIntegers L : Set (v.adicCompletion L)) by simp))
    let : LocallyCompactSpace
        (Matrix (Fin n) (Fin n) (v.adicCompletion L)) :=
      Pi.locallyCompactSpace_of_finite
    let : T1Space
        (Matrix (Fin n) (Fin n) (v.adicCompletion L)) := by
      infer_instance
    exact
      (inferInstance :
        LocallyCompactSpace
          (Matrix (Fin n) (Fin n) (v.adicCompletion L))ˣ)
  let : ∀ v : NumberField.InfinitePlace L,
      LocallyCompactSpace
        (Matrix.GeneralLinearGroup (Fin n) v.Completion) := harch
  let : ∀ v : Chapter15FinitePlace (𝓞 L),
      LocallyCompactSpace
        (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion L)) := hfiniteLocal
  let : Fact (∀ v : Chapter15FinitePlace (𝓞 L),
      IsOpen
        (chapter15FiniteMatrixIntegralSubgroup (R := 𝓞 L) (K := L) n v :
          Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion L)))) :=
    ⟨fun v => chapter15_finite_integral_matrix_group_is_open n v⟩
  have hfinite : LocallyCompactSpace
      (Chapter15FiniteMatrixGroup n (𝓞 L) L) :=
    RestrictedProduct.locallyCompactSpace_of_group
      (R := fun v : Chapter15FinitePlace (𝓞 L) =>
        Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion L))
      (B := fun v : Chapter15FinitePlace (𝓞 L) =>
        chapter15FiniteMatrixIntegralSubgroup (R := 𝓞 L) (K := L) n v)
      (Filter.Eventually.of_forall (fun v =>
        chapter15_finite_integral_matrix_group_is_compact n v))
  let : LocallyCompactSpace
      (Chapter15FiniteMatrixGroup n (𝓞 L) L) := hfinite
  let : LocallyCompactSpace
      (Chapter15ArchimedeanMatrixGroup n L) :=
    Pi.locallyCompactSpace_of_finite
  exact inferInstance

theorem chapter15_adelic_matrix_group_is_locally_compact_of_ring_of_integers
    (n : ℕ) [NumberField K] :
    LocallyCompactSpace (Chapter15GLnAdeles n (𝓞 K) K) := by
  exact chapter15_adelic_matrix_group_is_locally_compact n

def chapter15_rank_one_local_gl_is_multiplicative_group
    (A : Type*) [CommRing A] :
    Matrix.GeneralLinearGroup (Fin 1) A ≃* Aˣ := by
  exact
    { toFun := Matrix.GeneralLinearGroup.det
      invFun := Matrix.GeneralLinearGroup.scalar (Fin 1)
      left_inv := by
        intro g
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        simp [Matrix.GeneralLinearGroup.coe_scalar,
          Unique.eq_default i, Unique.eq_default j]
      right_inv := by
        intro u
        simpa only [Fintype.card_fin, pow_one] using
          (Matrix.GeneralLinearGroup.det_scalar (n := Fin 1) u)
      map_mul' := by
        intro u v
        exact Matrix.GeneralLinearGroup.det.map_mul u v }

/- The rank-one equivalence used in the adelic identification must also respect
the local topologies. -/
def chapter15_rank_one_local_gl_is_topological_multiplicative_group
    (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    Matrix.GeneralLinearGroup (Fin 1) A ≃ₜ* Aˣ := by
  have hscalar :
      Continuous
        (Matrix.GeneralLinearGroup.scalar (Fin 1) :
          Aˣ → Matrix.GeneralLinearGroup (Fin 1) A) := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · change Continuous
        (fun u : Aˣ => Matrix.scalar (Fin 1) (u : A))
      exact continuous_matrix fun i j => by
        simp [Unique.eq_default i, Unique.eq_default j]
        exact Units.continuous_val
    · change Continuous
        (fun u : Aˣ => Matrix.scalar (Fin 1) ((u⁻¹ : Aˣ) : A))
      exact continuous_matrix fun i j => by
        simp [Unique.eq_default i, Unique.eq_default j]
        exact Units.continuous_coe_inv
  exact
    { toMulEquiv := chapter15_rank_one_local_gl_is_multiplicative_group A
      continuous_toFun := Matrix.GeneralLinearGroup.continuous_det
      continuous_invFun := hscalar }

/- LOCAL_DEPENDENCY_GUESS: this is the book-facing rank-one identification of
the restricted matrix construction with the graph-topologized idele group. -/
def chapter15_rank_one_recovers_ideles
    (K : Type*) [Field K] [NumberField K] :
    Chapter15GLnAdeles 1 (𝓞 K) K ≃ₜ* Chapter15IdeleGroup (𝓞 K) K := by
  let e : ∀ v : Chapter15FinitePlace (𝓞 K),
      Matrix.GeneralLinearGroup (Fin 1) (v.adicCompletion K) ≃ₜ*
        (v.adicCompletion K)ˣ :=
    fun v =>
      chapter15_rank_one_local_gl_is_topological_multiplicative_group
        (v.adicCompletion K)
  have hφ : ∀ v : Chapter15FinitePlace (𝓞 K),
      MapsTo (e v)
        (chapter15FiniteMatrixIntegralSubgroup (R := 𝓞 K) (K := K) 1 v :
          Set (Matrix.GeneralLinearGroup (Fin 1) (v.adicCompletion K)))
        (chapter15FiniteUnitIntegralSubgroup (R := 𝓞 K) (K := K) v :
          Set ((v.adicCompletion K)ˣ)) := by
    intro v g hg
    change Matrix.GeneralLinearGroup.det g ∈
      (chapter15FiniteUnitIntegralSubgroup (R := 𝓞 K) (K := K) v :
        Set ((v.adicCompletion K)ˣ))
    rcases
        (chapter15_finite_integral_matrix_mem_iff
          (R := 𝓞 K) (K := K) 1 (by decide) v g).mp hg with
      ⟨_, u, hu⟩
    exact ⟨u, hu⟩
  have hφinv : ∀ v : Chapter15FinitePlace (𝓞 K),
      MapsTo (e v).symm
        (chapter15FiniteUnitIntegralSubgroup (R := 𝓞 K) (K := K) v :
          Set ((v.adicCompletion K)ˣ))
        (chapter15FiniteMatrixIntegralSubgroup (R := 𝓞 K) (K := K) 1 v :
          Set (Matrix.GeneralLinearGroup (Fin 1) (v.adicCompletion K))) := by
    intro v u hu
    rcases hu with ⟨x, hx⟩
    change Matrix.GeneralLinearGroup.scalar (Fin 1) u ∈
      (chapter15FiniteMatrixIntegralSubgroup (R := 𝓞 K) (K := K) 1 v :
        Set (Matrix.GeneralLinearGroup (Fin 1) (v.adicCompletion K)))
    apply
      (chapter15_finite_integral_matrix_mem_iff
        (R := 𝓞 K) (K := K) 1 (by decide) v
        (Matrix.GeneralLinearGroup.scalar (Fin 1) u)).mpr
    constructor
    · intro i j
      simp [Matrix.GeneralLinearGroup.coe_scalar,
        Unique.eq_default i, Unique.eq_default j, ← hx]
    · refine ⟨x, ?_⟩
      simpa only [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, pow_one] using hx
  let m : Chapter15FiniteMatrixGroup 1 (𝓞 K) K →
      Chapter15FiniteIdeleGroup (𝓞 K) K :=
    RestrictedProduct.map
      (φ := fun v => e v) (Filter.Eventually.of_forall hφ)
  let mInv : Chapter15FiniteIdeleGroup (𝓞 K) K →
      Chapter15FiniteMatrixGroup 1 (𝓞 K) K :=
    RestrictedProduct.map
      (φ := fun v => (e v).symm) (Filter.Eventually.of_forall hφinv)
  have hmleft : Function.LeftInverse mInv m := by
    intro x
    apply Subtype.ext
    funext v
    change (e v).symm ((e v) (x v)) = x v
    exact (e v).symm_apply_apply (x v)
  have hmright : Function.RightInverse mInv m := by
    intro x
    apply Subtype.ext
    funext v
    change (e v) ((e v).symm (x v)) = x v
    exact (e v).apply_symm_apply (x v)
  have hmcont : Continuous m := by
    exact RestrictedProduct.mapAlong_continuous
      (R₁ := fun v : Chapter15FinitePlace (𝓞 K) =>
        Matrix.GeneralLinearGroup (Fin 1) (v.adicCompletion K))
      (R₂ := fun v : Chapter15FinitePlace (𝓞 K) => (v.adicCompletion K)ˣ)
      (A₁ := fun v =>
        (chapter15FiniteMatrixIntegralSubgroup (R := 𝓞 K) (K := K) 1 v :
          Set (Matrix.GeneralLinearGroup (Fin 1) (v.adicCompletion K))))
      (A₂ := fun v =>
        (chapter15FiniteUnitIntegralSubgroup (R := 𝓞 K) (K := K) v :
          Set ((v.adicCompletion K)ˣ)))
      (f := id) Filter.tendsto_id (fun v => e v)
      (Filter.Eventually.of_forall hφ)
      (fun v => (e v).continuous_toFun)
  have hmInvCont : Continuous mInv := by
    exact RestrictedProduct.mapAlong_continuous
      (R₁ := fun v : Chapter15FinitePlace (𝓞 K) => (v.adicCompletion K)ˣ)
      (R₂ := fun v : Chapter15FinitePlace (𝓞 K) =>
        Matrix.GeneralLinearGroup (Fin 1) (v.adicCompletion K))
      (A₁ := fun v =>
        (chapter15FiniteUnitIntegralSubgroup (R := 𝓞 K) (K := K) v :
          Set ((v.adicCompletion K)ˣ)))
      (A₂ := fun v =>
        (chapter15FiniteMatrixIntegralSubgroup (R := 𝓞 K) (K := K) 1 v :
          Set (Matrix.GeneralLinearGroup (Fin 1) (v.adicCompletion K))))
      (f := id) Filter.tendsto_id (fun v => (e v).symm)
      (Filter.Eventually.of_forall hφinv)
      (fun v => (e v).symm.continuous_toFun)
  let efin : Chapter15FiniteMatrixGroup 1 (𝓞 K) K ≃ₜ*
      Chapter15FiniteIdeleGroup (𝓞 K) K :=
    { toMulEquiv :=
        { toFun := m
          invFun := mInv
          left_inv := hmleft
          right_inv := hmright
          map_mul' := by
            intro x y
            apply Subtype.ext
            funext v
            change e v (x v * y v) = e v (x v) * e v (y v)
            exact (e v).map_mul _ _ }
      continuous_toFun := hmcont
      continuous_invFun := hmInvCont }
  let ea : ∀ v : NumberField.InfinitePlace K,
      Matrix.GeneralLinearGroup (Fin 1) v.Completion ≃ₜ* (v.Completion)ˣ :=
    fun v =>
      chapter15_rank_one_local_gl_is_topological_multiplicative_group v.Completion
  let earch : Chapter15ArchimedeanMatrixGroup 1 K ≃ₜ*
      Chapter15ArchimedeanIdeleGroup K :=
    { toMulEquiv :=
        { toFun := fun x v => ea v (x v)
          invFun := fun x v => (ea v).symm (x v)
          left_inv := by
            intro x
            funext v
            exact (ea v).symm_apply_apply (x v)
          right_inv := by
            intro x
            funext v
            exact (ea v).apply_symm_apply (x v)
          map_mul' := by
            intro x y
            funext v
            exact (ea v).map_mul _ _ }
      continuous_toFun := by
        apply continuous_pi
        intro v
        exact (ea v).continuous_toFun.comp (continuous_apply v)
      continuous_invFun := by
        apply continuous_pi
        intro v
        exact (ea v).continuous_invFun.comp (continuous_apply v) }
  exact
    { toMulEquiv := earch.toMulEquiv.prodCongr efin.toMulEquiv
      continuous_toFun := by
        change Continuous
          (fun x : Chapter15GLnAdeles 1 (𝓞 K) K =>
            (earch x.1, efin x.2))
        exact
          (earch.continuous_toFun.comp continuous_fst).prodMk
            (efin.continuous_toFun.comp continuous_snd)
      continuous_invFun := by
        change Continuous
          (fun x : Chapter15IdeleGroup (𝓞 K) K =>
            (earch.symm x.1, efin.symm x.2))
        exact
          (earch.continuous_invFun.comp continuous_fst).prodMk
            (efin.continuous_invFun.comp continuous_snd) }

theorem chapter15_idele_group_is_locally_compact
    (K : Type*) [Field K] [NumberField K] :
    LocallyCompactSpace (Chapter15IdeleGroup (𝓞 K) K) := by
  let : LocallyCompactSpace (Chapter15GLnAdeles 1 (𝓞 K) K) :=
    chapter15_adelic_matrix_group_is_locally_compact_of_ring_of_integers 1
  exact
    (chapter15_rank_one_recovers_ideles K).toHomeomorph.symm.isOpenEmbedding.locallyCompactSpace

/- The same identification on the finite standard level. -/
def chapter15_rank_one_standard_level_recovers_finite_integral_ideles
    (K : Type*) [Field K] [NumberField K] :
    (chapter15StandardFiniteMatrixLevel (R := 𝓞 K) (K := K) 1 : Type _) ≃ₜ*
      (chapter15StandardFiniteIdeleLevel (R := 𝓞 K) (K := K) : Type _) := by
  let e : ∀ v : Chapter15FinitePlace (𝓞 K),
      Matrix.GeneralLinearGroup (Fin 1) (v.adicCompletion K) ≃ₜ*
        (v.adicCompletion K)ˣ :=
    fun v =>
      chapter15_rank_one_local_gl_is_topological_multiplicative_group
        (v.adicCompletion K)
  have hφ : ∀ v : Chapter15FinitePlace (𝓞 K),
      MapsTo (e v)
        (chapter15FiniteMatrixIntegralSubgroup (R := 𝓞 K) (K := K) 1 v :
          Set (Matrix.GeneralLinearGroup (Fin 1) (v.adicCompletion K)))
        (chapter15FiniteUnitIntegralSubgroup (R := 𝓞 K) (K := K) v :
          Set ((v.adicCompletion K)ˣ)) := by
    intro v g hg
    change Matrix.GeneralLinearGroup.det g ∈
      (chapter15FiniteUnitIntegralSubgroup (R := 𝓞 K) (K := K) v :
        Set ((v.adicCompletion K)ˣ))
    rcases
        (chapter15_finite_integral_matrix_mem_iff
          (R := 𝓞 K) (K := K) 1 (by decide) v g).mp hg with
      ⟨_, u, hu⟩
    exact ⟨u, hu⟩
  have hφinv : ∀ v : Chapter15FinitePlace (𝓞 K),
      MapsTo (e v).symm
        (chapter15FiniteUnitIntegralSubgroup (R := 𝓞 K) (K := K) v :
          Set ((v.adicCompletion K)ˣ))
        (chapter15FiniteMatrixIntegralSubgroup (R := 𝓞 K) (K := K) 1 v :
          Set (Matrix.GeneralLinearGroup (Fin 1) (v.adicCompletion K))) := by
    intro v u hu
    rcases hu with ⟨x, hx⟩
    change Matrix.GeneralLinearGroup.scalar (Fin 1) u ∈
      (chapter15FiniteMatrixIntegralSubgroup (R := 𝓞 K) (K := K) 1 v :
        Set (Matrix.GeneralLinearGroup (Fin 1) (v.adicCompletion K)))
    apply
      (chapter15_finite_integral_matrix_mem_iff
        (R := 𝓞 K) (K := K) 1 (by decide) v
        (Matrix.GeneralLinearGroup.scalar (Fin 1) u)).mpr
    constructor
    · intro i j
      simp [Matrix.GeneralLinearGroup.coe_scalar,
        Unique.eq_default i, Unique.eq_default j, ← hx]
    · refine ⟨x, ?_⟩
      simpa only [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, pow_one] using hx
  let m : Chapter15FiniteMatrixGroup 1 (𝓞 K) K →
      Chapter15FiniteIdeleGroup (𝓞 K) K :=
    RestrictedProduct.map
      (φ := fun v => e v) (Filter.Eventually.of_forall hφ)
  let mInv : Chapter15FiniteIdeleGroup (𝓞 K) K →
      Chapter15FiniteMatrixGroup 1 (𝓞 K) K :=
    RestrictedProduct.map
      (φ := fun v => (e v).symm) (Filter.Eventually.of_forall hφinv)
  have hmcont : Continuous m := by
    exact RestrictedProduct.mapAlong_continuous
      (R₁ := fun v : Chapter15FinitePlace (𝓞 K) =>
        Matrix.GeneralLinearGroup (Fin 1) (v.adicCompletion K))
      (R₂ := fun v : Chapter15FinitePlace (𝓞 K) => (v.adicCompletion K)ˣ)
      (A₁ := fun v =>
        (chapter15FiniteMatrixIntegralSubgroup (R := 𝓞 K) (K := K) 1 v :
          Set (Matrix.GeneralLinearGroup (Fin 1) (v.adicCompletion K))))
      (A₂ := fun v =>
        (chapter15FiniteUnitIntegralSubgroup (R := 𝓞 K) (K := K) v :
          Set ((v.adicCompletion K)ˣ)))
      (f := id) Filter.tendsto_id (fun v => e v)
      (Filter.Eventually.of_forall hφ)
      (fun v => (e v).continuous_toFun)
  have hmInvCont : Continuous mInv := by
    exact RestrictedProduct.mapAlong_continuous
      (R₁ := fun v : Chapter15FinitePlace (𝓞 K) => (v.adicCompletion K)ˣ)
      (R₂ := fun v : Chapter15FinitePlace (𝓞 K) =>
        Matrix.GeneralLinearGroup (Fin 1) (v.adicCompletion K))
      (A₁ := fun v =>
        (chapter15FiniteUnitIntegralSubgroup (R := 𝓞 K) (K := K) v :
          Set ((v.adicCompletion K)ˣ)))
      (A₂ := fun v =>
        (chapter15FiniteMatrixIntegralSubgroup (R := 𝓞 K) (K := K) 1 v :
          Set (Matrix.GeneralLinearGroup (Fin 1) (v.adicCompletion K))))
      (f := id) Filter.tendsto_id (fun v => (e v).symm)
      (Filter.Eventually.of_forall hφinv)
      (fun v => (e v).symm.continuous_toFun)
  let mS :
      (chapter15StandardFiniteMatrixLevel (R := 𝓞 K) (K := K) 1 : Type _) →
        (chapter15StandardFiniteIdeleLevel (R := 𝓞 K) (K := K) : Type _) :=
    fun x => ⟨m x.1, fun v => hφ v (x.2 v)⟩
  let mSInv :
      (chapter15StandardFiniteIdeleLevel (R := 𝓞 K) (K := K) : Type _) →
        (chapter15StandardFiniteMatrixLevel (R := 𝓞 K) (K := K) 1 : Type _) :=
    fun x => ⟨mInv x.1, fun v => hφinv v (x.2 v)⟩
  have hmScont : Continuous mS := by
    dsimp [mS]
    exact (hmcont.comp continuous_subtype_val).subtype_mk _
  have hmSInvCont : Continuous mSInv := by
    dsimp [mSInv]
    exact (hmInvCont.comp continuous_subtype_val).subtype_mk _
  have hmSleft : Function.LeftInverse mSInv mS := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    funext v
    change (e v).symm ((e v) (x.1 v)) = x.1 v
    exact (e v).symm_apply_apply (x.1 v)
  have hmSright : Function.RightInverse mSInv mS := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    funext v
    change (e v) ((e v).symm (x.1 v)) = x.1 v
    exact (e v).apply_symm_apply (x.1 v)
  exact
    { toMulEquiv :=
        { toFun := mS
          invFun := mSInv
          left_inv := hmSleft
          right_inv := hmSright
          map_mul' := by
            intro x y
            apply Subtype.ext
            apply Subtype.ext
            funext v
            change e v (x.1 v * y.1 v) = e v (x.1 v) * e v (y.1 v)
            exact (e v).map_mul _ _ }
      continuous_toFun := hmScont
      continuous_invFun := hmSInvCont }

def chapter15_rank_one_finite_matrix_group_recovers_finite_ideles
    (K : Type*) [Field K] [NumberField K] :
    Chapter15FiniteMatrixGroup 1 (𝓞 K) K ≃ₜ*
      Chapter15FiniteIdeleGroup (𝓞 K) K := by
  let e : ∀ v : Chapter15FinitePlace (𝓞 K),
      Matrix.GeneralLinearGroup (Fin 1) (v.adicCompletion K) ≃ₜ*
        (v.adicCompletion K)ˣ :=
    fun v =>
      chapter15_rank_one_local_gl_is_topological_multiplicative_group
        (v.adicCompletion K)
  have hφ : ∀ v : Chapter15FinitePlace (𝓞 K),
      MapsTo (e v)
        (chapter15FiniteMatrixIntegralSubgroup (R := 𝓞 K) (K := K) 1 v :
          Set (Matrix.GeneralLinearGroup (Fin 1) (v.adicCompletion K)))
        (chapter15FiniteUnitIntegralSubgroup (R := 𝓞 K) (K := K) v :
          Set ((v.adicCompletion K)ˣ)) := by
    intro v g hg
    change Matrix.GeneralLinearGroup.det g ∈
      (chapter15FiniteUnitIntegralSubgroup (R := 𝓞 K) (K := K) v :
        Set ((v.adicCompletion K)ˣ))
    rcases
        (chapter15_finite_integral_matrix_mem_iff
          (R := 𝓞 K) (K := K) 1 (by decide) v g).mp hg with
      ⟨_, u, hu⟩
    exact ⟨u, hu⟩
  have hφinv : ∀ v : Chapter15FinitePlace (𝓞 K),
      MapsTo (e v).symm
        (chapter15FiniteUnitIntegralSubgroup (R := 𝓞 K) (K := K) v :
          Set ((v.adicCompletion K)ˣ))
        (chapter15FiniteMatrixIntegralSubgroup (R := 𝓞 K) (K := K) 1 v :
          Set (Matrix.GeneralLinearGroup (Fin 1) (v.adicCompletion K))) := by
    intro v u hu
    rcases hu with ⟨x, hx⟩
    change Matrix.GeneralLinearGroup.scalar (Fin 1) u ∈
      (chapter15FiniteMatrixIntegralSubgroup (R := 𝓞 K) (K := K) 1 v :
        Set (Matrix.GeneralLinearGroup (Fin 1) (v.adicCompletion K)))
    apply
      (chapter15_finite_integral_matrix_mem_iff
        (R := 𝓞 K) (K := K) 1 (by decide) v
        (Matrix.GeneralLinearGroup.scalar (Fin 1) u)).mpr
    constructor
    · intro i j
      simp [Matrix.GeneralLinearGroup.coe_scalar,
        Unique.eq_default i, Unique.eq_default j, ← hx]
    · refine ⟨x, ?_⟩
      simpa only [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, pow_one] using hx
  let m : Chapter15FiniteMatrixGroup 1 (𝓞 K) K →
      Chapter15FiniteIdeleGroup (𝓞 K) K :=
    RestrictedProduct.map
      (φ := fun v => e v) (Filter.Eventually.of_forall hφ)
  let mInv : Chapter15FiniteIdeleGroup (𝓞 K) K →
      Chapter15FiniteMatrixGroup 1 (𝓞 K) K :=
    RestrictedProduct.map
      (φ := fun v => (e v).symm) (Filter.Eventually.of_forall hφinv)
  have hmleft : Function.LeftInverse mInv m := by
    intro x
    apply Subtype.ext
    funext v
    change (e v).symm ((e v) (x v)) = x v
    exact (e v).symm_apply_apply (x v)
  have hmright : Function.RightInverse mInv m := by
    intro x
    apply Subtype.ext
    funext v
    change (e v) ((e v).symm (x v)) = x v
    exact (e v).apply_symm_apply (x v)
  have hmcont : Continuous m := by
    exact RestrictedProduct.mapAlong_continuous
      (R₁ := fun v : Chapter15FinitePlace (𝓞 K) =>
        Matrix.GeneralLinearGroup (Fin 1) (v.adicCompletion K))
      (R₂ := fun v : Chapter15FinitePlace (𝓞 K) => (v.adicCompletion K)ˣ)
      (A₁ := fun v =>
        (chapter15FiniteMatrixIntegralSubgroup (R := 𝓞 K) (K := K) 1 v :
          Set (Matrix.GeneralLinearGroup (Fin 1) (v.adicCompletion K))))
      (A₂ := fun v =>
        (chapter15FiniteUnitIntegralSubgroup (R := 𝓞 K) (K := K) v :
          Set ((v.adicCompletion K)ˣ)))
      (f := id) Filter.tendsto_id (fun v => e v)
      (Filter.Eventually.of_forall hφ)
      (fun v => (e v).continuous_toFun)
  have hmInvCont : Continuous mInv := by
    exact RestrictedProduct.mapAlong_continuous
      (R₁ := fun v : Chapter15FinitePlace (𝓞 K) => (v.adicCompletion K)ˣ)
      (R₂ := fun v : Chapter15FinitePlace (𝓞 K) =>
        Matrix.GeneralLinearGroup (Fin 1) (v.adicCompletion K))
      (A₁ := fun v =>
        (chapter15FiniteUnitIntegralSubgroup (R := 𝓞 K) (K := K) v :
          Set ((v.adicCompletion K)ˣ)))
      (A₂ := fun v =>
        (chapter15FiniteMatrixIntegralSubgroup (R := 𝓞 K) (K := K) 1 v :
          Set (Matrix.GeneralLinearGroup (Fin 1) (v.adicCompletion K))))
      (f := id) Filter.tendsto_id (fun v => (e v).symm)
      (Filter.Eventually.of_forall hφinv)
      (fun v => (e v).symm.continuous_toFun)
  exact
    { toMulEquiv :=
        { toFun := m
          invFun := mInv
          left_inv := hmleft
          right_inv := hmright
          map_mul' := by
            intro x y
            apply Subtype.ext
            funext v
            change e v (x v * y v) = e v (x v) * e v (y v)
            exact (e v).map_mul _ _ }
      continuous_toFun := hmcont
      continuous_invFun := hmInvCont }

theorem chapter15_rank_one_finite_matrix_group_standard_level_image
    (K : Type*) [Field K] [NumberField K] :
    chapter15_rank_one_finite_matrix_group_recovers_finite_ideles K ''
        (chapter15StandardFiniteMatrixLevel (R := 𝓞 K) (K := K) 1 :
          Set (Chapter15FiniteMatrixGroup 1 (𝓞 K) K)) =
      (chapter15StandardFiniteIdeleLevel (R := 𝓞 K) (K := K) :
        Set (Chapter15FiniteIdeleGroup (𝓞 K) K)) := by
  let f := chapter15_rank_one_finite_matrix_group_recovers_finite_ideles K
  let s := chapter15_rank_one_standard_level_recovers_finite_integral_ideles K
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hs : (s ⟨x, hx⟩).1 ∈
        (chapter15StandardFiniteIdeleLevel (R := 𝓞 K) (K := K) :
          Set (Chapter15FiniteIdeleGroup (𝓞 K) K)) :=
      (s ⟨x, hx⟩).property
    have heq : f x = (s ⟨x, hx⟩).1 := by
      apply Subtype.ext
      funext v
      rfl
    rw [heq]
    exact hs
  · intro hy
    let y' : (chapter15StandardFiniteIdeleLevel (R := 𝓞 K) (K := K) : Type _) :=
      ⟨y, hy⟩
    have hs : (s.symm y').1 ∈
        (chapter15StandardFiniteMatrixLevel (R := 𝓞 K) (K := K) 1 :
          Set (Chapter15FiniteMatrixGroup 1 (𝓞 K) K)) :=
      (s.symm y').property
    have heq : f.symm y = (s.symm y').1 := by
      apply Subtype.ext
      funext v
      rfl
    refine ⟨f.symm y, ?_, f.apply_symm_apply y⟩
    rw [heq]
    exact hs

end

end LastLib.Book04AdelesAndIdeles.Chapter15
