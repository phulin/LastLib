import LastLib.Book04AdelesAndIdeles.Chapter15.Dependencies

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
  carrier := {g | g.2 ∈ Kf}
  one_mem' := Kf.one_mem
  mul_mem' := by
    intro g h hg hh
    simpa using Kf.mul_mem hg hh
  inv_mem' := by
    intro g hg
    simpa using Kf.inv_mem hg

theorem chapter15_global_level_subgroup_mem_iff
    (n : ℕ) (Kf : Subgroup (Chapter15FiniteMatrixGroup n R K))
    (g : Chapter15GLnAdeles n R K) :
    g ∈ chapter15GlobalLevelSubgroup n Kf ↔ g.2 ∈ Kf :=
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

theorem chapter15_raw_matrix_is_adelic_iff_entries_and_inverse_adelic
    (n : ℕ) [NumberField K]
    (g : (p : Chapter15Place R K) →
      Matrix.GeneralLinearGroup (Fin n) (chapter15LocalRing p)) :
    chapter15RawMatrixIsAdelic n g ↔ chapter15RawMatrixEntriesAreAdelic n g := by
  sorry

theorem chapter15_restricted_matrix_group_tail
    (n : ℕ) [NumberField K]
    (g : Chapter15RestrictedAdelicMatrixGroup n R K) :
    chapter15RawMatrixEntriesAreAdelic n (fun p => g p) := by
  sorry

/-! ### The local integral model -/

theorem chapter15_finite_integral_matrix_mem_iff
    (n : ℕ) (hn : 0 < n) (v : Chapter15FinitePlace R)
    (g : Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K)) :
    g ∈ chapter15FiniteMatrixIntegralSubgroup n v ↔
      (∀ i j : Fin n, g i j ∈ v.adicCompletionIntegers K) ∧
      ∃ u : (v.adicCompletionIntegers K)ˣ,
        Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom u =
          Matrix.GeneralLinearGroup.det g := by
  sorry

theorem chapter15_finite_integral_matrix_group_is_closed
    (n : ℕ) (v : Chapter15FinitePlace R) :
    IsClosed
      (chapter15FiniteMatrixIntegralSubgroup (R := R) (K := K) n v :
        Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K))) := by
  sorry

theorem chapter15_finite_integral_matrix_group_is_compact
    (n : ℕ) [NumberField K] (v : Chapter15FinitePlace R) :
    IsCompact
      (chapter15FiniteMatrixIntegralSubgroup (R := R) (K := K) n v :
        Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K))) := by
  sorry

theorem chapter15_finite_integral_matrix_group_is_open
    (n : ℕ) (v : Chapter15FinitePlace R) :
    IsOpen
      (chapter15FiniteMatrixIntegralSubgroup (R := R) (K := K) n v :
        Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K))) := by
  sorry

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
    (n : ℕ) [NumberField K] :
    IsCompact
      (chapter15StandardFiniteMatrixLevel (R := R) (K := K) n :
        Set (Chapter15FiniteMatrixGroup n R K)) := by
  sorry

theorem chapter15_standard_finite_matrix_level_is_open
    (n : ℕ) :
    IsOpen
      (chapter15StandardFiniteMatrixLevel (R := R) (K := K) n :
        Set (Chapter15FiniteMatrixGroup n R K)) := by
  sorry

/-! ### Local compactness and rank one -/

theorem chapter15_adelic_matrix_group_is_locally_compact
    (n : ℕ) [NumberField K] :
    LocallyCompactSpace (Chapter15GLnAdeles n R K) := by
  sorry

theorem chapter15_adelic_matrix_group_is_locally_compact_of_ring_of_integers
    (n : ℕ) [NumberField K] :
    LocallyCompactSpace (Chapter15GLnAdeles n (𝓞 K) K) := by
  sorry

def chapter15_rank_one_local_gl_is_multiplicative_group
    (A : Type*) [CommRing A] :
    Matrix.GeneralLinearGroup (Fin 1) A ≃* Aˣ := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: this is the book-facing rank-one identification of
the restricted matrix construction with the graph-topologized idele group. -/
def chapter15_rank_one_recovers_ideles
    [NumberField K] :
    Chapter15GLnAdeles 1 R K ≃* Chapter15IdeleGroup R K := by
  sorry

/- The same identification on the finite standard level. -/
def chapter15_rank_one_standard_level_recovers_finite_integral_ideles
    [NumberField K] :
    (chapter15StandardFiniteMatrixLevel (R := R) (K := K) 1 : Type _) ≃*
      Chapter15FiniteIdeleGroup R K := by
  sorry

end

end LastLib.Book04AdelesAndIdeles.Chapter15
