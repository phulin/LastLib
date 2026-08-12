import LastLib.Book04AdelesAndIdeles.Chapter07.Dependencies
import LastLib.Book04AdelesAndIdeles.Chapter07.Section02TheIdeleGroup

namespace LastLib.Book04AdelesAndIdeles.Chapter07

noncomputable section

open Set Filter Topology
open scoped BigOperators DirectSum RestrictedProduct NNReal

/-! # 7.5 Principal ideles -/

/-- The diagonal embedding of the global multiplicative group into the full idele group. -/
def chapter07PrincipalIdeleEmbedding
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    Kˣ →* chapter07IdeleGroup R K :=
  Units.map (algebraMap K (chapter07AdeleRing R K))

/-- The finite diagonal embedding, useful for recording the obstruction to finite density. -/
def chapter07FinitePrincipalIdeleEmbedding
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    Kˣ →* chapter07FiniteIdeleGroup R K :=
  IsDedekindDomain.FiniteAdeleRing.unitEmbedding R K

@[simp]
theorem chapter07PrincipalIdeleEmbedding_apply_infinite
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (a : Kˣ) (v : NumberField.InfinitePlace K) :
    (chapter07PrincipalIdeleEmbedding R K a).1.1 v = algebraMap K (v.Completion) a := by
  rfl

@[simp]
theorem chapter07PrincipalIdeleEmbedding_apply_finite
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (a : Kˣ) (v : chapter07FinitePlace R) :
    (chapter07PrincipalIdeleEmbedding R K a).1.2 v =
      algebraMap K (chapter07LocalField R K v) a := by
  sorry

@[simp]
theorem chapter07FinitePrincipalIdeleEmbedding_apply
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (a : Kˣ) :
    chapter07FinitePrincipalIdeleEmbedding R K a =
      IsDedekindDomain.FiniteAdeleRing.unitEmbedding R K a :=
  rfl

def chapter07PrincipalIdeleSubgroup
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    Subgroup (chapter07IdeleGroup R K) :=
  (chapter07PrincipalIdeleEmbedding R K).range

theorem chapter07_principal_idele_embedding_injective
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K] :
    Function.Injective (chapter07PrincipalIdeleEmbedding R K) := by
  sorry

theorem chapter07_principal_ideles_are_discrete
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K] :
    IsDiscrete (chapter07PrincipalIdeleSubgroup R K :
      Set (chapter07IdeleGroup R K)) := by
  sorry

theorem chapter07_principal_ideles_are_closed
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K] :
    IsClosed (chapter07PrincipalIdeleSubgroup R K :
      Set (chapter07IdeleGroup R K)) := by
  sorry

theorem chapter07_finite_principal_ideles_are_not_dense
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K] :
    ¬ DenseRange (chapter07FinitePrincipalIdeleEmbedding R K) := by
  sorry

theorem chapter07_finite_principal_ideles_have_finite_order_restrictions
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    (a : Kˣ) :
    ∀ᶠ v : chapter07FinitePlace R in cofinite,
      Valued.v ((chapter07FinitePrincipalIdeleEmbedding R K a).1 v) = 1 := by
  sorry

/-- The idele class group `C_K = A_K^× / K^×`. -/
abbrev chapter07IdeleClassGroup
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :=
  chapter07IdeleGroup R K ⧸ chapter07PrincipalIdeleSubgroup R K

def chapter07IdeleClassProjection
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    chapter07IdeleGroup R K →* chapter07IdeleClassGroup R K :=
  QuotientGroup.mk' (chapter07PrincipalIdeleSubgroup R K)

instance chapter07_idele_class_group_is_comm_group
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    CommGroup (chapter07IdeleClassGroup R K) := by
  infer_instance

theorem chapter07_idele_class_group_is_topological_group
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    IsTopologicalGroup (chapter07IdeleClassGroup R K) := by
  sorry

theorem chapter07_idele_class_projection_kernel
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    (chapter07IdeleClassProjection R K).ker =
      chapter07PrincipalIdeleSubgroup R K := by
  sorry

theorem chapter07_idele_class_group_is_locally_compact
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K] :
    LocallyCompactSpace (chapter07IdeleClassGroup R K) := by
  sorry

theorem chapter07_idele_class_group_is_hausdorff
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K] :
    T2Space (chapter07IdeleClassGroup R K) := by
  sorry

/-- The quotient's positive-size witness.  The usual construction is the product of normalized
local absolute values; the product formula makes it trivial on principal ideles. -/
structure Chapter07IdeleClassSizeWitness
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] where
  size : chapter07IdeleClassGroup R K →* ℝ≥0
  continuous_size : Continuous size
  nontrivial : ∃ c : chapter07IdeleClassGroup R K, size c ≠ 1

theorem chapter07_idele_class_group_has_positive_size
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K] :
    Nonempty (Chapter07IdeleClassSizeWitness R K) := by
  sorry

theorem chapter07_idele_class_group_not_compact
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K] :
    ¬ CompactSpace (chapter07IdeleClassGroup R K) := by
  sorry

theorem chapter07_idele_class_group_not_compact_from_positive_size
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    (w : Chapter07IdeleClassSizeWitness R K) :
    ¬ CompactSpace (chapter07IdeleClassGroup R K) := by
  sorry

end

end LastLib.Book04AdelesAndIdeles.Chapter07
