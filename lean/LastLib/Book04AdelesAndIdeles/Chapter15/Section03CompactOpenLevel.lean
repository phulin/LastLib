import LastLib.Book04AdelesAndIdeles.Chapter15.Section02DiagonalPointsAndDeterminants

namespace LastLib.Book04AdelesAndIdeles.Chapter15

noncomputable section

open Set Filter NumberField
open scoped RestrictedProduct

/-! ## 15.3. Compact open level -/

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

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

/-- The standard level as a level datum, not just its underlying subgroup. -/
def chapter15StandardFiniteMatrixLevelData (n : ℕ) [NumberField K] :
    Chapter15FiniteMatrixLevel (R := R) (K := K) n where
  localSubgroup := fun v => chapter15FiniteMatrixIntegralSubgroup n v
  subgroup := chapter15StandardFiniteMatrixLevel n
  mem_iff := fun g => Iff.rfl
  isCompact := chapter15_standard_finite_matrix_level_is_compact n
  isOpen := chapter15_standard_finite_matrix_level_is_open n
  standard_outside_finite := by
    refine ⟨∅, ?_⟩
    intro v hv
    simp

/-- The compact-open-level predicate used for arbitrary finite subgroups. -/
def chapter15IsCompactOpenMatrixLevel
    (n : ℕ) (Kf : Subgroup (Chapter15FiniteMatrixGroup n R K)) : Prop :=
  IsCompact (Kf : Set (Chapter15FiniteMatrixGroup n R K)) ∧
    IsOpen (Kf : Set (Chapter15FiniteMatrixGroup n R K))

theorem chapter15FiniteMatrixLevel_is_compact_open
    (n : ℕ) (L : Chapter15FiniteMatrixLevel (R := R) (K := K) n) :
    chapter15IsCompactOpenMatrixLevel n L.subgroup :=
  ⟨L.isCompact, L.isOpen⟩

/-! ### Local reduction and principal congruence subgroups -/

/-- Reduction of integral matrices modulo `𝔭_v^m`. -/
def chapter15LocalMatrixReduction (n : ℕ) (v : Chapter15FinitePlace R) (m : ℕ) :
    Matrix.GeneralLinearGroup (Fin n) (v.adicCompletionIntegers K) →*
      Matrix.GeneralLinearGroup (Fin n)
        ((v.adicCompletionIntegers K) ⧸ (IsLocalRing.maximalIdeal
          (v.adicCompletionIntegers K)) ^ m) :=
  Matrix.GeneralLinearGroup.map
    (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal
      (v.adicCompletionIntegers K)) ^ m))

/-- The local principal congruence subgroup is the kernel of reduction. -/
def chapter15LocalMatrixCongruenceKernel
    (n : ℕ) (v : Chapter15FinitePlace R) (m : ℕ) :
    Subgroup (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletionIntegers K)) :=
  (chapter15LocalMatrixReduction (R := R) (K := K) n v m).ker

/-- The corresponding subgroup inside the field-valued local GL group. -/
def chapter15LocalMatrixCongruenceSubgroup
    (n : ℕ) (v : Chapter15FinitePlace R) (m : ℕ) :
    Subgroup (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K)) :=
  Subgroup.map
    (Matrix.GeneralLinearGroup.map (v.adicCompletionIntegers K).subtype)
    (chapter15LocalMatrixCongruenceKernel (R := R) (K := K) n v m)

theorem chapter15_local_matrix_congruence_mem_iff
    (n : ℕ) (v : Chapter15FinitePlace R) (m : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) (v.adicCompletionIntegers K)) :
    g ∈ chapter15LocalMatrixCongruenceKernel n v m ↔
      chapter15LocalMatrixReduction n v m g = 1 := by
  exact MonoidHom.mem_ker

theorem chapter15_local_matrix_congruence_subgroup_mem_iff
    (n : ℕ) (v : Chapter15FinitePlace R) (m : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K)) :
    g ∈ chapter15LocalMatrixCongruenceSubgroup n v m ↔
      ∃ h : Matrix.GeneralLinearGroup (Fin n) (v.adicCompletionIntegers K),
        h ∈ chapter15LocalMatrixCongruenceKernel n v m ∧
          Matrix.GeneralLinearGroup.map
              (v.adicCompletionIntegers K).subtype h = g := by
  sorry

theorem chapter15_local_matrix_congruence_subgroup_entries_iff
    (n : ℕ) (v : Chapter15FinitePlace R) (m : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K)) :
    g ∈ chapter15LocalMatrixCongruenceSubgroup n v m ↔
      ∃ h : Matrix.GeneralLinearGroup (Fin n) (v.adicCompletionIntegers K),
        Matrix.GeneralLinearGroup.map
              (v.adicCompletionIntegers K).subtype h = g ∧
        ∀ i j : Fin n,
          (h i j - if i = j then 1 else 0) ∈
            (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ m := by
  sorry

/-- Reduction of integral units modulo `𝔭_v^m`. -/
def chapter15LocalUnitReduction (v : Chapter15FinitePlace R) (m : ℕ) :
    (v.adicCompletionIntegers K)ˣ →*
      ((v.adicCompletionIntegers K) ⧸ (IsLocalRing.maximalIdeal
        (v.adicCompletionIntegers K)) ^ m)ˣ :=
  Units.map
    (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal
      (v.adicCompletionIntegers K)) ^ m)).toMonoidHom

/-- The local principal unit congruence subgroup is the kernel of unit reduction. -/
def chapter15LocalUnitCongruenceKernel (v : Chapter15FinitePlace R) (m : ℕ) :
    Subgroup (v.adicCompletionIntegers K)ˣ :=
  (chapter15LocalUnitReduction (R := R) (K := K) v m).ker

/-- The corresponding principal congruence subgroup in the local field units. -/
def chapter15LocalFieldUnitCongruenceSubgroup
    (v : Chapter15FinitePlace R) (m : ℕ) : Subgroup ((v.adicCompletion K)ˣ) :=
  Subgroup.map (Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom)
    (chapter15LocalUnitCongruenceKernel (R := R) (K := K) v m)

theorem chapter15_local_unit_congruence_mem_iff
    (v : Chapter15FinitePlace R) (m : ℕ)
    (u : (v.adicCompletionIntegers K)ˣ) :
    u ∈ chapter15LocalUnitCongruenceKernel v m ↔
      chapter15LocalUnitReduction v m u = 1 := by
  exact MonoidHom.mem_ker

theorem chapter15_local_field_unit_congruence_subgroup_mem_iff
    (v : Chapter15FinitePlace R) (m : ℕ) (u : (v.adicCompletion K)ˣ) :
    u ∈ chapter15LocalFieldUnitCongruenceSubgroup v m ↔
      ∃ w : (v.adicCompletionIntegers K)ˣ,
        w ∈ chapter15LocalUnitCongruenceKernel v m ∧
          Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom w = u := by
  sorry

theorem chapter15_local_field_unit_congruence_subgroup_mem_iff_entries
    (v : Chapter15FinitePlace R) (m : ℕ) (u : (v.adicCompletion K)ˣ) :
    u ∈ chapter15LocalFieldUnitCongruenceSubgroup v m ↔
      ∃ w : (v.adicCompletionIntegers K)ˣ,
        Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom w = u ∧
          (w : v.adicCompletionIntegers K) - 1 ∈
            (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ m := by
  sorry

/-! ### The finite targets and compact-open consequences -/

theorem chapter15_local_matrix_reduction_target_finite
    (n : ℕ) (v : Chapter15FinitePlace R) (m : ℕ)
    [Finite ((v.adicCompletionIntegers K) ⧸
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ m)] :
    Finite (Matrix.GeneralLinearGroup (Fin n)
      ((v.adicCompletionIntegers K) ⧸
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ m)) := by
  infer_instance

theorem chapter15_local_unit_reduction_target_finite
    (v : Chapter15FinitePlace R) (m : ℕ)
    [Finite ((v.adicCompletionIntegers K) ⧸
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ m)] :
    Finite (((v.adicCompletionIntegers K) ⧸
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ m)ˣ) := by
  infer_instance

theorem chapter15_local_matrix_congruence_is_compact_open
    (n : ℕ) [NumberField K] (v : Chapter15FinitePlace R) (m : ℕ)
    [Finite ((v.adicCompletionIntegers K) ⧸
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ m)] :
    IsCompact
        (chapter15LocalMatrixCongruenceSubgroup (R := R) (K := K) n v m :
          Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K))) ∧
      IsOpen
        (chapter15LocalMatrixCongruenceSubgroup (R := R) (K := K) n v m :
          Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K))) := by
  sorry

theorem chapter15_local_field_unit_congruence_is_compact_open
    [NumberField K] (v : Chapter15FinitePlace R) (m : ℕ)
    [Finite ((v.adicCompletionIntegers K) ⧸
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ m)] :
    IsCompact
        (chapter15LocalFieldUnitCongruenceSubgroup (R := R) (K := K) v m :
          Set ((v.adicCompletion K)ˣ)) ∧
      IsOpen
        (chapter15LocalFieldUnitCongruenceSubgroup (R := R) (K := K) v m :
          Set ((v.adicCompletion K)ˣ)) := by
  sorry

/-! ### A principal congruence level at finitely many places -/

def chapter15PrincipalCongruenceLocalMatrixLevel
    (n : ℕ) (S : Finset (Chapter15FinitePlace R))
    (m : Chapter15FinitePlace R → ℕ) (v : Chapter15FinitePlace R) :
    Subgroup (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K)) := by
  classical
  by_cases hv : v ∈ S
  · exact chapter15LocalMatrixCongruenceSubgroup n v (m v)
  · exact chapter15FiniteMatrixIntegralSubgroup n v

def chapter15PrincipalCongruenceLocalUnitLevel
    (S : Finset (Chapter15FinitePlace R))
    (m : Chapter15FinitePlace R → ℕ) (v : Chapter15FinitePlace R) :
    Subgroup ((v.adicCompletion K)ˣ) := by
  classical
  by_cases hv : v ∈ S
  · exact chapter15LocalFieldUnitCongruenceSubgroup v (m v)
  · exact chapter15FiniteUnitIntegralSubgroup v

/- The exponent-zero and one-prime specializations are useful API bridges. -/
theorem chapter15_principal_congruence_local_matrix_level_outside_support
    (n : ℕ) (S : Finset (Chapter15FinitePlace R))
    (m : Chapter15FinitePlace R → ℕ) {v : Chapter15FinitePlace R} (hv : v ∉ S) :
    chapter15PrincipalCongruenceLocalMatrixLevel (R := R) (K := K) n S m v =
      chapter15FiniteMatrixIntegralSubgroup (R := R) (K := K) n v := by
  classical
  simp [chapter15PrincipalCongruenceLocalMatrixLevel, hv]

theorem chapter15_principal_congruence_local_unit_level_outside_support
    (S : Finset (Chapter15FinitePlace R))
    (m : Chapter15FinitePlace R → ℕ) {v : Chapter15FinitePlace R} (hv : v ∉ S) :
    chapter15PrincipalCongruenceLocalUnitLevel (R := R) (K := K) S m v =
      chapter15FiniteUnitIntegralSubgroup (R := R) (K := K) v := by
  classical
  simp [chapter15PrincipalCongruenceLocalUnitLevel, hv]

def chapter15PrincipalCongruenceMatrixLevelData
    (n : ℕ) [NumberField K] (S : Finset (Chapter15FinitePlace R))
    (m : Chapter15FinitePlace R → ℕ) :
    Chapter15FiniteMatrixLevel (R := R) (K := K) n where
  localSubgroup := chapter15PrincipalCongruenceLocalMatrixLevel n S m
  subgroup := by
    sorry
  mem_iff := by
    sorry
  isCompact := by
    sorry
  isOpen := by
    sorry
  standard_outside_finite := by
    refine ⟨S, ?_⟩
    intro v hv
    exact chapter15_principal_congruence_local_matrix_level_outside_support
      n S m hv

/-! ### Upper-triangular reduction levels -/

def chapter15UpperTriangularSubgroup (n : ℕ) (S : Type*) [Ring S] :
    Subgroup (Matrix.GeneralLinearGroup (Fin n) S) where
  carrier := {g | ∀ i j : Fin n, j < i → g i j = 0}
  one_mem' := by sorry
  mul_mem' := by
    intro g h hg hh i j hij
    sorry
  inv_mem' := by
    intro g hg i j hij
    sorry

def chapter15LocalUpperTriangularMatrixLevel
    (n : ℕ) (v : Chapter15FinitePlace R) :
    Subgroup (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K)) :=
  Subgroup.map
    (Matrix.GeneralLinearGroup.map (v.adicCompletionIntegers K).subtype)
    ((chapter15UpperTriangularSubgroup n
      ((v.adicCompletionIntegers K) ⧸ (IsLocalRing.maximalIdeal
        (v.adicCompletionIntegers K)) ^ 1)).comap
      (chapter15LocalMatrixReduction (R := R) (K := K) n v 1))

def chapter15UpperTriangularFiniteMatrixLevelData
    (n : ℕ) [NumberField K] (S : Finset (Chapter15FinitePlace R)) :
    Chapter15FiniteMatrixLevel (R := R) (K := K) n where
  localSubgroup := fun v => by
    classical
    by_cases hv : v ∈ S
    · exact chapter15LocalUpperTriangularMatrixLevel n v
    · exact chapter15FiniteMatrixIntegralSubgroup n v
  subgroup := by
    sorry
  mem_iff := by
    sorry
  isCompact := by
    sorry
  isOpen := by
    sorry
  standard_outside_finite := by
    refine ⟨S, ?_⟩
    intro v hv
    simp [hv]

/-! ### Level refinement -/

def chapter15LevelRefines {n : ℕ}
    (L₁ L₂ : Chapter15FiniteMatrixLevel (R := R) (K := K) n) : Prop :=
  L₁.subgroup ≤ L₂.subgroup

theorem chapter15_level_refines_iff_forgets_local_information
    {n : ℕ} (L₁ L₂ : Chapter15FiniteMatrixLevel (R := R) (K := K) n)
    (h : chapter15LevelRefines L₁ L₂) :
    ∀ g, g ∈ L₁.subgroup → g ∈ L₂.subgroup := by
  exact h

/- The right quotient at a larger level is therefore a coarser quotient; the
actual quotient map is constructed after the double-coset type in §15.4. -/

end

end LastLib.Book04AdelesAndIdeles.Chapter15
