import LastLib.Book04AdelesAndIdeles.Chapter05.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter05

noncomputable section

open Filter
open scoped Topology

universe u v w z

/-! ## 5.1. The diagonal embedding -/

variable {K : Type u} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
variable {V : Type v} {Kv : V → Type w}
variable [∀ v, Field (Kv v)] [∀ v, TopologicalSpace (Kv v)]
variable {A_f : Type z} {A : Type (max u z)}
variable [CommRing A_f] [CommRing A]
variable [TopologicalSpace A_f] [TopologicalSpace A]
variable [IsTopologicalAddGroup A]
variable {P : Chapter05PlaceSystem K V Kv}

variable (M : Chapter05AdeleModel P A_f A)

/-- The diagonal ring homomorphism `K → A_K`. -/
def chapter05Diagonal : K →+* A :=
  M.fullDiagonal

/-- The finite diagonal ring homomorphism `K → A_{K,f}`. -/
def chapter05FiniteDiagonal : K →+* A_f :=
  M.finiteDiagonal

@[simp]
theorem chapter05Diagonal_apply (a : K) :
    chapter05Diagonal M a = M.fullDiagonal a :=
  rfl

@[simp]
theorem chapter05FiniteDiagonal_apply (a : K) :
    chapter05FiniteDiagonal M a = M.finiteDiagonal a :=
  rfl

theorem chapter05_diagonal_injective :
    Function.Injective (chapter05Diagonal M) := by
  exact M.fullDiagonal_injective

theorem chapter05_finite_diagonal_injective :
    Function.Injective (chapter05FiniteDiagonal M) := by
  exact M.finiteDiagonal_injective

theorem chapter05_completion_map_injective (v : V) :
    Function.Injective (P.completionMap v) := by
  exact P.completionMap_injective v

theorem chapter05_diagonal_components
    (a : K) :
    M.decomposition (chapter05Diagonal M a) =
      (chapter05ArchimedeanDiagonal P a, chapter05FiniteDiagonal M a) := by
  exact M.decomposition_diagonal a

/- The following is the precise form of “at almost every finite place a is a
   unit or zero”: zero is allowed at every place, while the nonzero components
   are local units off a finite set. -/
theorem chapter05_diagonal_is_integral_at_almost_all_finite_places
    (a : K) :
    ({v | v ∈ P.finite ∧
      P.completionMap v a ∉ P.integral v} : Set V).Finite := by
  exact P.global_integrality a

theorem chapter05_diagonal_is_unit_or_zero_at_almost_all_finite_places
    (a : K) :
    ({v | v ∈ P.finite ∧ P.completionMap v a ≠ 0 ∧
      P.completionMap v a ∉ P.unit v} : Set V).Finite := by
  exact P.global_unit_or_zero_tail a

theorem chapter05_unit_or_zero_component_is_integral
    (a : K) (v : V) (h : P.completionMap v a = 0 ∨
      P.completionMap v a ∈ P.unit v) :
    P.completionMap v a ∈ P.integral v := by
  rcases h with hzero | hunit
  · simp [hzero]
  · exact P.unit_subset_integral v hunit

theorem chapter05_diagonal_integrality_iff
    (a : K) :
    a ∈ P.integerRing ↔
      ∀ v : V, v ∈ P.finite →
        P.completionMap v a ∈ P.integral v := by
  exact P.integer_global_iff a

/-! A proper subset of the archimedean coordinates may fail to control a
    global unit.  The witness is parameterized by the normalized local sizes,
    since the preceding places chapter owns their construction. -/

structure Chapter05UnitEscapeWitness
    (P : Chapter05PlaceSystem K V Kv) where
  unit : K
  unit_ne_zero : unit ≠ 0
  unit_mem_integer : unit ∈ P.integerRing
  inverse_mem_integer : unit⁻¹ ∈ P.integerRing
  shrinkingPlace : {v // v ∈ P.archimedean}
  growingPlace : {v // v ∈ P.archimedean}
  size : ∀ v : {v // v ∈ P.archimedean}, Kv v.1 → ℝ
  size_nonnegative :
    ∀ (v : {v // v ∈ P.archimedean}) (x : Kv v.1), 0 ≤ size v x
  size_one : ∀ (v : {v // v ∈ P.archimedean}), size v 1 = 1
  size_mul :
    ∀ (v : {v // v ∈ P.archimedean}) (x y : Kv v.1),
      size v (x * y) = size v x * size v y
  shrinking :
    Tendsto
      (fun n : ℕ => size shrinkingPlace
        (P.completionMap shrinkingPlace.1 (unit ^ n)))
      atTop (𝓝 0)
  growing :
    Tendsto
      (fun n : ℕ => size growingPlace
        (P.completionMap growingPlace.1 (unit ^ n)))
      atTop atTop

def chapter05PartialArchimedeanControlWarning
    (T : Finset {v // v ∈ P.archimedean}) : Prop :=
  by
    classical
    exact ∃ w : Chapter05UnitEscapeWitness P,
      w.shrinkingPlace ∉ T ∧ w.growingPlace ∉ T

/-! The two diagonal copies are identified with their ranges.  These range
    declarations are useful to later quotient and closure statements. -/

def chapter05DiagonalImage : Set A :=
  Set.range (chapter05Diagonal M)

def chapter05FiniteDiagonalImage : Set A_f :=
  Set.range (chapter05FiniteDiagonal M)

theorem chapter05_diagonal_image_mem_iff (x : A) :
    x ∈ chapter05DiagonalImage M ↔ ∃ a : K, chapter05Diagonal M a = x := by
  rfl

theorem chapter05_finite_diagonal_image_mem_iff (x : A_f) :
    x ∈ chapter05FiniteDiagonalImage M ↔
      ∃ a : K, chapter05FiniteDiagonal M a = x := by
  rfl

theorem chapter05_diagonal_image_eq_subgroup_carrier :
    chapter05DiagonalImage M =
      (chapter05FullDiagonalSubgroup M : Set A) := by
  rfl

theorem chapter05_finite_diagonal_image_eq_subgroup_carrier :
    chapter05FiniteDiagonalImage M =
      (chapter05FiniteDiagonalSubgroup M : Set A_f) := by
  rfl

end

end LastLib.Book04AdelesAndIdeles.Chapter05
