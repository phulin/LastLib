import LastLib.Book04AdelesAndIdeles.Chapter05.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter05

noncomputable section

open scoped Topology

universe u v w z

/-! ## 5.2. Strong approximation in the finite adeles -/

variable {K : Type u} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
variable {V : Type v} {Kv : V → Type w}
variable [∀ v, Field (Kv v)] [∀ v, TopologicalSpace (Kv v)]
variable {A_f : Type z} {A : Type (max u z)}
variable [CommRing A_f] [CommRing A]
variable [TopologicalSpace A_f] [TopologicalSpace A]
variable [IsTopologicalAddGroup A]
variable {P : Chapter05PlaceSystem K V Kv}

variable (M : Chapter05AdeleModel P A_f A)

/-- The finite congruence form of the approximation input. -/
theorem chapter05_finite_approximation_hits_congruences
    (S : Finset {v // v ∈ P.finite})
    (x : ∀ v : S, Kv v.1) (m : S → ℤ) :
    ∃ a : K,
      (∀ v : S,
        P.completionMap v.1 a - x v ∈ P.precision v.1 (m v)) ∧
      (∀ v : V, v ∈ P.finite → v ∉ chapter05FinsetSubtypeCoe S →
        P.completionMap v a ∈ P.integral v) := by
  exact P.finite_approximation S x m

/-- Every basic finite-adelic neighborhood of a target contains a diagonal
    global element.  The coordinate-basis field is the Chapter 4 topology
    bridge; the arithmetic part is `finite_approximation`. -/
theorem chapter05_finite_diagonal_hits_nhds
    (x : A_f) (U : Set A_f) (hU : U ∈ 𝓝 x) :
    ∃ a : K, M.finiteDiagonal a ∈ U := by
  sorry

/-!
**Theorem 5.1 (strong approximation away from infinity).** The diagonal
image of `K` is dense in the finite adele ring.
-/
theorem chapter05_theorem_5_1_strong_approximation_away_from_infinity :
    DenseRange M.finiteDiagonal := by
  sorry

theorem chapter05_strong_approximation_finite_adeles_closure :
    closure (Set.range M.finiteDiagonal) = (Set.univ : Set A_f) := by
  sorry

theorem chapter05_strong_approximation_finite_adeles_iff_nhds :
    DenseRange M.finiteDiagonal ↔
      ∀ (x : A_f) (U : Set A_f), U ∈ 𝓝 x →
        ∃ a : K, M.finiteDiagonal a ∈ U := by
  sorry

end

end LastLib.Book04AdelesAndIdeles.Chapter05
