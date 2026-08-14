import LastLib.Book04AdelesAndIdeles.Chapter05.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter05

noncomputable section

open scoped Topology

/-! ## 5.2. Strong approximation in the finite adeles -/

/-! The finite congruence input is the canonical Chapter 1 approximation
statement, expressed through the canonical completion map. -/

theorem chapter05_finite_approximation_hits_congruences
    (K : Type*) [Field K] [NumberField K]
    (S : Finset (Chapter05FinitePlace K))
    (x : ∀ v : Chapter05FinitePlace K, v ∈ S →
      Chapter05FiniteLocalField K v)
    (m : ∀ v : Chapter05FinitePlace K, v ∈ S → ℤ) :
    ∃ a : K,
      (∀ v (hv : v ∈ S),
        LastLib.Book04AdelesAndIdeles.Chapter01.chapter01LocallyClose
          v (x v hv) (chapter05FiniteDiagonal K a v) (m v hv)) ∧
      (∀ q : Chapter05FinitePlace K, q ∉ S →
        0 ≤ LastLib.Book04AdelesAndIdeles.Chapter01.chapter01Order q a) := by
  sorry

/-! Every canonical finite-adelic neighborhood contains a principal adele. -/

theorem chapter05_finite_diagonal_hits_nhds
    (K : Type*) [Field K] [NumberField K]
    (x : Chapter05FiniteAdeleRing K)
    (U : Set (Chapter05FiniteAdeleRing K)) (hU : U ∈ 𝓝 x) :
    ∃ a : K, chapter05FiniteDiagonal K a ∈ U := by
  sorry

/-!
**Theorem 5.1 (strong approximation away from infinity).** The canonical
diagonal image of `K` is dense in the finite adele ring.
-/
theorem chapter05_theorem_5_1_strong_approximation_away_from_infinity
    (K : Type*) [Field K] [NumberField K] :
    DenseRange (chapter05FiniteDiagonal K) := by
  sorry

theorem chapter05_strong_approximation_finite_adeles_closure
    (K : Type*) [Field K] [NumberField K] :
    closure (Set.range (chapter05FiniteDiagonal K)) =
      (Set.univ : Set (Chapter05FiniteAdeleRing K)) := by
  sorry

theorem chapter05_strong_approximation_finite_adeles_iff_nhds
    (K : Type*) [Field K] [NumberField K] :
    DenseRange (chapter05FiniteDiagonal K) ↔
      ∀ (x : Chapter05FiniteAdeleRing K)
        (U : Set (Chapter05FiniteAdeleRing K)), U ∈ 𝓝 x →
          ∃ a : K, chapter05FiniteDiagonal K a ∈ U := by
  sorry

end

end LastLib.Book04AdelesAndIdeles.Chapter05
