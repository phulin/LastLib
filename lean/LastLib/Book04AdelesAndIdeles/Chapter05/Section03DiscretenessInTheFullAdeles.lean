import LastLib.Book04AdelesAndIdeles.Chapter05.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter05

noncomputable section

open scoped Topology

universe u v w z

/-! ## 5.3. Discreteness in the full adeles -/

variable {K : Type u} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
variable {V : Type v} {Kv : V → Type w}
variable [∀ v, Field (Kv v)] [∀ v, TopologicalSpace (Kv v)]
variable {A_f : Type z} {A : Type (max u z)}
variable [CommRing A_f] [CommRing A]
variable [TopologicalSpace A_f] [TopologicalSpace A]
variable [IsTopologicalAddGroup A]
variable {P : Chapter05PlaceSystem K V Kv}

variable (M : Chapter05AdeleModel P A_f A)

theorem chapter05_finite_integral_is_compact_open :
    IsCompact (M.finiteIntegral : Set A_f) ∧
      IsOpen (M.finiteIntegral : Set A_f) := by
  exact ⟨M.finite_integral_compact, M.finite_integral_open⟩

theorem chapter05_exists_small_archimedean_neighborhood :
    ∃ Uinf : Set (chapter05MinkowskiSpace P),
      IsOpen Uinf ∧ Uinf ∈ 𝓝 (0 : chapter05MinkowskiSpace P) ∧
        Uinf ∩ (M.integerLattice.carrier : Set (chapter05MinkowskiSpace P)) =
          {0} := by
  sorry

theorem chapter05_full_zero_neighborhood_is_open
    (Uinf : Set (chapter05MinkowskiSpace P)) (hUinf : IsOpen Uinf) :
    IsOpen (chapter05FullZeroNeighborhood M Uinf) := by
  sorry

theorem chapter05_full_zero_neighborhood_is_nhds
    (Uinf : Set (chapter05MinkowskiSpace P))
    (hUinf : Uinf ∈ 𝓝 (0 : chapter05MinkowskiSpace P)) :
    chapter05FullZeroNeighborhood M Uinf ∈ 𝓝 (0 : A) := by
  sorry

theorem chapter05_full_zero_neighborhood_meets_diagonal_only_at_zero
    (Uinf : Set (chapter05MinkowskiSpace P))
    (hUinf : Uinf ∩ (M.integerLattice.carrier : Set (chapter05MinkowskiSpace P)) =
      {0}) :
    chapter05FullZeroNeighborhood M Uinf ∩ Set.range M.fullDiagonal =
      ({0} : Set A) := by
  sorry

/-!
**Theorem 5.2.** The diagonal copy of `K` is a discrete subgroup of the full
adele additive group.
-/
theorem chapter05_theorem_5_2_diagonal_is_discrete
    (Uinf : Set (chapter05MinkowskiSpace P))
    (hUinfOpen : IsOpen Uinf)
    (hUinfNhds : Uinf ∈ 𝓝 (0 : chapter05MinkowskiSpace P))
    (hUinf : Uinf ∩ (M.integerLattice.carrier : Set (chapter05MinkowskiSpace P)) =
      {0}) :
    chapter05IsDiscreteSubset (Set.range M.fullDiagonal) := by
  sorry

theorem chapter05_diagonal_full_is_closed
    [T2Space A]
    (hdisc : chapter05IsDiscreteSubset (Set.range M.fullDiagonal)) :
    IsClosed (Set.range M.fullDiagonal) := by
  sorry

theorem chapter05_theorem_5_2_diagonal_is_discrete_closed
    [T2Space A]
    (Uinf : Set (chapter05MinkowskiSpace P))
    (hUinfOpen : IsOpen Uinf)
    (hUinfNhds : Uinf ∈ 𝓝 (0 : chapter05MinkowskiSpace P))
    (hUinf : Uinf ∩ (M.integerLattice.carrier : Set (chapter05MinkowskiSpace P)) =
      {0}) :
    chapter05IsDiscreteSubset (Set.range M.fullDiagonal) ∧
      IsClosed (Set.range M.fullDiagonal) := by
  constructor
  · exact chapter05_theorem_5_2_diagonal_is_discrete M Uinf hUinfOpen hUinfNhds hUinf
  · exact chapter05_diagonal_full_is_closed M
      (chapter05_theorem_5_2_diagonal_is_discrete M Uinf hUinfOpen hUinfNhds hUinf)

theorem chapter05_finite_integral_preimage_of_diagonal :
    (M.finiteDiagonal ⁻¹' (M.finiteIntegral : Set A_f)) =
      (P.integerRing : Set K) := by
  ext a
  exact M.finite_integrality_iff a

theorem chapter05_finite_integral_intersection_eq_integer_image :
    Set.range M.finiteDiagonal ∩ (M.finiteIntegral : Set A_f) =
      M.finiteDiagonal '' (P.integerRing : Set K) := by
  sorry

theorem chapter05_finite_integral_intersection_is_infinite :
    Set.Infinite
      (Set.range M.finiteDiagonal ∩ (M.finiteIntegral : Set A_f)) := by
  sorry

/-! The last theorem is the finite-place warning from the source: the compact
    open finite integral neighborhood meets the diagonal in all global
    integers, so it cannot isolate zero. -/
theorem chapter05_finite_zero_neighborhood_meets_diagonal_in_integers :
    Set.range M.finiteDiagonal ∩ chapter05FiniteZeroNeighborhood M =
      M.finiteDiagonal '' (P.integerRing : Set K) ∧
      Set.Infinite
        (Set.range M.finiteDiagonal ∩ chapter05FiniteZeroNeighborhood M) := by
  constructor
  · exact chapter05_finite_integral_intersection_eq_integer_image M
  · exact chapter05_finite_integral_intersection_is_infinite M

end

end LastLib.Book04AdelesAndIdeles.Chapter05
