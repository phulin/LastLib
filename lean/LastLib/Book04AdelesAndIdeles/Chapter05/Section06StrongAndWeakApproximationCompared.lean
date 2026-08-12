import LastLib.Book04AdelesAndIdeles.Chapter05.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter05

noncomputable section

open scoped Topology

universe u v w z

/-! ## 5.6. Strong and weak approximation compared -/

variable {K : Type u} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
variable {V : Type v} {Kv : V → Type w}
variable [∀ v, Field (Kv v)] [∀ v, TopologicalSpace (Kv v)]
variable {P : Chapter05PlaceSystem K V Kv}

theorem chapter05_away_complement_is_finite_place
    (S : Set V) (hSinf : P.archimedean ⊆ S) :
    ∀ v : V, v ∉ S → v ∈ P.finite := by
  sorry

/-! For a finite set `S` containing all archimedean places, the following is
    the restricted product in the source's notation
    `A_K^S = ∏'_{v ∉ S} (K_v, O_v)`. -/

/-!
**Strong approximation with the archimedean places omitted.** If `S` is
finite and contains every archimedean place, then the diagonal is dense in
the restricted product away from `S`.
-/
theorem chapter05_theorem_5_6_strong_approximation_away_from_S
    (S : Set V) (hSfinite : S.Finite) (hSinf : P.archimedean ⊆ S) :
    chapter05StrongApproximationAwayFrom P S := by
  sorry

theorem chapter05_strong_approximation_away_neighborhood_form
    (S : Set V)
    (hstrong : chapter05StrongApproximationAwayFrom P S) :
    ∀ (T : Finset {v // v ∉ S})
      (x : ∀ v : T, Kv v.1) (W : ∀ v : T, Set (Kv v.1)),
      (∀ v : T, W v ∈ 𝓝 (0 : Kv v.1)) →
        ∃ a : K,
          (∀ v : T, P.completionMap v.1 a - x v ∈ W v) ∧
          (∀ v : V, v ∉ S → v ∉ chapter05FinsetSubtypeCoe T →
            P.completionMap v a ∈ P.integral v) := by
  exact hstrong

theorem chapter05_away_diagonal_dense
    (S : Set V) (hSfinite : S.Finite) (hSinf : P.archimedean ⊆ S)
    [TopologicalSpace (chapter05AdeleAwayFrom P S)]
    (hbasis : chapter05RestrictedProductBasis P S)
    (hstrong : chapter05StrongApproximationAwayFrom P S) :
    DenseRange (chapter05AwayDiagonal P S hSinf) := by
  sorry

theorem chapter05_away_diagonal_closure_eq_univ
    (S : Set V) (hSfinite : S.Finite) (hSinf : P.archimedean ⊆ S)
    [TopologicalSpace (chapter05AdeleAwayFrom P S)]
    (hbasis : chapter05RestrictedProductBasis P S)
    (hstrong : chapter05StrongApproximationAwayFrom P S) :
    closure (Set.range (chapter05AwayDiagonal P S hSinf)) =
      (Set.univ : Set (chapter05AdeleAwayFrom P S)) := by
  sorry

/-! The projection from the finite restricted product is the coordinate
    restriction in the canonical carrier. -/

theorem chapter05_finite_to_away_projection_coordinate
    (S : Set V) (hfinite : ∀ v, v ∉ S → v ∈ P.finite)
    (x : chapter05FiniteAdeleCarrier P)
    (v : {v // v ∉ S}) :
    (chapter05FiniteToAwayProjection P S hfinite x).1 v =
      x.1 ⟨v.1, hfinite v.1 v.2⟩ := by
  rfl

/-! With no places omitted, the target is the full adele group.  The
    discreteness result from §5.3 therefore prevents density as soon as the
    full adele group is nondiscrete. -/

variable {A_f : Type z} {A : Type (max u z)}
variable [CommRing A_f] [CommRing A]
variable [TopologicalSpace A_f] [TopologicalSpace A]
variable [IsTopologicalAddGroup A]
variable (M : Chapter05AdeleModel P A_f A)

theorem chapter05_full_adele_diagonal_not_dense
    [T2Space A]
    (Uinf : Set (chapter05MinkowskiSpace P))
    (hUinfOpen : IsOpen Uinf)
    (hUinfNhds : Uinf ∈ 𝓝 (0 : chapter05MinkowskiSpace P))
    (hUinf : Uinf ∩ (M.integerLattice.carrier : Set (chapter05MinkowskiSpace P)) =
      {0})
    (hnondiscrete : chapter05NondiscreteAtZero (G := A)) :
    ¬ DenseRange M.fullDiagonal := by
  sorry

theorem chapter05_strong_approximation_with_no_omitted_places_is_false
    [T2Space A]
    (Uinf : Set (chapter05MinkowskiSpace P))
    (hUinfOpen : IsOpen Uinf)
    (hUinfNhds : Uinf ∈ 𝓝 (0 : chapter05MinkowskiSpace P))
    (hUinf : Uinf ∩ (M.integerLattice.carrier : Set (chapter05MinkowskiSpace P)) =
      {0})
    (hnondiscrete : chapter05NondiscreteAtZero (G := A)) :
    ¬ DenseRange M.fullDiagonal := by
  exact chapter05_full_adele_diagonal_not_dense M Uinf hUinfOpen hUinfNhds hUinf hnondiscrete

end

end LastLib.Book04AdelesAndIdeles.Chapter05
