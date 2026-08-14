import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13.Dependencies
import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13.Section02TheWeightedLaplacianIdentity

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13

noncomputable section

open AlgebraicGeometry CategoryTheory Set
open scoped BigOperators Matrix

/-! ## 13.3. Negativity and its exact kernel -/

/- The standard connected-fibers theorem belongs to the earlier relative-surface
chapters.  This certificate therefore packages only its graph-connectedness
conclusion; unused proposition-valued metadata would not express hypotheses or
provide a proof route. -/
structure Chapter13ConnectedFibersCertificate
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)) where
  connectedFibers : chapter13GraphConnected T

theorem chapter13_graph_connected_of_connected_fibers_certificate
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    {T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)}
    (C : Chapter13ConnectedFibersCertificate T) :
    chapter13GraphConnected T := by
  exact C.connectedFibers

theorem chapter13_vertical_self_intersection_eq_zero_iff_constant_potential
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (hconn : chapter13GraphConnected T)
    (a : Fin T.r → ℚ) :
    chapter13VerticalSelfIntersection T a = 0 ↔
      ∃ c : ℚ, ∀ i, chapter13WeightedPotential T a i = c := by
  constructor
  · intro hzero
    have hedge :=
      (chapter13_vertical_self_intersection_eq_zero_iff_edge_potentials_equal
        T a).mp hzero
    let i₀ : Fin T.r := ⟨0, T.nonempty⟩
    refine ⟨chapter13WeightedPotential T a i₀, ?_⟩
    intro i
    have hconstant : ∀ {u : Fin T.r},
        Relation.ReflTransGen (chapter13Adjacency T) u i →
          chapter13WeightedPotential T a u =
            chapter13WeightedPotential T a i := by
      intro u hpath
      induction hpath using Relation.ReflTransGen.head_induction_on with
      | refl => rfl
      | head hstep hrest ih =>
          exact (hedge _ _ hstep.1 hstep.2).trans ih
    exact (hconstant (hconn i₀ i)).symm
  · rintro ⟨c, hc⟩
    apply
      (chapter13_vertical_self_intersection_eq_zero_iff_edge_potentials_equal
        T a).mpr
    intro i j hij hmeet
    rw [hc i, hc j]

theorem chapter13_vertical_self_intersection_eq_zero_iff_multiple_of_fiber
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (hconn : chapter13GraphConnected T)
    (a : Fin T.r → ℚ) :
    chapter13VerticalSelfIntersection T a = 0 ↔
      ∃ c : ℚ, a = c • chapter13RationalMultiplicityVector T := by
  rw [chapter13_vertical_self_intersection_eq_zero_iff_constant_potential T hconn a]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    funext i
    change a i = c * (T.multiplicity i : ℚ)
    exact (div_eq_iff (by
      exact_mod_cast (Nat.ne_of_gt (T.multiplicity_pos i)))).mp (hc i)
  · rintro ⟨c, ha⟩
    refine ⟨c, ?_⟩
    intro i
    rw [ha]
    change (c * (T.multiplicity i : ℚ)) /
      (T.multiplicity i : ℚ) = c
    apply (div_eq_iff (by
      exact_mod_cast (Nat.ne_of_gt (T.multiplicity_pos i)))).2
    rfl

theorem chapter13_rational_intersection_kernel_eq_multiplicity_line
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (hconn : chapter13GraphConnected T) :
    chapter13RationalMatrixKernel T = chapter13MultiplicityLine T := by
  ext a
  constructor
  · intro ha
    change ∀ i, ∑ j,
      (chapter13ComponentIntersection T i j : ℚ) * a j = 0 at ha
    have hV : chapter13VerticalSelfIntersection T a = 0 := by
      unfold chapter13VerticalSelfIntersection
      calc
        (∑ i, ∑ j,
            a i * a j * (chapter13ComponentIntersection T i j : ℚ)) =
            ∑ i, a i *
              (∑ j, (chapter13ComponentIntersection T i j : ℚ) * a j) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          rw [ha i, mul_zero]
    change ∃ c : ℚ, a = c • chapter13RationalMultiplicityVector T
    exact
      (chapter13_vertical_self_intersection_eq_zero_iff_multiple_of_fiber
        T hconn a).mp hV
  · intro ha
    change ∃ c : ℚ, a = c • chapter13RationalMultiplicityVector T at ha
    change ∀ i, ∑ j,
      (chapter13ComponentIntersection T i j : ℚ) * a j = 0
    obtain ⟨c, rfl⟩ := ha
    have hrow (i : Fin T.r) :
        ∑ j, (chapter13ComponentIntersection T i j : ℚ) *
          (T.multiplicity j : ℚ) = 0 := by
      calc
        (∑ j, (chapter13ComponentIntersection T i j : ℚ) *
            (T.multiplicity j : ℚ)) =
            ∑ j, (T.multiplicity j : ℚ) *
              (chapter13ComponentIntersection T j i : ℚ) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [show chapter13ComponentIntersection T i j =
            chapter13ComponentIntersection T j i from T.symmetric _ _]
          ring
        _ = 0 := by
          exact_mod_cast chapter13_fiber_relation T i
    intro i
    change ∑ j, (chapter13ComponentIntersection T i j : ℚ) *
      (c * (T.multiplicity j : ℚ)) = 0
    calc
      (∑ j, (chapter13ComponentIntersection T i j : ℚ) *
          (c * (T.multiplicity j : ℚ))) =
          c * (∑ j, (chapter13ComponentIntersection T i j : ℚ) *
            (T.multiplicity j : ℚ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 0 := by rw [hrow i, mul_zero]

theorem chapter13_rational_matrix_kernel_iff_linear_map_kernel
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (a : Fin T.r → ℚ) :
    a ∈ chapter13RationalMatrixKernel T ↔
      a ∈ LinearMap.ker
        (chapter13RationalMatrixLinearMap
          (chapter13RationalIntersectionMatrix T)) := by
  change (∀ i, ∑ j,
      (chapter13ComponentIntersection T i j : ℚ) * a j = 0) ↔
    ((chapter13RationalIntersectionMatrix T) *ᵥ a = 0)
  constructor
  · intro h
    funext i
    change ∑ j, (chapter13ComponentIntersection T i j : ℚ) * a j = 0
    exact h i
  · intro h i
    have hi := congrFun h i
    change ∑ j, (chapter13ComponentIntersection T i j : ℚ) * a j = 0 at hi
    exact hi

theorem chapter13_rational_matrix_kernel_mem_iff_multiple_of_fiber
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (hconn : chapter13GraphConnected T)
    (a : Fin T.r → ℚ) :
    a ∈ chapter13RationalMatrixKernel T ↔
      ∃ c : ℚ, a = c • chapter13RationalMultiplicityVector T := by
  rw [chapter13_rational_intersection_kernel_eq_multiplicity_line T hconn]
  rfl

def chapter13NegativeDefiniteModuloFiber
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)) : Prop :=
  ∀ a, a ∉ chapter13MultiplicityLine T →
    chapter13VerticalSelfIntersection T a < 0

def chapter13NegativeDefiniteOnFullCoefficientSpace
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)) : Prop :=
  ∀ a, a ≠ 0 → chapter13VerticalSelfIntersection T a < 0

theorem chapter13_rational_multiplicity_vector_ne_zero
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)) :
    chapter13RationalMultiplicityVector T ≠ 0 := by
  intro h
  let i₀ : Fin T.r := ⟨0, T.nonempty⟩
  have hi := congrFun h i₀
  change (T.multiplicity i₀ : ℚ) = 0 at hi
  have hpos : (0 : ℚ) < (T.multiplicity i₀ : ℚ) := by
    exact_mod_cast T.multiplicity_pos i₀
  exact (ne_of_gt hpos) hi

theorem chapter13_pairing_negative_definite_on_fiber_quotient
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (hconn : chapter13GraphConnected T) :
    chapter13NegativeDefiniteModuloFiber T := by
  intro a ha
  have hle := chapter13_vertical_self_intersection_nonpositive T a
  have hne : chapter13VerticalSelfIntersection T a ≠ 0 := by
    intro hzero
    apply ha
    exact
      (chapter13_vertical_self_intersection_eq_zero_iff_multiple_of_fiber
        T hconn a).mp hzero
  exact lt_of_le_of_ne hle hne

/- The quotient notation is also exposed as a reusable membership criterion;
the quotient by the whole fiber is essential because the unreduced matrix has
the nonzero fiber in its radical. -/
theorem chapter13_unreduced_matrix_is_not_negative_definite
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)) :
    chapter13VerticalSelfIntersection T
        (chapter13RationalMultiplicityVector T) = 0 ∧
      ¬ chapter13NegativeDefiniteOnFullCoefficientSpace T := by
  have hzero :
      chapter13VerticalSelfIntersection T
          (chapter13RationalMultiplicityVector T) = 0 := by
    rw [chapter13_weighted_laplacian_identity T]
    simp [chapter13WeightedLaplacianEnergy, chapter13WeightedPotential,
      chapter13RationalMultiplicityVector,
      fun i => Nat.ne_of_gt (T.multiplicity_pos i)]
  refine ⟨hzero, ?_⟩
  intro hneg
  have hlt := hneg (chapter13RationalMultiplicityVector T)
    (chapter13_rational_multiplicity_vector_ne_zero T)
  rw [hzero] at hlt
  exact (lt_irrefl 0) hlt

/-! ### Disconnected support -/

theorem chapter13_component_indicator_is_in_matrix_kernel
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (C : Set (Fin T.r))
    (hC : C.Nonempty)
      (hboundary : chapter13NoBoundaryEdges T C) :
    chapter13MatrixKernel (chapter13IntersectionMatrix T)
      (chapter13ComponentIndicator T C) := by
  classical
  obtain ⟨c, hc⟩ := hC
  intro i
  change ∑ j, chapter13ComponentIntersection T i j *
      (if j ∈ C then (T.multiplicity j : ℤ) else 0) = 0
  by_cases hi : i ∈ C
  · have hrow :
        ∑ j, chapter13ComponentIntersection T i j *
            (T.multiplicity j : ℤ) = 0 := by
      calc
        (∑ j, chapter13ComponentIntersection T i j *
            (T.multiplicity j : ℤ)) =
            ∑ j, (T.multiplicity j : ℤ) *
              chapter13ComponentIntersection T j i := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [show chapter13ComponentIntersection T i j =
            chapter13ComponentIntersection T j i from T.symmetric _ _]
          ring
        _ = 0 := chapter13_fiber_relation T i
    calc
      (∑ j, chapter13ComponentIntersection T i j *
          (if j ∈ C then (T.multiplicity j : ℤ) else 0)) =
          ∑ j, chapter13ComponentIntersection T i j *
            (T.multiplicity j : ℤ) := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hjC : j ∈ C
        · by_cases hjc : j = c
          · subst j
            simp [hc]
          · simp [hjC]
        · simp [hjC, hboundary i hi j hjC]
      _ = 0 := hrow
  · apply Finset.sum_eq_zero
    intro j hj
    by_cases hjC : j ∈ C
    · have hzero : chapter13ComponentIntersection T i j = 0 := by
        rw [show chapter13ComponentIntersection T i j =
          chapter13ComponentIntersection T j i from T.symmetric _ _]
        exact hboundary j hjC i hi
      simp [hjC, hzero]
    · simp [hjC]

theorem chapter13_disconnected_support_supplies_component_kernel_vector
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (C : Set (Fin T.r))
    (hC : C.Nonempty)
    (hproper : C ≠ Set.univ)
    (hboundary : chapter13NoBoundaryEdges T C) :
      chapter13MatrixKernel (chapter13IntersectionMatrix T)
      (chapter13ComponentIndicator T C) ∧
      chapter13ComponentIndicator T C ≠
        chapter13FiberMultiplicityVector T := by
  classical
  refine ⟨chapter13_component_indicator_is_in_matrix_kernel T C hC hboundary, ?_⟩
  obtain ⟨j, hj⟩ : ∃ j : Fin T.r, j ∉ C := by
    by_contra hnot
    apply hproper
    ext i
    simp only [Set.mem_univ, iff_true]
    by_contra hi
    exact hnot ⟨i, hi⟩
  intro heq
  have hj_eq := congrFun heq j
  change (if j ∈ C then (T.multiplicity j : ℤ) else 0) =
    (T.multiplicity j : ℤ) at hj_eq
  simp [hj] at hj_eq
  have hpos : (0 : ℤ) < (T.multiplicity j : ℤ) := by
    exact_mod_cast T.multiplicity_pos j
  exact (ne_of_gt hpos) hj_eq.symm

theorem chapter13_disconnected_graph_has_nontrivial_component_set
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (hdisc : ¬ chapter13GraphConnected T) :
    ∃ C : Set (Fin T.r), C.Nonempty ∧ C ≠ Set.univ ∧
      chapter13NoBoundaryEdges T C := by
  classical
  have hadj_symm {i j : Fin T.r} :
      chapter13Adjacency T i j → chapter13Adjacency T j i := by
    intro h
    refine ⟨h.1.symm, ?_⟩
    apply (chapter13_off_diagonal_positive_iff_meet T h.1.symm).mp
    rw [show chapter13ComponentIntersection T j i =
      chapter13ComponentIntersection T i j from T.symmetric _ _]
    exact (chapter13_off_diagonal_positive_iff_meet T h.1).2 h.2
  have hpath_symm {i j : Fin T.r} :
      Relation.ReflTransGen (chapter13Adjacency T) i j →
        Relation.ReflTransGen (chapter13Adjacency T) j i := by
    intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail hab hbc ih =>
        exact Relation.ReflTransGen.head (hadj_symm hbc) ih
  let v : Fin T.r := ⟨0, T.nonempty⟩
  let C : Set (Fin T.r) :=
    {j | Relation.ReflTransGen (chapter13Adjacency T) v j}
  have hC : C.Nonempty := by
    refine ⟨v, ?_⟩
    exact Relation.ReflTransGen.refl
  have hproper : C ≠ Set.univ := by
    intro hCu
    apply hdisc
    intro i j
    have hiC : i ∈ C := by
      rw [hCu]
      trivial
    have hjC : j ∈ C := by
      rw [hCu]
      trivial
    change Relation.ReflTransGen (chapter13Adjacency T) v i at hiC
    change Relation.ReflTransGen (chapter13Adjacency T) v j at hjC
    exact (hpath_symm hiC).trans hjC
  have hboundary : chapter13NoBoundaryEdges T C := by
    intro i hi j hj
    change Relation.ReflTransGen (chapter13Adjacency T) v i at hi
    change ¬ Relation.ReflTransGen (chapter13Adjacency T) v j at hj
    by_contra hne
    have hij : i ≠ j := by
      intro heq
      apply hj
      simpa [heq] using hi
    have hpos : 0 < chapter13ComponentIntersection T i j :=
      lt_of_le_of_ne
        (chapter13_off_diagonal_nonnegative T hij) (Ne.symm hne)
    have hadj : chapter13Adjacency T i j :=
      ⟨hij, (chapter13_off_diagonal_positive_iff_meet T hij).mp hpos⟩
    exact hj (Relation.ReflTransGen.tail hi hadj)
  exact ⟨C, hC, hproper, hboundary⟩

theorem chapter13_disconnected_graph_supplies_component_kernel_vector
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (hdisc : ¬ chapter13GraphConnected T) :
    ∃ C : Set (Fin T.r), C.Nonempty ∧ C ≠ Set.univ ∧
      chapter13MatrixKernel (chapter13IntersectionMatrix T)
        (chapter13ComponentIndicator T C) ∧
      chapter13ComponentIndicator T C ≠
        chapter13FiberMultiplicityVector T := by
  obtain ⟨C, hC, hproper, hboundary⟩ :=
    chapter13_disconnected_graph_has_nontrivial_component_set T hdisc
  obtain ⟨hkernel, hne⟩ :=
    chapter13_disconnected_support_supplies_component_kernel_vector
      T C hC hproper hboundary
  exact ⟨C, hC, hproper, hkernel, hne⟩

/-! ### Component self-intersections -/

theorem chapter13_component_self_intersection_formula
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (i : Fin T.r) :
    (chapter13ComponentIntersection T i i : ℚ) =
      -(1 / (T.multiplicity i : ℚ)) *
        ∑ j ∈ Finset.univ.erase i,
          (T.multiplicity j : ℚ) *
            (chapter13ComponentIntersection T i j : ℚ) := by
  have hrel :
      (T.multiplicity i : ℚ) *
          (chapter13ComponentIntersection T i i : ℚ) =
        -(∑ j ∈ Finset.univ.erase i,
          (T.multiplicity j : ℚ) *
            (chapter13ComponentIntersection T i j : ℚ)) := by
    exact_mod_cast chapter13_diagonal_entry_relation T i
  have hm0 : (T.multiplicity i : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (T.multiplicity_pos i))
  calc
    (chapter13ComponentIntersection T i i : ℚ) =
        (-(∑ j ∈ Finset.univ.erase i,
          (T.multiplicity j : ℚ) *
            (chapter13ComponentIntersection T i j : ℚ))) /
          (T.multiplicity i : ℚ) :=
      (eq_div_iff hm0).2 (by
        rw [mul_comm]
        exact hrel)
    _ = -(1 / (T.multiplicity i : ℚ)) *
        ∑ j ∈ Finset.univ.erase i,
          (T.multiplicity j : ℚ) *
            (chapter13ComponentIntersection T i j : ℚ) := by
      ring

theorem chapter13_component_self_intersection_negative_of_meeting_rest
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (i : Fin T.r)
    (hmeet : ∃ j, i ≠ j ∧ T.components_meet i j) :
    chapter13ComponentIntersection T i i < 0 := by
  obtain ⟨j, hij, hmeet⟩ := hmeet
  have hjmem : j ∈ Finset.univ.erase i := by
    exact Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
  have hsumpos :
      0 < ∑ k ∈ Finset.univ.erase i,
        (T.multiplicity k : ℤ) * chapter13ComponentIntersection T i k := by
    apply Finset.sum_pos'
    · intro k hk
      apply mul_nonneg
      · exact Int.natCast_nonneg _
      · rw [show chapter13ComponentIntersection T i k =
          chapter13ComponentIntersection T k i from T.symmetric _ _]
        exact chapter13_off_diagonal_nonnegative T
          (Finset.mem_erase.mp hk).1
    · refine ⟨j, hjmem, ?_⟩
      apply mul_pos
      · exact_mod_cast T.multiplicity_pos j
      · exact_mod_cast
          ((chapter13_off_diagonal_positive_iff_meet T hij).2 hmeet)
  have hprod :
      (T.multiplicity i : ℤ) * chapter13ComponentIntersection T i i < 0 := by
    rw [chapter13_diagonal_entry_relation T i]
    exact neg_lt_zero.mpr hsumpos
  have hmpos : (0 : ℤ) < (T.multiplicity i : ℤ) := by
    exact_mod_cast T.multiplicity_pos i
  by_contra hnot
  have hnonneg : 0 ≤ chapter13ComponentIntersection T i i := le_of_not_gt hnot
  exact (not_lt_of_ge (mul_nonneg (le_of_lt hmpos) hnonneg)) hprod

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13
