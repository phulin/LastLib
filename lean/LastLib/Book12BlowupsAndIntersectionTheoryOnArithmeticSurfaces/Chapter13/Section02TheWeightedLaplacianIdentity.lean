import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13.Dependencies
import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13.Section01TheFiberRelation

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped BigOperators

/-! ## 13.2. The weighted Laplacian identity -/

theorem chapter13_weighted_laplacian_identity
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (a : Fin T.r → ℚ) :
    chapter13VerticalSelfIntersection T a =
      -chapter13WeightedLaplacianEnergy T a := by
  classical
  have hsplit (i : Fin T.r) (g : Fin T.r → Fin T.r → ℚ) :
      (∑ j ∈ Finset.univ.erase i, g i j) =
        (∑ j ∈ Finset.Ioi i, g i j) + (∑ j ∈ Finset.Iio i, g i j) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.erase i)
      (fun j => i < j) (fun j => g i j)]
    have hupper : (Finset.univ.erase i).filter (fun j => i < j) =
        Finset.Ioi i := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
        Finset.mem_Ioi]
      constructor
      · intro h
        exact h.2
      · intro h
        exact ⟨⟨h.ne', trivial⟩, h⟩
    have hlower : (Finset.univ.erase i).filter (fun j => ¬ i < j) =
        Finset.Iio i := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
        Finset.mem_Iio]
      constructor
      · intro h
        exact lt_of_le_of_ne (le_of_not_gt h.2) h.1.1
      · intro h
        exact ⟨⟨h.ne, trivial⟩, not_lt_of_ge h.le⟩
    rw [hupper, hlower]
  have hlower (g : Fin T.r → Fin T.r → ℚ) :
      (∑ i, ∑ j ∈ Finset.Iio i, g i j) =
        ∑ i, ∑ j ∈ Finset.Ioi i, g j i := by
    have hIio (i : Fin T.r) :
        Finset.Iio i = Finset.univ.filter (fun j => j < i) := by
      ext j
      simp
    have hIoi (i : Fin T.r) :
        Finset.Ioi i = Finset.univ.filter (fun j => i < j) := by
      ext j
      simp
    simp_rw [hIio, hIoi, Finset.sum_filter]
    rw [Finset.sum_comm]
  have htriangle (g : Fin T.r → Fin T.r → ℚ) :
      (∑ i, ∑ j ∈ Finset.univ.erase i, g i j) =
        ∑ i, ∑ j ∈ Finset.Ioi i, (g i j + g j i) := by
    calc
      (∑ i, ∑ j ∈ Finset.univ.erase i, g i j) =
          ∑ i, ((∑ j ∈ Finset.Ioi i, g i j) +
            (∑ j ∈ Finset.Iio i, g i j)) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hsplit i g
      _ = (∑ i, ∑ j ∈ Finset.Ioi i, g i j) +
          (∑ i, ∑ j ∈ Finset.Iio i, g i j) := by
        rw [Finset.sum_add_distrib]
      _ = (∑ i, ∑ j ∈ Finset.Ioi i, g i j) +
          (∑ i, ∑ j ∈ Finset.Ioi i, g j i) := by
        rw [hlower g]
      _ = ∑ i, ∑ j ∈ Finset.Ioi i, (g i j + g j i) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_add_distrib]
  let b : Fin T.r → ℚ := fun i => chapter13WeightedPotential T a i
  let w : Fin T.r → Fin T.r → ℚ := fun i j =>
    (T.multiplicity i : ℚ) * (T.multiplicity j : ℚ) *
      (chapter13ComponentIntersection T i j : ℚ)
  have hrel (i : Fin T.r) :
      (∑ j, (T.multiplicity j : ℚ) *
        (chapter13ComponentIntersection T j i : ℚ)) = 0 := by
    exact_mod_cast chapter13_fiber_relation T i
  have hm0 (i : Fin T.r) : (T.multiplicity i : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (T.multiplicity_pos i))
  have ha (i : Fin T.r) :
      a i = (T.multiplicity i : ℚ) * b i := by
    dsimp [b, chapter13WeightedPotential]
    rw [mul_comm]
    exact (div_mul_cancel₀ (a i) (hm0 i)).symm
  have hwsym (i j : Fin T.r) : w i j = w j i := by
    change (T.multiplicity i : ℚ) * (T.multiplicity j : ℚ) *
        (chapter13ComponentIntersection T i j : ℚ) =
      (T.multiplicity j : ℚ) * (T.multiplicity i : ℚ) *
        (chapter13ComponentIntersection T j i : ℚ)
    rw [show chapter13ComponentIntersection T i j =
      chapter13ComponentIntersection T j i from T.symmetric _ _]
    ring
  have hrow (i : Fin T.r) : (∑ j, w i j) = 0 := by
    calc
      (∑ j, w i j) =
          (T.multiplicity i : ℚ) *
            (∑ j, (T.multiplicity j : ℚ) *
              (chapter13ComponentIntersection T j i : ℚ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [w]
        rw [show chapter13ComponentIntersection T i j =
          chapter13ComponentIntersection T j i from T.symmetric _ _]
        ring
      _ = 0 := by rw [hrel i, mul_zero]
  have hdiag (i : Fin T.r) :
      w i i * b i ^ 2 =
        -(∑ j ∈ Finset.univ.erase i, w i j * b i ^ 2) := by
    have h := hrow i
    have hsum := Finset.sum_erase_add (s := Finset.univ)
      (f := fun j : Fin T.r => w i j) (Finset.mem_univ i)
    rw [← hsum] at h
    have h' : w i i + ∑ j ∈ Finset.univ.erase i, w i j = 0 := by
      rw [add_comm]
      exact h
    calc
      w i i * b i ^ 2 =
          (-(∑ j ∈ Finset.univ.erase i, w i j)) * b i ^ 2 := by
        rw [eq_neg_of_add_eq_zero_left h']
      _ = -(∑ j ∈ Finset.univ.erase i, w i j * b i ^ 2) := by
        rw [neg_mul, Finset.sum_mul]
  have hV :
      chapter13VerticalSelfIntersection T a =
        ∑ i, ∑ j, w i j * b i * b j := by
    unfold chapter13VerticalSelfIntersection
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [ha i, ha j]
    dsimp [w]
    ring
  have hVoff :
      (∑ i, ∑ j, w i j * b i * b j) =
        ∑ i, ∑ j ∈ Finset.univ.erase i,
          w i j * (b i * b j - b i ^ 2) := by
    calc
      (∑ i, ∑ j, w i j * b i * b j) =
          ∑ i, (w i i * b i ^ 2 +
            ∑ j ∈ Finset.univ.erase i, w i j * b i * b j) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hsum := Finset.sum_erase_add (s := Finset.univ)
          (f := fun j : Fin T.r => w i j * b i * b j)
          (Finset.mem_univ i)
        calc
          (∑ j, w i j * b i * b j) =
              (∑ j ∈ Finset.univ.erase i, w i j * b i * b j) +
                w i i * b i * b i := hsum.symm
          _ = w i i * b i ^ 2 +
              ∑ j ∈ Finset.univ.erase i, w i j * b i * b j := by
            ring
      _ = ∑ i, ∑ j ∈ Finset.univ.erase i,
          w i j * (b i * b j - b i ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hdiag i]
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib]
        have hcomm :
            (∑ x ∈ Finset.univ.erase i, w i x * b i ^ 2) =
              ∑ x ∈ Finset.univ.erase i, b i ^ 2 * w i x := by
          apply Finset.sum_congr rfl
          intro x hx
          ring
        rw [hcomm]
        ring_nf
  have hpair :
      (∑ i, ∑ j ∈ Finset.univ.erase i,
          w i j * (b i * b j - b i ^ 2)) =
        ∑ i, ∑ j ∈ Finset.Ioi i,
          (w i j * (b i * b j - b i ^ 2) +
            w j i * (b j * b i - b j ^ 2)) := by
    exact htriangle (fun i j => w i j * (b i * b j - b i ^ 2))
  have henergy :
      (∑ i, ∑ j ∈ Finset.Ioi i,
          (w i j * (b i * b j - b i ^ 2) +
            w j i * (b j * b i - b j ^ 2))) =
        -∑ i, ∑ j ∈ Finset.Ioi i, w i j * (b i - b j) ^ 2 := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hwsym j i]
    ring
  calc
    chapter13VerticalSelfIntersection T a =
        ∑ i, ∑ j, w i j * b i * b j := hV
    _ = ∑ i, ∑ j ∈ Finset.univ.erase i,
        w i j * (b i * b j - b i ^ 2) := hVoff
    _ = ∑ i, ∑ j ∈ Finset.Ioi i,
        (w i j * (b i * b j - b i ^ 2) +
          w j i * (b j * b i - b j ^ 2)) := hpair
    _ = -∑ i, ∑ j ∈ Finset.Ioi i, w i j * (b i - b j) ^ 2 := henergy
    _ = -chapter13WeightedLaplacianEnergy T a := by
      rfl

theorem chapter13_weighted_laplacian_term_nonnegative
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (a : Fin T.r → ℚ) (i j : Fin T.r) (hij : i < j) :
    0 ≤
      (T.multiplicity i : ℚ) * (T.multiplicity j : ℚ) *
        (chapter13ComponentIntersection T i j : ℚ) *
          (chapter13WeightedPotential T a i -
            chapter13WeightedPotential T a j) ^ 2 := by
  have hmi : (0 : ℚ) ≤ (T.multiplicity i : ℚ) := by
    exact_mod_cast (Nat.zero_le (T.multiplicity i))
  have hmj : (0 : ℚ) ≤ (T.multiplicity j : ℚ) := by
    exact_mod_cast (Nat.zero_le (T.multiplicity j))
  have hinter : (0 : ℚ) ≤ (chapter13ComponentIntersection T i j : ℚ) := by
    exact_mod_cast (chapter13_off_diagonal_nonnegative T (ne_of_lt hij))
  exact mul_nonneg (mul_nonneg (mul_nonneg hmi hmj) hinter)
    (sq_nonneg _)

theorem chapter13_weighted_laplacian_identity_expanded
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (a : Fin T.r → ℚ) :
    chapter13VerticalSelfIntersection T a =
      -∑ i, ∑ j ∈ Finset.Ioi i,
        (T.multiplicity i : ℚ) * (T.multiplicity j : ℚ) *
          (chapter13ComponentIntersection T i j : ℚ) *
            (chapter13WeightedPotential T a i -
              chapter13WeightedPotential T a j) ^ 2 := by
  simpa [chapter13WeightedLaplacianEnergy] using
    chapter13_weighted_laplacian_identity T a

theorem chapter13_vertical_self_intersection_nonpositive
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (a : Fin T.r → ℚ) :
    chapter13VerticalSelfIntersection T a ≤ 0 := by
  rw [chapter13_weighted_laplacian_identity T a]
  apply neg_nonpos.mpr
  unfold chapter13WeightedLaplacianEnergy
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  exact chapter13_weighted_laplacian_term_nonnegative T a i j
    (Finset.mem_Ioi.mp hj)

theorem chapter13_vertical_self_intersection_eq_zero_iff_edge_potentials_equal
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (a : Fin T.r → ℚ) :
    chapter13VerticalSelfIntersection T a = 0 ↔
      ∀ i j, i ≠ j → T.components_meet i j →
        chapter13WeightedPotential T a i = chapter13WeightedPotential T a j := by
  constructor
  · intro hzero
    have hE : chapter13WeightedLaplacianEnergy T a = 0 := by
      have h := chapter13_weighted_laplacian_identity T a
      rw [hzero] at h
      exact neg_eq_zero.mp h.symm
    unfold chapter13WeightedLaplacianEnergy at hE
    have houter :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i hi => by
        apply Finset.sum_nonneg
        intro j hj
        exact chapter13_weighted_laplacian_term_nonnegative T a i j
          (Finset.mem_Ioi.mp hj))).mp hE
    have hordered (i j : Fin T.r) (hij : i < j)
        (hmeet : T.components_meet i j) :
        chapter13WeightedPotential T a i =
          chapter13WeightedPotential T a j := by
      have hi0 := houter i (Finset.mem_univ i)
      have hterm :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => by
          exact chapter13_weighted_laplacian_term_nonnegative T a i j
            (Finset.mem_Ioi.mp hj))).mp hi0 j
          (Finset.mem_Ioi.mpr hij)
      have hmi : (0 : ℚ) < (T.multiplicity i : ℚ) := by
        exact_mod_cast T.multiplicity_pos i
      have hmj : (0 : ℚ) < (T.multiplicity j : ℚ) := by
        exact_mod_cast T.multiplicity_pos j
      have hI : (0 : ℚ) < (chapter13ComponentIntersection T i j : ℚ) := by
        exact_mod_cast
          ((chapter13_off_diagonal_positive_iff_meet T (ne_of_lt hij)).2 hmeet)
      have hcoef : (0 : ℚ) <
          (T.multiplicity i : ℚ) * (T.multiplicity j : ℚ) *
            (chapter13ComponentIntersection T i j : ℚ) :=
        mul_pos (mul_pos hmi hmj) hI
      have hsq :
          (chapter13WeightedPotential T a i -
            chapter13WeightedPotential T a j) ^ 2 = 0 := by
        exact (mul_eq_zero.mp hterm).resolve_left (ne_of_gt hcoef)
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
    intro i j hij hmeet
    by_cases hlt : i < j
    · exact hordered i j hlt hmeet
    · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hlt) hij.symm
      have hpos : 0 < chapter13ComponentIntersection T j i := by
        rw [show chapter13ComponentIntersection T j i =
          chapter13ComponentIntersection T i j from T.symmetric _ _]
        exact (chapter13_off_diagonal_positive_iff_meet T hij).2 hmeet
      have hmeet' : T.components_meet j i :=
        (chapter13_off_diagonal_positive_iff_meet T (ne_of_lt hji)).mp hpos
      exact (hordered j i hji hmeet').symm
  · intro hpot
    have hterm (i j : Fin T.r) (hij : i < j) :
        (T.multiplicity i : ℚ) * (T.multiplicity j : ℚ) *
          (chapter13ComponentIntersection T i j : ℚ) *
            (chapter13WeightedPotential T a i -
              chapter13WeightedPotential T a j) ^ 2 = 0 := by
      by_cases hzero :
          (chapter13ComponentIntersection T i j : ℚ) = 0
      · simp [hzero]
      · have hneZ : chapter13ComponentIntersection T i j ≠ 0 := by
          intro h
          apply hzero
          simp [h]
        have hposZ : 0 < chapter13ComponentIntersection T i j :=
          lt_of_le_of_ne
            (chapter13_off_diagonal_nonnegative T (ne_of_lt hij)) hneZ.symm
        have hmeet : T.components_meet i j :=
          (chapter13_off_diagonal_positive_iff_meet T (ne_of_lt hij)).mp hposZ
        have heq := hpot i j (ne_of_lt hij) hmeet
        simp [heq]
    have hE : chapter13WeightedLaplacianEnergy T a = 0 := by
      unfold chapter13WeightedLaplacianEnergy
      apply (Finset.sum_eq_zero_iff_of_nonneg (fun i hi => by
        apply Finset.sum_nonneg
        intro j hj
        exact chapter13_weighted_laplacian_term_nonnegative T a i j
          (Finset.mem_Ioi.mp hj))).2
      intro i hi
      apply (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => by
        exact chapter13_weighted_laplacian_term_nonnegative T a i j
          (Finset.mem_Ioi.mp hj))).2
      intro j hj
      exact hterm i j (Finset.mem_Ioi.mp hj)
    calc
      chapter13VerticalSelfIntersection T a =
          -chapter13WeightedLaplacianEnergy T a :=
        chapter13_weighted_laplacian_identity T a
      _ = 0 := by rw [hE, neg_zero]

theorem chapter13_vertical_self_intersection_eq_zero_iff_off_diagonal_potentials_equal
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (a : Fin T.r → ℚ) :
    chapter13VerticalSelfIntersection T a = 0 ↔
      ∀ i j, i ≠ j → chapter13ComponentIntersection T i j ≠ 0 →
        chapter13WeightedPotential T a i = chapter13WeightedPotential T a j := by
  rw [chapter13_vertical_self_intersection_eq_zero_iff_edge_potentials_equal T a]
  constructor
  · intro hedge i j hij hne
    apply hedge i j hij
    apply (chapter13_off_diagonal_positive_iff_meet T hij).mp
    exact lt_of_le_of_ne
      (chapter13_off_diagonal_nonnegative T hij) hne.symm
  · intro hoff i j hij hmeet
    apply hoff i j hij
    exact ne_of_gt
      ((chapter13_off_diagonal_positive_iff_meet T hij).2 hmeet)

/- The source's graph interpretation is now an API statement: the symmetric
intersection form is the negative of the conductance energy after the vertex
potential is rescaled by the fiber multiplicity. -/
theorem chapter13_intersection_form_is_negative_weighted_graph_laplacian
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)) :
    ∀ a : Fin T.r → ℚ,
      chapter13VerticalSelfIntersection T a =
        -chapter13WeightedLaplacianEnergy T a := by
  intro a
  exact chapter13_weighted_laplacian_identity T a

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13
