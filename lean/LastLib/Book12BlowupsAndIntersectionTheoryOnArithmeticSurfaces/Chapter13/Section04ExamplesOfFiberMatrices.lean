import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13.Dependencies

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped BigOperators

/-! ## 13.4. Examples of fiber matrices -/

def chapter13SingleComponentFiberMatrix (_m : ℕ) :
    Matrix (Fin 1) (Fin 1) ℤ :=
  fun _ _ => 0

def chapter13LabeledSingleComponentFiber (m : ℕ) : Fin 1 → ℕ :=
  fun _ => m

theorem chapter13_smooth_irreducible_fiber_self_intersection_zero
    (selfIntersection : ℤ)
    (hfiber_relation : (1 : ℤ) * selfIntersection = 0) :
    selfIntersection = 0 ∧
      chapter13SingleComponentFiberMatrix 1 =
        fun _ _ => 0 := by
  refine ⟨by simpa using hfiber_relation, ?_⟩
  rfl

def chapter13RationalizeMatrix {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => M i j

def chapter13MatrixHasEigenvalue {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℤ) (eigenvalue : ℚ) : Prop :=
  ∃ v : Fin n → ℚ, v ≠ 0 ∧
    ∀ i, ∑ j, (M i j : ℚ) * v j = eigenvalue * v i

def chapter13TwoComponentFiberMatrix (q : ℕ) :
    Matrix (Fin 2) (Fin 2) ℤ :=
  fun i j =>
    if i = 0 then
      if j = 0 then -(q : ℤ) else (q : ℤ)
    else if j = 0 then (q : ℤ) else -(q : ℤ)

theorem chapter13_two_component_fiber_matrix_entries (q : ℕ) :
    chapter13TwoComponentFiberMatrix q 0 0 = -(q : ℤ) ∧
      chapter13TwoComponentFiberMatrix q 0 1 = (q : ℤ) ∧
      chapter13TwoComponentFiberMatrix q 1 0 = (q : ℤ) ∧
      chapter13TwoComponentFiberMatrix q 1 1 = -(q : ℤ) := by
  simp [chapter13TwoComponentFiberMatrix]

theorem chapter13_two_component_fiber_matrix_is_negative_laplacian
    (q : ℕ) :
    chapter13TwoComponentFiberMatrix q =
      fun i j =>
        if i = j then -(q : ℤ) else (q : ℤ) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [chapter13TwoComponentFiberMatrix]

theorem chapter13_two_component_fiber_matrix_kernel
    (q : ℕ) (hq : 0 < q) :
    ∀ x : Fin 2 → ℚ,
      chapter13MatrixKernel (chapter13RationalizeMatrix
        (chapter13TwoComponentFiberMatrix q)) x ↔
        ∃ c : ℚ, x = c • (fun _ : Fin 2 => (1 : ℚ)) := by
  intro x
  constructor
  · intro hx
    change ∀ i, ∑ j,
      (chapter13TwoComponentFiberMatrix q i j : ℚ) * x j = 0 at hx
    have hq0 : (q : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hq)
    have h0 := hx (0 : Fin 2)
    rw [Fin.sum_univ_two] at h0
    simp [chapter13TwoComponentFiberMatrix] at h0
    have hdiff : (q : ℚ) * x 1 - (q : ℚ) * x 0 = 0 := by
      calc
        (q : ℚ) * x 1 - (q : ℚ) * x 0 =
            -(q : ℚ) * x 0 + (q : ℚ) * x 1 := by ring
        _ = 0 := by simpa [neg_mul] using h0
    have hx10 : x 1 = x 0 := by
      apply mul_left_cancel₀ hq0
      exact sub_eq_zero.mp hdiff
    refine ⟨x 0, ?_⟩
    funext i
    fin_cases i
    · simp
    · simp [hx10]
  · rintro ⟨c, rfl⟩
    change ∀ i, ∑ j,
      (chapter13TwoComponentFiberMatrix q i j : ℚ) *
        (c • (fun _ : Fin 2 => (1 : ℚ))) j = 0
    intro i
    fin_cases i <;>
      simp [chapter13TwoComponentFiberMatrix, Fin.sum_univ_two]

theorem chapter13_two_component_fiber_matrix_eigenvalues
    (q : ℕ) (hq : 0 < q) :
    chapter13MatrixHasEigenvalue (chapter13TwoComponentFiberMatrix q) 0 ∧
      chapter13MatrixHasEigenvalue (chapter13TwoComponentFiberMatrix q)
        (-(2 * (q : ℚ))) ∧
      ∀ eigenvalue : ℚ,
        chapter13MatrixHasEigenvalue (chapter13TwoComponentFiberMatrix q) eigenvalue →
          eigenvalue = 0 ∨ eigenvalue = -(2 * (q : ℚ)) := by
  unfold chapter13MatrixHasEigenvalue
  constructor
  · refine ⟨(fun _ : Fin 2 => (1 : ℚ)), ?_, ?_⟩
    · intro h
      have h0 := congrFun h (0 : Fin 2)
      simp at h0
    · intro i
      fin_cases i <;>
        simp [chapter13TwoComponentFiberMatrix, Fin.sum_univ_two]
  constructor
  · refine ⟨(fun i : Fin 2 => if i = 0 then (q : ℚ) else -(q : ℚ)), ?_, ?_⟩
    · intro h
      have h0 := congrFun h (0 : Fin 2)
      simp at h0
      exact (Nat.ne_of_gt hq) h0
    · intro i
      fin_cases i <;>
        simp [chapter13TwoComponentFiberMatrix, Fin.sum_univ_two] <;> ring
  · intro eigenvalue h
    rcases h with ⟨v, hv, heq⟩
    have h0 := heq (0 : Fin 2)
    have h1 := heq (1 : Fin 2)
    rw [Fin.sum_univ_two] at h0 h1
    simp [chapter13TwoComponentFiberMatrix] at h0 h1
    have h0' : -(q : ℚ) * v 0 + (q : ℚ) * v 1 =
        eigenvalue * v 0 := by
      simpa [neg_mul] using h0
    have h1' : (q : ℚ) * v 0 - (q : ℚ) * v 1 =
        eigenvalue * v 1 := by
      simpa only [sub_eq_add_neg] using h1
    by_cases hlambda : eigenvalue = 0
    · exact Or.inl hlambda
    · right
      have hsum : eigenvalue * (v 0 + v 1) = 0 := by
        calc
          eigenvalue * (v 0 + v 1) =
              eigenvalue * v 0 + eigenvalue * v 1 := by ring
          _ = (-(q : ℚ) * v 0 + (q : ℚ) * v 1) +
              ((q : ℚ) * v 0 - (q : ℚ) * v 1) := by
            rw [h0', h1']
          _ = 0 := by ring
      have hsumzero : v 0 + v 1 = 0 :=
        (mul_eq_zero.mp hsum).resolve_left hlambda
      have hv1 : v 1 = -v 0 := eq_neg_of_add_eq_zero_right hsumzero
      have hv0 : v 0 ≠ 0 := by
        intro hv0
        have hv1zero : v 1 = 0 := by rw [hv1, hv0, neg_zero]
        apply hv
        funext i
        fin_cases i <;> simp [hv0, hv1zero]
      have hcoef : (-(2 * (q : ℚ))) * v 0 = eigenvalue * v 0 := by
        calc
          (-(2 * (q : ℚ))) * v 0 =
              -(q : ℚ) * v 0 + (q : ℚ) * v 1 := by
                rw [hv1]
                ring
          _ = eigenvalue * v 0 := h0'
      exact (mul_right_cancel₀ hv0 hcoef).symm

def chapter13ResidueDegreeTotal {q : ℕ} (d : Fin q → ℕ) : ℕ :=
  ∑ j, d j

theorem chapter13_two_component_residue_degree_weighting
    {q : ℕ}
    (d : Fin q → ℕ) :
    chapter13TwoComponentFiberMatrix (chapter13ResidueDegreeTotal d) =
      fun i j =>
        if i = j then -(chapter13ResidueDegreeTotal d : ℤ)
        else (chapter13ResidueDegreeTotal d : ℤ) := by
  exact chapter13_two_component_fiber_matrix_is_negative_laplacian
    (chapter13ResidueDegreeTotal d)

/-! ### Normal-crossing chains -/

def chapter13ChainAdjacent {n : ℕ} (i j : Fin n) : Prop :=
  i.val + 1 = j.val ∨ j.val + 1 = i.val

def chapter13ChainValency (n : ℕ) (i : Fin n) : ℕ :=
  if 2 ≤ n then
    if i.val = 0 ∨ i.val + 1 = n then 1 else 2
  else 0

def chapter13ChainIntersectionMatrix (n : ℕ) :
    Matrix (Fin n) (Fin n) ℤ :=
  by
    classical
    exact fun i j =>
      if i = j then -(chapter13ChainValency n i : ℤ)
      else if chapter13ChainAdjacent i j then 1 else 0

structure Chapter13RationalTransverseChain where
  n : ℕ
  atLeastTwo : 2 ≤ n
  edgeIntersection : Fin n → Fin n → ℤ
  edgeIntersection_rational_transverse :
    ∀ i j, chapter13ChainAdjacent i j → edgeIntersection i j = 1
  nonedge_intersection_zero :
    ∀ i j, i ≠ j → ¬chapter13ChainAdjacent i j → edgeIntersection i j = 0

def chapter13RationalTransverseChainMatrix
    (C : Chapter13RationalTransverseChain) :
    Matrix (Fin C.n) (Fin C.n) ℤ :=
  fun i j =>
    if i = j then -(chapter13ChainValency C.n i : ℤ)
    else C.edgeIntersection i j

theorem chapter13_rational_transverse_chain_matrix_is_negative_graph_laplacian
    (C : Chapter13RationalTransverseChain) :
    chapter13RationalTransverseChainMatrix C =
      chapter13ChainIntersectionMatrix C.n := by
  funext i j
  by_cases hij : i = j
  · subst j
    simp [chapter13RationalTransverseChainMatrix,
      chapter13ChainIntersectionMatrix]
  · by_cases hadj : chapter13ChainAdjacent i j
    · simp [chapter13RationalTransverseChainMatrix,
        chapter13ChainIntersectionMatrix, hij, hadj,
        C.edgeIntersection_rational_transverse i j hadj]
    · simp [chapter13RationalTransverseChainMatrix,
        chapter13ChainIntersectionMatrix, hij, hadj,
        C.nonedge_intersection_zero i j hij hadj]

theorem chapter13_chain_end_component_has_square_minus_one
    (n : ℕ) (hn : 2 ≤ n) (i : Fin n)
    (hi : i.val = 0 ∨ i.val + 1 = n) :
    chapter13ChainIntersectionMatrix n i i = -1 := by
  simp [chapter13ChainIntersectionMatrix, chapter13ChainValency, hn, hi]

/-! The geometric certificate for an inverse point blowup is kept separate
from the numerical end-component entry. -/
structure Chapter13ExceptionalEndComponent where
  selfIntersection : ℤ
  projectiveLine : Prop
  normalBundleMinusOne : Prop
  inversePointBlowup : Prop
  inversePointBlowup_requires_projectiveLine :
    inversePointBlowup → projectiveLine
  inversePointBlowup_requires_normalBundleMinusOne :
    inversePointBlowup → normalBundleMinusOne

def chapter13InversePointBlowupCertificate
    (E : Chapter13ExceptionalEndComponent) : Prop :=
  E.projectiveLine ∧ E.normalBundleMinusOne ∧ E.inversePointBlowup

/- The numerical end-component datum is deliberately separated from the
geometric certificate needed for an inverse point blowup. -/
def chapter13NumericalEndComponentDatum
    (E : Chapter13ExceptionalEndComponent) : Prop :=
  E.selfIntersection = -1

theorem chapter13_inverse_point_blowup_requires_projective_line_and_normal_bundle
    (E : Chapter13ExceptionalEndComponent)
    (hE : E.inversePointBlowup) :
    E.projectiveLine ∧ E.normalBundleMinusOne := by
  exact ⟨E.inversePointBlowup_requires_projectiveLine hE,
    E.inversePointBlowup_requires_normalBundleMinusOne hE⟩

/-! ### Smooth irreducible and multiple irreducible fibers -/

theorem chapter13_multiple_irreducible_fiber_matrix_is_zero
    (m : ℕ) (hm : 0 < m) (selfIntersection : ℤ)
    (hfiber_relation : (m : ℤ) * selfIntersection = 0) :
    (chapter13SingleComponentFiberMatrix m = fun _ _ => 0) ∧
      selfIntersection = 0 := by
  have hm0 : (m : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm)
  refine ⟨rfl, ?_⟩
  exact (mul_eq_zero.mp hfiber_relation).resolve_left hm0

theorem chapter13_single_component_matrix_does_not_detect_multiplicity
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    chapter13SingleComponentFiberMatrix m =
        chapter13SingleComponentFiberMatrix n ∧
      chapter13LabeledSingleComponentFiber m ≠
        chapter13LabeledSingleComponentFiber n := by
  refine ⟨rfl, ?_⟩
  by_cases hmz : m = 0
  · exact (Nat.ne_of_gt hm hmz).elim
  by_cases hnz : n = 0
  · exact (Nat.ne_of_gt hn hnz).elim
  intro h
  apply hmn
  have h0 := congrFun h (0 : Fin 1)
  simpa [chapter13LabeledSingleComponentFiber] using h0

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13
