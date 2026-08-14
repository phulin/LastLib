import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13.Section03NegativityAndTheExactKernel

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped BigOperators

/-! ## 13.4. Examples of fiber matrices -/

def chapter13SingleComponentFiberMatrix (m : ℕ) :
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
  sorry

def chapter13RationalizeMatrix {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => M i j

def chapter13MatrixHasEigenvalue {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℤ) (λ : ℚ) : Prop :=
  ∃ v : Fin n → ℚ, v ≠ 0 ∧
    ∀ i, ∑ j, (M i j : ℚ) * v j = λ * v i

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
  sorry

theorem chapter13_two_component_fiber_matrix_is_negative_laplacian
    (q : ℕ) :
    chapter13TwoComponentFiberMatrix q =
      fun i j =>
        if i = j then -(q : ℤ) else (q : ℤ) := by
  sorry

theorem chapter13_two_component_fiber_matrix_kernel
    (q : ℕ) (hq : 0 < q) :
    ∀ x : Fin 2 → ℚ,
      chapter13MatrixKernel (chapter13RationalizeMatrix
        (chapter13TwoComponentFiberMatrix q)) x ↔
        ∃ c : ℚ, x = c • (fun _ : Fin 2 => (1 : ℚ)) := by
  sorry

theorem chapter13_two_component_fiber_matrix_eigenvalues
    (q : ℕ) (hq : 0 < q) :
    chapter13MatrixHasEigenvalue (chapter13TwoComponentFiberMatrix q) 0 ∧
      chapter13MatrixHasEigenvalue (chapter13TwoComponentFiberMatrix q)
        (-(2 * (q : ℚ))) ∧
      ∀ λ : ℚ,
        chapter13MatrixHasEigenvalue (chapter13TwoComponentFiberMatrix q) λ →
          λ = 0 ∨ λ = -(2 * (q : ℚ)) := by
  sorry

def chapter13ResidueDegreeTotal {q : ℕ} (d : Fin q → ℕ) : ℕ :=
  ∑ j, d j

theorem chapter13_two_component_residue_degree_weighting
    {q : ℕ}
    (d : Fin q → ℕ) :
    chapter13TwoComponentFiberMatrix (chapter13ResidueDegreeTotal d) =
      fun i j =>
        if i = j then -(chapter13ResidueDegreeTotal d : ℤ)
        else (chapter13ResidueDegreeTotal d : ℤ) := by
  sorry

/-! ### Normal-crossing chains -/

def chapter13ChainAdjacent {n : ℕ} (i j : Fin n) : Prop :=
  i.val + 1 = j.val ∨ j.val + 1 = i.val

def chapter13ChainValency (n : ℕ) (i : Fin n) : ℕ :=
  if 2 ≤ n then
    if i.val = 0 ∨ i.val + 1 = n then 1 else 2
  else 0

def chapter13ChainIntersectionMatrix (n : ℕ) :
    Matrix (Fin n) (Fin n) ℤ :=
  fun i j =>
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
  sorry

theorem chapter13_chain_end_component_has_square_minus_one
    (n : ℕ) (hn : 2 ≤ n) (i : Fin n)
    (hi : i.val = 0 ∨ i.val + 1 = n) :
    chapter13ChainIntersectionMatrix n i i = -1 := by
  sorry

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
    chapter13SingleComponentFiberMatrix m = fun _ _ => 0 ∧
      selfIntersection = 0 := by
  sorry

theorem chapter13_single_component_matrix_does_not_detect_multiplicity
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    chapter13SingleComponentFiberMatrix m =
        chapter13SingleComponentFiberMatrix n ∧
      chapter13LabeledSingleComponentFiber m ≠
        chapter13LabeledSingleComponentFiber n := by
  sorry

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13
