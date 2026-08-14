import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter13.Dependencies

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter13

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

/-! ## 13.1. A two-term model -/

/--
The local two-term model from (13.1)--(13.2).  The identifications are with the
canonical additive-group cohomology objects, while the kernel and cokernel are
formed in the module category after scalar extension.
-/
structure Chapter13LocalTwoTermModel
    (C : Chapter13RelativeCurve) (E : Chapter13VectorBundle C.X) where
  chart : Chapter13AffineBase C
  model : Chapter13TwoTermModel chart.A
  h0_identification :
    ∀ (B : Chapter13AAlgebra chart.A),
      letI := B.commRingB
      letI := B.algebraAB
      Nonempty
        (chapter13BaseChangeCohomology C E (chart.mapToBase B) 0 ≅
          chapter13TwoTermH0 (model.baseChange B).d)
  h1_identification :
    ∀ (B : Chapter13AAlgebra chart.A),
      letI := B.commRingB
      letI := B.algebraAB
      Nonempty
        (chapter13BaseChangeCohomology C E (chart.mapToBase B) 1 ≅
          chapter13TwoTermH1 (model.baseChange B).d)

/-- The matrix in the local model. -/
abbrev chapter13TwoTermMatrix
    {C : Chapter13RelativeCurve} {E : Chapter13VectorBundle C.X}
    (M : Chapter13LocalTwoTermModel C E) :
    M.model.K0.carrier ⟶ M.model.K1.carrier :=
  M.model.d

/-- The virtual rank of a finite free two-term model. -/
def chapter13TwoTermVirtualRank
    {A : Type u} [CommRing A] (M : Chapter13TwoTermModel A) : ℤ :=
  (M.K0.rank : ℤ) - (M.K1.rank : ℤ)

@[simp]
theorem chapter13TwoTermVirtualRank_baseChange
    {A : Type u} [CommRing A] (M : Chapter13TwoTermModel A)
    (B : Chapter13AAlgebra A) :
    chapter13TwoTermVirtualRank (M.baseChange B) =
      chapter13TwoTermVirtualRank M := by
  rfl

/- LOCAL_DEPENDENCY_GUESS: perfectness of the derived pushforward of a vector
bundle on a projective flat relative curve, together with its uniform arbitrary
base-change comparison, is not packaged by the pinned imports. -/

/-- Existence of a finite free two-term model after shrinking to an affine base. -/
theorem chapter13_two_term_model_exists
    (C : Chapter13RelativeCurve) (E : Chapter13VectorBundle C.X) :
    Nonempty (Chapter13LocalTwoTermModel C E) := by
  sorry

/-- The degree-zero cohomology calculation in (13.2). -/
theorem chapter13_two_term_model_h0
    {C : Chapter13RelativeCurve} {E : Chapter13VectorBundle C.X}
    (M : Chapter13LocalTwoTermModel C E)
    (B : Chapter13AAlgebra M.chart.A) :
    letI := B.commRingB
      letI := B.algebraAB
      Nonempty
        (chapter13BaseChangeCohomology C E (M.chart.mapToBase B) 0 ≅
        chapter13TwoTermH0 (M.model.baseChange B).d) := by
  exact M.h0_identification B

/-- The degree-one cohomology calculation in (13.2). -/
theorem chapter13_two_term_model_h1
    {C : Chapter13RelativeCurve} {E : Chapter13VectorBundle C.X}
    (M : Chapter13LocalTwoTermModel C E)
    (B : Chapter13AAlgebra M.chart.A) :
    letI := B.commRingB
      letI := B.algebraAB
      Nonempty
        (chapter13BaseChangeCohomology C E (M.chart.mapToBase B) 1 ≅
        chapter13TwoTermH1 (M.model.baseChange B).d) := by
  exact M.h1_identification B

end
end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter13
