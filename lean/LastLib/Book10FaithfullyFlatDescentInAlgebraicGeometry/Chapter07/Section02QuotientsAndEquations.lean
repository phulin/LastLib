import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter07.Section01DescentOfAlgebraStructures

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter07

open scoped TensorProduct

universe u

/-- Stability of an ideal under the two maps in a descent overlap. -/
structure Chapter07StableIdeal {C D : Type u} [CommRing C] [CommRing D]
    (J : Ideal C) where
  left : C →+* D
  right : C →+* D
  stable : J.map left = J.map right

@[ext]
theorem Chapter07StableIdeal.ext {C D : Type u} [CommRing C] [CommRing D]
    {J : Ideal C} (x y : Chapter07StableIdeal J)
    (hleft : x.left = y.left) (hright : x.right = y.right) : x = y := by
  cases x
  cases y
  simp_all

/-- The algebra and ideal data needed for quotient descent. -/
structure Chapter07IdealDescentData
    (A B R C : Type u) [CommRing A] [CommRing B] [CommRing R] [CommRing C]
    [Algebra A B] [Algebra A R] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    where
  base_change : Nonempty (B ⊗[A] R ≃ₐ[B] C)
  J : Ideal C
  stable : Chapter07StableIdeal J

/-- The descended ideal and the quotient comparison isomorphism. -/
structure Chapter07IdealDescentResult
    {A B R C : Type u} [CommRing A] [CommRing B] [CommRing R] [CommRing C]
    [Algebra A B] [Algebra A R] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (D : Chapter07IdealDescentData A B R C) where
  I : Ideal R
  quotient_comparison : Nonempty (B ⊗[A] (R ⧸ I) ≃ₐ[B] (C ⧸ D.J))

/- LOCAL_DEPENDENCY_GUESS: this is the ideal-level effectivity interface supplied by the
earlier module descent chapters; the present chapter records its algebra quotient output. -/
theorem chapter07_stable_ideal_descends
    {A B R C : Type u} [CommRing A] [CommRing B] [CommRing R] [CommRing C]
    [Algebra A B] [Algebra A R] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (D : Chapter07IdealDescentData A B R C)
    (hff : RingHom.FaithfullyFlat (algebraMap A B)) :
    Nonempty (Chapter07IdealDescentResult D) := by
  sorry

theorem chapter07_quotient_base_change
    {A B R C : Type u} [CommRing A] [CommRing B] [CommRing R] [CommRing C]
    [Algebra A B] [Algebra A R] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (D : Chapter07IdealDescentData A B R C)
    (E : Chapter07IdealDescentResult D) :
    Nonempty (B ⊗[A] (R ⧸ E.I) ≃ₐ[B] (C ⧸ D.J)) :=
  E.quotient_comparison

theorem chapter07_finitely_generated_stable_ideal_descends
    {A B R C : Type u} [CommRing A] [CommRing B] [CommRing R] [CommRing C]
    [Algebra A B] [Algebra A R] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (D : Chapter07IdealDescentData A B R C)
    (E : Chapter07IdealDescentResult D)
    (hJ : D.J.FG) : E.I.FG := by
  sorry

/- The nilpotence argument is recorded both as the general faithfully-flat statement and as the
base-change instance used by the prose. -/
theorem chapter07_reducedness_descends_of_faithfullyFlat
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (hff : RingHom.FaithfullyFlat (algebraMap A B))
    (hB : IsReduced B) : IsReduced A := by
  sorry

theorem chapter07_faithfully_flat_reflects_zero_after_tensoring
    {A B R : Type u} [CommRing A] [CommRing B] [CommRing R]
    [Algebra A B] [Algebra A R] [Module.FaithfullyFlat A B] (r : R) :
    (1 ⊗ₜ[A] r = 0) ↔ r = 0 := by
  sorry

theorem chapter07_nilpotence_is_reflected_by_faithfully_flat_base_change
    {A B R : Type u} [CommRing A] [CommRing B] [CommRing R]
    [Algebra A B] [Algebra A R] [Module.FaithfullyFlat A B]
    (hbase : IsReduced (B ⊗[A] R)) (r : R) (n : ℕ) (hr : r ^ n = 0) : r = 0 := by
  sorry

theorem chapter07_reducedness_descends_from_base_change
    {A B R : Type u} [CommRing A] [CommRing B] [CommRing R]
    [Algebra A B] [Algebra A R]
    (hff : RingHom.FaithfullyFlat (algebraMap A B))
    (hbase : IsReduced (B ⊗[A] R)) : IsReduced R := by
  sorry

/-- The stronger, all-field-extensions formulation of geometric reducedness used in §7.2. -/
def Chapter07GeometricallyReduced (k R : Type u) [Field k] [CommRing R] [Algebra k R] : Prop :=
  ∀ (K : Type u) [Field K] [Algebra k K], IsReduced (K ⊗[k] R)

theorem chapter07_geometricallyReduced_implies_reduced
    {k R : Type u} [Field k] [CommRing R] [Algebra k R]
    (h : Chapter07GeometricallyReduced k R) : IsReduced R := by
  sorry

/-- A compact witness interface for the inseparable counterexamples to ascent. -/
structure Chapter07InseparableReducednessExample where
  k : Type u
  K : Type u
  R : Type u
  field_k : Field k
  field_K : Field K
  commRing_R : CommRing R
  algebra_k_K :
    letI : Field k := field_k
    letI : Field K := field_K
    Algebra k K
  algebra_k_R :
    letI : Field k := field_k
    letI : CommRing R := commRing_R
    Algebra k R
  not_separable :
    letI : Field k := field_k
    letI : Field K := field_K
    letI : Algebra k K := algebra_k_K
    ¬ Algebra.IsSeparable k K
  reduced :
    letI : Field k := field_k
    letI : CommRing R := commRing_R
    letI : Algebra k R := algebra_k_R
    IsReduced R
  not_reduced_after_inseparable_base_change :
    letI : Field k := field_k
    letI : Field K := field_K
    letI : Algebra k K := algebra_k_K
    letI : CommRing R := commRing_R
    letI : Algebra k R := algebra_k_R
    ¬ IsReduced (K ⊗[k] R)
  not_geometrically_reduced :
    letI : Field k := field_k
    letI : CommRing R := commRing_R
    letI : Algebra k R := algebra_k_R
    ¬ Chapter07GeometricallyReduced k R

/- LOCAL_DEPENDENCY_GUESS: the explicit inseparable field example is deferred to the field-theory
chapter; this existential records the precise non-ascent warning without choosing a presentation. -/
theorem chapter07_reducedness_ascent_fails_for_inseparable_extensions :
    Nonempty Chapter07InseparableReducednessExample := by
  sorry

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter07
