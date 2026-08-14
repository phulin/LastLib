import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter07.Section01DescentOfAlgebraStructures
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.RatFunc.Valuation
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.TensorProduct.Basis

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter07

open CategoryTheory
open scoped Polynomial TensorProduct

universe u

/-- Stability of an ideal under the actual overlap coaction of an algebra descent datum. -/
def chapter07IdealSubmodule
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (D : Chapter07AlgebraDescentData A B C) (J : Ideal C) :
    Submodule B D.moduleDatum.A :=
  ((J : Submodule C C).restrictScalars B).comap D.carrier.hom.hom

/- This is the effective submodule form of overlap stability: it says that the ideal pulled back
to the datum's ambient module is the image of a sub-datum. -/
structure Chapter07StableIdeal
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (D : Chapter07AlgebraDescentData A B C) (J : Ideal C) where
  stable :
    ∃ E : Chapter07ModuleDescentDatum A B,
      ∃ e : E.A ≅ ModuleCat.of B (chapter07IdealSubmodule D J),
        ∃ i : E ⟶ D.moduleDatum,
          e.hom ≫ ModuleCat.ofHom (chapter07IdealSubmodule D J).subtype = i.f

@[ext]
theorem Chapter07StableIdeal.ext
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    {D : Chapter07AlgebraDescentData A B C} {J : Ideal C}
    (x y : Chapter07StableIdeal D J) : x = y := by
  cases x
  cases y
  rfl

/-- The algebra and ideal data needed for quotient descent. -/
structure Chapter07IdealDescentData
    (A B R C : Type u) [CommRing A] [CommRing B] [CommRing R] [CommRing C]
    [Algebra A B] [Algebra A R] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    where
  algebraDescent : Chapter07AlgebraDescentData A B C
  base_change : B ⊗[A] R ≃ₐ[B] C
  base_change_compatible :
    Chapter07ComparisonCompatible algebraDescent base_change
  J : Ideal C
  stable : Chapter07StableIdeal algebraDescent J

/-- The descended ideal and the quotient comparison isomorphism. -/
structure Chapter07IdealDescentResult
    {A B R C : Type u} [CommRing A] [CommRing B] [CommRing R] [CommRing C]
    [Algebra A B] [Algebra A R] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  (D : Chapter07IdealDescentData A B R C) where
  I : Ideal R
  /-- The descended ideal agrees with the base change of `I` under the specified
  algebra comparison.  Without this compatibility, an abstract isomorphism of
  quotient algebras does not say that `I` descends from `D.J`. -/
  ideal_compatibility :
      Ideal.map
        (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := R)).toRingHom I =
      Ideal.map (D.base_change.symm.toRingHom : C →+* (B ⊗[A] R)) D.J
  quotient_comparison : B ⊗[A] (R ⧸ I) ≃ₐ[B] (C ⧸ D.J)
  /-- The quotient comparison is induced by the specified base-change comparison. -/
  quotient_comparison_commutes :
    ∀ (b : B) (r : R),
      quotient_comparison (b ⊗ₜ[A] (Ideal.Quotient.mk I r)) =
        Ideal.Quotient.mk D.J (D.base_change (b ⊗ₜ[A] r))

theorem chapter07_stable_ideal_descends
    {A B R C : Type u} [CommRing A] [CommRing B] [CommRing R] [CommRing C]
    [Algebra A B] [Algebra A R] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (D : Chapter07IdealDescentData A B R C)
    (hff : RingHom.FaithfullyFlat (algebraMap A B)) :
    Nonempty (Chapter07IdealDescentResult D) := by
  sorry

theorem chapter07_stable_ideal_descends_unique
    {A B R C : Type u} [CommRing A] [CommRing B] [CommRing R] [CommRing C]
    [Algebra A B] [Algebra A R] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (D : Chapter07IdealDescentData A B R C)
    (hff : RingHom.FaithfullyFlat (algebraMap A B))
    (E E' : Chapter07IdealDescentResult D) : E.I = E'.I := by
  let _ : Module.FaithfullyFlat A B :=
    (RingHom.faithfullyFlat_algebraMap_iff).mp hff
  let _ : Module.FaithfullyFlat R (R ⊗[A] B) := inferInstance
  let _ : Algebra R (B ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
  let _ : Module.FaithfullyFlat R (B ⊗[A] R) :=
    Module.FaithfullyFlat.of_linearEquiv
      R (R ⊗[A] B) (Algebra.TensorProduct.commRight A R B).symm.toLinearEquiv
  apply Ideal.map_injective_of_faithfullyFlat (A := R) (B := B ⊗[A] R)
  rw [show algebraMap R (B ⊗[A] R) =
      (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := R)).toRingHom by rfl]
  rw [E.ideal_compatibility, E'.ideal_compatibility]

def chapter07_quotient_base_change
    {A B R C : Type u} [CommRing A] [CommRing B] [CommRing R] [CommRing C]
    [Algebra A B] [Algebra A R] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (D : Chapter07IdealDescentData A B R C)
    (E : Chapter07IdealDescentResult D) :
    B ⊗[A] (R ⧸ E.I) ≃ₐ[B] (C ⧸ D.J) :=
  E.quotient_comparison

theorem chapter07_quotient_base_change_commutes
    {A B R C : Type u} [CommRing A] [CommRing B] [CommRing R] [CommRing C]
    [Algebra A B] [Algebra A R] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (D : Chapter07IdealDescentData A B R C)
    (E : Chapter07IdealDescentResult D) (b : B) (r : R) :
    E.quotient_comparison (b ⊗ₜ[A] (Ideal.Quotient.mk E.I r)) =
      Ideal.Quotient.mk D.J (D.base_change (b ⊗ₜ[A] r)) := by
  exact E.quotient_comparison_commutes b r

theorem chapter07_finitely_generated_stable_ideal_descends
    {A B R C : Type u} [CommRing A] [CommRing B] [CommRing R] [CommRing C]
    [Algebra A B] [Algebra A R] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (D : Chapter07IdealDescentData A B R C)
    (E : Chapter07IdealDescentResult D)
    (hff : RingHom.FaithfullyFlat (algebraMap A B))
    (hJ : D.J.FG) : E.I.FG := by
  let _ : Module.FaithfullyFlat A B :=
    (RingHom.faithfullyFlat_algebraMap_iff).mp hff
  let _ : Module.FaithfullyFlat R (R ⊗[A] B) := inferInstance
  let _ : Algebra R (B ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
  let _ : Module.FaithfullyFlat R (B ⊗[A] R) :=
    Module.FaithfullyFlat.of_linearEquiv
      R (R ⊗[A] B) (Algebra.TensorProduct.commRight A R B).symm.toLinearEquiv
  apply Ideal.FG.of_FG_map_of_faithfullyFlat (R := R) (S := B ⊗[A] R)
  rw [show algebraMap R (B ⊗[A] R) =
      (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := R)).toRingHom by rfl]
  rw [E.ideal_compatibility]
  exact hJ.map _

/- The nilpotence argument is recorded both as the general faithfully-flat statement and as the
base-change instance used by the prose. -/
theorem chapter07_reducedness_descends_of_faithfullyFlat
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (hff : RingHom.FaithfullyFlat (algebraMap A B))
    (hB : IsReduced B) : IsReduced A := by
  let _ : IsReduced B := hB
  exact isReduced_of_injective (algebraMap A B) hff.injective

theorem chapter07_faithfully_flat_reflects_zero_after_tensoring
    {A B R : Type u} [CommRing A] [CommRing B] [CommRing R]
    [Algebra A B] [Algebra A R] [Module.FaithfullyFlat A B] (r : R) :
    ((1 : B) ⊗ₜ[A] r = 0) ↔ r = 0 := by
  exact Module.FaithfullyFlat.one_tmul_eq_zero_iff A R r

theorem chapter07_nilpotence_is_reflected_by_faithfully_flat_base_change
    {A B R : Type u} [CommRing A] [CommRing B] [CommRing R]
    [Algebra A B] [Algebra A R] [Module.FaithfullyFlat A B]
    (hbase : IsReduced (B ⊗[A] R)) (r : R) (n : ℕ) (hr : r ^ n = 0) : r = 0 := by
  apply (chapter07_faithfully_flat_reflects_zero_after_tensoring (A := A) (B := B) r).mp
  apply hbase.eq_zero
  refine ⟨n, ?_⟩
  rw [Algebra.TensorProduct.tmul_pow, one_pow, hr, TensorProduct.tmul_zero]

theorem chapter07_reducedness_descends_from_base_change
    {A B R : Type u} [CommRing A] [CommRing B] [CommRing R]
    [Algebra A B] [Algebra A R]
    (hff : RingHom.FaithfullyFlat (algebraMap A B))
    (hbase : IsReduced (B ⊗[A] R)) : IsReduced R := by
  let _ : Module.FaithfullyFlat A B :=
    (RingHom.faithfullyFlat_algebraMap_iff).mp hff
  constructor
  intro r ⟨n, hr⟩
  exact chapter07_nilpotence_is_reflected_by_faithfully_flat_base_change hbase r n hr

/-- The canonical algebraic-closure formulation of geometric reducedness used in §7.2. -/
def Chapter07GeometricallyReduced (k R : Type u) [Field k] [CommRing R] [Algebra k R] : Prop :=
  Algebra.IsGeometricallyReduced k R

theorem chapter07_geometricallyReduced_implies_reduced
    {k R : Type u} [Field k] [CommRing R] [Algebra k R]
    (h : Chapter07GeometricallyReduced k R) : IsReduced R := by
  exact @Algebra.isReduced_of_isGeometricallyReduced k R _ _ _ h

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
  algebraic :
    letI : Field k := field_k
    letI : Field K := field_K
    letI : Algebra k K := algebra_k_K
    Algebra.IsAlgebraic k K
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

private instance chapter07_fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private theorem chapter07_ratFunc_two_no_square :
    ∀ b : RatFunc (ZMod 2), b ^ 2 ≠ RatFunc.X := by sorry

private theorem chapter07_adjoinRoot_not_separable
    {k : Type u} [Field k] {f : k[X]} [Fact (Irreducible f)]
    (hfmonic : f.Monic) (hderiv : Polynomial.derivative f = 0) :
    ¬ Algebra.IsSeparable k (AdjoinRoot f) := by sorry

private theorem chapter07_ratFunc_two_polynomial_data :
    (Polynomial.X ^ 2 - Polynomial.C (RatFunc.X : RatFunc (ZMod 2))).Monic ∧
      Polynomial.derivative
          (Polynomial.X ^ 2 - Polynomial.C (RatFunc.X : RatFunc (ZMod 2))) = 0 := by sorry

private theorem chapter07_adjoinRoot_algebraic
    {k : Type u} [Field k] {f : k[X]} [Fact (Irreducible f)]
    (hfmonic : f.Monic) : Algebra.IsAlgebraic k (AdjoinRoot f) := by sorry

private theorem chapter07_tensor_root_difference_not_reduced
    {k : Type u} [Field k] {f : k[X]} [Fact (Irreducible f)] {a : k}
    (hfmonic : f.Monic) (hnat : f.natDegree = 2)
    (hroot : (AdjoinRoot.root f) ^ 2 = algebraMap k (AdjoinRoot f) a)
    (hchar : (2 : k) = 0) (hroot_ne_zero : AdjoinRoot.root f ≠ 0) :
    ¬ IsReduced (AdjoinRoot f ⊗[k] AdjoinRoot f) := by sorry

theorem chapter07_reducedness_ascent_fails_for_inseparable_extensions :
    Nonempty Chapter07InseparableReducednessExample := by sorry

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter07
