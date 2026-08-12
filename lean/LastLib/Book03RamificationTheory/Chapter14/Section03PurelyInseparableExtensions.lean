import LastLib.Book03RamificationTheory.Chapter14.Core
import LastLib.Book03RamificationTheory.Chapter07.Section04KaehlerDifferentials
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.RingTheory.Finiteness.Nakayama
import Mathlib.RingTheory.LaurentSeries

namespace LastLib.Book03RamificationTheory.Chapter14

noncomputable section

open Polynomial
open scoped BigOperators LaurentSeries Polynomial

/-!
## 14.3. Purely inseparable extensions
-/

def chapter14TracePairing
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : LinearMap.BilinForm K L :=
  LastLib.Book03RamificationTheory.Chapter07.chapter07TracePairing K L

theorem chapter14_trace_pairing_nondegenerate_iff_separable
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l] :
    LastLib.Book03RamificationTheory.Chapter07.chapter07TracePairingNondegenerate l k
        (LastLib.Book03RamificationTheory.Chapter07.chapter07FiniteAlgebraTracePairing k l) ↔
      Algebra.IsSeparable k l := by
  exact LastLib.Book03RamificationTheory.Chapter07.chapter07_field_trace_pairing_nondegenerate_iff_separable
    k l

theorem chapter14_trace_zero_of_not_separable
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (hnot : ¬ Algebra.IsSeparable K L) :
    Algebra.trace K L = 0 := by
  exact Algebra.trace_eq_zero_of_not_isSeparable hnot

theorem chapter14_purely_inseparable_trace_zero
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (_hpure : IsPurelyInseparable K L)
    (hnot : ¬ Algebra.IsSeparable K L) :
    Algebra.trace K L = 0 := by
  exact chapter14_trace_zero_of_not_separable hnot

/- A nontrivial purely inseparable element can have a minimal polynomial with
zero derivative.  The conclusion is separated from the stronger assertion
that every element has this property, which would be false for base elements. -/
def chapter14ZeroDerivativeMinimalPolynomial
    (K L : Type*) [Field K] [Field L] [Algebra K L] (x : L) : Prop :=
  (minpoly K x).derivative = 0

theorem chapter14_purely_inseparable_has_zero_derivative_element
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (hpure : IsPurelyInseparable K L)
    (hnot : ¬ Algebra.IsSeparable K L) :
    ∃ x : L, chapter14ZeroDerivativeMinimalPolynomial K L x := by
  sorry

/- The classical complementary-module/different construction is therefore
guarded by separability.  Kähler differentials remain available without that
guard. -/
def chapter14SeparableTraceDifferentBoundary
    (K L : Type*) [Field K] [Field L] [Algebra K L] : Prop :=
  Algebra.IsSeparable K L

def chapter14ClassicalArtinSwanDomain
    (K L : Type*) [Field K] [Field L] [Algebra K L] : Prop :=
  IsGalois K L

theorem chapter14_nontrivial_purely_inseparable_has_no_galois_symmetry
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsPurelyInseparable K L]
    (hdegree : Module.finrank K L ≠ 1) :
    ¬ IsGalois K L := by
  intro hgalois
  exact hdegree
    (@LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.purely_inseparable_galois_extension_is_trivial
      K L _ _ _ _ _ hgalois)

theorem chapter14_e_one_does_not_imply_unramified
    (residueSeparable : Prop) (hnot : ¬ residueSeparable) :
    ¬(1 = 1 ∧ residueSeparable) := by
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.ramification_index_one_without_separable_residue_is_not_unramified
    residueSeparable hnot

abbrev chapter14KaehlerDifferential
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] :=
  KaehlerDifferential A B

theorem chapter14_kaehler_differentials_vanish_of_surjective
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (hsurj : Function.Surjective (algebraMap A B)) :
    Subsingleton (KaehlerDifferential A B) := by
  exact KaehlerDifferential.subsingleton_of_surjective A B hsurj

/- SOURCE_ISSUE: The source says, “Valuation theory still supplies $e$, $f$,
and $[L:K]=ef$ for finite extensions of complete discretely valued fields.”
Completeness and discreteness alone do not exclude defect over an imperfect
residue field, so the displayed equality is false without a defectless
hypothesis.  The minimal principled correction is a perfect base residue
field (or an explicit defectless assumption). -/
structure Chapter14DefectlessDegreeProfile where
  degree : ℕ
  ramificationIndex : ℕ
  residueDegree : ℕ
  defectless : Prop
  degree_eq_ef : defectless → degree = ramificationIndex * residueDegree

theorem chapter14_defectless_degree_profile_formula
    (p : Chapter14DefectlessDegreeProfile) (h : p.defectless) :
    p.degree = p.ramificationIndex * p.residueDegree :=
  p.degree_eq_ef h

/- The concrete imperfect-residue model uses the canonical Laurent-series
uniformizer and records both the residue polynomial and its lifted equation. -/
abbrev chapter14LaurentSeries (k : Type*) [Field k] : Type _ := LaurentSeries k

noncomputable def chapter14ImperfectResiduePolynomial
    (k : Type*) [Field k] (p : ℕ) (a : k) : k[X] :=
  X ^ p - C a

noncomputable def chapter14ImperfectLaurentPolynomial
    (k : Type*) [Field k] (p : ℕ) (a : k) :
    (chapter14LaurentSeries k)[X] :=
  X ^ p + C (LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.laurentSeriesUniformizer k) * X -
    C (algebraMap k (chapter14LaurentSeries k) a)

theorem chapter14_imperfect_residue_polynomial_irreducible
    (k : Type*) [Field k] (p : ℕ) (hp : p.Prime) (a : k)
    (ha : a ∉ Set.range (fun x : k => x ^ p)) :
    Irreducible (chapter14ImperfectResiduePolynomial k p a) := by
  apply X_pow_sub_C_irreducible_of_prime hp
  intro b hb
  exact ha ⟨b, hb⟩

theorem chapter14_imperfect_laurent_polynomial_irreducible
    (k : Type*) [Field k] (p : ℕ) (hp : p.Prime) (a : k)
    (ha : a ∉ Set.range (fun x : k => x ^ p)) :
    Irreducible (chapter14ImperfectLaurentPolynomial k p a) := by
  sorry

theorem chapter14_imperfect_residue_polynomial_derivative_zero
    (k : Type*) [Field k] (p : ℕ) (a : k) [CharP k p] :
    (chapter14ImperfectResiduePolynomial k p a).derivative = 0 := by
  sorry

def chapter14PurelyInseparablePolynomial
    {k : Type*} [Field k] (f : k[X]) : Prop :=
  Irreducible f ∧ f.derivative = 0

theorem chapter14_imperfect_residue_polynomial_is_purely_inseparable
    (k : Type*) [Field k] (p : ℕ) (hp : p.Prime) (a : k)
    (ha : a ∉ Set.range (fun x : k => x ^ p)) [CharP k p] :
    chapter14PurelyInseparablePolynomial
      (chapter14ImperfectResiduePolynomial k p a) := by
  exact ⟨chapter14_imperfect_residue_polynomial_irreducible k p hp a ha,
    chapter14_imperfect_residue_polynomial_derivative_zero k p a⟩

theorem chapter14_imperfect_laurent_polynomial_derivative
    (k : Type*) [Field k] (p : ℕ) (hp : p.Prime) (a : k) [CharP k p] :
    (chapter14ImperfectLaurentPolynomial k p a).derivative =
      C (LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.laurentSeriesUniformizer k) := by
  sorry

theorem chapter14_imperfect_laurent_polynomial_derivative_ne_zero
    (k : Type*) [Field k] (p : ℕ) (a : k) [CharP k p]
    (ht : LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.laurentSeriesUniformizer k ≠ 0) :
    (chapter14ImperfectLaurentPolynomial k p a).derivative ≠ 0 := by
  sorry

theorem chapter14_imperfect_laurent_polynomial_separable
    (k : Type*) [Field k] (p : ℕ) (hp : p.Prime) (a : k)
    (ha : a ∉ Set.range (fun x : k => x ^ p)) [CharP k p] :
    (chapter14ImperfectLaurentPolynomial k p a).Separable := by
  sorry

/- Reduction of the lifted equation is the irreducible purely inseparable
polynomial `X^p-a`; the following predicate keeps the reduction isomorphism
and the Nakayama step explicit rather than hiding them in `B = A[α]`. -/
def chapter14OrderReductionIsomorphism
    (C : Type*) (D : Type*) [CommRing C] [CommRing D]
    (I : Ideal C) (J : Ideal D) : Prop :=
  Nonempty ((C ⧸ I) ≃+* (D ⧸ J))

def chapter14NakayamaGenerationCondition
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (C : Subalgebra A B) (t : A) : Prop :=
  ∀ x : B, ∃ c : C, ∃ y : B,
    x = (c : B) + algebraMap A B t * y

theorem chapter14_reduction_isomorphism_implies_nakayama_condition
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (C : Subalgebra A B) (I : Ideal C) (J : Ideal B)
    (t : A)
    (hquot : chapter14OrderReductionIsomorphism C B I J)
    (hcompat : ∀ x : B, ∃ c : C, ∃ y : B,
      x - (c : B) = algebraMap A B t * y) :
    chapter14NakayamaGenerationCondition A B C t := by
  sorry

theorem chapter14_nakayama_generates_order
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] (C : Subalgebra A B)
    [Module.Finite A (B ⧸ C.toSubmodule)] (t : A)
    (ht : t ∈ IsLocalRing.maximalIdeal A)
    (hgen : chapter14NakayamaGenerationCondition A B C t) :
    C = ⊤ := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the full explicit example is a source-facing profile.
Its fields expose
the root equation, residue generator, order generation, and the numerical and
different conclusions without pretending that the imperfect residue is
unramified. -/
structure Chapter14ImperfectResidueExample
    (k L l A B : Type*) [Field k] [Field L] [Field l]
    [CommRing A] [CommRing B]
    [Algebra k l] [Algebra (chapter14LaurentSeries k) L]
    [Algebra A B] [Algebra A (chapter14LaurentSeries k)] [Algebra B L]
    [Algebra A L] [IsScalarTower A (chapter14LaurentSeries k) L]
    [IsScalarTower A B L] where
  p : ℕ
  prime : p.Prime
  characteristic : CharP k p
  a : k
  a_not_pth_power : a ∉ Set.range (fun x : k => x ^ p)
  alpha : L
  root_equation :
    alpha ^ p +
        algebraMap (chapter14LaurentSeries k) L
          (LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.laurentSeriesUniformizer k) * alpha -
      algebraMap (chapter14LaurentSeries k) L
        (algebraMap k (chapter14LaurentSeries k) a) = 0
  field_degree : Module.finrank (chapter14LaurentSeries k) L = p
  residue_alpha : l
  residue_alpha_pow : residue_alpha ^ p = algebraMap k l a
  residue_generator : Algebra.adjoin k ({residue_alpha} : Set l) = ⊤
  residue_purely_inseparable : IsPurelyInseparable k l
  residue_degree : Module.finrank k l = p
  ramificationIndex : ℕ
  ramificationIndex_eq_one : ramificationIndex = 1
  order_generator : B
  order_eq_adjoin : Algebra.adjoin A ({order_generator} : Set B) = ⊤
  order_finite : Module.Finite A B
  uniformizer : A
  uniformizer_maps_to_t :
    algebraMap A (chapter14LaurentSeries k) uniformizer =
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.laurentSeriesUniformizer k
  different : Ideal B
  different_eq_uniformizer :
    different = Ideal.span ({algebraMap A B uniformizer} : Set B)
  differentExponent : ℕ
  differentExponent_eq_one : differentExponent = 1
  residueDegree : ℕ
  residueDegree_eq_p : residueDegree = p
  discriminantExponent : ℕ
  discriminantExponent_eq_p : discriminantExponent = p
  degree_eq_ef :
    Module.finrank (chapter14LaurentSeries k) L = ramificationIndex * residueDegree
  discriminant_eq_residue_mul_different :
    discriminantExponent = residueDegree * differentExponent

theorem chapter14_imperfect_example_numerical_profile
    {k L l A B : Type*} [Field k] [Field L] [Field l]
    [CommRing A] [CommRing B]
    [Algebra k l] [Algebra (chapter14LaurentSeries k) L]
    [Algebra A B] [Algebra A (chapter14LaurentSeries k)] [Algebra B L]
    [Algebra A L] [IsScalarTower A (chapter14LaurentSeries k) L]
    [IsScalarTower A B L]
    (E : Chapter14ImperfectResidueExample k L l A B) :
    E.ramificationIndex = 1 ∧ E.residueDegree = E.p ∧
      E.differentExponent = 1 ∧ E.discriminantExponent = E.p := by
  exact ⟨E.ramificationIndex_eq_one, E.residueDegree_eq_p,
    E.differentExponent_eq_one, E.discriminantExponent_eq_p⟩

theorem chapter14_prime_degree_forces_e_one_f_p
    (p e f : ℕ) (hp : p.Prime) (he : 0 < e) (hf : 0 < f)
    (hdegree : p = e * f) : e = 1 ∧ f = p := by
  sorry

theorem chapter14_imperfect_discriminant_profile
    {k L l A B : Type*} [Field k] [Field L] [Field l]
    [CommRing A] [CommRing B]
    [Algebra k l] [Algebra (chapter14LaurentSeries k) L]
    [Algebra A B] [Algebra A (chapter14LaurentSeries k)] [Algebra B L]
    [Algebra A L] [IsScalarTower A (chapter14LaurentSeries k) L]
    [IsScalarTower A B L]
    (E : Chapter14ImperfectResidueExample k L l A B) :
    E.discriminantExponent = E.residueDegree * E.differentExponent := by
  exact E.discriminant_eq_residue_mul_different

end
end LastLib.Book03RamificationTheory.Chapter14
