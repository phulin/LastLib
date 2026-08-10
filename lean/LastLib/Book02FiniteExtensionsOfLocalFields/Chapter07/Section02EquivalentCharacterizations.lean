import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07.Section01IsolatingResidueGrowth

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07

open Set
open Polynomial

noncomputable section

/-! # Book 2, Chapter 7, §7.2: equivalent characterizations -/

/-- The extension of a base ideal to the integral-extension ring. -/
def Chapter07ExtendedIdeal
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (m : Ideal A) : Ideal B :=
  Ideal.map (algebraMap A B) m

/-- The ideal-theoretic form of `m_L = m_K B`. -/
def Chapter07MaximalIdealExtension
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (m : Ideal A) (P : Ideal B) : Prop :=
  P = Chapter07ExtendedIdeal A B m

/-- Finite étale is written with the standard Mathlib predicates: finite as a
module and étale as an algebra. -/
def Chapter07FiniteEtaleExtension
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] : Prop :=
  Module.Finite A B ∧ Algebra.Etale A B

/--
The fourth criterion in Theorem 7.1.  The ring hom `res` records the chosen
reduction of coefficients.  Both minimal-polynomial equalities are retained,
so a later proof cannot accidentally replace “the reduction of `g`” by an
arbitrary polynomial with the same degree.
-/
structure Chapter07MonogenicResiduePresentation
    (A B K L k l : Type*) [CommRing A] [CommRing B]
    [Field K] [Field L] [Field k] [Field l]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L]
    [Algebra A L] [Algebra k l]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [FiniteDimensional K L] [FiniteDimensional k l] [Module.Finite A B]
    (P : Ideal B) (res : A →+* k) where
  theta : B
  residueTheta : l
  residueMap : B →+* l
  residue_theta_eq : residueMap theta = residueTheta
  residueMap_compatible :
    residueMap.comp (algebraMap A B) =
      (algebraMap k l).comp res
  residueMap_surjective : Function.Surjective residueMap
  residueMap_kernel : RingHom.ker residueMap = P
  polynomial : A[X]
  polynomial_monic : polynomial.Monic
  generic_minpoly :
    minpoly K (algebraMap B L theta) = polynomial.map (algebraMap A K)
  residue_minpoly :
    minpoly k residueTheta = polynomial.map res
  residue_polynomial_separable : (polynomial.map res).Separable
  unit_derivative :
    IsUnit (eval₂ (algebraMap A B) theta polynomial.derivative)
  residue_generates : Algebra.adjoin k ({residueTheta} : Set l) = ⊤
  ring_generates : Algebra.adjoin A ({theta} : Set B) = ⊤

/-! Theorem 7.1.  The hypotheses identify the abstract profile from §7.1
with one finite normalization branch.  Completeness/henselianity is expressed
by `HenselianLocalRing A`, while the normalization and residue maps remain
explicit interfaces for later proof passes. -/

/-- The five field/ring/residue criteria for an unramified extension. -/
-- STATEMENT_NEEDS_UPDATE: The forward data only constrain the numeric profile and the chosen map A →+* k; they do not supply a residue map B →+* l or the presentation data needed for the Nonempty monogenic clause, nor do they imply Algebra.Etale A B. Add those normalization/presentation hypotheses or weaken the equivalence conclusion.
theorem chapter07_unramified_criteria
    {A B K L k l : Type*} [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] [Field K] [Field L] [Field k] [Field l]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L]
    [Algebra A L] [Algebra k l]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [FiniteDimensional k l]
    [IsIntegralClosure B A L] [HenselianLocalRing A]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Module.Finite A B]
    (E : Chapter07FiniteLocalExtensionData K L k l)
    (m : Ideal A) (P : Ideal B) (res : A →+* k)
    (hm : m = IsLocalRing.maximalIdeal A)
    (hP : P = IsLocalRing.maximalIdeal B)
    (hres_surjective : Function.Surjective res)
    (hres_kernel : RingHom.ker res = m)
    (hE : E.ramificationIndex =
      P.ramificationIdx A)
    (hf : E.residueDegree =
      P.inertiaDeg A) :
    Chapter07UnramifiedExtension E ↔
      (E.ramificationIndex = 1 ∧
          Chapter07ResidueExtensionIsSeparable k l) ∧
        (Chapter07MaximalIdealExtension A B m P ∧
          Chapter07ResidueExtensionIsSeparable k l) ∧
        Nonempty (Chapter07MonogenicResiduePresentation A B K L k l P res) ∧
        Chapter07FiniteEtaleExtension A B := by
  sorry

/-- The monogenic criterion retains the unit-derivative clause explicitly. -/
theorem chapter07_monogenic_presentation_has_unit_derivative
    {A B K L k l : Type*} [CommRing A] [CommRing B]
    [Field K] [Field L] [Field k] [Field l]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L]
    [Algebra A L] [Algebra k l]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [FiniteDimensional K L] [FiniteDimensional k l] [Module.Finite A B]
    {P : Ideal B} {res : A →+* k}
    (p : Chapter07MonogenicResiduePresentation A B K L k l P res) :
    IsUnit (eval₂ (algebraMap A B) p.theta p.polynomial.derivative) := by
  exact p.unit_derivative

/-- The separable-reduction clause is available directly from a monogenic
presentation. -/
theorem chapter07_unit_derivative_presentation_is_separable
    {A B K L k l : Type*} [CommRing A] [CommRing B]
    [Field K] [Field L] [Field k] [Field l]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L]
    [Algebra A L] [Algebra k l]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [FiniteDimensional K L] [FiniteDimensional k l] [Module.Finite A B]
    {P : Ideal B} {res : A →+* k}
    (p : Chapter07MonogenicResiduePresentation A B K L k l P res) :
    (p.polynomial.map res).Separable := by
  exact p.residue_polynomial_separable

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07
