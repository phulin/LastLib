import LastLib.Book03RamificationTheory.Chapter14.Core
import LastLib.Book03RamificationTheory.Chapter07.Section03TheDerivativeFormula
import LastLib.Book03RamificationTheory.Chapter12.Section03TowersAndTransitivity

namespace LastLib.Book03RamificationTheory.Chapter14

noncomputable section

open Polynomial
open scoped BigOperators Polynomial nonZeroDivisors

/-!
## 14.1. What remains intrinsic without Galois symmetry
-/

/- The complementary module and different are the canonical trace-dual and
inverse-trace-dual objects from Chapter 7. -/
def chapter14ComplementaryModule
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] : Submodule B L :=
  LastLib.Book03RamificationTheory.Chapter07.chapter07Codifferent A B K L

noncomputable def chapter14DifferentIdeal
    (A B : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [Algebra A B] [IsDedekindDomain B] [Module.IsTorsionFree A B] : Ideal B :=
  LastLib.Book03RamificationTheory.Chapter07.chapter07DifferentIdeal A B

noncomputable def chapter14DifferentFractionalIdeal
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDedekindDomain B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra K L]
    [Algebra B L] [Algebra A L] [IsScalarTower A K L]
    [IsScalarTower A B L] [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsIntegralClosure B A L] [IsIntegrallyClosed A]
    [Module.IsTorsionFree A B] : FractionalIdeal B⁰ L :=
  LastLib.Book03RamificationTheory.Chapter07.chapter07DifferentFractionalIdeal A B K L

/- LOCAL_DEPENDENCY_GUESS: the preceding chapters expose the relative field
discriminant as an ideal-valued invariant, but not yet under a stable Chapter
14 name.  Keeping its codomain explicit avoids conflating it with a model
discriminant or with the different upstairs. -/
abbrev Chapter14FieldDiscriminant (A : Type*) [Semiring A] := Ideal A

structure Chapter14IntrinsicValuationExtension
    (K L Γ : Type*) [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ] where
  baseValuation : Valuation K Γ
  extensionValuation : Valuation L Γ
  unique_extension :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05UniqueValuationExtension
      baseValuation extensionValuation

structure Chapter14IntrinsicLocalExtension
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] where
  numbers : Chapter14LocalExtensionNumbers
  discriminant : Chapter14FieldDiscriminant A

theorem chapter14_intrinsic_different_is_chapter07_different
    (A B : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [Algebra A B] [IsDedekindDomain B] [Module.IsTorsionFree A B] :
    chapter14DifferentIdeal A B =
      LastLib.Book03RamificationTheory.Chapter07.chapter07DifferentIdeal A B :=
  rfl

noncomputable def chapter14DifferentExponent
    {B : Type*} [CommRing B] (mB D : Ideal B)
    (hD : ∃! d : ℕ, D = mB ^ d) : ℕ :=
  LastLib.Book03RamificationTheory.Chapter07.chapter07DifferentExponent mB D hD

theorem chapter14DifferentExponent_spec
    {B : Type*} [CommRing B] (mB D : Ideal B)
    (hD : ∃! d : ℕ, D = mB ^ d) :
    D = mB ^ chapter14DifferentExponent mB D hD := by
  exact LastLib.Book03RamificationTheory.Chapter07.chapter07DifferentExponent_spec
    mB D hD

/- The derivative construction is available exactly under the monogenic and
separable hypotheses used by Chapter 7. -/
theorem chapter14_monogenic_different_eq_derivative_ideal
    (A B K L : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDedekindDomain B]
    [IsDiscreteValuationRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B]
    (α : B) (f : A[X])
    (hmono : LastLib.Book03RamificationTheory.Chapter07.chapter07MonogenicPresentation
      A B K L α f) :
    chapter14DifferentIdeal A B =
      Ideal.span ({LastLib.Book03RamificationTheory.Chapter07.chapter07DerivativeAt
        A B f α} : Set B) := by
  exact LastLib.Book03RamificationTheory.Chapter07.chapter07_different_eq_derivative_ideal
    A B K L α f hmono

theorem chapter14_monogenic_codifferent_eq_inverse_derivative_principal
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDedekindDomain B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra K L]
    [Algebra B L] [Algebra A L] [IsScalarTower A K L]
    [IsScalarTower A B L] [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsIntegralClosure B A L] [IsIntegrallyClosed A]
    (α : B) (f : A[X])
    (hmono : LastLib.Book03RamificationTheory.Chapter07.chapter07MonogenicPresentation
      A B K L α f) :
    (chapter14ComplementaryModule A B K L : Set L) =
      LastLib.Book03RamificationTheory.Chapter07.chapter07InversePrincipalSet
        A B K L
        (LastLib.Book03RamificationTheory.Chapter07.chapter07DerivativeAt A B f α) := by
  sorry

/- The numerical tower API is inherited without changing conventions. -/
abbrev Chapter14TowerNumericalData :=
  LastLib.Book03RamificationTheory.Chapter12.Chapter12TowerNumericalData

theorem chapter14_tower_different_transitivity
    (T : Chapter14TowerNumericalData) :
    T.topOverBase.differentExponent =
      T.topOverMiddle.differentExponent +
        T.topOverMiddle.ramificationIndex * T.middleOverBase.differentExponent :=
  T.different_transitivity

theorem chapter14_tower_discriminant_exponent_expansion
    (T : Chapter14TowerNumericalData) :
    T.topOverBase.discriminantExponent =
      T.middleOverBase.discriminantExponent * T.topOverMiddle.degree +
        T.middleOverBase.residueDegree * T.topOverMiddle.discriminantExponent := by
  exact LastLib.Book03RamificationTheory.Chapter12.chapter12_tower_discriminant_exponent_expansion T

theorem chapter14_tower_degree_multiplication
    (T : Chapter14TowerNumericalData) :
    T.topOverBase.degree = T.topOverMiddle.degree * T.middleOverBase.degree :=
  T.degree_mul

/- The hypothesis of residue separability is kept visible at the tame
boundary.  The closure equivalence itself is postponed to the permutation
interface in §14.2. -/
def chapter14TameClosureData (baseTame closureTame : Prop) : Prop :=
  chapter14TameClosureEquivalence baseTame closureTame

@[simp] theorem chapter14TameClosureData_iff
    (baseTame closureTame : Prop) :
    chapter14TameClosureData baseTame closureTame ↔
      (baseTame ↔ closureTame) :=
  Iff.rfl

end
end LastLib.Book03RamificationTheory.Chapter14
