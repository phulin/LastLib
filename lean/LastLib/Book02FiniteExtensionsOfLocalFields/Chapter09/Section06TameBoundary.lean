import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.Section08PrimeToP_RadicalExtensions
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.Section03CleanDecomposition

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09

open scoped BigOperators Polynomial
open Ideal IsLocalRing Polynomial

noncomputable section

/-! ## Book 2, Chapter 9.6: the tame boundary -/

/-- Tameness at the exponential characteristic of the residue field.  The
use of coprimality makes the characteristic-zero case automatic because
ringExpChar is one there. -/
-- SOURCE_ISSUE: Over an imperfect residue field, coprimality of `e` and the
-- residue characteristic does not by itself exclude finite defect, so the
-- source's extension-level use of “tamely ramified” needs a defectless (or
-- perfect-residue) hypothesis.  This predicate intentionally records only
-- the numerical prime-to-`p` condition stated in the section.
def chapter09Tame (k : Type*) [Ring k] (e : ℕ) : Prop :=
  Nat.Coprime e (ringExpChar k)

/-- Wild ramification in the separable-residue setting. -/
def chapter09Wild (k : Type*) [Ring k] (e : ℕ)
    (residueSeparable : Prop) : Prop :=
  residueSeparable ∧ ¬ chapter09Tame k e

/-- In residue characteristic zero the characteristic exponent is one, so
every ramification index is tame. -/
theorem chapter09_char_zero_is_tame
    (k : Type*) [Ring k] [CharZero k] (e : ℕ) :
    chapter09Tame k e := by
  simp [chapter09Tame]

/-- For a finite separable residue extension and a supplied ramification index,
the index is either tame or wild. -/
theorem chapter09_tame_or_wild
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l]
    (e : ℕ) (hseparable : Algebra.IsSeparable k l) :
    chapter09Tame k e ∨ chapter09Wild k e (Algebra.IsSeparable k l) := by
  by_cases ht : chapter09Tame k e
  · exact Or.inl ht
  · exact Or.inr ⟨hseparable, ht⟩

/-- A characteristic-exponent form of the wild condition.  The hypothesis
that p is the positive residue characteristic is kept explicit, so no
characteristic-zero assertion is silently treated as wild. -/
theorem chapter09_wild_iff_prime_dvd
    (k : Type*) [Field k] (p e : ℕ) [Fact p.Prime] [CharP k p]
    (hchar : ringExpChar k = p) :
    (¬ chapter09Tame k e) ↔ p ∣ e := by
  have hp : p.Prime := Fact.out
  simpa [chapter09Tame, hchar, Nat.coprime_comm] using
    (hp.dvd_iff_not_coprime (n := e)).symm

/-- Replacing an inertia subgroup by its cardinality preserves the tame
criterion.  This is the bridge from the numerical definition to the finite
Galois statement about inertia. -/
theorem chapter09_tame_iff_inertia_order_coprime
    (k G : Type*) [Ring k] [Group G] [Finite G]
    (e : ℕ) (I : Subgroup G) (hI : Nat.card I = e) :
    chapter09Tame k e ↔ Nat.Coprime (Nat.card I) (ringExpChar k) := by
  simp [chapter09Tame, hI]

/-- Finite-Galois ramification data over a perfect residue field. -/
structure Chapter09FiniteGaloisRamificationData
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsLocalHom (algebraMap A B)] [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [Module.Finite A B] [Module.IsTorsionFree A B]
    [FaithfulSMul A B] [IsIntegralClosure B A L]
    [Module.Finite (chapter09BaseResidueField A)
      (chapter09ExtensionResidueField B)]
    [Chapter09FiniteLocalExtension A B K L] [IsGalois K L]
    [PerfectField (chapter09BaseResidueField A)]
    [Finite (L ≃ₐ[K] L)] where
  inertia : Subgroup (L ≃ₐ[K] L)
  inertia_order : Nat.card inertia =
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex A B
      (IsLocalRing.maximalIdeal B)
  residue_action : Chapter09ResidueActionData A B K L
  inertia_eq_kernel : inertia =
    MonoidHom.ker residue_action.action

/-- The finite-Galois perfect-residue theorem records the inertia order and
the residue action; the chapter introduces no wild-inertia filtration. -/
theorem chapter09_finite_galois_inertia_order
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsLocalHom (algebraMap A B)] [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [Module.Finite A B] [Module.IsTorsionFree A B]
    [FaithfulSMul A B] [IsIntegralClosure B A L]
    [Module.Finite (chapter09BaseResidueField A)
      (chapter09ExtensionResidueField B)]
    [Chapter09FiniteLocalExtension A B K L] [IsGalois K L]
    [PerfectField (chapter09BaseResidueField A)]
    [Finite (L ≃ₐ[K] L)] :
    Nonempty (Chapter09FiniteGaloisRamificationData A B K L) := by
  sorry

/-- A post-base-change Kummer presentation for the ramified stage.  The
coefficient ring is the valuation ring after adjoining the needed roots of
unity or making the suitable unramified base change; an integral-model
package is needed to state the corresponding total-ramification predicate. -/
structure Chapter09TameKummerPresentation
    (A K L : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Field L]
    [Algebra A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsFractionRing A K]
    [FiniteDimensional K L]
    (e : ℕ) (π : A) where
  tame : chapter09Tame (chapter09BaseResidueField A) e
  positive : 0 < e
  roots_of_unity : ∃ ζ : K, IsPrimitiveRoot ζ e
  uniformizer :
    Ideal.span ({π} : Set A) = IsLocalRing.maximalIdeal A
  alpha : L
  alpha_pow_eq_uniformizer : alpha ^ e = algebraMap A L π
  generates : Algebra.adjoin K ({alpha} : Set L) = ⊤
  degree : Module.finrank K L = e

/- The chapter deliberately stops before introducing higher ramification
filtrations, jumps, wild inertia subgroups, different ideals, or discriminants. -/

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09
