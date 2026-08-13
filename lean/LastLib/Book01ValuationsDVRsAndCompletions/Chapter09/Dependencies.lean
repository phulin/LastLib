import LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.Section03LiftingFactorizations
namespace LastLib.Book01ValuationsDVRsAndCompletions
namespace Chapter09

open scoped Polynomial
open Ideal IsLocalRing Polynomial

noncomputable section

/-! Shared Chapter 9 interfaces.

The book uses coprime factorization lifting as its primary definition of
henselianity.  Mathlib's `HenselianLocalRing` class is the simple-root form.
The easy implication from the book's definition to Mathlib's interface is
proved in Section 9.4; the converse is deliberately not an early dependency.
-/

/-- The simple-residue-root lifting property. -/
def SimpleResidueRootLiftingProperty (A : Type*) [CommRing A] [IsLocalRing A] : Prop :=
  ∀ (f : A[X]) (a₀ : ResidueRing A), f.Monic →
    (residuePolynomial f).eval a₀ = 0 →
    IsUnit ((residuePolynomial f).derivative.eval a₀) →
    ∃! a : A, f.eval a = 0 ∧ residueClass a = a₀

/-- The coprime-factorization lifting property. -/
def HenselianFactorizationProperty (A : Type*) [CommRing A] [IsLocalRing A] : Prop :=
  ∀ (f : A[X]) (g₀ h₀ : Polynomial (ResidueRing A)), f.Monic →
    g₀.Monic → h₀.Monic → IsCoprime g₀ h₀ → residuePolynomial f = g₀ * h₀ →
    ∃! gh : A[X] × A[X], IsFactorizationLift f g₀ h₀ gh.1 gh.2

/-! This is the chapter's primary henselian predicate.  Keeping a separate
name makes theorem statements readable without identifying it with Mathlib's
strictly weaker API prematurely. -/
abbrev IsHenselianLocalRingChapter09 (A : Type*) [CommRing A] [IsLocalRing A] : Prop :=
  HenselianFactorizationProperty A

/-- Complete and separated maximal-ideal-adic local rings. -/
def IsMaximalIdealAdicallyCompleteSeparated (A : Type*) [CommRing A] [IsLocalRing A] : Prop :=
  IsAdicComplete (IsLocalRing.maximalIdeal A) A

end
end Chapter09
end LastLib.Book01ValuationsDVRsAndCompletions
