import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.Section04TheValuationOfANorm

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04

noncomputable section

open Ideal IsLocalRing
open scoped BigOperators Polynomial

/-! ## 4.5. Residue-field shadows -/

/- A residue map is recorded by its quotient kernel and surjectivity. -/
def chapter04ResidueMap
    (R k : Type*) [CommRing R] [Field k] (m : Ideal R)
    (ρ : R →+* k) : Prop :=
  Function.Surjective ρ ∧ ∀ x : R, ρ x = 0 ↔ x ∈ m

/- The pair of reduced formulas used in Proposition 4.2 (§4.5). -/
def chapter04ResidueTraceNormStatement
    {A B k l : Type*} [CommRing A] [CommRing B] [Field k] [Field l]
    [Algebra k l] [FiniteDimensional k l]
    (redA : A →+* k) (redB : B →+* l)
    (e : ℕ) (t n : A) (x u : B) : Prop :=
  redA t = (e : k) * Algebra.trace k l (redB x) ∧
    redA n = Algebra.norm k (redB u) ^ e

/-
Proposition 4.2.  The maps `redA` and `redB` are explicit residue maps, and
`hcompat` says that the local algebra map descends to the residue extension.
This avoids identifying quotient representatives by definitional equality.
-/
theorem chapter04_residue_trace_and_norm
    (A B K L k l : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [IsDomain B] [IsLocalRing A] [IsLocalRing B] [Field K] [Field L]
    [Field k] [Field l] [Algebra A B] [Algebra A K] [Algebra B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L]
    [IsScalarTower A K L] [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [Algebra k l] [FiniteDimensional k l]
    [IsIntegrallyClosed A] [IsDedekindDomain B] [Module.Finite A B]
    [Module.Free A B] [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    (redA : A →+* k) (redB : B →+* l)
    (hredA : chapter04ResidueMap A k (IsLocalRing.maximalIdeal A) redA)
    (hredB : chapter04ResidueMap B l (IsLocalRing.maximalIdeal B) redB)
    (hcompat : ∀ a : A,
      redB (algebraMap A B a) = algebraMap k l (redA a))
    (e : ℕ) (t n : A) (x : B) (u : Bˣ)
    (htrace : algebraMap A K t = Algebra.trace K L (algebraMap B L x))
    (hnorm : algebraMap A K n = Algebra.norm K (algebraMap B L (u : B)))
    (he : e = (IsLocalRing.maximalIdeal B).ramificationIdx A) :
    chapter04ResidueTraceNormStatement
      redA redB e t n x (u : B) := by
  sorry

/- For an unramified extension, the integer factor is one (§4.5). -/
theorem chapter04_unramified_reduction_commutes_with_trace_and_norm
    {k l : Type*} [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l] (redA : k →+* k) (redB : l →+* l)
    (t n : k) (x u : l)
    (h : chapter04ResidueTraceNormStatement redA redB 1 t n x u) :
    redA t = Algebra.trace k l (redB x) ∧
      redA n = Algebra.norm k (redB u) := by
  sorry

/- When the residue extension is trivial, Proposition 4.2 becomes a power
formula for the residue of a unit (§4.5). -/
theorem chapter04_totally_ramified_residue_norm_of_unit
    (k : Type*) [Field k] (redA : k →+* k) (redB : k →+* k)
    (e : ℕ) (n u : k)
    (h : redA n = Algebra.norm k u ^ e) :
    redA n = u ^ e := by
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04
