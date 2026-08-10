import Mathlib
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter11

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08

noncomputable section

open Polynomial
open scoped BigOperators WithTop

/-! # 8.1. Isolating value-group growth

The valuation language below uses Book 1's additive valuation interface.  In
particular, the residue degree is a module rank of residue fields, while the
ramification index is kept as a separate numerical invariant.
-/

-- BOOK2_DEPENDENCY_GUESS: expected from Chapter 9; a maximal unramified
-- intermediate field is represented by an intermediate field together with an
-- unramified predicate and its maximality property.
structure Chapter08MaximalUnramifiedSubextension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (isUnramified : IntermediateField K L → Prop) where
  carrier : IntermediateField K L
  isUnramified_carrier : isUnramified carrier
  maximal : ∀ M : IntermediateField K L, isUnramified M → M ≤ carrier

/-! The following predicate is the valuation-theoretic form of `f = 1`. -/

/-- Book §8.1: a finite valued extension is totally ramified when its residue
degree is one.  No separability or Galois hypothesis is built into this
definition. -/
def chapter08TotallyRamified
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (h : vK.IsEquiv (AddValuation.comap (algebraMap K L) vL)) : Prop :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree vK vL h = 1

/-- Book §8.1: equality of residue fields, used as the ring-theoretic reading
of residue degree one. -/
def chapter08ResidueFieldsEqual
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) : Prop :=
  Nonempty
    (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueField vK ≃+*
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueField vL)

/-- Book §8.1: for a finite extension, total ramification is equivalent to no
residue-field growth. -/
theorem chapter08_total_ramification_iff_residue_fields_equal
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (h : vK.IsEquiv (AddValuation.comap (algebraMap K L) vL)) :
    chapter08TotallyRamified vK vL h ↔ chapter08ResidueFieldsEqual vK vL := by
  sorry

/-- Book §8.1: the fundamental equality specializes to `[L : K] = e` at the
totally ramified endpoint. -/
theorem chapter08_total_ramification_degree_formula
    (p : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10FiniteExtensionProfile)
    (hdegree : p.degree = p.ramificationIndex * p.residueDegree)
    (htotal : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10TotallyRamified p) :
    p.degree = p.ramificationIndex := by
  sorry

/-- A root relation of the form used by the equal-characteristic example
`k((t^(1/p)))/k((t))`. -/
def chapter08RadicalPresentation
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (π : K) (α : L) (n : ℕ) : Prop :=
  algebraMap K L π = α ^ n

/-- Book §8.1: a purely inseparable radical extension can still be totally
ramified; total ramification does not imply separability. -/
theorem chapter08_purely_inseparable_radical_is_totally_ramified
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsPurelyInseparable K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (h : vK.IsEquiv (AddValuation.comap (algebraMap K L) vL))
    (p : ℕ) (hp : Nat.Prime p) (π : K) (α : L)
    (hroot : chapter08RadicalPresentation π α p)
    (hdegree : Module.finrank K L = p)
    (hresidue : LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree vK vL h = 1) :
    chapter08TotallyRamified vK vL h := by
  sorry

/-- Book §8.1: a finite extension which is both Galois and purely inseparable
is trivial, so the displayed purely inseparable example is not Galois. -/
theorem chapter08_galois_purely_inseparable_extension_is_trivial
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsPurelyInseparable K L] :
    Module.finrank K L = 1 := by
  sorry

/-- Book §8.1: total ramification is inherited by both stages of a tower.
The hypotheses expose the residue-degree multiplication and do not assume
separability. -/
theorem chapter08_total_ramification_inherited_by_subextensions
    (K M L : Type*) [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L] [FiniteDimensional K M] [FiniteDimensional M L]
    (fKM fML fKL : ℕ)
    (htower : fKL = fKM * fML) (htotal : fKL = 1) :
    fKM = 1 ∧ fML = 1 := by
  sorry

/-- The invariant-level interface for the unramified base-change assertion in
Book §8.1. -/
def chapter08UnramifiedBaseChangeProfile
    (base p p' : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10FiniteExtensionProfile) : Prop :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10Unramified base ∧
    p'.residueDegree = p.residueDegree

/-- Book §8.1: unramified base change preserves total ramification once the
residue-degree compatibility supplied by the base-change theorem is recorded. -/
theorem chapter08_total_ramification_preserved_under_unramified_base_change
    (base p p' : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10FiniteExtensionProfile)
    (hbase : chapter08UnramifiedBaseChangeProfile base p p')
    (htotal : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10TotallyRamified p) :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10TotallyRamified p' := by
  sorry

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08
