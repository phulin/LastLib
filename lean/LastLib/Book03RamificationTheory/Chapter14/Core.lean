import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.Section05HigherRamificationBoundary
import LastLib.Book03RamificationTheory.Chapter12.Core
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Notation
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.GroupAction.Quotient

namespace LastLib.Book03RamificationTheory.Chapter14

noncomputable section

open scoped BigOperators

/-!
## Shared interfaces for Chapter 14

Chapter 14 keeps the numerical and conductor conventions of Chapter 12.  The
small definitions in this file are the common boundaries used by the four
source sections; section-specific constructions remain in their leaves.
-/

abbrev Chapter14LocalExtensionNumbers :=
  LastLib.Book03RamificationTheory.Chapter12.Chapter12LocalExtensionNumbers

namespace Chapter14LocalExtensionNumbers

def discriminantExponent (p : Chapter14LocalExtensionNumbers) : ℕ :=
  p.residueDegree * p.differentExponent

@[simp] theorem discriminantExponent_def (p : Chapter14LocalExtensionNumbers) :
    p.discriminantExponent = p.residueDegree * p.differentExponent :=
  rfl

end Chapter14LocalExtensionNumbers

/- The field-facing degree identity is named separately so that later leaves
can state the defectless hypothesis explicitly. -/
def chapter14DegreeFormula (degree e f : ℕ) : Prop :=
  degree = e * f

@[simp] theorem chapter14DegreeFormula_iff (degree e f : ℕ) :
    chapter14DegreeFormula degree e f ↔ degree = e * f :=
  Iff.rfl

/- This is deliberately the exact separability proposition used by Mathlib,
not the stronger perfectness condition. -/
def chapter14ResidueExtensionSeparable
    (k l : Type*) [Field k] [Field l] [Algebra k l] : Prop :=
  Algebra.IsSeparable k l

@[simp] theorem chapter14ResidueExtensionSeparable_iff
    (k l : Type*) [Field k] [Field l] [Algebra k l] :
    chapter14ResidueExtensionSeparable k l ↔ Algebra.IsSeparable k l :=
  Iff.rfl

/- Positive residue characteristic is separated from the characteristic-zero
case.  The residue-separability conjunct is part of the tame boundary. -/
def chapter14TameAtResidueCharacteristic
    (residueSeparable : Prop) (e p : ℕ) : Prop :=
  residueSeparable ∧
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05TameAtResidueCharacteristic e p

theorem chapter14_numerical_tame_iff_coprime_of_separable_residue
    (residueSeparable : Prop) (e p : ℕ)
    (hres : residueSeparable) :
    chapter14TameAtResidueCharacteristic residueSeparable e p ↔
      Nat.Coprime e p := by
  simp [chapter14TameAtResidueCharacteristic,
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05TameAtResidueCharacteristic,
    hres]

/- SOURCE_ISSUE: The source says, “A finite separable extension $M/K$ with
separable residue extension is tame exactly when
$\gcd(e(M/K),p)=1$.”  Over an imperfect residue field, coprimality does not
exclude a finite defect, so this is not an extension-level tameness criterion
without a defectless/perfect-residue hypothesis.  The preceding predicate is
therefore only the numerical tame boundary; the corrected extension-level
interface below includes defectlessness. -/
def chapter14DefectlessTameExtension
    (defectless residueSeparable : Prop) (e p : ℕ) : Prop :=
  defectless ∧ chapter14TameAtResidueCharacteristic residueSeparable e p

theorem chapter14_defectless_tame_iff_coprime
    (defectless residueSeparable : Prop) (e p : ℕ)
    (hdefectless : defectless) (hres : residueSeparable) :
    chapter14DefectlessTameExtension defectless residueSeparable e p ↔
      Nat.Coprime e p := by
  simp [chapter14DefectlessTameExtension,
    chapter14TameAtResidueCharacteristic,
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05TameAtResidueCharacteristic,
    hdefectless, hres]

/- LOCAL_DEPENDENCY_GUESS: stability of tame extensions under compositum and
subextension should provide the numerical equivalence below for a normal
closure.  The bridge itself uses only the weakest visible data: positive
residue characteristic, separable residues, and equivalence of the two
prime-to-`p` conditions. -/
theorem chapter14_tame_closure_iff_of_coprime_equivalence
    (baseResidueSeparable closureResidueSeparable : Prop)
    (baseE closureE p : ℕ)
    (hbase : baseResidueSeparable)
    (hclosure : closureResidueSeparable)
    (hcoprime : Nat.Coprime baseE p ↔ Nat.Coprime closureE p) :
    chapter14TameAtResidueCharacteristic baseResidueSeparable baseE p ↔
      chapter14TameAtResidueCharacteristic closureResidueSeparable closureE p := by
  simp [chapter14TameAtResidueCharacteristic,
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05TameAtResidueCharacteristic,
    hbase, hclosure, hcoprime]

/- A finite separable extension without normality has a smaller automorphism
group than its field degree.  This is the precise replacement for treating
`Gal(M/K)` as a degree-sized symmetry group. -/
structure Chapter14NongaloisExtension
    (K M : Type*) [Field K] [Field M] [Algebra K M]
    [FiniteDimensional K M] where
  separable : Algebra.IsSeparable K M
  nongalois : ¬ IsGalois K M

theorem chapter14_nongalois_automorphisms_have_smaller_cardinality
    {K M : Type*} [Field K] [Field M] [Algebra K M]
    [FiniteDimensional K M]
    (E : Chapter14NongaloisExtension K M) [Finite (Gal(M / K))] :
    Nat.card (Gal(M / K)) < Module.finrank K M := by
  sorry

/- The closure comparison in §14.1 is recorded as a reusable proposition.
Its two sides are intentionally abstract here; Section 2 supplies the
normal-closure and permutation representations to which it is applied. -/
def chapter14TameClosureEquivalence (baseTame closureTame : Prop) : Prop :=
  baseTame ↔ closureTame

@[simp] theorem chapter14TameClosureEquivalence_iff
    (baseTame closureTame : Prop) :
    chapter14TameClosureEquivalence baseTame closureTame ↔
      (baseTame ↔ closureTame) :=
  Iff.rfl

end
end LastLib.Book03RamificationTheory.Chapter14
