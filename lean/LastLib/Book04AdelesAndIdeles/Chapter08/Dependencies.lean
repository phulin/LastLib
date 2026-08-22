import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Int.WithZero
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Topology.Algebra.RestrictedProduct.Units
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Order
import LastLib.Book04AdelesAndIdeles.Chapter07.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter08

open LastLib.Book04AdelesAndIdeles.Chapter07

noncomputable section

open scoped BigOperators nonZeroDivisors RestrictedProduct

/-!
The chapter uses the standard number-field choices throughout.  The finite adele, finite idele,
and finite divisor types below are the Chapter 7 interfaces specialized to the ring of integers.
Chapter 7 also identifies the restricted-product graph topology with the ambient unit topology.
-/

abbrev Chapter08Integers (K : Type*) [Field K] [NumberField K] :=
  NumberField.RingOfIntegers K

abbrev Chapter08FiniteAdeles (K : Type*) [Field K] [NumberField K] :=
  chapter07FiniteAdeleRing (Chapter08Integers K) K

abbrev Chapter08FiniteIdeles (K : Type*) [Field K] [NumberField K] :=
  chapter07FiniteIdeleGroup (Chapter08Integers K) K

abbrev Chapter08InfiniteAdeles (K : Type*) [Field K] [NumberField K] :=
  NumberField.InfiniteAdeleRing K

abbrev Chapter08InfiniteIdeles (K : Type*) [Field K] [NumberField K] :=
  (Chapter08InfiniteAdeles K)ˣ

abbrev Chapter08Ideles (K : Type*) [Field K] [NumberField K] :=
  Chapter08InfiniteIdeles K × Chapter08FiniteIdeles K

abbrev Chapter08FractionalIdeal (K : Type*) [Field K] [NumberField K] :=
  FractionalIdeal (Chapter08Integers K)⁰ K

abbrev Chapter08IdealGroup (K : Type*) [Field K] [NumberField K] :=
  (Chapter08FractionalIdeal K)ˣ

abbrev Chapter08OrdinaryClassGroup (K : Type*) [Field K] [NumberField K] :=
  ClassGroup (Chapter08Integers K)

abbrev Chapter08FiniteDivisors (K : Type*) [Field K] [NumberField K] :=
  chapter07FiniteDivisorGroup (Chapter08Integers K)

/-! A small reusable interface for exact displays in the source chapter. -/

def chapter08IsExact {A B C : Type*} [Group A] [Group B] [Group C]
    (f : A →* B) (g : B →* C) : Prop :=
  MonoidHom.range f = MonoidHom.ker g

def chapter08IsShortExact {A B C : Type*} [Group A] [Group B] [Group C]
    (f : A →* B) (g : B →* C) : Prop :=
  Function.Injective f ∧ chapter08IsExact f g ∧ Function.Surjective g

/-! The graph topology on the finite idele group and the resulting product topology on ideles. -/

@[instance_reducible]
def chapter08FiniteIdeleGraphTopology (K : Type*) [Field K] [NumberField K] :
    TopologicalSpace (Chapter08FiniteIdeles K) :=
  TopologicalSpace.induced
    (chapter07FiniteIdeleEquiv (Chapter08Integers K) K)
    inferInstance

@[instance_reducible]
def chapter08IdelesTopology (K : Type*) [Field K] [NumberField K] :
    TopologicalSpace (Chapter08Ideles K) :=
  letI : TopologicalSpace (Chapter08FiniteIdeles K) :=
    chapter08FiniteIdeleGraphTopology K
  inferInstance

end

end LastLib.Book04AdelesAndIdeles.Chapter08
