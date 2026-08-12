import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Notation
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.RingTheory.Norm.Transitivity

namespace LastLib.Book05LocalClassFieldTheory.Chapter09

noncomputable section

/-!
## Interfaces shared by Chapter 09

The preceding chapters supply local reciprocity and the finite-extension
instances used here.  This chapter is drafted independently of their current
file layout, so the small records below name those interfaces explicitly.
They are dependency interfaces, not new mathematical assumptions about the
compatibility theorems proved later in the chapter.
-/

/-- The multiplicative map induced by a field inclusion. -/
def chapter09FieldInclusionHom
    (K L : Type*) [Field K] [Field L] [Algebra K L] : Kˣ →* Lˣ :=
  Units.map (algebraMap K L).toMonoidHom

/-- The unit-group map induced by the algebraic norm. -/
def chapter09NormHom
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Lˣ →* Kˣ :=
  Units.map (Algebra.norm K : L →* K)

/-- The image subgroup of the norm on units. -/
def chapter09NormSubgroup
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Subgroup Kˣ :=
  (chapter09NormHom K L).range

theorem chapter09_mem_normSubgroup_iff
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : Kˣ) :
    x ∈ chapter09NormSubgroup K L ↔
      ∃ y : Lˣ, chapter09NormHom K L y = x := by
  simp [chapter09NormSubgroup]

/--
The inclusion of automorphism groups obtained by restricting scalars.

The common scalar tower is part of the data: without it there is no canonical
map from `Gal(Ks/L)` to `Gal(Ks/K)`.
-/
def chapter09GaloisInclusion
    (K L Ks : Type*) [Field K] [Field L] [Field Ks]
    [Algebra K L] [Algebra K Ks] [Algebra L Ks]
    [IsScalarTower K L Ks] :
    Gal(Ks / L) →* Gal(Ks / K) :=
  { toFun := fun σ => σ.restrictScalars K
    map_one' := by rfl
    map_mul' := by intro σ τ; rfl }

theorem chapter09_galoisInclusion_injective
    (K L Ks : Type*) [Field K] [Field L] [Field Ks]
    [Algebra K L] [Algebra K Ks] [Algebra L Ks]
    [IsScalarTower K L Ks] :
    Function.Injective (chapter09GaloisInclusion K L Ks) := by
  intro σ τ h
  exact AlgEquiv.restrictScalars_injective K h

/-- The range subgroup of the Galois inclusion. -/
def chapter09GaloisSubgroup
    (K L Ks : Type*) [Field K] [Field L] [Field Ks]
    [Algebra K L] [Algebra K Ks] [Algebra L Ks]
    [IsScalarTower K L Ks] : Subgroup (Gal(Ks / K)) :=
  (chapter09GaloisInclusion K L Ks).range

/-- The map induced on abelianizations by Galois-group inclusion. -/
def chapter09GaloisInclusionAbelianization
    (K L Ks : Type*) [Field K] [Field L] [Field Ks]
    [Algebra K L] [Algebra K Ks] [Algebra L Ks]
    [IsScalarTower K L Ks] :
    Abelianization (Gal(Ks / L)) →* Abelianization (Gal(Ks / K)) :=
  Abelianization.map (chapter09GaloisInclusion K L Ks)

/-!
The next record is the minimal common-separable-closure interface used by
the chapter.  The finite-index field is a local dependency guess for the
standard finite-extension theorem from the preceding local class field theory
chapters; it does not encode either reciprocity compatibility statement.
-/

/- LOCAL_DEPENDENCY_GUESS: the preceding chapters expose the standard fact
that a separable closure of `K` is also a separable closure of a finite
separable intermediate field `L`. -/
theorem chapter09_isSepClosure_over_extension_of_base
    (K L Ks : Type*) [Field K] [Field L] [Field Ks]
    [Algebra K L] [Algebra K Ks] [Algebra L Ks]
    [IsScalarTower K L Ks] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (hKs : IsSepClosure K Ks) :
    IsSepClosure L Ks := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the preceding chapters expose the finite-index
fact for the restriction subgroup of a finite separable extension. -/
structure Chapter09FiniteSeparableExtension
    (K L Ks : Type*) [Field K] [Field L] [Field Ks]
    [Algebra K L] [Algebra K Ks] [Algebra L Ks]
    [IsScalarTower K L Ks] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] where
  closure_over_base : IsSepClosure K Ks
  galoisInclusion_finiteIndex :
    (chapter09GaloisSubgroup K L Ks).FiniteIndex

/- LOCAL_DEPENDENCY_GUESS: the preceding chapters expose the two local
reciprocity homomorphisms on unit groups. -/
structure Chapter09ReciprocitySystem
    (K L Ks : Type*) [Field K] [Field L] [Field Ks]
    [Algebra K L] [Algebra K Ks] [Algebra L Ks]
    [IsScalarTower K L Ks] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (T : Chapter09FiniteSeparableExtension K L Ks) where
  recK : Kˣ →* Abelianization (Gal(Ks / K))
  recL : Lˣ →* Abelianization (Gal(Ks / L))

/- LOCAL_DEPENDENCY_GUESS: finite abelian reciprocity identifies the indicated
norm quotient with the finite Galois group. -/
structure Chapter09FiniteAbelianReciprocity
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L] where
  quotientEquiv :
    (Kˣ ⧸ chapter09NormSubgroup K L) ≃* Gal(L / K)

end

end LastLib.Book05LocalClassFieldTheory.Chapter09
