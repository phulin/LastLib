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
import LastLib.Book05LocalClassFieldTheory.Chapter05.Section06FiniteReciprocity

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
  LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05AlgebraMapUnits K L

/-- The unit-group map induced by the algebraic norm. -/
noncomputable def chapter09NormHom
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Lˣ →* Kˣ :=
  LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05NormMap K L

/-- The image subgroup of the norm on units. -/
def chapter09NormSubgroup
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Subgroup Kˣ :=
  LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05NormSubgroup K L

theorem chapter09_mem_normSubgroup_iff
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : Kˣ) :
    x ∈ chapter09NormSubgroup K L ↔
      ∃ y : Lˣ, chapter09NormHom K L y = x := by
  sorry

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
The finite quotient of an absolute Galois abelianization is not an arbitrary
homomorphism to a finite Galois group.  It is the restriction of an absolute
automorphism to the embedded finite field.  This predicate records that
field-theoretic meaning without choosing a separate representative for the
restriction map.
-/
def chapter09FiniteGaloisRestriction
    (K E Ks : Type*) [Field K] [Field E] [Field Ks]
    [Algebra K E] [Algebra K Ks] [Algebra E Ks]
    [IsScalarTower K E Ks]
    (q : Abelianization (Gal(Ks / K)) →* Gal(E / K)) : Prop :=
  ∀ (σ : Gal(Ks / K)) (x : E),
    algebraMap E Ks (q (Abelianization.of σ) x) =
      σ (algebraMap E Ks x)

theorem chapter09_finiteGaloisRestriction_ext
    (K E Ks : Type*) [Field K] [Field E] [Field Ks]
    [Algebra K E] [Algebra K Ks] [Algebra E Ks]
    [IsScalarTower K E Ks]
    {q₁ q₂ : Abelianization (Gal(Ks / K)) →* Gal(E / K)}
    (hq₁ : chapter09FiniteGaloisRestriction K E Ks q₁)
    (hq₂ : chapter09FiniteGaloisRestriction K E Ks q₂) :
    q₁ = q₂ := by
  sorry

/-!
The next records separate canonical finite-reciprocity normalization from the
two functoriality equalities proved later in the chapter.  Finite maps are
obtained from Chapter 5, while the absolute reciprocity records only how those
canonical maps are seen at finite levels; it does not assume either final
compatibility square.
-/

structure Chapter09FiniteReciprocityNormalization
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (D : LastLib.Book05LocalClassFieldTheory.Chapter05.Chapter05LocalClassFormationData
      K L) where
  quotientEquiv :
    LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05NormQuotient K L ≃*
      Gal(L / K)
  compatibility :
    LastLib.Book05LocalClassFieldTheory.Chapter05.Chapter05FiniteReciprocityCompatibility
      D quotientEquiv

noncomputable def Chapter09FiniteReciprocityNormalization.canonical
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (D : LastLib.Book05LocalClassFieldTheory.Chapter05.Chapter05LocalClassFormationData
      K L) :
    Chapter09FiniteReciprocityNormalization D :=
  { quotientEquiv :=
      (LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05_finite_local_reciprocity D).choose
    compatibility :=
      (LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05_finite_local_reciprocity D).choose_spec.1 }

theorem chapter09_finiteReciprocityNormalization_quotientEquiv_eq_canonical
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (D : LastLib.Book05LocalClassFieldTheory.Chapter05.Chapter05LocalClassFormationData
      K L)
    (N : Chapter09FiniteReciprocityNormalization D) :
    N.quotientEquiv =
      (Chapter09FiniteReciprocityNormalization.canonical D).quotientEquiv := by
  sorry

structure Chapter09AbsoluteReciprocityNormalization
    (K Ks : Type) [Field K] [Field Ks] [Algebra K Ks]
    (reciprocity : Kˣ →* Abelianization (Gal(Ks / K))) where
  closure : IsSepClosure K Ks
  finite_level :
    ∀ (E : Type) [Field E] [Algebra K E] [Algebra E Ks]
      [IsScalarTower K E Ks] [FiniteDimensional K E]
      [IsAbelianGalois K E] [Fintype (Gal(E / K))]
      (D : LastLib.Book05LocalClassFieldTheory.Chapter05.Chapter05LocalClassFormationData
        K E),
        ∃ q : Abelianization (Gal(Ks / K)) →* Gal(E / K),
        chapter09FiniteGaloisRestriction K E Ks q ∧
        q.comp reciprocity =
          (Chapter09FiniteReciprocityNormalization.canonical D).quotientEquiv.toMonoidHom.comp
            (QuotientGroup.mk'
              (LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05NormSubgroup K E))

structure Chapter09NormalizedReciprocityMap
    (K Ks : Type) [Field K] [Field Ks] [Algebra K Ks] where
  reciprocity : Kˣ →* Abelianization (Gal(Ks / K))
  normalization :
    Chapter09AbsoluteReciprocityNormalization K Ks reciprocity

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

structure Chapter09ReciprocitySystem
    (K L Ks : Type) [Field K] [Field L] [Field Ks]
    [Algebra K L] [Algebra K Ks] [Algebra L Ks]
    [IsScalarTower K L Ks] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (T : Chapter09FiniteSeparableExtension K L Ks) where
  recK : Chapter09NormalizedReciprocityMap K Ks
  recL : Chapter09NormalizedReciprocityMap L Ks

structure Chapter09FiniteAbelianReciprocity
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))] where
  classFormation :
    LastLib.Book05LocalClassFieldTheory.Chapter05.Chapter05LocalClassFormationData K L
  quotientEquiv :
    LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05NormQuotient K L ≃*
      Gal(L / K)
  normalization :
    LastLib.Book05LocalClassFieldTheory.Chapter05.Chapter05FiniteReciprocityCompatibility
      classFormation quotientEquiv

theorem chapter09_finiteAbelianReciprocity_quotientEquiv_eq_canonical
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (R : Chapter09FiniteAbelianReciprocity K L) :
    R.quotientEquiv =
      (Chapter09FiniteReciprocityNormalization.canonical R.classFormation).quotientEquiv := by
  sorry

end

end LastLib.Book05LocalClassFieldTheory.Chapter09
