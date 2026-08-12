import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.TopologicalAbelianization
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.OpenSubgroup

namespace LastLib.Book05LocalClassFieldTheory.Chapter11

noncomputable section

open CategoryTheory
open scoped Topology

/-!
Shared interfaces for Chapter 11.

The preceding Book 5 chapters are not present in this checkout.  The
interfaces marked `LOCAL_DEPENDENCY_GUESS` are therefore the smallest
book-facing interfaces needed below.  Their fields are deliberately
canonical constructions (the local unit filtration, reciprocity, and the
finite abelian existence theorem), rather than propositions tailored to one
of the conclusions of this chapter.
-/

abbrev Chapter11GaloisGroup (K : Type*) [Field K] := Field.absoluteGaloisGroup K

abbrev Chapter11GaloisAbelianization (K : Type*) [Field K] :=
  Field.absoluteGaloisGroupAbelianization K

abbrev Chapter11ProfiniteCompletion (G : Type*) [Group G] : Type _ :=
  (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) : Type _)

abbrev Chapter11ContinuousCharacter
    (G A : Type*) [Monoid G] [Monoid A] [TopologicalSpace G] [TopologicalSpace A] :=
  G →ₜ* A

def chapter11FiniteImage
    {X A : Type*} [Monoid X] [Monoid A]
    [TopologicalSpace X] [TopologicalSpace A]
    (χ : X →ₜ* A) : Prop := (Set.range χ).Finite

def chapter11FiniteOrderCharacter
    {X A : Type*} [Monoid X] [Monoid A]
    [TopologicalSpace X] [TopologicalSpace A]
    (χ : X →ₜ* A) : Prop :=
  chapter11FiniteImage χ

/-- The quotient map to the topological abelianization. -/
def chapter11AbelianizationMap
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    G →ₜ* TopologicalAbelianization G :=
  { toMonoidHom := QuotientGroup.mk' (Subgroup.topologicalClosure (commutator G))
    continuous_toFun := continuous_quotient_mk' }

/-!
The multiplicative group of a local field is split into the uniformizer
direction and the valuation-ring units.  `unitFiltration n` is the subgroup
called `Uⁿ` in the source; positive levels are the principal-unit groups.
-/

/- LOCAL_DEPENDENCY_GUESS: identify this with the canonical local-field and
  unit-filtration package produced by Book 5, Chapters 1--10. -/
structure Chapter11LocalFieldData
    (K : Type*) [Field K] [TopologicalSpace Kˣ] where
  /-- The book's valuation-ring unit group, as a subgroup of `Kˣ`. -/
  unitGroup : Subgroup Kˣ
  /-- A chosen uniformizer. -/
  uniformizer : Kˣ
  /-- The normalized valuation on `Kˣ`, written additively. -/
  valuation : Kˣ →* Multiplicative ℤ
  valuation_uniformizer : valuation uniformizer = Multiplicative.ofAdd 1
  valuation_unit :
    ∀ u : unitGroup, valuation (u : Kˣ) = Multiplicative.ofAdd 0
  /-- The algebraic decomposition `ℤ × O_Kˣ ≃ Kˣ`. -/
  decomposition : (Multiplicative ℤ × unitGroup) ≃* Kˣ
  decomposition_apply :
    ∀ r : Multiplicative ℤ, ∀ u : unitGroup,
      decomposition (r, u) = uniformizer ^ r.toAdd * (u : Kˣ)
  /-- The unit filtration `Uⁿ`. -/
  unitFiltration : ℕ → Subgroup Kˣ
  unitFiltration_zero : unitFiltration 0 = unitGroup
  unitFiltration_succ_le : ∀ n, unitFiltration (n + 1) ≤ unitFiltration n
  unitFiltration_open : ∀ n, IsOpen (unitFiltration n : Set Kˣ)
  unitFiltration_basis :
    ∀ s ∈ 𝓝 (1 : Kˣ), ∃ n, (unitFiltration n : Set Kˣ) ⊆ s
  unitGroup_compact : IsCompact (unitGroup : Set Kˣ)

abbrev Chapter11UnitGroup
    {K : Type*} [Field K] [TopologicalSpace Kˣ]
    (D : Chapter11LocalFieldData K) : Type _ := D.unitGroup

def chapter11UnitInclusion
    {K : Type*} [Field K] [TopologicalSpace Kˣ]
    (D : Chapter11LocalFieldData K) : D.unitGroup →ₜ* Kˣ :=
  { toMonoidHom := D.unitGroup.subtype
    continuous_toFun := continuous_subtype_val }

/-!
Reciprocity is recorded as a continuous map into the canonical topological
abelianization.  The comparison with `ProfiniteCompletion.completion` is the
universal-property interface used by the character classification.
-/

/- LOCAL_DEPENDENCY_GUESS: replace this with the canonical reciprocity and
  profinite-completion comparison from Book 5, Chapters 1--10. -/
structure Chapter11ReciprocityData
    (K G : Type*) [Field K] [Group G]
    [TopologicalSpace Kˣ] [TopologicalSpace G] [IsTopologicalGroup G] where
  reciprocity : Kˣ →ₜ* TopologicalAbelianization G
  completionEquiv :
    Chapter11ProfiniteCompletion Kˣ ≃ₜ* TopologicalAbelianization G
  reciprocity_eq_completion :
    ∀ x : Kˣ,
      reciprocity x = completionEquiv
        (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of Kˣ) x)

/-!
The two Frobenius/inertia facts used in §11.3 are kept separate from the
reciprocity comparison, since they are consequences of the earlier
unramified and ramification chapters.
-/

/- LOCAL_DEPENDENCY_GUESS: supply the canonical arithmetic Frobenius and
  inertia filtration from the preceding local reciprocity chapters. -/
structure Chapter11FrobeniusData
    (K G : Type*) [Field K] [Group G]
    [TopologicalSpace Kˣ] [TopologicalSpace G] [IsTopologicalGroup G]
    (D : Chapter11LocalFieldData K)
    (R : Chapter11ReciprocityData K G) where
  inertia : Subgroup G
  arithmeticFrobenius : TopologicalAbelianization G
  reciprocity_uniformizer :
    R.reciprocity D.uniformizer = arithmeticFrobenius
  inertia_ab_eq_reciprocity_unit_image :
    inertia.map (chapter11AbelianizationMap G).toMonoidHom =
      D.unitGroup.map R.reciprocity.toMonoidHom

/-!
The existence theorem of §11.2 is exposed as an earlier-chapter interface.
The extension objects are intentionally abstract here; the merged Chapters
1--10 can replace them by their actual finite abelian extensions without
changing the character statements below.
-/

/- LOCAL_DEPENDENCY_GUESS: replace this interface by the finite abelian
  extension/norm-group construction from Book 5, Chapters 6--10. -/
class Chapter11ClassFieldExistenceData
    (K : Type*) [Field K] [TopologicalSpace Kˣ] where
  extension : Type*
  normGroup : extension → Subgroup Kˣ
  degree : extension → ℕ
  cyclic : extension → Prop
  residueDegree : extension → ℕ
  realizes :
    ∀ H : Subgroup Kˣ, IsOpen (H : Set Kˣ) → H.FiniteIndex →
      ∃ e : extension, normGroup e = H
  degree_eq_index :
    ∀ (e : extension) [_h : (normGroup e).FiniteIndex],
      degree e = (normGroup e).index

/-!
Tower compatibility is stated on chosen topological models of the two Galois
groups.  The restriction and transfer maps are the two distinct Galois
operations in the source dictionary.
-/

/- LOCAL_DEPENDENCY_GUESS: provide these maps from a chosen common separable
  closure and the finite-index transfer construction. -/
structure Chapter11TowerData
    (K L Gₖ Gₗ : Type*) [Field K] [Field L] [Algebra K L]
    [Group Gₖ] [Group Gₗ]
    [TopologicalSpace Gₖ] [TopologicalSpace Gₗ]
    [IsTopologicalGroup Gₖ] [IsTopologicalGroup Gₗ] where
  restriction :
    Gₗ →ₜ* Gₖ
  restrictionAb :
    TopologicalAbelianization Gₗ →ₜ* TopologicalAbelianization Gₖ
  transferAb :
    TopologicalAbelianization Gₖ →ₜ* TopologicalAbelianization Gₗ
  restrictionAb_compatibility :
    restrictionAb.comp (chapter11AbelianizationMap Gₗ) =
      (chapter11AbelianizationMap Gₖ).comp restriction

def chapter11NormHom
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Lˣ →* Kˣ :=
  Units.map (Algebra.norm K)

def chapter11ContinuousNormHom
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [TopologicalSpace Lˣ] [TopologicalSpace Kˣ] : Lˣ →ₜ* Kˣ :=
  { toMonoidHom := chapter11NormHom K L
    continuous_toFun := by sorry }

def chapter11MultiplicativeInclusion
    (K L : Type*) [Field K] [Field L] [Algebra K L] : Kˣ →* Lˣ :=
  Units.map (algebraMap K L).toMonoidHom

def chapter11ContinuousMultiplicativeInclusion
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [TopologicalSpace Kˣ] [TopologicalSpace Lˣ] : Kˣ →ₜ* Lˣ :=
  { toMonoidHom := chapter11MultiplicativeInclusion K L
    continuous_toFun := by sorry }

def chapter11NormRestrictionCompatibility
    {K L Gₖ Gₗ : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [Group Gₖ] [Group Gₗ] [TopologicalSpace Kˣ] [TopologicalSpace Lˣ]
    [TopologicalSpace Gₖ] [TopologicalSpace Gₗ] [IsTopologicalGroup Gₖ]
    [IsTopologicalGroup Gₗ]
    (Rₖ : Chapter11ReciprocityData K Gₖ)
    (Rₗ : Chapter11ReciprocityData L Gₗ)
    (T : Chapter11TowerData K L Gₖ Gₗ) : Prop :=
  T.restrictionAb.comp Rₗ.reciprocity =
    Rₖ.reciprocity.comp (chapter11ContinuousNormHom K L)

def chapter11TransferInclusionCompatibility
    {K L Gₖ Gₗ : Type*} [Field K] [Field L] [Algebra K L]
    [Group Gₖ] [Group Gₗ] [TopologicalSpace Kˣ] [TopologicalSpace Lˣ]
    [TopologicalSpace Gₖ] [TopologicalSpace Gₗ] [IsTopologicalGroup Gₖ]
    [IsTopologicalGroup Gₗ]
    (Rₖ : Chapter11ReciprocityData K Gₖ)
    (Rₗ : Chapter11ReciprocityData L Gₗ)
    (T : Chapter11TowerData K L Gₖ Gₗ) : Prop :=
  T.transferAb.comp Rₖ.reciprocity =
    Rₗ.reciprocity.comp (chapter11ContinuousMultiplicativeInclusion K L)

/- A local coefficient-field unit group, used in §§11.1 and 11.6. -/
structure Chapter11CoefficientUnitData
    (E : Type*) [Field E] [TopologicalSpace Eˣ] where
  unitGroup : Subgroup Eˣ
  unitGroup_compact : IsCompact (unitGroup : Set Eˣ)
  unitGroup_totallyDisconnected : TotallyDisconnectedSpace unitGroup
  unitGroup_t2 : T2Space unitGroup

/- A unit-part map is supplied by the standard coefficient-field valuation. -/
structure Chapter11UnitPartData (F U : Type*) [Group F] [CommGroup U] where
  unitPart : F →* U

end
end LastLib.Book05LocalClassFieldTheory.Chapter11
