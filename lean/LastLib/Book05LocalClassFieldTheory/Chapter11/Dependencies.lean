import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.TopologicalAbelianization
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.OpenSubgroup
import LastLib.Book05LocalClassFieldTheory.Chapter07.Section05ProfiniteCompletion
import LastLib.Book05LocalClassFieldTheory.Chapter08.Dependencies
import LastLib.Book05LocalClassFieldTheory.Chapter10.Dependencies

namespace LastLib.Book05LocalClassFieldTheory.Chapter11

noncomputable section

open scoped Topology

/-!
Shared interfaces for Chapter 11.

The preceding Book 5 chapters expose concrete field-side APIs.  The
interfaces marked `LOCAL_DEPENDENCY_GUESS` are therefore small book-facing
wrappers for the topological and character-theoretic statements needed below.
Their fields are deliberately canonical constructions or earlier theorems,
rather than propositions tailored to one of the conclusions of this chapter.
-/

abbrev Chapter11GaloisGroup (K : Type*) [Field K] := Field.absoluteGaloisGroup K

abbrev Chapter11GaloisAbelianization (K : Type*) [Field K] :=
  Field.absoluteGaloisGroupAbelianization K

abbrev Chapter11ProfiniteCompletion (G : Type*) [CommGroup G]
    [TopologicalSpace G] : Type _ :=
  (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletion G : Type _)

abbrev Chapter11ContinuousCharacter
    (G A : Type*) [Monoid G] [Monoid A] [TopologicalSpace G] [TopologicalSpace A] :=
  G →ₜ* A

def chapter11FiniteImage
    {X A : Type*} [Monoid X] [Monoid A]
    [TopologicalSpace X] [TopologicalSpace A]
    (χ : X →ₜ* A) : Prop := (Set.range χ).Finite

def chapter11FiniteOrderCharacter
    {X A : Type*} [Group X] [CommGroup A]
    [TopologicalSpace X] [TopologicalSpace A]
    (χ : X →ₜ* A) : Prop :=
  chapter11FiniteImage χ

theorem chapter11_finite_image_character_kernel_finite_index
    {X A : Type*} [Group X] [CommGroup A]
    [TopologicalSpace X] [TopologicalSpace A]
    (χ : X →ₜ* A) (hχ : chapter11FiniteImage χ) :
    χ.toMonoidHom.ker.FiniteIndex := by
  change (Set.range χ).Finite at hχ
  let _ : Finite (Set.range χ) := Set.finite_coe_iff.mp hχ
  let _ : Finite χ.toMonoidHom.range :=
    Finite.of_injective
      (fun x : χ.toMonoidHom.range =>
        (⟨x.1, by
          rcases x.2 with ⟨g, hg⟩
          exact ⟨g, hg⟩⟩ : Set.range χ))
      (by
        intro x y h
        exact Subtype.ext (congrArg Subtype.val h))
  exact Subgroup.finiteIndex_ker χ.toMonoidHom

def chapter11CharacterKernel
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A]
    (χ : Kˣ →ₜ* A) : Subgroup Kˣ :=
  χ.toMonoidHom.ker

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
  /-- The canonical local-field presentation from Chapter 8. -/
  base : LastLib.Book05LocalClassFieldTheory.Chapter08.Chapter08LocalFieldData K
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
  /-- The decomposition is a homeomorphism for the local-field topology. -/
  decomposition_continuous : Continuous decomposition
  decomposition_symm_continuous : Continuous decomposition.symm
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
  /-- The local field data is the Chapter 8 data, with a selected topology. -/
  unitGroup_eq_canonical :
    unitGroup = Chapter08.chapter08Units base.valuation
  uniformizer_eq_canonical :
    uniformizer = base.uniformizer
  valuation_eq_canonical :
    valuation = base.coordinate.valuation
  unitFiltration_eq_canonical :
    ∀ n, unitFiltration n = Chapter08.chapter08UnitFiltration base.valuation n

/-!
The abstract profinite completion forgets the original topology on `Kˣ`.
When it is compared with continuous characters for that topology, one needs
the local-field fact that ordinary neighborhoods contain open finite-index
subgroups. Keeping this as a separate hypothesis makes the completion
criterion valid for the intended local-field instances without baking an
unrelated finite-index assertion into the decomposition record.
-/
def chapter11OpenFiniteIndexCofinality
    {K : Type*} [Field K] [TopologicalSpace Kˣ] : Prop :=
  ∀ V : Set Kˣ, V ∈ 𝓝 (1 : Kˣ) →
    ∃ H : Subgroup Kˣ,
      IsOpen (H : Set Kˣ) ∧ H.FiniteIndex ∧ (H : Set Kˣ) ⊆ V

def chapter11ResidueDegreeOfSubgroup
    {K : Type*} [Field K] [TopologicalSpace Kˣ]
    (D : Chapter11LocalFieldData K) (H : Subgroup Kˣ)
    (_hH : H.FiniteIndex) : ℕ :=
  orderOf (QuotientGroup.mk'
    (D.unitGroup.map (QuotientGroup.mk' H))
    (QuotientGroup.mk' H D.uniformizer))

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
abelianization.  The comparison with the open finite-index profinite
completion is the universal-property interface used by the character
classification.
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
        (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionEtaFn
          Kˣ x)
  /-- The local-field topology is cofinal with the finite-index topology. -/
  openFiniteIndexCofinality : chapter11OpenFiniteIndexCofinality (K := K)

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
  localFieldData : Chapter11LocalFieldData K
  extension : Type*
  normGroup : extension → Subgroup Kˣ
  normGroup_open : ∀ e : extension, IsOpen (normGroup e : Set Kˣ)
  normGroup_finiteIndex : ∀ e : extension, (normGroup e).FiniteIndex
  degree : extension → ℕ
  cyclic : extension → Prop
  residueDegree : extension → ℕ
  cyclic_iff_quotient_isCyclic :
    ∀ e : extension, cyclic e ↔ IsCyclic (Kˣ ⧸ normGroup e)
  realizes :
    ∀ H : Subgroup Kˣ, IsOpen (H : Set Kˣ) → H.FiniteIndex →
      ∃ e : extension, normGroup e = H
  degree_eq_index :
    ∀ (e : extension), degree e = (normGroup e).index
  residueDegree_eq_subgroup :
    ∀ (e : extension),
      residueDegree e =
        chapter11ResidueDegreeOfSubgroup localFieldData (normGroup e)
          (normGroup_finiteIndex e)

/-!
Tower compatibility is stated on chosen topological models of the two Galois
groups.  The restriction and transfer maps are the two distinct Galois
operations in the source dictionary.
-/

/- LOCAL_DEPENDENCY_GUESS: provide these maps from a chosen common separable
  closure and the finite-index transfer construction. -/
structure Chapter11TowerData
    (K L Gₖ Gₗ : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [TopologicalSpace Kˣ] [TopologicalSpace Lˣ]
    [Group Gₖ] [Group Gₗ]
    [TopologicalSpace Gₖ] [TopologicalSpace Gₗ]
    [IsTopologicalGroup Gₖ] [IsTopologicalGroup Gₗ] where
  restriction :
    Gₗ →ₜ* Gₖ
  restrictionAb :
    TopologicalAbelianization Gₗ →ₜ* TopologicalAbelianization Gₖ
  transferAb :
    TopologicalAbelianization Gₖ →ₜ* TopologicalAbelianization Gₗ
  restriction_injective : Function.Injective restriction
  norm_continuous :
    Continuous (Units.map (Algebra.norm K) : Lˣ → Kˣ)
  inclusion_continuous :
    Continuous (Units.map (algebraMap K L).toMonoidHom : Kˣ → Lˣ)
  restrictionAb_compatibility :
    restrictionAb.comp (chapter11AbelianizationMap Gₗ) =
      (chapter11AbelianizationMap Gₖ).comp restriction

abbrev chapter11NormHom
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Lˣ →* Kˣ :=
  LastLib.Book05LocalClassFieldTheory.Chapter10.chapter10NormHom K L

abbrev chapter11NormGroup
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Subgroup Kˣ :=
  LastLib.Book05LocalClassFieldTheory.Chapter10.chapter10NormSubgroup K L

/-!
Finite reciprocity is the earlier-chapter input needed to turn an embedding of
a finite abelian Galois group into a continuous multiplicative character.
-/
structure Chapter11FiniteArtinData
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [TopologicalSpace Kˣ] [TopologicalSpace (Gal(L / K))]
    [DiscreteTopology (Gal(L / K))] where
  reciprocity : Kˣ →ₜ* Gal(L / K)
  reciprocity_surjective : Function.Surjective reciprocity
  kernel_eq_norm :
    reciprocity.toMonoidHom.ker = chapter11NormGroup K L

def chapter11ContinuousNormHom
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [TopologicalSpace Lˣ] [TopologicalSpace Kˣ]
    (hcont : Continuous (chapter11NormHom K L)) : Lˣ →ₜ* Kˣ :=
  { toMonoidHom := chapter11NormHom K L
    continuous_toFun := hcont }

def chapter11MultiplicativeInclusion
    (K L : Type*) [Field K] [Field L] [Algebra K L] : Kˣ →* Lˣ :=
  Units.map (algebraMap K L).toMonoidHom

def chapter11ContinuousMultiplicativeInclusion
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [TopologicalSpace Kˣ] [TopologicalSpace Lˣ]
    (hcont : Continuous (chapter11MultiplicativeInclusion K L)) : Kˣ →ₜ* Lˣ :=
  { toMonoidHom := chapter11MultiplicativeInclusion K L
    continuous_toFun := hcont }

def chapter11NormRestrictionCompatibility
    {K L Gₖ Gₗ : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Group Gₖ] [Group Gₗ] [TopologicalSpace Kˣ] [TopologicalSpace Lˣ]
    [TopologicalSpace Gₖ] [TopologicalSpace Gₗ] [IsTopologicalGroup Gₖ]
    [IsTopologicalGroup Gₗ]
  (Rₖ : Chapter11ReciprocityData K Gₖ)
  (Rₗ : Chapter11ReciprocityData L Gₗ)
  (T : Chapter11TowerData K L Gₖ Gₗ) : Prop :=
  T.restrictionAb.comp Rₗ.reciprocity =
    Rₖ.reciprocity.comp
      (chapter11ContinuousNormHom K L T.norm_continuous)

def chapter11TransferInclusionCompatibility
    {K L Gₖ Gₗ : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Group Gₖ] [Group Gₗ] [TopologicalSpace Kˣ] [TopologicalSpace Lˣ]
    [TopologicalSpace Gₖ] [TopologicalSpace Gₗ] [IsTopologicalGroup Gₖ]
    [IsTopologicalGroup Gₗ]
  (Rₖ : Chapter11ReciprocityData K Gₖ)
  (Rₗ : Chapter11ReciprocityData L Gₗ)
  (T : Chapter11TowerData K L Gₖ Gₗ) : Prop :=
  T.transferAb.comp Rₖ.reciprocity =
    Rₗ.reciprocity.comp
      (chapter11ContinuousMultiplicativeInclusion K L T.inclusion_continuous)

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
