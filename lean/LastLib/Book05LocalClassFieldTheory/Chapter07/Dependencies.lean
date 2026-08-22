import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.Section01TheLocalExtensionProblem
import LastLib.Book05LocalClassFieldTheory.Chapter01.Section01WhatKindOfLocalFieldIsMeant
import LastLib.Book05LocalClassFieldTheory.Chapter01.Section02TheClassificationOneHopesFor
import LastLib.Book05LocalClassFieldTheory.Chapter05.Section05NormLimitation
import Mathlib.Algebra.Category.Grp.FiniteGrp
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.GroupTheory.FiniteIndexNormalSubgroup
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.Quotient

namespace LastLib.Book05LocalClassFieldTheory.Chapter07

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators WithZero

universe u v

/-!
Shared interfaces for Chapter 7.  The preceding chapters supply the finite
Artin maps, their norm kernels, and the maximal-abelian model; the aliases
below retain the Chapter 7-facing names.  The topology-sensitive completion
and precision/cofinality interfaces are Chapter 7-specific.  None of these
interfaces assumes a conclusion of the infinite reciprocity theorem.
-/

/-- Compatibility name for the canonical finite abelian levels from Chapter 1. -/
abbrev Chapter07FiniteAbelianIndex
    (K KAb : Type*) [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] :=
  LastLib.Book05LocalClassFieldTheory.Chapter01.Chapter01FiniteAbelianIndex K KAb

/- LOCAL_DEPENDENCY_GUESS: Chapter 1 supplies the canonical local-field and
valuation-coordinate interfaces used by the infinite reciprocity arguments. -/
structure Chapter07LocalFieldData (K : Type*) [Field K]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ] where
  valuation : AddValuation K (WithTop ℤ)
  local_field :
    LastLib.Book05LocalClassFieldTheory.Chapter01.Chapter01LocalField valuation
  [residue_finite : Finite
      (LastLib.Book05LocalClassFieldTheory.Chapter01.Chapter01ResidueField
        valuation)]
  valuation_coordinate :
    LastLib.Book05LocalClassFieldTheory.Chapter01.Chapter01ValuationCoordinateData
      valuation
  [unit_group_topology :
      TopologicalSpace
        (LastLib.Book05LocalClassFieldTheory.Chapter01.Chapter01UnitGroup
          valuation)]
  [unit_group_topological :
      IsTopologicalGroup
        (LastLib.Book05LocalClassFieldTheory.Chapter01.Chapter01UnitGroup
          valuation)]
  coordinate_equiv :
    Nonempty
      (Kˣ ≃ₜ*
        Multiplicative ℤ ×
          LastLib.Book05LocalClassFieldTheory.Chapter01.Chapter01UnitGroup
            valuation)

/-- Compatibility name for the canonical multiplicative norm homomorphism. -/
abbrev chapter07NormHom
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Lˣ →* Kˣ :=
  LastLib.Book05LocalClassFieldTheory.Chapter01.chapter01NormHom K L

/-- Compatibility name for the canonical norm subgroup of K-units. -/
abbrev chapter07NormSubgroup
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Subgroup Kˣ :=
  LastLib.Book05LocalClassFieldTheory.Chapter01.chapter01NormSubgroup K L

@[simp]
theorem chapter07_mem_norm_subgroup_iff
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : Kˣ) :
    x ∈ chapter07NormSubgroup (K := K) (L := L) ↔
      ∃ y : Lˣ, chapter07NormHom (K := K) (L := L) y = x := by
  rfl

/- The finite Artin system is supplied canonically by Chapter 1; this name
keeps the Chapter 7-facing API stable while avoiding a duplicate record. -/
abbrev Chapter07FiniteArtinSystem
    (K KAb : Type*) [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] :=
  LastLib.Book05LocalClassFieldTheory.Chapter01.Chapter01FiniteArtinSystem K KAb

/-- The compatible family of finite Artin values as a point of the canonical
Mathlib inverse limit of finite Galois groups. -/
noncomputable def Chapter07FiniteArtinSystem.toLimitHom
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb) :
    Kˣ →* ProfiniteGrp.limit (InfiniteGalois.asProfiniteGaloisGroupFunctor K KAb) where
  toFun x :=
    { val := fun L => S.artin L.unop x
      property := by
        intro L₁ L₂ f
        exact S.compatible f x }
  map_one' := by
    apply Subtype.ext
    funext L
    exact map_one (S.artin L.unop)
  map_mul' x y := by
    apply Subtype.ext
    funext L
    exact map_mul (S.artin L.unop) x y

/-- The book's maximality predicate for a chosen model of K-ab. -/
abbrev chapter07IsMaximalAbelianExtension
    (K : Type u) (KAb : Type v) [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] : Prop :=
  LastLib.Book05LocalClassFieldTheory.Chapter01.chapter01IsMaximalAbelianExtension K KAb

/-- A chosen model for the compositum of all finite abelian extensions.  The
preceding chapters may replace this book-facing carrier by a subfield of a
fixed separable closure during reconciliation. -/
abbrev Chapter07MaximalAbelianExtensionData
    (K : Type*) [Field K] :=
  LastLib.Book05LocalClassFieldTheory.Chapter01.Chapter01MaximalAbelianExtensionData K

/-- Open finite-index subgroups of a topological group.  The underlying
subgroup is a subtype so that its order is inherited from Subgroup. -/
abbrev Chapter07OpenFiniteIndexSubgroup
    (G : Type*) [Group G] [TopologicalSpace G] :=
  LastLib.Book05LocalClassFieldTheory.Chapter01.Chapter01OpenFiniteIndexSubgroup G

/-! The source completion is indexed by open finite-index quotients.  Mathlib's
abstract `ProfiniteCompletion` uses all finite-index normal subgroups, which is
strictly larger in general; the topology-sensitive diagram below keeps the two
constructions distinct. -/

abbrev Chapter07OpenFiniteIndexNormalSubgroup
    (G : Type*) [Group G] [TopologicalSpace G] :=
  LastLib.Book05LocalClassFieldTheory.Chapter01.Chapter01OpenFiniteIndexNormalSubgroup G

abbrev chapter07OpenFiniteIndexDiagram
    (G : Type*) [CommGroup G] [TopologicalSpace G] :
    Chapter07OpenFiniteIndexNormalSubgroup G ⥤ FiniteGrp :=
  LastLib.Book05LocalClassFieldTheory.Chapter01.chapter01OpenFiniteIndexDiagram G

abbrev chapter07OpenFiniteIndexProfiniteDiagram
    (G : Type*) [CommGroup G] [TopologicalSpace G] :
    Chapter07OpenFiniteIndexNormalSubgroup G ⥤ ProfiniteGrp :=
  LastLib.Book05LocalClassFieldTheory.Chapter01.chapter01OpenFiniteIndexProfiniteDiagram G

/-- The topology-sensitive profinite completion over open finite-index
quotients. -/
abbrev chapter07OpenProfiniteCompletion
    (G : Type*) [CommGroup G] [TopologicalSpace G] : ProfiniteGrp :=
  LastLib.Book05LocalClassFieldTheory.Chapter01.chapter01OpenProfiniteCompletion G

abbrev Chapter07OpenProfiniteCompletion
    (G : Type*) [CommGroup G] [TopologicalSpace G] : Type _ :=
  (chapter07OpenProfiniteCompletion G : Type _)

abbrev chapter07OpenProfiniteCompletionEtaFn
    (G : Type*) [CommGroup G] [TopologicalSpace G] (g : G) :
    Chapter07OpenProfiniteCompletion G :=
  LastLib.Book05LocalClassFieldTheory.Chapter01.chapter01OpenProfiniteCompletionEtaFn G g

abbrev chapter07OpenProfiniteCompletionEta
    (G : Type*) [CommGroup G] [TopologicalSpace G] :
    G →* Chapter07OpenProfiniteCompletion G :=
  LastLib.Book05LocalClassFieldTheory.Chapter01.chapter01OpenProfiniteCompletionEta G

abbrev chapter07OpenProfiniteCompletionProjection
    (G : Type*) [CommGroup G] [TopologicalSpace G]
    (H : Chapter07OpenFiniteIndexNormalSubgroup G) :
    Chapter07OpenProfiniteCompletion G →* (G ⧸ H.toSubgroup) :=
  LastLib.Book05LocalClassFieldTheory.Chapter01.chapter01OpenProfiniteCompletionProjection G H

@[simp]
theorem chapter07OpenProfiniteCompletionProjection_eta
    (G : Type*) [CommGroup G] [TopologicalSpace G]
    (H : Chapter07OpenFiniteIndexNormalSubgroup G) (g : G) :
    chapter07OpenProfiniteCompletionProjection G H
        (chapter07OpenProfiniteCompletionEta G g) = QuotientGroup.mk g := by
  exact LastLib.Book05LocalClassFieldTheory.Chapter01.chapter01OpenProfiniteCompletionProjection_eta
    G H g

noncomputable def chapter07OpenFiniteIndexSubgroup.toNormal
    {G : Type*} [CommGroup G] [TopologicalSpace G]
    (H : Chapter07OpenFiniteIndexSubgroup G) :
    Chapter07OpenFiniteIndexNormalSubgroup G :=
  { toSubgroup := H.1
    isNormal' := by infer_instance
    isFiniteIndex' := H.2.2
    isOpen := H.2.1 }

@[simp]
theorem chapter07OpenFiniteIndexSubgroup.toNormal_toSubgroup
    {G : Type*} [CommGroup G] [TopologicalSpace G]
    (H : Chapter07OpenFiniteIndexSubgroup G) :
    (chapter07OpenFiniteIndexSubgroup.toNormal H).toSubgroup = H.1 :=
  rfl

/-- Positive integer indices used for the cofinal precision family. -/
abbrev Chapter07PositiveNat := {n : ℕ // 0 < n}

/-- A book-facing valuation/unit interface for the separation argument.  The
three fields are the exact elementary bridges used to pass from precision
subgroups to valuation divisibility and then to the identity. -/
structure Chapter07PrecisionData (G : Type*) [CommGroup G] where
  valuation : G →* Multiplicative ℤ
  uniformizer : G
  unitFiltration : ℕ → Subgroup G
  valuation_uniformizer :
    valuation uniformizer = Multiplicative.ofAdd 1
  valuation_precision :
    ∀ {m n : Chapter07PositiveNat} {x : G},
      x ∈ Subgroup.zpowers (uniformizer ^ m.1) ⊔ unitFiltration n.1 →
        (m.1 : ℤ) ∣ Multiplicative.toAdd (valuation x)
  normalized_precision :
    ∀ {m n : Chapter07PositiveNat} {x : G},
      x ∈ Subgroup.zpowers (uniformizer ^ m.1) ⊔ unitFiltration n.1 →
        x * uniformizer ^ (-(Multiplicative.toAdd (valuation x))) ∈
          unitFiltration n.1
  units_separated :
    ∀ {x : G}, (∀ n : ℕ, x ∈ unitFiltration n) → x = 1

/-- The standard finite-precision subgroup pi^(mZ) U^n. -/
def chapter07PrecisionSubgroup
    {G : Type*} [CommGroup G] (D : Chapter07PrecisionData G)
    (m n : Chapter07PositiveNat) : Subgroup G :=
  Subgroup.zpowers (D.uniformizer ^ m.1) ⊔ D.unitFiltration n.1

@[simp]
theorem chapter07_mem_precision_subgroup_iff
    {G : Type*} [CommGroup G] (D : Chapter07PrecisionData G)
    (m n : Chapter07PositiveNat) (x : G) :
    x ∈ chapter07PrecisionSubgroup D m n ↔
      ∃ z : ℤ, ∃ u : G, u ∈ D.unitFiltration n.1 ∧
        x = D.uniformizer ^ (m.1 * z) * u := by
  sorry

/-- The intersection of all positive precision subgroups. -/
def chapter07PrecisionIntersection
    {G : Type*} [CommGroup G] (D : Chapter07PrecisionData G) : Subgroup G :=
  ⨅ m : Chapter07PositiveNat, ⨅ n : Chapter07PositiveNat,
    chapter07PrecisionSubgroup D m n

/- LOCAL_DEPENDENCY_GUESS: Chapter 6's explicit unramified/formal-module
construction supplies finite abelian norm subgroups refining every displayed
precision subgroup.  This is the cofinality input needed to control the
kernel; it does not assume the kernel conclusion itself. -/
def chapter07KernelCofinality
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb]
    (D : Chapter07PrecisionData Kˣ) : Prop :=
  ∀ (m n : Chapter07PositiveNat),
    ∃ L : Chapter07FiniteAbelianIndex K KAb,
      chapter07NormSubgroup (K := K) (L := L) ≤
        chapter07PrecisionSubgroup D m n

/- LOCAL_DEPENDENCY_GUESS: the finite-level existence theorem identifies all
open finite-index subgroups with norm subgroups inside the selected K-ab.
It is kept as a proposition so the completion and order-correspondence
statements can depend on the exact source-facing assertion. -/
def chapter07ExistenceProperty
    (K KAb : Type*) [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsAbelianGalois K KAb] : Prop :=
  ∀ H : Chapter07OpenFiniteIndexSubgroup Kˣ,
    ∃! L : Chapter07FiniteAbelianIndex K KAb,
      chapter07NormSubgroup (K := K) (L := L) = H.1

/-- The abstract profinite completion of a group, using Mathlib's finite-index
normal subgroup diagram.  The topology-sensitive local-field completion is
`Chapter07OpenProfiniteCompletion` below. -/
abbrev Chapter07ProfiniteCompletion (G : Type*) [Group G] : Type _ :=
  LastLib.Book05LocalClassFieldTheory.Chapter01.Chapter01ProfiniteCompletion G

/-- The profinite integers in the multiplicative presentation used by
ProfiniteGrp. -/
abbrev Chapter07ProfiniteIntegers : Type _ :=
  Chapter07OpenProfiniteCompletion (Multiplicative ℤ)

/-- The canonical copy of the integer z in the profinite integers. -/
noncomputable def chapter07IntegerToProfiniteCompletionHom :
    Multiplicative ℤ →* Chapter07ProfiniteIntegers where
  toFun := chapter07OpenProfiniteCompletionEtaFn (Multiplicative ℤ)
  map_one' := rfl
  map_mul' _ _ := rfl

noncomputable def chapter07IntegerToProfiniteCompletion
    (z : ℤ) : Chapter07ProfiniteIntegers :=
  chapter07IntegerToProfiniteCompletionHom (Multiplicative.ofAdd z)

@[simp]
theorem chapter07IntegerToProfiniteCompletion_zero :
    chapter07IntegerToProfiniteCompletion 0 = 1 := by
  rfl

@[simp]
theorem chapter07IntegerToProfiniteCompletion_add (m n : ℤ) :
    chapter07IntegerToProfiniteCompletion (m + n) =
      chapter07IntegerToProfiniteCompletion m *
        chapter07IntegerToProfiniteCompletion n := by
  rfl

end

end LastLib.Book05LocalClassFieldTheory.Chapter07
