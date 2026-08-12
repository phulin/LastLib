import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.Section01TheLocalExtensionProblem
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.Topology.Algebra.Group.Basic

namespace LastLib.Book05LocalClassFieldTheory.Chapter07

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators WithZero

universe u v

/-!
Shared interfaces for Chapter 7.  The preceding chapters supply the finite
Artin maps, their norm kernels, the cofinal precision family, and the local
existence theorem.  Those declarations are not present in this isolated
chapter draft, so the records below keep exactly those interfaces explicit.
They do not assume any of the conclusions of the infinite reciprocity
theorem.
-/

/-- The finite abelian levels inside a chosen maximal abelian extension. -/
abbrev Chapter07FiniteAbelianIndex
    (K KAb : Type*) [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] :=
  FiniteGaloisIntermediateField K KAb

/- LOCAL_DEPENDENCY_GUESS: earlier Book 5 chapters should expose a canonical
local-field context; until it is reconciled, this is the exact Book 2
valuation/completeness/finite-residue interface used by Chapter 7. -/
structure Chapter07LocalFieldData (K : Type*) [Field K] where
  valuation : Valuation K ℤᵐ⁰
  complete_discrete :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.chapter01CompleteDiscreteValuation
      K valuation
  [residue_finite : Finite
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.chapter01ResidueField
        valuation)]

/-- The multiplicative norm homomorphism on units. -/
noncomputable def chapter07NormHom
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Lˣ →* Kˣ :=
  Units.map (Algebra.norm K (S := L))

/-- The norm subgroup of K-units attached to a finite extension L/K. -/
noncomputable def chapter07NormSubgroup
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Subgroup Kˣ :=
  (chapter07NormHom (K := K) (L := L)).range

@[simp]
theorem chapter07_mem_norm_subgroup_iff
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : Kˣ) :
    x ∈ chapter07NormSubgroup (K := K) (L := L) ↔
      ∃ y : Lˣ, chapter07NormHom (K := K) (L := L) y = x := by
  rfl

/- LOCAL_DEPENDENCY_GUESS: this is the finite-level interface supplied by
Chapters 3--6.  The kernel equation is the finite reciprocity/norm theorem;
the compatibility field is the restriction compatibility needed to form the
inverse-limit tuple. -/
structure Chapter07FiniteArtinSystem
    (K KAb : Type*) [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] where
  artin : ∀ L : Chapter07FiniteAbelianIndex K KAb, Kˣ →* Gal(L / K)
  surjective : ∀ L, Function.Surjective (artin L)
  kernel_eq_norm : ∀ L,
    (artin L).ker = chapter07NormSubgroup (K := K) (L := L)
  compatible :
    ∀ {L₁ L₂ : (FiniteGaloisIntermediateField K KAb)ᵒᵖ}
      (f : L₁ ⟶ L₂) (x : Kˣ),
      (finGaloisGroupMap f).hom (artin L₁.unop x) = artin L₂.unop x

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
def chapter07IsMaximalAbelianExtension
    (K : Type u) (KAb : Type v) [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] : Prop :=
  ∀ (L : Type v) [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L], Nonempty (L →ₐ[K] KAb)

/-- A chosen model for the compositum of all finite abelian extensions.  The
preceding chapters may replace this book-facing carrier by a subfield of a
fixed separable closure during reconciliation. -/
structure Chapter07MaximalAbelianExtensionData
    (K : Type*) [Field K] where
  extension : IntermediateField K (AlgebraicClosure K)
  [abelian_galois_extension : IsAbelianGalois K extension]
  maximal : chapter07IsMaximalAbelianExtension K extension
  contained_in_separable_closure :
    extension ≤ separableClosure K (AlgebraicClosure K)

/-- Open finite-index subgroups of a topological group.  The underlying
subgroup is a subtype so that its order is inherited from Subgroup. -/
abbrev Chapter07OpenFiniteIndexSubgroup
    (G : Type*) [Group G] [TopologicalSpace G] :=
  {H : Subgroup G // IsOpen (H : Set G) ∧ H.FiniteIndex}

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
construction supplies this cofinality statement. -/
def chapter07KernelCofinality
    {G H : Type*} [CommGroup G] [Group H]
    (r : G →* H) (D : Chapter07PrecisionData G) : Prop :=
  ∀ {x : G}, x ∈ r.ker →
    ∀ (m n : Chapter07PositiveNat), x ∈ chapter07PrecisionSubgroup D m n

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

/-- The profinite completion of a group, using Mathlib's finite-index normal
subgroup diagram.  For the abelian group K-units, this is the completion over
all finite-index subgroups. -/
abbrev Chapter07ProfiniteCompletion (G : Type*) [Group G] : Type _ :=
  (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) : Type _)

/-- The profinite integers in the multiplicative presentation used by
ProfiniteGrp. -/
abbrev Chapter07ProfiniteIntegers : Type _ :=
  Chapter07ProfiniteCompletion (Multiplicative ℤ)

/-- The canonical copy of the integer z in the profinite integers. -/
noncomputable def chapter07IntegerToProfiniteCompletionHom :
    Multiplicative ℤ →* Chapter07ProfiniteIntegers where
  toFun :=
    ProfiniteGrp.ProfiniteCompletion.etaFn
      (GrpCat.of (Multiplicative ℤ))
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
