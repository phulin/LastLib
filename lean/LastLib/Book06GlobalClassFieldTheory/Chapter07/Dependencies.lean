import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Subring.Units
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.FractionalIdeal
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Multiplicity
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Topology.Algebra.Group.Quotient
import LastLib.Book06GlobalClassFieldTheory.Chapter06.Section04ClassificationByOpenSubgroups

/-!
# Chapter 7: shared interfaces

This file is deliberately a small book-facing interface layer.  Mathlib has the
local completions, valuation subrings, fractional ideals, and class groups used
below, but it does not expose a global idele class field theory API.  The
`IdeleContext` and `AbelianArtinData` structures are therefore explicit
dependency interfaces for the preceding global class field theory chapters.
They are not replacement definitions of the canonical objects.
-/

namespace LastLib.Book06GlobalClassFieldTheory.Chapter07

open scoped BigOperators nonZeroDivisors
open NumberField

noncomputable section

/-! ### Places and moduli -/

abbrev RealPlace (K : Type*) [Field K] [NumberField K] :=
  {v : NumberField.InfinitePlace K // v.IsReal}

noncomputable instance realPlaceFintype (K : Type*) [Field K] [NumberField K] :
    Fintype (RealPlace K) :=
  Fintype.ofFinite (RealPlace K)

/-- A modulus is a nonzero finite ideal together with a finite set of real places.

The finite ideal is stored as a whole rather than as an ideal plus a formal
infinite component.  Its `multiplicity` at a finite place is the exponent used
by the local unit filtration.
-/
structure Modulus (K : Type*) [Field K] [NumberField K] where
  finitePart : Ideal (𝓞 K)
  finitePart_ne_bot : finitePart ≠ ⊥
  infinitePart : Finset (RealPlace K)

namespace Modulus

variable {K : Type*} [Field K] [NumberField K]

instance : Inhabited (Modulus K) := ⟨
  { finitePart := ⊤
    finitePart_ne_bot := by simp
    infinitePart := ∅ }⟩

/-- The empty modulus, corresponding to the ordinary unramified condition. -/
def one : Modulus K := default

@[simp] theorem one_finitePart : (one : Modulus K).finitePart = ⊤ := rfl
@[simp] theorem one_infinitePart : (one : Modulus K).infinitePart = ∅ := rfl

/-- The finite conductor exponent attached to a finite place. -/
def finiteExponent (m : Modulus K) (v : NumberField.FinitePlace K) : ℕ :=
  multiplicity v.maximalIdeal.asIdeal m.finitePart

/-- Divisibility of moduli: ideal divisibility and inclusion of real places. -/
def Divides (m n : Modulus K) : Prop :=
  m.finitePart ∣ n.finitePart ∧
    ∀ v, v ∈ m.infinitePart → v ∈ n.infinitePart

instance : LE (Modulus K) := ⟨fun m n => Divides m n⟩

theorem divides_iff {m n : Modulus K} : m ≤ n ↔ Divides m n := Iff.rfl

theorem finiteExponent_eq_zero_of_not_dvd
    (m : Modulus K) (v : NumberField.FinitePlace K)
    (h : ¬v.maximalIdeal.asIdeal ∣ m.finitePart) :
    m.finiteExponent v = 0 := by
  sorry

theorem finiteExponent_pos_iff_dvd
    (m : Modulus K) (v : NumberField.FinitePlace K) :
    0 < m.finiteExponent v ↔ v.maximalIdeal.asIdeal ∣ m.finitePart := by
  sorry

theorem finiteExponent_le_of_divides {m n : Modulus K} (h : m ≤ n)
    (v : NumberField.FinitePlace K) :
    m.finiteExponent v ≤ n.finiteExponent v := by
  sorry

theorem finitePart_eq_finprod (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    (∏ᶠ v : NumberField.FinitePlace K,
      v.maximalIdeal.asIdeal ^ multiplicity v.maximalIdeal.asIdeal I) = I := by
  sorry

theorem finitePart_eq_finprod_exponents (m : Modulus K) :
    (∏ᶠ v : NumberField.FinitePlace K,
      v.maximalIdeal.asIdeal ^ m.finiteExponent v) = m.finitePart := by
  exact finitePart_eq_finprod m.finitePart m.finitePart_ne_bot

theorem infinitePart_mem_isReal (m : Modulus K) {v : RealPlace K}
    (_hv : v ∈ m.infinitePart) : v.1.IsReal := by
  exact v.2

end Modulus

/-! ### The local subgroups occurring in a modulus -/

variable {K : Type*} [Field K] [NumberField K]

/-- The subgroup (U_v^n) in the multiplicative group of the finite completion.

For `n = 0` this is the unit group of the valuation ring.  For positive `n` it
is the subgroup of units whose difference from one lies in the `n`-th power of
the maximal ideal of the valuation ring.  The subgroup proofs are the standard
local-ring calculation and are intentionally left for the proof pass.
-/
def finiteUnitFiltration (v : NumberField.FinitePlace K) (n : ℕ) :
    Subgroup ((v.maximalIdeal.adicCompletion K)ˣ) where
  carrier := {x | if n = 0 then
      x ∈ (v.maximalIdeal.adicCompletionIntegers K).unitGroup
    else
      ∃ hx : ((x : v.maximalIdeal.adicCompletion K) - 1) ∈
          (v.maximalIdeal.adicCompletionIntegers K : Set _),
        (⟨(x : v.maximalIdeal.adicCompletion K) - 1, hx⟩ :
            v.maximalIdeal.adicCompletionIntegers K) ∈
          (IsLocalRing.maximalIdeal (v.maximalIdeal.adicCompletionIntegers K)) ^ n}
  one_mem' := by
    sorry
  mul_mem' := by
    sorry
  inv_mem' := by
    sorry

@[simp] theorem finiteUnitFiltration_zero (v : NumberField.FinitePlace K) :
    finiteUnitFiltration v 0 =
      (v.maximalIdeal.adicCompletionIntegers K).unitGroup := by
  sorry

theorem finiteUnitFiltration_one (v : NumberField.FinitePlace K) :
    finiteUnitFiltration v 1 =
      (v.maximalIdeal.adicCompletionIntegers K).principalUnitGroup := by
  sorry

theorem finiteUnitFiltration_antitone (v : NumberField.FinitePlace K) :
    Antitone (finiteUnitFiltration v) := by
  sorry

theorem finiteUnitFiltration_mem_iff (v : NumberField.FinitePlace K)
    (n : ℕ) (x : (v.maximalIdeal.adicCompletion K)ˣ) :
    x ∈ finiteUnitFiltration v n ↔
      (if n = 0 then
        x ∈ (v.maximalIdeal.adicCompletionIntegers K).unitGroup
      else
        ∃ hx : ((x : v.maximalIdeal.adicCompletion K) - 1) ∈
            (v.maximalIdeal.adicCompletionIntegers K : Set _),
          (⟨(x : v.maximalIdeal.adicCompletion K) - 1, hx⟩ :
              v.maximalIdeal.adicCompletionIntegers K) ∈
            (IsLocalRing.maximalIdeal (v.maximalIdeal.adicCompletionIntegers K)) ^ n) := by
  rfl

/-- The positive subgroup at a real infinite place, transported from `ℝ`. -/
def realPositiveUnitSubgroup (v : RealPlace K) : Subgroup (v.1.Completion)ˣ :=
  (Units.posSubgroup ℝ).comap
    (Units.map
      (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal v.2).toMonoidHom)

/-- The infinite component of the unit subgroup attached to a modulus. -/
def infiniteUnitSubgroup (m : Modulus K) (v : NumberField.InfinitePlace K) :
    Subgroup (v.Completion)ˣ := by
  classical
  by_cases hv : v.IsReal
  · by_cases hvm : (⟨v, hv⟩ : RealPlace K) ∈ m.infinitePart
    · exact realPositiveUnitSubgroup (⟨v, hv⟩ : RealPlace K)
    · exact ⊤
  · exact ⊤

theorem infiniteUnitSubgroup_eq_top_of_not_selected
    (m : Modulus K) (v : NumberField.InfinitePlace K)
    (hv : ¬v.IsReal ∨ (∀ h : v.IsReal, (⟨v, h⟩ : RealPlace K) ∉ m.infinitePart)) :
    infiniteUnitSubgroup m v = ⊤ := by
  sorry

/-! ### Idele and Artin dependency interfaces -/

/-!
`IdeleContext` remains the local-component interface used by the chapter, but
the class-field statements below also retain an explicit bridge to the
canonical global existence and norm--Artin API from Chapter 6.  The full
ray-unit subgroup is supplied as part of this dependency interface: it cannot
be reconstructed as an algebraic supremum of the individual local images,
since a restricted product also contains arbitrary simultaneous local
components.
-/
structure IdeleContext (K I : Type*) [Field K] [NumberField K]
    [CommGroup I] [TopologicalSpace I] [IsTopologicalGroup I] where
  principal : Kˣ →* I
  principal_injective : Function.Injective principal
  finiteComponent :
    ∀ v : NumberField.FinitePlace K,
      (v.maximalIdeal.adicCompletion K)ˣ →* I
  infiniteComponent :
    ∀ v : NumberField.InfinitePlace K,
      v.Completionˣ →* I
  ideleToFractionalIdeal :
    I →* (FractionalIdeal (𝓞 K)⁰ K)ˣ
  principal_toPrincipalIdeal :
    ideleToFractionalIdeal.comp principal = toPrincipalIdeal (𝓞 K) K
  rayUnits : Modulus K → Subgroup I
  rayUnits_antitone :
    ∀ {m n : Modulus K}, m ≤ n → rayUnits n ≤ rayUnits m
  finiteComponent_mem_rayUnits :
    ∀ (m : Modulus K) (v : NumberField.FinitePlace K),
      Subgroup.map (finiteComponent v) (finiteUnitFiltration v (m.finiteExponent v)) ≤
        rayUnits m
  infiniteComponent_mem_rayUnits :
    ∀ (m : Modulus K) (v : NumberField.InfinitePlace K),
      Subgroup.map (infiniteComponent v) (infiniteUnitSubgroup m v) ≤ rayUnits m
  rayUnits_isOpen : ∀ m, IsOpen (rayUnits m : Set I)
  rayUnits_isClosed : ∀ m, IsClosed (rayUnits m : Set I)
  rayClassSubgroup_isOpen :
    ∀ m, IsOpen
      (Subgroup.map (QuotientGroup.mk' principal.range) (rayUnits m) :
        Set (I ⧸ principal.range))
  rayClassSubgroup_isClosed :
    ∀ m, IsClosed
      (Subgroup.map (QuotientGroup.mk' principal.range) (rayUnits m) :
        Set (I ⧸ principal.range))
  rayClassGroup_finite :
    ∀ m, Finite
      ((I ⧸ principal.range) ⧸
        Subgroup.map (QuotientGroup.mk' principal.range) (rayUnits m))

variable {K I : Type*} [Field K] [NumberField K]
  [CommGroup I] [TopologicalSpace I] [IsTopologicalGroup I]

/-! `LOCAL_DEPENDENCY_GUESS`: the preceding global chapters should eventually
replace `IdeleContext` by their canonical ideles, principal ideles, and local
component maps. -/

abbrev ideleClassGroup (D : IdeleContext K I) : Type _ :=
  I ⧸ D.principal.range

def ideleClassQuotient (D : IdeleContext K I) : I →* ideleClassGroup D :=
  QuotientGroup.mk' D.principal.range

theorem ideleClassQuotient_ker (D : IdeleContext K I) :
    (ideleClassQuotient D).ker = D.principal.range := by
  sorry

/-- The subgroup of ideles specified by the finite and infinite parts of a modulus. -/
def rayIdeleSubgroup (D : IdeleContext K I) (m : Modulus K) : Subgroup I :=
  D.rayUnits m

def rayClassSubgroup (D : IdeleContext K I) (m : Modulus K) :
    Subgroup (ideleClassGroup D) :=
  Subgroup.map (ideleClassQuotient D) (rayIdeleSubgroup D m)

abbrev rayClassGroup (D : IdeleContext K I) (m : Modulus K) : Type _ :=
  ideleClassGroup D ⧸ rayClassSubgroup D m

def rayClassQuotient (D : IdeleContext K I) (m : Modulus K) :
    I →* rayClassGroup D m :=
  (QuotientGroup.mk' (rayClassSubgroup D m)).comp (ideleClassQuotient D)

theorem rayClassQuotient_ker (D : IdeleContext K I) (m : Modulus K) :
    (rayClassQuotient D m).ker = D.principal.range ⊔ rayIdeleSubgroup D m := by
  sorry

abbrev ideleQuotientByPrincipalAndUnits (D : IdeleContext K I) (m : Modulus K) : Type _ :=
  I ⧸ (D.principal.range ⊔ rayIdeleSubgroup D m)

def rayClassGroup_equiv_ideleQuotient (D : IdeleContext K I) (m : Modulus K) :
    rayClassGroup D m ≃* ideleQuotientByPrincipalAndUnits D m := by
  sorry

/-! These are the topology and finiteness bridges used in Section 7.1.  The
preceding global idele API supplies them through `IdeleContext`. -/

theorem rayIdeleSubgroup_isOpen (D : IdeleContext K I) (m : Modulus K) :
    IsOpen (rayIdeleSubgroup D m : Set I) := by
  exact D.rayUnits_isOpen m

theorem rayIdeleSubgroup_isClosed (D : IdeleContext K I) (m : Modulus K) :
    IsClosed (rayIdeleSubgroup D m : Set I) := by
  exact D.rayUnits_isClosed m

theorem rayClassSubgroup_isOpen (D : IdeleContext K I) (m : Modulus K) :
    IsOpen (rayClassSubgroup D m : Set (ideleClassGroup D)) := by
  exact D.rayClassSubgroup_isOpen m

theorem rayClassSubgroup_isClosed (D : IdeleContext K I) (m : Modulus K) :
    IsClosed (rayClassSubgroup D m : Set (ideleClassGroup D)) := by
  exact D.rayClassSubgroup_isClosed m

theorem rayClassGroup_finite (D : IdeleContext K I) (m : Modulus K) :
    Finite (rayClassGroup D m) := by
  exact D.rayClassGroup_finite m

/-! ### Canonical global existence bridge -/

/- The preceding global-existence correspondence is parameterized by a chosen
   separable closure and character-field assignment.  Keeping that choice in
   one package makes the Chapter 7 ray-field API depend on the canonical
   correspondence rather than on an unrelated quotient witness. -/
structure CanonicalGlobalExistenceData (K : Type*) [Field K] [NumberField K] where
  Ks : Type
  [fieldKs : Field Ks]
  [algebraKs : Algebra K Ks]
  [isGaloisKs : IsGalois K Ks]
  [isSepClosedKs : IsSepClosed Ks]
  assignment :
    LastLib.Book06GlobalClassFieldTheory.Chapter06.Chapter06CharacterFieldAssignment
      K Ks (LastLib.Book06GlobalClassFieldTheory.Chapter01.BookIdeleClassGroup K)
  correspondence :
    LastLib.Book06GlobalClassFieldTheory.Chapter06.Chapter06GlobalExistenceCorrespondence
      K Ks (LastLib.Book06GlobalClassFieldTheory.Chapter01.BookIdeleClassGroup K)
      assignment

attribute [instance] CanonicalGlobalExistenceData.fieldKs
  CanonicalGlobalExistenceData.algebraKs CanonicalGlobalExistenceData.isGaloisKs
  CanonicalGlobalExistenceData.isSepClosedKs

/- The ray quotient is identified with the quotient indexed by the same open
   subgroup on the canonical idele class group.  This is the precise bridge
   needed before invoking Chapter 6 existence and inclusion reversal. -/
structure CanonicalRayClassFieldBridge
    (D : IdeleContext K I) (m : Modulus K) where
  canonicalSubgroup :
    LastLib.Book06GlobalClassFieldTheory.Chapter06.Chapter06OpenFiniteIndexSubgroup
      (LastLib.Book06GlobalClassFieldTheory.Chapter01.BookIdeleClassGroup K)
  /-- Identification of the abstract idele class group with the canonical one. -/
  canonicalClassGroupEquiv :
    ideleClassGroup D ≃*
      LastLib.Book06GlobalClassFieldTheory.Chapter01.BookIdeleClassGroup K
  rayQuotientEquiv :
    rayClassGroup D m ≃*
      (LastLib.Book06GlobalClassFieldTheory.Chapter01.BookIdeleClassGroup K ⧸
        canonicalSubgroup.subgroup)
  /-- The quotient identification is induced by the class-group identification. -/
  quotient_map_commutes :
    rayQuotientEquiv.toMonoidHom.comp
        (QuotientGroup.mk' (rayClassSubgroup D m)) =
      (QuotientGroup.mk' canonicalSubgroup.subgroup).comp
        canonicalClassGroupEquiv.toMonoidHom
  globalExistence : CanonicalGlobalExistenceData K

/-! ### Artin and extension presentations -/

variable {G : Type*} [CommGroup G] [Fintype G]

structure AbelianArtinData (D : IdeleContext K I) (G : Type*)
    [CommGroup G] [Fintype G] where
  artin : I →* G
  classArtin : ideleClassGroup D →* G
  classArtin_factor : classArtin.comp (ideleClassQuotient D) = artin
  classArtin_character_continuous :
    ∀ θ : G →* ℂˣ, Continuous (θ.comp classArtin)
  finiteLocalNorm :
    ∀ v : NumberField.FinitePlace K,
      Subgroup ((v.maximalIdeal.adicCompletion K)ˣ)
  finiteLocalNorm_eq_localArtin_kernel :
    ∀ v : NumberField.FinitePlace K,
      finiteLocalNorm v =
        (artin.comp (D.finiteComponent v)).ker
  finiteNorm_nonempty :
    ∀ v : NumberField.FinitePlace K,
      Set.Nonempty {n : ℕ | finiteUnitFiltration v n ≤ finiteLocalNorm v}
  finiteArtinSupport : Finset (NumberField.FinitePlace K)
  finiteLocalArtin_trivial_outside_support :
    ∀ {v : NumberField.FinitePlace K}, v ∉ finiteArtinSupport →
      ∀ u, u ∈ finiteUnitFiltration v 0 →
        (artin.comp (D.finiteComponent v)) u = 1
  complexified : RealPlace K → Prop
  infiniteArtin_trivial_at_complex_places :
    ∀ {v : NumberField.InfinitePlace K}, ¬v.IsReal →
      ∀ x, (artin.comp (D.infiniteComponent v)) x = 1
  infiniteArtin_trivial_on_real_positive :
    ∀ (v : RealPlace K) (x : v.1.Completionˣ),
      x ∈ realPositiveUnitSubgroup v →
        (artin.comp (D.infiniteComponent v.1)) x = 1
  infiniteArtin_trivial_at_uncomplexified_real :
    ∀ (v : RealPlace K), ¬complexified v →
      ∀ x, (artin.comp (D.infiniteComponent v.1)) x = 1
  complexified_iff_real_sign_nontrivial :
    ∀ v : RealPlace K,
      complexified v ↔
        (artin.comp (D.infiniteComponent v.1)) (-1 : v.1.Completionˣ) ≠ 1
  /-- The restricted-product step: local triviality on every component of a
  ray-unit subgroup implies triviality on the whole subgroup. -/
  rayUnits_killed_of_local_triviality :
    ∀ (m : Modulus K),
      (∀ v : NumberField.FinitePlace K,
        Subgroup.map (D.finiteComponent v)
            (finiteUnitFiltration v (m.finiteExponent v)) ≤ artin.ker) →
      (∀ v : NumberField.InfinitePlace K,
        Subgroup.map (D.infiniteComponent v)
            (infiniteUnitSubgroup m v) ≤ artin.ker) →
      D.rayUnits m ≤ artin.ker

def artinKernel {D : IdeleContext K I}
    (A : AbelianArtinData (K := K) (I := I) D G) : Subgroup (ideleClassGroup D) :=
  A.classArtin.ker

structure FiniteAbelianExtensionRealization
    (K L G : Type*) [Field K] [NumberField K] [Field L] [Algebra K L]
    [NumberField L] [FiniteDimensional K L] [IsGalois K L] [CommGroup G] [Fintype G] where
  galoisEquiv : G ≃* Gal(L / K)
  /-- The actual complete character group of this finite abelian extension. -/
  characterGroup : Finset (G →* ℂˣ)
  characterGroup_complete : ∀ θ : G →* ℂˣ, θ ∈ characterGroup

end

end LastLib.Book06GlobalClassFieldTheory.Chapter07
