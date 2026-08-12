import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Subring.Units
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.FractionalIdeal
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Multiplicity
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Topology.Algebra.Group.Quotient

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
`IdeleContext` is the one intentionally provisional interface in this chapter.
Earlier chapter files in the repository do not yet expose one canonical global
idele object, so all later definitions factor through these principal and local
component homomorphisms, together with the valuation map and its principal
compatibility.  The global product/restricted-product laws belong to the
earlier global API.
-/
structure IdeleContext (K I : Type*) [Field K] [NumberField K]
    [CommGroup I] [TopologicalSpace I] [IsTopologicalGroup I] where
  principal : Kˣ →* I
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
  (⨆ v : NumberField.FinitePlace K,
      Subgroup.map (D.finiteComponent v) (finiteUnitFiltration v (m.finiteExponent v))) ⊔
    (⨆ v : NumberField.InfinitePlace K,
      Subgroup.map (D.infiniteComponent v) (infiniteUnitSubgroup m v))

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

/-! These are the topology and finiteness bridges used in Section 7.1.  They
are the precise places where the preceding global idele topology and the
finite-index theorem will be plugged in during the fixup pass. -/

theorem rayIdeleSubgroup_isOpen (D : IdeleContext K I) (m : Modulus K) :
    IsOpen (rayIdeleSubgroup D m : Set I) := by
  sorry

theorem rayIdeleSubgroup_isClosed (D : IdeleContext K I) (m : Modulus K) :
    IsClosed (rayIdeleSubgroup D m : Set I) := by
  sorry

theorem rayClassSubgroup_isOpen (D : IdeleContext K I) (m : Modulus K) :
    IsOpen (rayClassSubgroup D m : Set (ideleClassGroup D)) := by
  sorry

theorem rayClassSubgroup_isClosed (D : IdeleContext K I) (m : Modulus K) :
    IsClosed (rayClassSubgroup D m : Set (ideleClassGroup D)) := by
  sorry

theorem rayClassGroup_finite (D : IdeleContext K I) (m : Modulus K) :
    Finite (rayClassGroup D m) := by
  sorry

/-! ### Artin and extension presentations -/

variable {G : Type*} [CommGroup G] [Fintype G]

structure AbelianArtinData (D : IdeleContext K I) (G : Type*)
    [CommGroup G] [Fintype G] where
  artin : I →* G
  classArtin : ideleClassGroup D →* G
  classArtin_factor : classArtin.comp (ideleClassQuotient D) = artin
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
  complexified : RealPlace K → Prop

def artinKernel {D : IdeleContext K I}
    (A : AbelianArtinData (K := K) (I := I) D G) : Subgroup (ideleClassGroup D) :=
  A.classArtin.ker

structure FiniteAbelianExtensionRealization
    (K L G : Type*) [Field K] [NumberField K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [CommGroup G] [Fintype G] where
  galoisEquiv : G ≃* Gal(L / K)

end

end LastLib.Book06GlobalClassFieldTheory.Chapter07
