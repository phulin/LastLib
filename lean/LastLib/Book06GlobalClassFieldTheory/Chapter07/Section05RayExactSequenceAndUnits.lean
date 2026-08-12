import LastLib.Book06GlobalClassFieldTheory.Chapter07.Section02IdealTheoreticRayClasses
import Mathlib.Data.ZMod.QuotientRing

/-!
# 7.5. The ray exact sequence and units

The exact sequence is presented as a structure so that its three maps and the
two exactness points are available to later sections without hiding the weak
approximation step in a quotient definition.  The standard cardinality formula
is included because it is the precise form of the source's observation that
global units can reduce the ray class number.
-/

namespace LastLib.Book06GlobalClassFieldTheory.Chapter07

open scoped BigOperators nonZeroDivisors
open NumberField

noncomputable section

variable {K I : Type*} [Field K] [NumberField K]
  [CommGroup I] [TopologicalSpace I] [IsTopologicalGroup I]

def rayResidueSignGroup (m : Modulus K) : Type _ :=
  (𝓞 K ⧸ m.finitePart)ˣ ×
    ({v : RealPlace K // v ∈ m.infinitePart} → ℤˣ)

instance rayResidueSignGroupCommGroup (m : Modulus K) :
    CommGroup (rayResidueSignGroup m) := by
  change CommGroup ((𝓞 K ⧸ m.finitePart)ˣ ×
    ({v : RealPlace K // v ∈ m.infinitePart} → ℤˣ))
  infer_instance

def residueUnitMap (m : Modulus K) :
    (𝓞 K)ˣ →* (𝓞 K ⧸ m.finitePart)ˣ :=
  Units.map (Ideal.Quotient.mk m.finitePart).toMonoidHom

def realSignOfUnit (v : RealPlace K) : (𝓞 K)ˣ →* ℤˣ := by
  refine
    { toFun := fun u =>
        if 0 < v.1.embedding_of_isReal v.2
            (algebraMap (𝓞 K) K (u : 𝓞 K)) then 1 else -1
      map_one' := ?_
      map_mul' := ?_ }
  · sorry
  · intro u w
    sorry

def globalUnitResidueSignMap (m : Modulus K) :
    (𝓞 K)ˣ →* rayResidueSignGroup m := by
  refine
    { toFun := fun u =>
        (residueUnitMap m u,
          fun v => realSignOfUnit v.1 u)
      map_one' := ?_
      map_mul' := ?_ }
  · sorry
  · sorry

noncomputable instance globalUnitResidueSignRangeFintype
    (m : Modulus K) [Fintype (rayResidueSignGroup m)] :
    Fintype ((globalUnitResidueSignMap m).range) :=
  Fintype.ofFinite _

structure RayExactSequenceData (m : Modulus K) where
  unitMap : (𝓞 K)ˣ →* rayResidueSignGroup m
  residueToRay : rayResidueSignGroup m →* idealRayClassGroup m
  rayToClass : idealRayClassGroup m →* ClassGroup (𝓞 K)
  unitMap_is_global : unitMap = globalUnitResidueSignMap m
  exact_at_residue : Function.MulExact unitMap residueToRay
  exact_at_ray : Function.MulExact residueToRay rayToClass
  rayToClass_surjective : Function.Surjective rayToClass

noncomputable def ray_exact_sequence (m : Modulus K) : RayExactSequenceData m := by
  sorry

theorem ray_exact_sequence_is
    (m : Modulus K) :
    Function.MulExact (globalUnitResidueSignMap m)
      (ray_exact_sequence m).residueToRay := by
  rw [← (ray_exact_sequence m).unitMap_is_global]
  exact (ray_exact_sequence m).exact_at_residue

theorem ray_exact_sequence_is_exact_at_class_group
    (m : Modulus K) :
    Function.MulExact (ray_exact_sequence m).residueToRay
      (ray_exact_sequence m).rayToClass :=
  (ray_exact_sequence m).exact_at_ray

theorem ray_exact_sequence_surjects_onto_class_group
    (m : Modulus K) :
    Function.Surjective (ray_exact_sequence m).rayToClass :=
  (ray_exact_sequence m).rayToClass_surjective

theorem ray_exact_sequence_card_formula
    (m : Modulus K)
    [Fintype (rayResidueSignGroup m)] [Fintype (idealRayClassGroup m)]
    [Fintype (ClassGroup (𝓞 K))] :
    Fintype.card (idealRayClassGroup m) *
        Fintype.card ((globalUnitResidueSignMap m).range) =
      Fintype.card (rayResidueSignGroup m) * Fintype.card (ClassGroup (𝓞 K)) := by
  sorry

theorem positive_rank_units_can_reduce_the_ray_class_number
    (m : Modulus K)
    [Fintype (rayResidueSignGroup m)] [Fintype (idealRayClassGroup m)]
    [Fintype (ClassGroup (𝓞 K))]
    (hunits : 1 < Fintype.card ((globalUnitResidueSignMap m).range)) :
    Fintype.card (idealRayClassGroup m) <
      Fintype.card (rayResidueSignGroup m) * Fintype.card (ClassGroup (𝓞 K)) := by
  sorry

/-! ### The rational example -/

def rationalFiniteModulus (n : ℕ) (hn : n ≠ 0) : Modulus ℚ :=
  { finitePart := Ideal.span ({(n : 𝓞 ℚ)} : Set (𝓞 ℚ))
    finitePart_ne_bot := by
      sorry
    infinitePart := ∅ }

def rationalNarrowModulus (n : ℕ) (hn : n ≠ 0) : Modulus ℚ :=
  { finitePart := Ideal.span ({(n : 𝓞 ℚ)} : Set (𝓞 ℚ))
    finitePart_ne_bot := by
      sorry
    infinitePart := Finset.univ }

def rationalSignSubgroup (n : ℕ) : Subgroup (ZMod n)ˣ :=
  Subgroup.closure ({(-1 : (ZMod n)ˣ)} : Set (ZMod n)ˣ)

noncomputable def rational_narrow_ray_class_group_equiv_units_mod
    (n : ℕ) (hn : n ≠ 0) :
    idealRayClassGroup (rationalNarrowModulus n hn) ≃* (ZMod n)ˣ := by
  sorry

noncomputable def rational_ordinary_ray_class_group_equiv_units_mod_signs
    (n : ℕ) (hn : n ≠ 0) :
    idealRayClassGroup (rationalFiniteModulus n hn) ≃*
      (ZMod n)ˣ ⧸ rationalSignSubgroup n := by
  sorry

noncomputable def rational_ordinary_ray_class_group_is_the_quotient_by_pm_one
    (n : ℕ) (hn : n ≠ 0) :
    idealRayClassGroup (rationalFiniteModulus n hn) ≃*
      ((ZMod n)ˣ ⧸ rationalSignSubgroup n) := by
  exact rational_ordinary_ray_class_group_equiv_units_mod_signs n hn

theorem rational_infinity_adds_the_sign_condition
    (n : ℕ) (hn : n ≠ 0) :
    ∀ u : (𝓞 ℚ)ˣ,
      Units.map (algebraMap (𝓞 ℚ) ℚ).toMonoidHom u ∈
        rayPrincipalCongruence (rationalNarrowModulus n hn) →
        0 < algebraMap (𝓞 ℚ) ℚ (u : 𝓞 ℚ) := by
  intro u hu
  sorry

end

end LastLib.Book06GlobalClassFieldTheory.Chapter07
