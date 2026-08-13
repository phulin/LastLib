import LastLib.Book06GlobalClassFieldTheory.Chapter07.Dependencies

/-!
# 7.2. Ideal-theoretic ray classes

This file gives the ideal-side objects which are equivalent to the idele
quotients from Section 7.1.  The principal congruence subgroup is kept as a
subgroup of `Kˣ`; the fractional-ideal realization then makes the ordinary and
narrow specializations visible without identifying them by notation alone.
-/

namespace LastLib.Book06GlobalClassFieldTheory.Chapter07

open scoped BigOperators nonZeroDivisors
open NumberField

noncomputable section

variable {K I : Type*} [Field K] [NumberField K]
  [CommGroup I] [TopologicalSpace I] [IsTopologicalGroup I]

abbrev FractionalIdealUnit (K : Type*) [Field K] [NumberField K] :=
  (FractionalIdeal (𝓞 K)⁰ K)ˣ

def finiteIdeleValuation (D : IdeleContext K I) :
    I →* FractionalIdealUnit K :=
  D.ideleToFractionalIdeal

theorem finiteIdeleValuation_on_principal (D : IdeleContext K I) :
    (finiteIdeleValuation D).comp D.principal = toPrincipalIdeal (𝓞 K) K :=
  D.principal_toPrincipalIdeal

/-! A fractional ideal is prime to the finite part when its canonical
fractional-ideal valuation is zero at every prime occurring in the modulus. -/

def FractionalIdealUnitPrimeTo (m : Modulus K) (J : FractionalIdealUnit K) : Prop :=
  ∀ v : NumberField.FinitePlace K,
    m.finiteExponent v ≠ 0 →
      FractionalIdeal.count K v.maximalIdeal J.1 = 0

def rayFractionalIdealSubgroup (m : Modulus K) :
    Subgroup (FractionalIdealUnit K) where
  carrier := {J | FractionalIdealUnitPrimeTo m J}
  one_mem' := by
    sorry
  mul_mem' := by
    sorry
  inv_mem' := by
    sorry

abbrev RayFractionalIdealGroup (m : Modulus K) :=
  rayFractionalIdealSubgroup m

/-! The global congruence and sign conditions on a principal generator. -/

def rayPrincipalCongruence (m : Modulus K) : Subgroup Kˣ where
  carrier := {a |
    (∀ v : NumberField.FinitePlace K,
      0 < m.finiteExponent v →
        ∃ ha : ((a : K) : v.maximalIdeal.adicCompletion K) - 1 ∈
            (v.maximalIdeal.adicCompletionIntegers K : Set _),
          (⟨((a : K) : v.maximalIdeal.adicCompletion K) - 1, ha⟩ :
              v.maximalIdeal.adicCompletionIntegers K) ∈
            (IsLocalRing.maximalIdeal (v.maximalIdeal.adicCompletionIntegers K)) ^
              m.finiteExponent v) ∧
    (∀ v : {v : RealPlace K // v ∈ m.infinitePart},
      0 < v.1.1.embedding_of_isReal v.1.2 (a : K))}
  one_mem' := by
    sorry
  mul_mem' := by
    sorry
  inv_mem' := by
    sorry

theorem rayPrincipalCongruence_mem_iff (m : Modulus K) (a : Kˣ) :
    a ∈ rayPrincipalCongruence m ↔
      (∀ v : NumberField.FinitePlace K,
        0 < m.finiteExponent v →
          ∃ ha : ((a : K) : v.maximalIdeal.adicCompletion K) - 1 ∈
              (v.maximalIdeal.adicCompletionIntegers K : Set _),
            (⟨((a : K) : v.maximalIdeal.adicCompletion K) - 1, ha⟩ :
                v.maximalIdeal.adicCompletionIntegers K) ∈
              (IsLocalRing.maximalIdeal (v.maximalIdeal.adicCompletionIntegers K)) ^
                m.finiteExponent v) ∧
      (∀ v : {v : RealPlace K // v ∈ m.infinitePart},
        0 < v.1.1.embedding_of_isReal v.1.2 (a : K)) := by
  rfl

def principalRayHom (m : Modulus K) :
    rayPrincipalCongruence m →* rayFractionalIdealSubgroup m := by
  classical
  exact
    { toFun := fun a =>
        ⟨toPrincipalIdeal (𝓞 K) K (a : Kˣ), by
          sorry⟩
      map_one' := by
        sorry
      map_mul' := by
        sorry }

def principalRaySubgroup (m : Modulus K) :
    Subgroup (rayFractionalIdealSubgroup m) :=
  (principalRayHom m).range

abbrev idealRayClassGroup (m : Modulus K) : Type _ :=
  rayFractionalIdealSubgroup m ⧸ principalRaySubgroup m

def idealRayClassQuotient (m : Modulus K) :
    rayFractionalIdealSubgroup m →* idealRayClassGroup m :=
  QuotientGroup.mk' (principalRaySubgroup m)

/-! ### Ordinary and narrow specializations -/

def narrowModulus : Modulus K :=
  { finitePart := ⊤
    finitePart_ne_bot := by simp
    infinitePart := Finset.univ }

noncomputable def narrowToOrdinaryRayClassMap (D : IdeleContext K I) :
    rayClassGroup D narrowModulus →* rayClassGroup D Modulus.one := by
  refine QuotientGroup.map (rayClassSubgroup D narrowModulus)
    (rayClassSubgroup D Modulus.one) (MonoidHom.id _) ?_
  sorry

/-! The weak-approximation comparison with the idele presentation is recorded
as canonical ray-unit data.  The quotient map itself comes from the inclusion
of the narrow ray subgroup into the ordinary one. -/

structure CanonicalRayUnitComparison (D : IdeleContext K I) where
  rayClassEquiv : ∀ m : Modulus K,
    rayClassGroup D m ≃* idealRayClassGroup m
  ordinaryEquiv : rayClassGroup D Modulus.one ≃* ClassGroup (𝓞 K)
  signPatternToNarrow :
    ({v : RealPlace K // v ∈ (narrowModulus : Modulus K).infinitePart} → ℤˣ) →*
      rayClassGroup D narrowModulus
  signPatternToNarrow_trivial_on_global_unit_signs :
    ∀ u : (𝓞 K)ˣ,
      signPatternToNarrow
        (fun v => if 0 < v.1.1.embedding_of_isReal v.1.2
            (algebraMap (𝓞 K) K (u : 𝓞 K)) then 1 else -1) = 1
  narrowToOrdinary_kernel_eq_sign_patterns :
    (narrowToOrdinaryRayClassMap D).ker = signPatternToNarrow.range

abbrev IdeleIdealRayClassComparison (D : IdeleContext K I) :=
  CanonicalRayUnitComparison D

theorem idealRayClassGroup_finite (m : Modulus K) : Finite (idealRayClassGroup m) := by
  sorry

/-! Weak approximation gives the equivalence with the idele definition. -/

noncomputable def rayClassGroup_idealRayClassGroup_equiv
    (D : IdeleContext K I) (C : IdeleIdealRayClassComparison D) (m : Modulus K) :
    rayClassGroup D m ≃* idealRayClassGroup m :=
  C.rayClassEquiv m

theorem principal_ray_class_iff_local_congruence
    (m : Modulus K) (a : Kˣ) :
    a ∈ rayPrincipalCongruence m ↔
      (∀ v : NumberField.FinitePlace K,
        m.finiteExponent v = 0 ∨
          Units.map (algebraMap K (v.maximalIdeal.adicCompletion K)).toMonoidHom a ∈
            finiteUnitFiltration v (m.finiteExponent v)) ∧
        (∀ v : {v : RealPlace K // v ∈ m.infinitePart},
          0 < v.1.1.embedding_of_isReal v.1.2 (a : K)) := by
  sorry

abbrev NarrowClassGroup (K : Type*) [Field K] [NumberField K] :=
  idealRayClassGroup (narrowModulus (K := K))

@[simp] theorem narrowModulus_finitePart :
    (narrowModulus (K := K) : Modulus K).finitePart = ⊤ := rfl

@[simp] theorem narrowModulus_infinitePart :
    (narrowModulus (K := K) : Modulus K).infinitePart =
      (Finset.univ : Finset (RealPlace K)) := rfl

noncomputable def ordinary_ray_class_group_equiv_class_group
    (D : IdeleContext K I) (C : IdeleIdealRayClassComparison D) :
    rayClassGroup D Modulus.one ≃* ClassGroup (𝓞 K) :=
  C.ordinaryEquiv

theorem ordinary_ray_class_group_has_no_infinite_condition
    :
    ∀ v : NumberField.InfinitePlace K,
      infiniteUnitSubgroup (Modulus.one : Modulus K) v = ⊤ := by
  intro v
  exact infiniteUnitSubgroup_eq_top_of_not_selected
    (Modulus.one : Modulus K) v (Or.inr (fun h => by
      simp [Modulus.one_infinitePart]))

theorem narrow_ray_class_group_is_the_all_real_specialization
    :
    ∀ v : RealPlace K, v ∈ (narrowModulus : Modulus K).infinitePart := by
  intro v
  change v ∈ (Finset.univ : Finset (RealPlace K))
  simp

theorem narrow_to_ordinary_ray_class_map_surjective
    (D : IdeleContext K I) :
    Function.Surjective (narrowToOrdinaryRayClassMap D) := by
  sorry

noncomputable def ray_class_group_narrow_equiv_narrow_class_group
    (D : IdeleContext K I) (C : IdeleIdealRayClassComparison D) :
    rayClassGroup D narrowModulus ≃* NarrowClassGroup K := by
  exact C.rayClassEquiv narrowModulus

/-!
The equality of ordinary and narrow ray class groups is controlled by the sign
image of global units.  The exact sequence and its cardinality form are
recorded in Section 7.5; this predicate is the reusable bridge used there.
-/

def GlobalUnitSignPatternsSupplied (m : Modulus K) : Prop :=
  ∀ s : {v : RealPlace K // v ∈ m.infinitePart} → ℤˣ,
    ∃ u : (𝓞 K)ˣ, ∀ v,
      s v = if 0 < v.1.1.embedding_of_isReal v.1.2
          (algebraMap (𝓞 K) K (u : 𝓞 K)) then 1 else -1

def narrowToOrdinarySignPatternKernel
    (D : IdeleContext K I) (C : CanonicalRayUnitComparison D) :
    Subgroup (rayClassGroup D narrowModulus) := C.signPatternToNarrow.range

theorem narrow_to_ordinary_ray_class_map_kernel
    (D : IdeleContext K I) (C : CanonicalRayUnitComparison D) :
    (narrowToOrdinaryRayClassMap D).ker =
      narrowToOrdinarySignPatternKernel D C := by
  exact C.narrowToOrdinary_kernel_eq_sign_patterns

noncomputable def ordinary_and_narrow_coincide_of_all_sign_patterns
    (D : IdeleContext K I) (C : CanonicalRayUnitComparison D)
    (h : GlobalUnitSignPatternsSupplied
      (narrowModulus : Modulus K)) :
    rayClassGroup D Modulus.one ≃* rayClassGroup D narrowModulus := by
  sorry

theorem real_quadratic_norm_minus_one_unit_supplies_all_sign_patterns
    (hdeg : Module.finrank ℚ K = 2)
    (u : (𝓞 K)ˣ)
    (hnorm : Algebra.norm ℚ (algebraMap (𝓞 K) K (u : 𝓞 K)) = -1) :
    GlobalUnitSignPatternsSupplied (narrowModulus : Modulus K) := by
  sorry

theorem a_single_norm_minus_one_unit_is_not_a_general_sign_criterion :
    ¬ (∀ (K : Type*) [Field K] [NumberField K],
        ∀ u : (𝓞 K)ˣ,
          Algebra.norm ℚ (algebraMap (𝓞 K) K (u : 𝓞 K)) = -1 →
          GlobalUnitSignPatternsSupplied (narrowModulus : Modulus K)) := by
  sorry

end

end LastLib.Book06GlobalClassFieldTheory.Chapter07
