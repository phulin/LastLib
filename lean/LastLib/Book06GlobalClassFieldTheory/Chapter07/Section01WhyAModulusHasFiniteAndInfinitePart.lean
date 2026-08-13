import LastLib.Book06GlobalClassFieldTheory.Chapter07.Dependencies

/-!
# 7.1. Why a modulus has a finite and an infinite part

The source section is recorded here as the interface between local ramification
conditions and the open subgroup used in the idele class group.  The local
filtration itself is defined in `Dependencies.lean`; this file supplies the
book-facing modulus and quotient statements in source order.
-/

namespace LastLib.Book06GlobalClassFieldTheory.Chapter07

open scoped BigOperators nonZeroDivisors
open NumberField

noncomputable section

variable {K I : Type*} [Field K] [NumberField K]
  [CommGroup I] [TopologicalSpace I] [IsTopologicalGroup I]

theorem modulus_has_nonzero_finite_part (m : Modulus K) :
    m.finitePart ≠ (⊥ : Ideal (𝓞 K)) :=
  m.finitePart_ne_bot

theorem modulus_infinite_part_contains_only_real_places (m : Modulus K)
    {v : RealPlace K} (hv : v ∈ m.infinitePart) : v.1.IsReal := by
  exact (fun _ : v ∈ m.infinitePart => v.2) hv

theorem complex_places_are_never_selected (m : Modulus K)
    {v : NumberField.InfinitePlace K} (hv : ¬v.IsReal) :
    infiniteUnitSubgroup m v = ⊤ := by
  exact infiniteUnitSubgroup_eq_top_of_not_selected m v (Or.inl hv)

theorem unramified_finite_place_uses_full_integral_unit_group
    (m : Modulus K) (v : NumberField.FinitePlace K)
    (hv : ¬v.maximalIdeal.asIdeal ∣ m.finitePart) :
    finiteUnitFiltration v (m.finiteExponent v) =
      (v.maximalIdeal.adicCompletionIntegers K).unitGroup := by
  rw [Modulus.finiteExponent_eq_zero_of_not_dvd m v hv]
  exact finiteUnitFiltration_zero v

theorem selected_finite_place_uses_the_prescribed_depth
    (m : Modulus K) (v : NumberField.FinitePlace K) :
    finiteUnitFiltration v (m.finiteExponent v) ≤
      (v.maximalIdeal.adicCompletionIntegers K).unitGroup := by
  sorry

theorem finite_component_lies_in_ray_idele_subgroup
    (D : IdeleContext K I) (m : Modulus K) (v : NumberField.FinitePlace K) :
    Subgroup.map (D.finiteComponent v)
        (finiteUnitFiltration v (m.finiteExponent v)) ≤ rayIdeleSubgroup D m := by
  exact D.finiteComponent_mem_rayUnits m v

theorem infinite_component_lies_in_ray_idele_subgroup
    (D : IdeleContext K I) (m : Modulus K) (v : NumberField.InfinitePlace K) :
    Subgroup.map (D.infiniteComponent v) (infiniteUnitSubgroup m v) ≤
      rayIdeleSubgroup D m := by
  exact D.infiniteComponent_mem_rayUnits m v

theorem ray_unit_subgroup_is_open_and_closed
    (D : IdeleContext K I) (m : Modulus K) :
    IsOpen (rayIdeleSubgroup D m : Set I) ∧
      IsClosed (rayIdeleSubgroup D m : Set I) := by
  exact ⟨rayIdeleSubgroup_isOpen D m, rayIdeleSubgroup_isClosed D m⟩

theorem ray_class_subgroup_is_open_and_closed
    (D : IdeleContext K I) (m : Modulus K) :
    IsOpen (rayClassSubgroup D m : Set (ideleClassGroup D)) ∧
      IsClosed (rayClassSubgroup D m : Set (ideleClassGroup D)) := by
  exact ⟨rayClassSubgroup_isOpen D m, rayClassSubgroup_isClosed D m⟩

theorem ray_class_group_is_finite
    (D : IdeleContext K I) (m : Modulus K) : Finite (rayClassGroup D m) := by
  exact rayClassGroup_finite D m

/-! The two standard descriptions of a ray class group.  The second one is the
book's (I/K^\times U(\mathfrak m)) notation; the first is its quotient in
the idele class group. -/

theorem ray_class_group_is_idele_class_quotient
    (D : IdeleContext K I) (m : Modulus K) :
    rayClassGroup D m = (ideleClassGroup D ⧸ rayClassSubgroup D m) := rfl

noncomputable def ray_class_group_is_idele_quotient
    (D : IdeleContext K I) (m : Modulus K) :
    rayClassGroup D m ≃* ideleQuotientByPrincipalAndUnits D m := by
  exact rayClassGroup_equiv_ideleQuotient D m

theorem ray_class_subgroup_needs_no_topological_closure
    (D : IdeleContext K I) (m : Modulus K) :
    IsClosed (rayClassSubgroup D m : Set (ideleClassGroup D)) := by
  exact rayClassSubgroup_isClosed D m

end

end LastLib.Book06GlobalClassFieldTheory.Chapter07
