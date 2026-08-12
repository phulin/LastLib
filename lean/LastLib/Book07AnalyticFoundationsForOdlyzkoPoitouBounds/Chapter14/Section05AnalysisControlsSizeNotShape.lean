import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter14.Dependencies
import LastLib.Book06GlobalClassFieldTheory.Chapter08.Dependencies
import Mathlib.Data.ZMod.Basic

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter14

noncomputable section

universe u v w

open NumberField Polynomial

/-! ## 14.5. Analysis controls size, not group shape -/

def chapter14DegreeCap
    (K : Type*) [Field K] [NumberField K] (N : ℕ) : Prop :=
  chapter14Degree K < N

def chapter14GaloisGroupOrder
    (K : Type*) [Field K] [NumberField K] : ℕ :=
  Nat.card (Gal(K / ℚ))

theorem chapter14_galois_group_order_lt_of_degree_cap
    (K : Type*) [Field K] [NumberField K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    {N : ℕ} (hN : chapter14DegreeCap K N) :
    chapter14GaloisGroupOrder K < N := by
  sorry

theorem chapter14_equal_group_orders_need_not_give_equal_group_shape :
    Nat.card (ZMod 4) = Nat.card (ZMod 2 × ZMod 2) ∧
      ¬ Nonempty (ZMod 4 ≃+ (ZMod 2 × ZMod 2)) := by
  sorry

def chapter14ReducibleQuadratic : Polynomial ℚ :=
  X ^ 2 - C 1

def chapter14IrreducibleQuadratic : Polynomial ℚ :=
  X ^ 2 - C 2

theorem chapter14_degree_does_not_determine_polynomial_reducibility :
    chapter14ReducibleQuadratic.natDegree = 2 ∧
      chapter14IrreducibleQuadratic.natDegree = 2 ∧
      ¬ Irreducible chapter14ReducibleQuadratic ∧
      Irreducible chapter14IrreducibleQuadratic := by
  sorry

/- Mathlib has no single global ray-class-group object.  The earlier Book 6
  presentation is therefore retained as the explicit arithmetic input rather
  than being inferred from a root-discriminant or degree bound. -/
abbrev chapter14RayClassGroup
    {K : Type u} {I : Type v} {C : Type w} [Field K] [NumberField K]
    [CommGroup I] [CommGroup C]
    (R : LastLib.Book06GlobalClassFieldTheory.Chapter08.Chapter08RayClassPresentation
      K I C) : Type v :=
  LastLib.Book06GlobalClassFieldTheory.Chapter08.chapter08RayClassGroup
    (K := K) (I := I) (C := C) R

abbrev chapter14OrdinaryClassGroup
    (K : Type*) [Field K] [NumberField K] := ClassGroup (𝓞 K)

theorem chapter14_unramified_extension_preserves_rootDiscriminant
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (hunramified : chapter14UnramifiedAtFinitePrimes K L) :
    chapter14RootDiscriminant L = chapter14RootDiscriminant K := by
  sorry

theorem chapter14_gaussian_field_has_nontrivial_galois_group :
    1 < chapter14GaloisGroupOrder chapter14GaussianField := by
  sorry

theorem chapter14_gaussian_field_galois_group_order :
    chapter14GaloisGroupOrder chapter14GaussianField = 2 := by
  sorry

/-!
The following family interface separates bounded degree from both nesting and
the existence of a common finite compositum.  This is the structural boundary
that the analytic ledger cannot cross on its own.
-/

theorem chapter14_pairwise_nonnested_bounded_degree_need_not_stabilize
    (Ω : Type*) [Field Ω] [Algebra ℚ Ω]
    (F : ℕ → IntermediateField ℚ Ω) (N : ℕ)
    (hbounded : chapter14BoundedDegreeFamily Ω F N)
    (hnonnested : chapter14PairwiseNonnestedFamily Ω F) :
    ¬ chapter14FamilyEventuallyConstant Ω F := by
  sorry

theorem chapter14_pairwise_nonnested_family_is_not_a_tower
    (Ω : Type*) [Field Ω] [Algebra ℚ Ω]
    (F : ℕ → IntermediateField ℚ Ω)
    (hnonnested : chapter14PairwiseNonnestedFamily Ω F) :
    ¬ chapter14FamilyIsNested Ω F := by
  sorry

theorem chapter14_common_finite_compositum_ceiling_stabilizes_nested_chain
    (Ω : Type*) [Field Ω] [NumberField Ω]
    (C : LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter01.Chapter01NestedFieldChain Ω)
    (U : IntermediateField ℚ Ω)
    (hceiling : chapter14CommonFiniteCompositumCeiling Ω C.field U) :
    ∃ i₀ : ℕ, ∀ j : ℕ, i₀ ≤ j → C.field j = C.field i₀ := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter14
