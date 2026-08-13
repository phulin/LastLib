import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.ModEq
import LastLib.Book06GlobalClassFieldTheory.Chapter01.Section03FourKindsOfNormAssertion
import LastLib.Book06GlobalClassFieldTheory.Chapter09.Section01TheKnotBetweenLocalAndGlobalNorms

namespace LastLib.Book06GlobalClassFieldTheory.Chapter09

noncomputable section

universe u

/-!
The cohomological obstruction uses the actual Mathlib group-cohomology object
with trivial integral coefficients.  A subgroup restriction is the canonical
map supplied by `groupCohomology.map`.
-/
abbrev chapter09H3 (G : Type) [Group G] :=
  groupCohomology (Rep.trivial ℤ G ℤ) 3

structure Chapter09DecompositionData (G : Type) [Group G] where
  places : Type*
  decompositionGroup : places → Subgroup G

noncomputable def chapter09TrivialRestriction
    {G : Type} [Group G] (D : Subgroup G) :
    Rep.res D.subtype (Rep.trivial ℤ G ℤ) ⟶ Rep.trivial ℤ D ℤ :=
  Rep.ofHom
    ((LinearMap.id : ℤ →ₗ[ℤ] ℤ).intertwiningMap_of_isIntertwiningMap
      (Rep.res D.subtype (Rep.trivial ℤ G ℤ)).ρ
      (Rep.trivial ℤ D ℤ).ρ
      (fun _ _ => by simp))

noncomputable def chapter09H3Restriction
    {G : Type} [Group G] (D : Subgroup G) :
    chapter09H3 G ⟶ chapter09H3 D :=
  groupCohomology.map D.subtype (chapter09TrivialRestriction D) 3

noncomputable def chapter09H3LocalizationMap
    {G : Type} [Group G] (P : Chapter09DecompositionData G) :
    chapter09H3 G →ₗ[ℤ] ∀ v, chapter09H3 (P.decompositionGroup v) :=
  { toFun := fun x v => chapter09H3Restriction (P.decompositionGroup v) x
    map_add' := by
      intro x y
      funext v
      simp [chapter09H3Restriction]
    map_smul' := by
      sorry }

def chapter09H3LocalizationKernel
    {G : Type} [Group G] (P : Chapter09DecompositionData G) :
    Submodule ℤ (chapter09H3 G) :=
  LinearMap.ker (chapter09H3LocalizationMap P)

instance chapter09_hilbert90_degree_one
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] :
    Unique (groupCohomology.H1 (Rep.ofAlgebraAutOnUnits K L)) :=
  inferInstance

noncomputable def chapter09_shapiro_lemma
    {G : Type} [Group G] {D : Subgroup G}
    (A : Rep ℤ D) (n : ℕ) :
    groupCohomology (Rep.coind D.subtype A) n ≅
      groupCohomology A n :=
  groupCohomology.coindIso A n

/-!
The fundamental class supplies the degree shift by two which turns the class
module into the degree-three cohomology appearing in the obstruction formula.
The concrete class module and its extension are supplied by the preceding
global class-field-theory chapters.
-/
structure Chapter09FundamentalClassShiftData
    (R G : Type u) [CommRing R] [Group G] [Fintype G] where
  classModule : Rep.{u} R G
  shiftedModule : Rep.{u} R G
  shift_by_two :
    tateCohomology classModule (1 : ℤ) ≅
      groupCohomology shiftedModule 3

noncomputable def chapter09_fundamental_class_shift_by_two
    {R G : Type u} [CommRing R] [Group G] [Fintype G]
    (F : Chapter09FundamentalClassShiftData R G) :
    tateCohomology F.classModule (1 : ℤ) ≅
      groupCohomology F.shiftedModule 3 :=
  F.shift_by_two

/- LOCAL_DEPENDENCY_GUESS: the following data package is the canonical idele
resolution/local-decomposition realization of the exact sequence in Section
9.1.  Mathlib has the cohomology, Shapiro, and Tate interfaces, but not this
global idelic comparison theorem.  Packaging the decomposition data together
with its comparison prevents an arbitrary family of subgroups from being
mistaken for the actual local decomposition groups of `L / K`.
-/
structure Chapter09KnotCohomologyRealization
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L] [FiniteDimensional K L]
    [IsGalois K L] [Fintype (Gal(L / K))]
    {I_K I_L : Type*} [CommGroup I_K] [CommGroup I_L]
    (D : Chapter09IdeleNormData K L I_K I_L)
    [Finite (chapter09KnotGroup D)]
    [TopologicalSpace (chapter09KnotGroup D)]
    [IsTopologicalGroup (chapter09KnotGroup D)]
    [DiscreteTopology (chapter09KnotGroup D)] where
  decompositionData : Chapter09DecompositionData (Gal(L / K))
  comparison :
    Additive (PontryaginDual (chapter09KnotGroup D)) ≃+
      chapter09H3LocalizationKernel decompositionData

noncomputable def chapter09_knot_cohomology_formula_at
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L] [FiniteDimensional K L]
    [IsGalois K L] [Fintype (Gal(L / K))]
    {I_K I_L : Type*} [CommGroup I_K] [CommGroup I_L]
    (D : Chapter09IdeleNormData K L I_K I_L)
    [Finite (chapter09KnotGroup D)]
    [TopologicalSpace (chapter09KnotGroup D)]
    [IsTopologicalGroup (chapter09KnotGroup D)]
    [DiscreteTopology (chapter09KnotGroup D)]
    (R : Chapter09KnotCohomologyRealization D) :
    Additive (PontryaginDual (chapter09KnotGroup D)) ≃+
      chapter09H3LocalizationKernel R.decompositionData :=
  R.comparison

theorem chapter09_h3_cyclic_subgroup_vanishes
    {C : Type} [Group C] [Fintype C] [IsCyclic C] :
    Subsingleton (chapter09H3 C) := by
  sorry

abbrev chapter09KleinFour : Type :=
  Multiplicative (ZMod 2 × ZMod 2)

theorem chapter09_h3_klein_four :
    Nonempty (chapter09H3 chapter09KleinFour ≃+ ZMod 2) := by
  sorry

theorem chapter09_h3_localization_kernel_nontrivial
    (P : Chapter09DecompositionData chapter09KleinFour)
    (hcyclic : ∀ v, IsCyclic (P.decompositionGroup v)) :
    Nontrivial (chapter09H3LocalizationKernel P) := by
  sorry

theorem chapter09_h3_localization_kernel_card_two
    (P : Chapter09DecompositionData chapter09KleinFour)
    (hcyclic : ∀ v, IsCyclic (P.decompositionGroup v))
    [Finite (chapter09H3LocalizationKernel P)] :
    Nat.card (chapter09H3LocalizationKernel P) = 2 := by
  sorry

/-!
The two elementary congruences used to analyze the biquadratic example are
kept as reusable arithmetic facts, while the p-adic square conclusions are
left as the local Hensel/norm-interface lemmas used by the later proof pass.
-/
theorem chapter09_biquadratic_congruence_at_13 :
    Int.ModEq 13 17 4 := by
  norm_num

theorem chapter09_biquadratic_congruence_at_17 :
    Int.ModEq 17 (8 ^ 2) 13 := by
  norm_num

theorem chapter09_biquadratic_congruence_at_2 :
    Int.ModEq 8 17 1 := by
  norm_num

theorem chapter09_seventeen_is_square_in_13adic [Fact (Nat.Prime 13)] :
    IsSquare (17 : ℚ_[13]) := by
  sorry

theorem chapter09_thirteen_is_square_in_17adic [Fact (Nat.Prime 17)] :
    IsSquare (13 : ℚ_[17]) := by
  sorry

theorem chapter09_seventeen_is_square_in_2adic [Fact (Nat.Prime 2)] :
    IsSquare (17 : ℚ_[2]) := by
  sorry

theorem chapter09_biquadratic_positive_at_infinity :
    0 < (13 : ℝ) ∧ 0 < (17 : ℝ) := by
  norm_num

/-!
This presentation records the meaning of `L = ℚ(√13, √17)` without inventing
a new field type.  The local analysis below is parameterized by the canonical
finite-place/decomposition data for this presentation.
-/
structure Chapter09BiquadraticPresentation
    (L : Type) [Field L] [Algebra ℚ L] [NumberField L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L] where
  sqrt13 : L
  sqrt17 : L
  sqrt13_sq : sqrt13 ^ 2 = (13 : L)
  sqrt17_sq : sqrt17 ^ 2 = (17 : L)
  adjoin_eq_top :
    IntermediateField.adjoin ℚ ({sqrt13, sqrt17} : Set L) = ⊤
  galoisGroup_equiv : Gal(L / ℚ) ≃* chapter09KleinFour

def chapter09BiquadraticDiscriminants : Set ℤ :=
  {13, 17, 13 * 17}

def chapter09BiquadraticRamifiedPrimes : Set ℕ :=
  {13, 17}

/-!
`finitePlaces` and `primeBelow` are an abstract presentation of the finite
places used by the book, with `place` locating them in the decomposition data.
In the canonical instance, the ramification field
identifies ramified primes with the primes dividing the recorded quadratic
discriminants, and the decomposition-group field records that every local
degree is at most two.  The resulting cyclicity is proved separately below.
-/
structure Chapter09BiquadraticLocalAnalysis
    (L : Type) [Field L] [Algebra ℚ L] [NumberField L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (E : Chapter09BiquadraticPresentation L)
    (P : Chapter09DecompositionData (Gal(L / ℚ)))
    [Fintype (Gal(L / ℚ))] where
  quadraticDiscriminants : Set ℤ
  quadraticDiscriminants_eq :
    quadraticDiscriminants = chapter09BiquadraticDiscriminants
  finitePlaces : Type*
  place : finitePlaces → P.places
  primeBelow : finitePlaces → ℕ
  primeBelow_prime : ∀ v, Nat.Prime (primeBelow v)
  ramified : finitePlaces → Prop
  ramified_iff_discriminant_support :
    ∀ v, ramified v ↔
      ∃ d ∈ quadraticDiscriminants, (primeBelow v : ℤ) ∣ d
  decomposition_groups_card_le_two :
    ∀ v : P.places, Nat.card (P.decompositionGroup v) ≤ 2

theorem chapter09_biquadratic_only_13_17_ramify
    {L : Type} [Field L] [Algebra ℚ L] [NumberField L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (E : Chapter09BiquadraticPresentation L)
    (P : Chapter09DecompositionData (Gal(L / ℚ)))
    [Fintype (Gal(L / ℚ))]
    (A : Chapter09BiquadraticLocalAnalysis L E P) :
    ∀ v, A.ramified v ↔ A.primeBelow v = 13 ∨ A.primeBelow v = 17 := by
  sorry

theorem chapter09_biquadratic_ramified_iff_discriminant_support
    {L : Type} [Field L] [Algebra ℚ L] [NumberField L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (E : Chapter09BiquadraticPresentation L)
    (P : Chapter09DecompositionData (Gal(L / ℚ)))
    [Fintype (Gal(L / ℚ))]
    (A : Chapter09BiquadraticLocalAnalysis L E P) :
    ∀ v, A.ramified v ↔
      ∃ d ∈ A.quadraticDiscriminants, (A.primeBelow v : ℤ) ∣ d :=
  A.ramified_iff_discriminant_support

theorem chapter09_biquadratic_quadratic_discriminants
    {L : Type} [Field L] [Algebra ℚ L] [NumberField L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (E : Chapter09BiquadraticPresentation L)
    (P : Chapter09DecompositionData (Gal(L / ℚ)))
    [Fintype (Gal(L / ℚ))]
    (A : Chapter09BiquadraticLocalAnalysis L E P) :
    A.quadraticDiscriminants = chapter09BiquadraticDiscriminants :=
  A.quadraticDiscriminants_eq

theorem chapter09_biquadratic_decomposition_groups_are_cyclic
    {L : Type} [Field L] [Algebra ℚ L] [NumberField L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (E : Chapter09BiquadraticPresentation L)
    (P : Chapter09DecompositionData (Gal(L / ℚ)))
    [Fintype (Gal(L / ℚ))]
    (A : Chapter09BiquadraticLocalAnalysis L E P) :
    ∀ v, IsCyclic (P.decompositionGroup v) := by
  sorry

theorem chapter09_biquadratic_decomposition_groups_card_le_two
    {L : Type} [Field L] [Algebra ℚ L] [NumberField L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (E : Chapter09BiquadraticPresentation L)
    (P : Chapter09DecompositionData (Gal(L / ℚ)))
    [Fintype (Gal(L / ℚ))]
    (A : Chapter09BiquadraticLocalAnalysis L E P) :
    ∀ v, Nat.card (P.decompositionGroup v) ≤ 2 :=
  A.decomposition_groups_card_le_two

/-!
The local algebra used by the displayed example is the canonical tensor
product from Chapter 1, not an arbitrary family of monoids.  The
decomposition-group/local-analysis package below records the remaining
finite-place bridge; the norm failure itself is stated using the canonical
element/local norm predicates from the same earlier interface.
-/
structure Chapter09CanonicalBiquadraticCounterexample where
  L : Type
  [field_L : Field L]
  [numberField_L : NumberField L]
  [algebra_L : Algebra ℚ L]
  [finiteDimensional_L : FiniteDimensional ℚ L]
  [galois_L : IsGalois ℚ L]
  [fintype_galois_L : Fintype (Gal(L / ℚ))]
  presentation : Chapter09BiquadraticPresentation L
  decompositionData : Chapter09DecompositionData (Gal(L / ℚ))
  localAnalysis : Chapter09BiquadraticLocalAnalysis L presentation decompositionData

attribute [instance] Chapter09CanonicalBiquadraticCounterexample.field_L
  Chapter09CanonicalBiquadraticCounterexample.numberField_L
  Chapter09CanonicalBiquadraticCounterexample.algebra_L
  Chapter09CanonicalBiquadraticCounterexample.finiteDimensional_L
  Chapter09CanonicalBiquadraticCounterexample.galois_L
  Chapter09CanonicalBiquadraticCounterexample.fintype_galois_L

theorem chapter09_canonical_biquadratic_local_products
    {L : Type} [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] :
    ∀ v : LastLib.Book06GlobalClassFieldTheory.Chapter01.BookPlace ℚ,
      LastLib.Book06GlobalClassFieldTheory.Chapter01.IsLocalProductAlgebra ℚ L v :=
  LastLib.Book06GlobalClassFieldTheory.Chapter01.local_tensor_product_product_decomposition

/- LOCAL_DEPENDENCY_GUESS: this is the canonical realization of the displayed
biquadratic field, its decomposition groups, and its local tensor norms. -/
theorem chapter09_canonical_biquadratic_counterexample_data :
    Nonempty Chapter09CanonicalBiquadraticCounterexample := by
  sorry

noncomputable def chapter09CanonicalBiquadraticCounterexample :
    Chapter09CanonicalBiquadraticCounterexample :=
  Classical.choice chapter09_canonical_biquadratic_counterexample_data

theorem chapter09_biquadratic_exists_local_not_global_norm_unconditional :
    ∃ a : ℚ, a ≠ 0 ∧
      LastLib.Book06GlobalClassFieldTheory.Chapter01.IsLocalElementNorm ℚ
        chapter09CanonicalBiquadraticCounterexample.L a ∧
      ¬ LastLib.Book06GlobalClassFieldTheory.Chapter01.IsElementNorm ℚ
        chapter09CanonicalBiquadraticCounterexample.L a := by
  sorry

/-!
The realization structure expresses the canonical compatibility between the
idele norm and the family of local norms.  It is the missing bridge needed to
turn the order-two knot into an explicit local-but-not-global norm statement.
-/
structure Chapter09NormRealizationData
    (K L I_K I_L V : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [CommGroup I_K] [CommGroup I_L]
    (K_v A_v : V → Type*)
    [∀ v, Monoid (K_v v)] [∀ v, Monoid (A_v v)] where
  idele : Chapter09IdeleNormData K L I_K I_L
  localNormData : Chapter09LocalNormData K V K_v A_v
  everywhere_iff_principal :
    ∀ a, chapter09EverywhereLocalNorm localNormData a ↔
      a ∈ chapter09PrincipalNormSubgroup idele

/- LOCAL_DEPENDENCY_GUESS: instantiate `R` with the canonical idele and local
completion data of the displayed biquadratic field.  The hypotheses are the
norm-realization compatibility and the cohomological order-two computation,
not the desired existence conclusion itself.
-/
theorem chapter09_biquadratic_knot_has_order_two
    {L : Type} {I_K I_L : Type*} [Field L] [Algebra ℚ L]
    [NumberField L] [FiniteDimensional ℚ L] [IsGalois ℚ L]
    [Fintype (Gal(L / ℚ))]
    (E : Chapter09BiquadraticPresentation L)
    [CommGroup I_K] [CommGroup I_L]
    (D : Chapter09IdeleNormData ℚ L I_K I_L)
    [Finite (chapter09KnotGroup D)]
    [TopologicalSpace (chapter09KnotGroup D)]
    [IsTopologicalGroup (chapter09KnotGroup D)]
    [DiscreteTopology (chapter09KnotGroup D)]
    (R : Chapter09KnotCohomologyRealization D)
    (A : Chapter09BiquadraticLocalAnalysis L E R.decompositionData) :
    Nat.card (chapter09KnotGroup D) = 2 := by
  sorry

theorem chapter09_biquadratic_exists_local_not_global_norm
    {L : Type} {I_K I_L V : Type*} [Field L] [Algebra ℚ L]
    [NumberField L] [FiniteDimensional ℚ L] [IsGalois ℚ L]
    [CommGroup I_K] [CommGroup I_L]
    {K_v A_v : V → Type*}
    [∀ v, Monoid (K_v v)] [∀ v, Monoid (A_v v)]
    (R : Chapter09NormRealizationData ℚ L I_K I_L V K_v A_v)
    [Finite (chapter09KnotGroup R.idele)]
    (hknot : Nat.card (chapter09KnotGroup R.idele) = 2) :
    ∃ a : ℚˣ,
      chapter09EverywhereLocalNorm R.localNormData a ∧
        a ∉ chapter09FieldNormSubgroup ℚ L := by
  sorry

end

end LastLib.Book06GlobalClassFieldTheory.Chapter09
