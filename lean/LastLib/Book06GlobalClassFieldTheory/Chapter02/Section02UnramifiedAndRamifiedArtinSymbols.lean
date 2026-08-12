import LastLib.Book06GlobalClassFieldTheory.Chapter02.Section01DecompositionGroups
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace LastLib.Book06GlobalClassFieldTheory.Chapter02

noncomputable section

open scoped BigOperators Pointwise

universe u v w

/-! ## 2.2. Unramified and ramified Artin symbols -/

/-- A finite place is unramified when its inertia subgroup is trivial. -/
def chapter02IsUnramified
    {D k l : Type*} [Group D] [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l] [IsGalois k l]
    (R : Chapter02ResidueActionData D k l) : Prop :=
  R.inertia = ⊥

/-- A finite place is ramified when its inertia subgroup is nontrivial. -/
def chapter02IsRamified
    {D k l : Type*} [Group D] [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l] [IsGalois k l]
    (R : Chapter02ResidueActionData D k l) : Prop :=
  R.inertia ≠ ⊥

theorem chapter02_isUnramified_iff_inertia_bot
    {D k l : Type*} [Group D] [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l] [IsGalois k l]
    (R : Chapter02ResidueActionData D k l) :
    chapter02IsUnramified R ↔ R.inertia = ⊥ :=
  Iff.rfl

theorem chapter02_isRamified_iff_not_isUnramified
    {D k l : Type*} [Group D] [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l] [IsGalois k l]
    (R : Chapter02ResidueActionData D k l) :
    chapter02IsRamified R ↔ ¬ chapter02IsUnramified R := by
  rfl

theorem chapter02_unramified_local_units_are_norms
    {B E D k l : Type*} [CommGroup B] [CommGroup E] [CommGroup D]
    [Field k] [Field l] [Algebra k l] [FiniteDimensional k l] [IsGalois k l]
    (R : Chapter02LocalReciprocityData B E D)
    (S : Chapter02ResidueActionData D k l)
    (hI : S.inertia = ⊥) (hRI : R.inertia = S.inertia) :
    Function.Surjective (chapter02LocalUnitNorm R) := by
  apply chapter02_local_unit_norm_surjective R
  exact hRI.trans hI

/-- The arithmetic residue Frobenius element. -/
noncomputable def chapter02FrobeniusLift
    {D k l : Type*} [Group D] [Field k] [Field l] [Fintype k] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l]
    (R : Chapter02ResidueActionData D k l) : D :=
  Classical.choose
    (R.reduction_surjective (chapter02ArithmeticFrobenius (k := k) (l := l)))

@[simp]
theorem chapter02_frobeniusLift_reduces_to_arithmetic_frobenius
    {D k l : Type*} [Group D] [Field k] [Field l] [Fintype k] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l]
    (R : Chapter02ResidueActionData D k l) :
    R.reduction (chapter02FrobeniusLift R) =
      chapter02ArithmeticFrobenius (k := k) (l := l) := by
  exact Classical.choose_spec
    (R.reduction_surjective (chapter02ArithmeticFrobenius (k := k) (l := l)))

/-- The set of all lifts of arithmetic residue Frobenius. -/
def chapter02FrobeniusCoset
    {D k l : Type*} [Group D] [Field k] [Field l] [Fintype k] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l]
    (R : Chapter02ResidueActionData D k l) : Set D :=
  {σ | R.reduction σ = chapter02ArithmeticFrobenius (k := k) (l := l)}

theorem chapter02_frobeniusLift_mem_coset
    {D k l : Type*} [Group D] [Field k] [Field l] [Fintype k] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l]
    (R : Chapter02ResidueActionData D k l) :
    chapter02FrobeniusLift R ∈ chapter02FrobeniusCoset R := by
  exact chapter02_frobeniusLift_reduces_to_arithmetic_frobenius R

theorem chapter02_frobenius_coset_nonempty
    {D k l : Type*} [Group D] [Field k] [Field l] [Fintype k] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l]
    (R : Chapter02ResidueActionData D k l) :
    (chapter02FrobeniusCoset R).Nonempty := by
  exact ⟨chapter02FrobeniusLift R, chapter02_frobeniusLift_mem_coset R⟩

/-
The quotient class, rather than a chosen lift, is the canonical ramified
Frobenius object.
-/

theorem chapter02_frobenius_lifts_have_same_inertia_coset
    {D k l : Type*} [Group D] [Field k] [Field l] [Fintype k] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l]
    (R : Chapter02ResidueActionData D k l) {σ τ : D}
    (hσ : σ ∈ chapter02FrobeniusCoset R)
    (hτ : τ ∈ chapter02FrobeniusCoset R) :
    QuotientGroup.mk' R.inertia σ = QuotientGroup.mk' R.inertia τ := by
  sorry

theorem chapter02_frobenius_lift_is_unique_when_unramified
    {D k l : Type*} [Group D] [Field k] [Field l] [Fintype k] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l]
    (R : Chapter02ResidueActionData D k l) (hI : R.inertia = ⊥) :
    ∃! σ : D, σ ∈ chapter02FrobeniusCoset R := by
  sorry

theorem chapter02_frobeniusLift_eq_of_unramified
    {D k l : Type*} [Group D] [Field k] [Field l] [Fintype k] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l]
    (R : Chapter02ResidueActionData D k l) (hI : R.inertia = ⊥)
    {σ : D} (hσ : σ ∈ chapter02FrobeniusCoset R) :
    σ = chapter02FrobeniusLift R := by
  sorry

/-- The ideal-theoretic Artin symbol is defined only in the unramified case. -/
noncomputable def chapter02IdealArtinSymbol
    {D k l : Type*} [Group D] [Field k] [Field l] [Fintype k] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l]
    (R : Chapter02ResidueActionData D k l) (_hI : R.inertia = ⊥) : D :=
  chapter02FrobeniusLift R

theorem chapter02_ideal_artin_symbol_mem_frobenius_coset
    {D k l : Type*} [Group D] [Field k] [Field l] [Fintype k] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l]
    (R : Chapter02ResidueActionData D k l) (hI : R.inertia = ⊥) :
    chapter02IdealArtinSymbol R hI ∈ chapter02FrobeniusCoset R := by
  exact chapter02_frobeniusLift_mem_coset R

theorem chapter02_ideal_artin_symbol_eq_of_mem_frobenius_coset
    {D k l : Type*} [Group D] [Field k] [Field l] [Fintype k] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l]
    (R : Chapter02ResidueActionData D k l) (hI : R.inertia = ⊥)
    {σ : D} (hσ : σ ∈ chapter02FrobeniusCoset R) :
    σ = chapter02IdealArtinSymbol R hI := by
  exact chapter02_frobeniusLift_eq_of_unramified R hI hσ

/-!
### The valuation formula
-/

theorem chapter02_local_artin_at_uniformizer_is_frobenius
    {B E D k l : Type*} [CommGroup B] [CommGroup E] [CommGroup D]
    [Field k] [Field l] [Fintype k] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l]
    (R : Chapter02LocalReciprocityData B E D)
    (S : Chapter02ResidueActionData D k l)
    (V : Chapter02DiscreteValuationData B R.unitSubgroup)
    (hI : S.inertia = ⊥) (hRI : R.inertia = S.inertia)
    (hπ : S.reduction (chapter02LocalArtinMap R V.uniformizer) =
      chapter02ArithmeticFrobenius (k := k) (l := l)) :
    chapter02LocalArtinMap R V.uniformizer = chapter02FrobeniusLift S := by
  sorry

theorem chapter02_local_artin_unramified_formula
    {B E D k l : Type*} [CommGroup B] [CommGroup E] [CommGroup D]
    [Field k] [Field l] [Fintype k] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l]
    (R : Chapter02LocalReciprocityData B E D)
    (S : Chapter02ResidueActionData D k l)
    (V : Chapter02DiscreteValuationData B R.unitSubgroup)
    (hI : S.inertia = ⊥) (hRI : R.inertia = S.inertia)
    (hπ : S.reduction (chapter02LocalArtinMap R V.uniformizer) =
      chapter02ArithmeticFrobenius (k := k) (l := l)) (x : B) :
    chapter02LocalArtinMap R x =
      (chapter02FrobeniusLift S) ^ V.ord x := by
  sorry

theorem chapter02_unramified_artin_depends_only_on_valuation
    {B E D k l : Type*} [CommGroup B] [CommGroup E] [CommGroup D]
    [Field k] [Field l] [Fintype k] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l]
    (R : Chapter02LocalReciprocityData B E D)
    (S : Chapter02ResidueActionData D k l)
    (V : Chapter02DiscreteValuationData B R.unitSubgroup)
    (hI : S.inertia = ⊥) (hRI : R.inertia = S.inertia)
    (hπ : S.reduction (chapter02LocalArtinMap R V.uniformizer) =
      chapter02ArithmeticFrobenius (k := k) (l := l)) {x y : B}
    (hxy : V.ord x = V.ord y) :
    chapter02LocalArtinMap R x = chapter02LocalArtinMap R y := by
  rw [chapter02_local_artin_unramified_formula R S V hI hRI hπ,
    chapter02_local_artin_unramified_formula R S V hI hRI hπ, hxy]

/-!
### Ramified places and the uniformizer ambiguity
-/

theorem chapter02_ramified_frobenius_has_no_canonical_lift
    {D k l : Type*} [Group D] [Field k] [Field l] [Fintype k] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l]
    (R : Chapter02ResidueActionData D k l)
    (hI : ∃ i : R.inertia, (i : D) ≠ 1) :
    ¬ ∃! σ : D, σ ∈ chapter02FrobeniusCoset R := by
  sorry

theorem chapter02_uniformizer_change_by_unit
    {B E D : Type*} [CommGroup B] [CommGroup E] [CommGroup D]
    (R : Chapter02LocalReciprocityData B E D) (π π' : B)
    (u : R.unitSubgroup) (hπ : π' = (u : B) * π) :
    chapter02LocalArtinMap R π' =
      chapter02LocalArtinMap R π * chapter02LocalArtinMap R (u : B) := by
  sorry

theorem chapter02_uniformizer_change_is_inertia
    {B E D : Type*} [CommGroup B] [CommGroup E] [CommGroup D]
    (R : Chapter02LocalReciprocityData B E D) (π π' : B)
    (u : R.unitSubgroup) (hπ : π' = (u : B) * π) :
    ∃ i : R.inertia,
      chapter02LocalArtinMap R π' = chapter02LocalArtinMap R π * i := by
  sorry

theorem chapter02_ramified_frobenius_lifts_are_equal_only_modulo_inertia
    {B E D k l : Type*} [CommGroup B] [CommGroup E] [CommGroup D]
    [Field k] [Field l] [Fintype k] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l]
    (R : Chapter02LocalReciprocityData B E D)
    (S : Chapter02ResidueActionData D k l) (π π' : B)
    (hπ : S.reduction (chapter02LocalArtinMap R π) =
      chapter02ArithmeticFrobenius (k := k) (l := l))
    (hπ' : S.reduction (chapter02LocalArtinMap R π') =
      chapter02ArithmeticFrobenius (k := k) (l := l)) :
    QuotientGroup.mk' S.inertia (chapter02LocalArtinMap R π) =
      QuotientGroup.mk' S.inertia (chapter02LocalArtinMap R π') := by
  exact chapter02_frobenius_lifts_have_same_inertia_coset S hπ hπ'

/-!
### Quadratic example
-/

/-- The decomposition-group formulation of complete splitting at a place. -/
def chapter02CompletelySplitAt
    {G : Type u} [Group G] {V : Type v} {W : Type w} [MulAction G W]
    (P : Chapter02ChosenPlace G V W) : Prop :=
  chapter02DecompositionGroup P = ⊥

/-- The decomposition-group formulation of remaining prime/inertness. -/
def chapter02RemainsPrimeAt
    {G : Type u} [Group G] {V : Type v} {W : Type w} [MulAction G W]
    (P : Chapter02ChosenPlace G V W) : Prop :=
  chapter02DecompositionGroup P = ⊤

theorem chapter02_completely_split_iff_decomposition_group_bot
    {G : Type u} [Group G] {V : Type v} {W : Type w} [MulAction G W]
    (P : Chapter02ChosenPlace G V W) :
    chapter02CompletelySplitAt P ↔ chapter02DecompositionGroup P = ⊥ :=
  Iff.rfl

theorem chapter02_remains_prime_iff_decomposition_group_top
    {G : Type u} [Group G] {V : Type v} {W : Type w} [MulAction G W]
    (P : Chapter02ChosenPlace G V W) :
    chapter02RemainsPrimeAt P ↔ chapter02DecompositionGroup P = ⊤ :=
  Iff.rfl

theorem chapter02_quadratic_unramified_symbol_eq_one_iff_split
    {G : Type u} [CommGroup G] [Fintype G]
    {V : Type v} {W : Type w} [MulAction G W]
    {B E k l : Type*} [CommGroup B] [CommGroup E]
    [Field k] [Field l] [Fintype k] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l]
    (hquadratic : Fintype.card G = 2)
    (P : Chapter02ChosenPlace G V W)
    (R : Chapter02LocalReciprocityData B E (chapter02DecompositionGroup P))
    (S : Chapter02ResidueActionData (chapter02DecompositionGroup P) k l)
    (Vv : Chapter02DiscreteValuationData B R.unitSubgroup)
    (hI : S.inertia = ⊥) (hRI : R.inertia = S.inertia)
    (hπ : S.reduction (chapter02LocalArtinMap R Vv.uniformizer) =
      chapter02ArithmeticFrobenius (k := k) (l := l)) :
    chapter02LocalArtinMapAtChosenPlace P R Vv.uniformizer = 1 ↔
      chapter02CompletelySplitAt P := by
  sorry

theorem chapter02_quadratic_unramified_symbol_eq_nontrivial_iff_inert
    {G : Type u} [CommGroup G] [Fintype G]
    {V : Type v} {W : Type w} [MulAction G W]
    {B E k l : Type*} [CommGroup B] [CommGroup E]
    [Field k] [Field l] [Fintype k] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l]
    (hquadratic : Fintype.card G = 2) (σ : G) (hσ : σ ≠ 1)
    (P : Chapter02ChosenPlace G V W)
    (R : Chapter02LocalReciprocityData B E (chapter02DecompositionGroup P))
    (S : Chapter02ResidueActionData (chapter02DecompositionGroup P) k l)
    (Vv : Chapter02DiscreteValuationData B R.unitSubgroup)
    (hI : S.inertia = ⊥) (hRI : R.inertia = S.inertia)
    (hπ : S.reduction (chapter02LocalArtinMap R Vv.uniformizer) =
      chapter02ArithmeticFrobenius (k := k) (l := l)) :
    chapter02LocalArtinMapAtChosenPlace P R Vv.uniformizer = σ ↔
      chapter02RemainsPrimeAt P := by
  sorry

theorem chapter02_ramified_uniformizer_and_units_generate_decomposition_group
    {B E D : Type*} [CommGroup B] [CommGroup E] [CommGroup D]
    (R : Chapter02LocalReciprocityData B E D)
    (V : Chapter02DiscreteValuationData B R.unitSubgroup) :
    Subgroup.closure
        ({chapter02LocalArtinMap R V.uniformizer} ∪
          Set.range ((chapter02LocalArtinMap R).comp R.unitSubgroup.subtype)) = ⊤ := by
  sorry

/- WARNING FROM THE SOURCE: no ideal symbol is defined at a ramified place.
   The API deliberately exposes only `chapter02FrobeniusCoset` and local Artin
   maps there; `chapter02IdealArtinSymbol` requires an explicit unramified
   proof. -/

end

end LastLib.Book06GlobalClassFieldTheory.Chapter02
