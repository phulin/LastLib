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
    (R : Chapter02ResidueActionData D k l) : Prop :=
  R.inertia = ⊥

/-- A finite place is ramified when its inertia subgroup is nontrivial. -/
def chapter02IsRamified
    {D k l : Type*} [Group D] [Field k] [Field l] [Algebra k l]
    (R : Chapter02ResidueActionData D k l) : Prop :=
  R.inertia ≠ ⊥

theorem chapter02_isUnramified_iff_inertia_bot
    {D k l : Type*} [Group D] [Field k] [Field l] [Algebra k l]
    (R : Chapter02ResidueActionData D k l) :
    chapter02IsUnramified R ↔ R.inertia = ⊥ :=
  Iff.rfl

theorem chapter02_isRamified_iff_not_isUnramified
    {D k l : Type*} [Group D] [Field k] [Field l] [Algebra k l]
    (R : Chapter02ResidueActionData D k l) :
    chapter02IsRamified R ↔ ¬ chapter02IsUnramified R := by
  rfl

theorem chapter02_unramified_local_units_are_norms
    {B E D k l : Type*} [CommGroup B] [CommGroup E] [CommGroup D]
    [Field k] [Field l] [Algebra k l]
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
  change R.reduction σ = _ at hσ
  change R.reduction τ = _ at hτ
  refine (QuotientGroup.mk'_eq_mk' R.inertia).2 ⟨σ⁻¹ * τ, ?_, ?_⟩
  · rw [← R.kernel_eq_inertia]
    change R.reduction (σ⁻¹ * τ) = 1
    rw [map_mul, map_inv, hσ, hτ]
    simp
  · simp

theorem chapter02_frobenius_lift_is_unique_when_unramified
    {D k l : Type*} [Group D] [Field k] [Field l] [Fintype k] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l]
    (R : Chapter02ResidueActionData D k l) (hI : R.inertia = ⊥) :
    ∃! σ : D, σ ∈ chapter02FrobeniusCoset R := by
  refine ⟨chapter02FrobeniusLift R, chapter02_frobeniusLift_mem_coset R, ?_⟩
  intro σ hσ
  have hcoset := chapter02_frobenius_lifts_have_same_inertia_coset R hσ
    (chapter02_frobeniusLift_mem_coset R)
  rcases (QuotientGroup.mk'_eq_mk' R.inertia).1 hcoset with ⟨z, hz, hσz⟩
  have hz' : z = 1 := by
    rw [hI] at hz
    simpa using hz
  simpa [hz'] using hσz

theorem chapter02_frobeniusLift_eq_of_unramified
    {D k l : Type*} [Group D] [Field k] [Field l] [Fintype k] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l]
    (R : Chapter02ResidueActionData D k l) (hI : R.inertia = ⊥)
    {σ : D} (hσ : σ ∈ chapter02FrobeniusCoset R) :
    σ = chapter02FrobeniusLift R := by
  have hunique := chapter02_frobenius_lift_is_unique_when_unramified R hI
  exact hunique.unique hσ (chapter02_frobeniusLift_mem_coset R)

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
    (hI : S.inertia = ⊥)
    (hπ : S.reduction (chapter02LocalArtinMap R V.uniformizer) =
      chapter02ArithmeticFrobenius (k := k) (l := l)) :
    chapter02LocalArtinMap R V.uniformizer = chapter02FrobeniusLift S := by
  exact chapter02_frobeniusLift_eq_of_unramified S hI hπ

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
  obtain ⟨u, hu⟩ := V.decomposition x
  have hu_mem : chapter02LocalArtinMap R (u : B) ∈ R.inertia := by
    rw [← chapter02_local_artin_units_eq_inertia R]
    exact ⟨u, rfl⟩
  have hu_one : chapter02LocalArtinMap R (u : B) = 1 := by
    rw [hRI, hI] at hu_mem
    simpa using hu_mem
  calc
    chapter02LocalArtinMap R x =
        chapter02LocalArtinMap R ((u : B) * V.uniformizer ^ V.ord x) := by
      exact congrArg (chapter02LocalArtinMap R) hu
    _ = chapter02LocalArtinMap R (u : B) *
        (chapter02LocalArtinMap R V.uniformizer) ^ V.ord x := by
      rw [map_mul, (chapter02LocalArtinMap R).map_zpow]
    _ = (chapter02LocalArtinMap R V.uniformizer) ^ V.ord x := by rw [hu_one, one_mul]
    _ = (chapter02FrobeniusLift S) ^ V.ord x := by
      rw [chapter02_local_artin_at_uniformizer_is_frobenius R S V hI hπ]

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
  rintro ⟨σ, hσ, huniq⟩
  rcases hI with ⟨i, hi⟩
  let τ : D := (i : D) * chapter02FrobeniusLift R
  have hτ : τ ∈ chapter02FrobeniusCoset R := by
    change R.reduction ((i : D) * chapter02FrobeniusLift R) = _
    rw [map_mul]
    have hi_kernel : R.reduction (i : D) = 1 := by
      exact (chapter02_residue_kernel_membership_iff R (i : D)).mp i.property
    rw [hi_kernel, one_mul]
    exact chapter02_frobeniusLift_reduces_to_arithmetic_frobenius R
  have hτ_ne : τ ≠ chapter02FrobeniusLift R := by
    intro hτ_eq
    apply hi
    apply mul_right_cancel (b := (chapter02FrobeniusLift R))
    simpa [τ] using hτ_eq
  have hτ_eq : τ = chapter02FrobeniusLift R :=
    (huniq τ hτ).trans (huniq (chapter02FrobeniusLift R)
      (chapter02_frobeniusLift_mem_coset R)).symm
  exact hτ_ne hτ_eq

theorem chapter02_uniformizer_change_by_unit
    {B E D : Type*} [CommGroup B] [CommGroup E] [CommGroup D]
    (R : Chapter02LocalReciprocityData B E D) (π π' : B)
    (u : R.unitSubgroup) (hπ : π' = (u : B) * π) :
    chapter02LocalArtinMap R π' =
      chapter02LocalArtinMap R π * chapter02LocalArtinMap R (u : B) := by
  rw [hπ, map_mul, mul_comm]

theorem chapter02_uniformizer_change_is_inertia
    {B E D : Type*} [CommGroup B] [CommGroup E] [CommGroup D]
    (R : Chapter02LocalReciprocityData B E D) (π π' : B)
    (u : R.unitSubgroup) (hπ : π' = (u : B) * π) :
    ∃ i : R.inertia,
      chapter02LocalArtinMap R π' = chapter02LocalArtinMap R π * i := by
  have hmem : chapter02LocalArtinMap R (u : B) ∈ R.inertia := by
    rw [← chapter02_local_artin_units_eq_inertia R]
    exact ⟨u, rfl⟩
  refine ⟨⟨chapter02LocalArtinMap R (u : B), hmem⟩, ?_⟩
  exact chapter02_uniformizer_change_by_unit R π π' u hπ

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
  have _hquadratic := hquadratic
  have hFrob := chapter02_local_artin_at_uniformizer_is_frobenius
    R S Vv hI hπ
  have hvalue :
      chapter02LocalArtinMapAtChosenPlace P R Vv.uniformizer = 1 ↔
        chapter02LocalArtinMap R Vv.uniformizer = 1 := by
    simp [chapter02LocalArtinMapAtChosenPlace]
  constructor
  · intro hvalue_one
    have hlocal_one : chapter02LocalArtinMap R Vv.uniformizer = 1 :=
      hvalue.mp hvalue_one
    have hfrob_one : chapter02FrobeniusLift S = 1 := by
      exact hFrob.symm.trans hlocal_one
    change chapter02DecompositionGroup P = ⊥
    apply le_antisymm
    · intro d hd
      let d' : chapter02DecompositionGroup P := ⟨d, hd⟩
      rcases chapter02_local_artin_surjective R d' with ⟨x, hx⟩
      have hd'_one : d' = 1 := by
        calc
          d' = chapter02LocalArtinMap R x := hx.symm
          _ = (chapter02FrobeniusLift S) ^ Vv.ord x :=
            chapter02_local_artin_unramified_formula R S Vv hI hRI hπ x
          _ = 1 := by rw [hfrob_one]; simp
      have hd_one : d = 1 := by
        simpa [d'] using congrArg Subtype.val hd'_one
      simp [hd_one]
    · exact bot_le
  · intro hsplit
    have hD_one : ∀ d : chapter02DecompositionGroup P, d = 1 := by
      intro d
      apply Subtype.ext
      have hd : (d : G) ∈ (⊥ : Subgroup G) := by
        rw [← hsplit]
        exact d.property
      simpa using hd
    have hlocal_one : chapter02LocalArtinMap R Vv.uniformizer = 1 :=
      hD_one _
    exact hvalue.mpr hlocal_one

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
  classical
  have hclass : ∀ g : G, g = 1 ∨ g = σ := by
    intro g
    let s : Finset G := insert 1 ({σ} : Finset G)
    have hset_univ : s = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      simpa [s, hσ, ne_comm] using hquadratic.le
    have hg : g ∈ s := by
      rw [hset_univ]
      simp
    simpa [s] using hg
  have hFrob := chapter02_local_artin_at_uniformizer_is_frobenius
    R S Vv hI hπ
  have hvalue :
      chapter02LocalArtinMapAtChosenPlace P R Vv.uniformizer = 1 ↔
        chapter02LocalArtinMap R Vv.uniformizer = 1 := by
    simp [chapter02LocalArtinMapAtChosenPlace]
  constructor
  · intro hsymbol
    change chapter02DecompositionGroup P = ⊤
    calc
      chapter02DecompositionGroup P =
          (chapter02LocalArtinMapAtChosenPlace P R).range :=
        (chapter02_local_artin_map_at_chosen_place_range P R).symm
      _ = ⊤ := by
        apply le_antisymm le_top
        intro g _
        rcases hclass g with rfl | rfl
        · exact ⟨1, by simp [chapter02LocalArtinMapAtChosenPlace]⟩
        · exact ⟨Vv.uniformizer, hsymbol⟩
  · intro hinert
    have hsymbol_ne :
        chapter02LocalArtinMapAtChosenPlace P R Vv.uniformizer ≠ 1 := by
      intro hone
      have hlocal_one : chapter02LocalArtinMap R Vv.uniformizer = 1 :=
        hvalue.mp hone
      have hfrob_one : chapter02FrobeniusLift S = 1 :=
        hFrob.symm.trans hlocal_one
      have hσ_mem : σ ∈ chapter02DecompositionGroup P := by
        rw [hinert]
        simp
      let dσ : chapter02DecompositionGroup P := ⟨σ, hσ_mem⟩
      rcases chapter02_local_artin_surjective R dσ with ⟨x, hx⟩
      have hdσ_one : dσ = 1 := by
        calc
          dσ = chapter02LocalArtinMap R x := hx.symm
          _ = (chapter02FrobeniusLift S) ^ Vv.ord x :=
            chapter02_local_artin_unramified_formula R S Vv hI hRI hπ x
          _ = 1 := by rw [hfrob_one]; simp
      apply hσ
      simpa [dσ] using congrArg Subtype.val hdσ_one
    rcases hclass (chapter02LocalArtinMapAtChosenPlace P R Vv.uniformizer) with h_one | h_nontriv
    · exact (hsymbol_ne h_one).elim
    · exact h_nontriv

theorem chapter02_ramified_uniformizer_and_units_generate_decomposition_group
    {B E D : Type*} [CommGroup B] [CommGroup E] [CommGroup D]
    (R : Chapter02LocalReciprocityData B E D)
    (V : Chapter02DiscreteValuationData B R.unitSubgroup) :
    Subgroup.closure
        ({chapter02LocalArtinMap R V.uniformizer} ∪
          Set.range ((chapter02LocalArtinMap R).comp R.unitSubgroup.subtype)) = ⊤ := by
  apply le_antisymm le_top
  intro d _
  rcases chapter02_local_artin_surjective R d with ⟨x, rfl⟩
  obtain ⟨u, hu⟩ := V.decomposition x
  rw [hu, map_mul, (chapter02LocalArtinMap R).map_zpow]
  apply Subgroup.mul_mem
  · exact Subgroup.subset_closure (Or.inr ⟨u, rfl⟩)
  · have hπ : chapter02LocalArtinMap R V.uniformizer ∈
        ({chapter02LocalArtinMap R V.uniformizer} ∪
          Set.range ((chapter02LocalArtinMap R).comp R.unitSubgroup.subtype)) := by
      exact Or.inl (by rfl)
    exact (Subgroup.closure
      ({chapter02LocalArtinMap R V.uniformizer} ∪
        Set.range ((chapter02LocalArtinMap R).comp R.unitSubgroup.subtype))).zpow_mem
      (Subgroup.subset_closure hπ) _

/- WARNING FROM THE SOURCE: no ideal symbol is defined at a ramified place.
   The API deliberately exposes only `chapter02FrobeniusCoset` and local Artin
   maps there; `chapter02IdealArtinSymbol` requires an explicit unramified
   proof. -/

end

end LastLib.Book06GlobalClassFieldTheory.Chapter02
