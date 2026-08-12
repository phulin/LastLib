import LastLib.Book03RamificationTheory.Chapter02.Dependencies
import Mathlib.RingTheory.Adjoin.Basic

namespace LastLib.Book03RamificationTheory.Chapter02

noncomputable section

open scoped BigOperators Pointwise

universe u

/-! ## 2.1. Why displacement is the right measurement -/

/--
The book-facing data of a finite lower filtration.  The displacement field is
normalized so that the identity has value `+∞`, and the lower groups use the
deliberate one-step shift `n + 1`.
-/
structure Chapter02LowerFiltration (G : Type u) [Group G] [Finite G] where
  group : ℕ → Subgroup G
  normal : ∀ n : ℕ, (group n).Normal
  descending : ∀ n : ℕ, group (n + 1) ≤ group n
  eventually_trivial : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → group n = ⊥
  displacement : G → WithTop ℤ
  displacement_one : displacement 1 = ⊤
  lower_mem_iff :
    ∀ {σ : G}, σ ≠ 1 → ∀ n : ℕ,
      σ ∈ group n ↔ ((n + 1 : ℕ) : WithTop ℤ) ≤ displacement σ

namespace Chapter02LowerFiltration

variable {G : Type u} [Group G] [Finite G]

instance : CoeFun (Chapter02LowerFiltration G) (fun _ => ℕ → Subgroup G) :=
  ⟨Chapter02LowerFiltration.group⟩

@[simp]
theorem group_apply (F : Chapter02LowerFiltration G) (n : ℕ) :
    F n = F.group n := rfl

end Chapter02LowerFiltration

instance chapter02LowerFiltrationNormalInstance
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) (n : ℕ) :
    (F.group n).Normal :=
  F.normal n

@[ext]
theorem Chapter02LowerFiltration.ext
    {G : Type u} [Group G] [Finite G]
    {F F' : Chapter02LowerFiltration G}
    (hgroup : ∀ n : ℕ, F.group n = F'.group n)
    (hdisp : F.displacement = F'.displacement) : F = F' := by
  sorry

/-- Extend the nonnegative filtration to the integer convention of the book. -/
def chapter02IntegerLowerGroup
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) (i : ℤ) : Subgroup G :=
  if i < 0 then ⊤ else F.group i.toNat

@[simp]
theorem chapter02IntegerLowerGroup_neg_one
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) :
    chapter02IntegerLowerGroup F (-1) = ⊤ := by
  sorry

theorem chapter02IntegerLowerGroup_of_nonnegative
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) {i : ℤ} (hi : 0 ≤ i) :
    chapter02IntegerLowerGroup F i = F.group i.toNat := by
  sorry

theorem chapter02IntegerLowerGroup_succ_le
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) (i : ℤ) (hi : -1 ≤ i) :
    chapter02IntegerLowerGroup F (i + 1) ≤
      chapter02IntegerLowerGroup F i := by
  sorry

theorem chapter02IntegerLowerGroup_anti
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) {i j : ℤ}
    (hi : -1 ≤ i) (hij : i ≤ j) :
    chapter02IntegerLowerGroup F j ≤ chapter02IntegerLowerGroup F i := by
  sorry

theorem chapter02IntegerLowerGroup_normal
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) (i : ℤ) :
    (chapter02IntegerLowerGroup F i).Normal := by
  sorry

/-- A lower break is a strict change between consecutive integer levels. -/
def chapter02LowerBreak
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) (n : ℕ) : Prop :=
  F.group n ≠ F.group (n + 1)

/-- The displacement minimum is attained and finite away from the identity. -/
theorem chapter02Displacement_attained_of_ne_one
    (K : Type u) {L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : AddValuation L (WithTop ℤ))
    [Valuation.IsRankOneDiscrete v.toValuation]
    (σ : chapter02DecompositionGroup K v) (hσ : σ ≠ 1) :
    ∃ x : v.toValuation.valuationSubring,
      v ((σ : Gal(L / K)) (x : L) - (x : L)) =
        chapter02Displacement K v σ ∧
      chapter02Displacement K v σ ≠ ⊤ := by
  sorry

/-- The displacement and congruence descriptions of the lower groups agree. -/
theorem chapter02_lower_group_mem_iff_congruence
    (K : Type u) {L : Type u} [Field K] [Field L] [Algebra K L]
    (v : AddValuation L (WithTop ℤ))
    (i : ℤ) (σ : chapter02DecompositionGroup K v) :
    σ ∈ chapter02LowerGroup K v i ↔ chapter02HigherCongruence K v i σ := by
  sorry

theorem chapter02_lower_group_of_nonnegative
    (K : Type u) {L : Type u} [Field K] [Field L] [Algebra K L]
    (v : AddValuation L (WithTop ℤ)) {i : ℤ} (hi : 0 ≤ i) :
    chapter02LowerGroup K v i = chapter02LowerGroupNat K v i.toNat := by
  sorry

theorem chapter02_lower_group_of_negative
    (K : Type u) {L : Type u} [Field K] [Field L] [Algebra K L]
    (v : AddValuation L (WithTop ℤ)) {i : ℤ} (hi : i < 0) :
    chapter02LowerGroup K v i = ⊤ := by
  sorry

theorem chapter02_higher_congruence_of_nonnegative
    (K : Type u) {L : Type u} [Field K] [Field L] [Algebra K L]
    (v : AddValuation L (WithTop ℤ)) {i : ℤ} (hi : 0 ≤ i)
    (σ : chapter02DecompositionGroup K v) :
    chapter02HigherCongruence K v i σ ↔
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05HigherCongruence
        v.toValuation.valuationSubring (i.toNat + 1) σ := by
  sorry

theorem chapter02_higher_congruence_of_negative
    (K : Type u) {L : Type u} [Field K] [Field L] [Algebra K L]
    (v : AddValuation L (WithTop ℤ)) {i : ℤ} (hi : i < 0)
    (σ : chapter02DecompositionGroup K v) :
    chapter02HigherCongruence K v i σ := by
  sorry

/-- The lower-group membership criterion in terms of `i_G`. -/
theorem chapter02_lower_group_mem_iff_displacement
    (K : Type u) {L : Type u} [Field K] [Field L] [Algebra K L]
    (v : AddValuation L (WithTop ℤ))
    [Valuation.IsRankOneDiscrete v.toValuation]
    (σ : chapter02DecompositionGroup K v) (hσ : σ ≠ 1) (n : ℕ) :
    σ ∈ chapter02LowerGroup K v n ↔
      ((n + 1 : ℕ) : WithTop ℤ) ≤ chapter02Displacement K v σ := by
  sorry

/-- Reduction detects non-inertial displacement at value zero. -/
theorem chapter02_not_inertia_has_zero_displacement
    (K : Type u) {L : Type u} [Field K] [Field L] [Algebra K L]
    (v : AddValuation L (WithTop ℤ))
    (σ : chapter02DecompositionGroup K v)
    (hσ : σ ∉
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05InertiaGroup
        K v.toValuation.valuationSubring) :
    ∃ x : v.toValuation.valuationSubring,
      v ((σ : Gal(L / K)) (x : L) - (x : L)) = 0 := by
  sorry

/-- A nonidentity inertial automorphism has positive finite displacement. -/
theorem chapter02_inertia_displacement_pos
    (K : Type u) {L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : AddValuation L (WithTop ℤ))
    [Valuation.IsRankOneDiscrete v.toValuation]
    (σ : chapter02DecompositionGroup K v)
    (hσI : σ ∈
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05InertiaGroup
        K v.toValuation.valuationSubring) (hσ : σ ≠ 1) :
    (0 : WithTop ℤ) < chapter02Displacement K v σ ∧
      chapter02Displacement K v σ ≠ ⊤ := by
  sorry

/-- The zeroth lower group is inertia, without a residue-separability hypothesis. -/
theorem chapter02_lower_group_zero_eq_inertia
    (K : Type u) {L : Type u} [Field K] [Field L] [Algebra K L]
    (v : AddValuation L (WithTop ℤ)) :
    chapter02LowerGroup K v 0 =
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05InertiaGroup
        K v.toValuation.valuationSubring := by
  simpa [chapter02LowerGroupNat, chapter02LowerGroup] using
    (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FirstRamificationGroup_eq_inertia
      (A := v.toValuation.valuationSubring))

@[simp]
theorem chapter02_lower_group_neg_one_eq_top
    (K : Type u) {L : Type u} [Field K] [Field L] [Algebra K L]
    (v : AddValuation L (WithTop ℤ)) :
    chapter02LowerGroup K v (-1) = ⊤ := by
  sorry

/-- A convenient book-facing name for the monogenic integral presentation. -/
def chapter02IntegralRingGeneratedByUniformizer
    {C A : Type*} [CommRing C] [CommRing A] [Algebra C A]
    (π : A) : Prop :=
  Algebra.adjoin C ({π} : Set A) = ⊤

/- DEPENDENCY_GUESS: The preceding chapter's tame character package is not
   present in this checkout.  The fixed coefficient ring and its generation by
   a uniformizer below are the minimal local interface needed for the
   uniformizer-displacement lemma. -/
/-- In the separable-residue case the minimum can be tested on a uniformizer. -/
theorem chapter02_displacement_eq_uniformizer
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    [Valuation.IsRankOneDiscrete vK.toValuation]
    [Valuation.IsRankOneDiscrete vL.toValuation]
    (hext : vK.IsEquiv (vL.comap (algebraMap K L)))
    (π : vL.toValuation.valuationSubring)
    (hπ : vL.toValuation.IsUniformizer (π : L))
    (C : Type*) [CommRing C]
    [Algebra C vL.toValuation.valuationSubring]
    [Algebra (IsLocalRing.ResidueField vK.toValuation.valuationSubring)
      (IsLocalRing.ResidueField vL.toValuation.valuationSubring)]
    (hseparable : Algebra.IsSeparable
      (IsLocalRing.ResidueField vK.toValuation.valuationSubring)
      (IsLocalRing.ResidueField vL.toValuation.valuationSubring))
    (hgen : chapter02IntegralRingGeneratedByUniformizer
      (C := C) (A := vL.toValuation.valuationSubring) π)
    (hfixed : ∀ σ : chapter02DecompositionGroup K vL,
      σ ∈ LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05InertiaGroup
        K vL.toValuation.valuationSubring →
      ∀ c : C,
        σ • algebraMap C vL.toValuation.valuationSubring c =
          algebraMap C vL.toValuation.valuationSubring c)
    (σ : chapter02DecompositionGroup K vL)
    (hσI : σ ∈ LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05InertiaGroup
      K vL.toValuation.valuationSubring)
    (hσ : σ ≠ 1) :
    chapter02Displacement K vL σ =
      vL ((σ : Gal(L / K)) (π : L) - (π : L)) := by
  sorry

/-- The canonical lower filtration attached to a finite Galois valuation branch. -/
def chapter02CanonicalLowerFiltration
    (K : Type u) {L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : AddValuation L (WithTop ℤ))
    -- The finite Galois hypothesis normally supplies this instance; it is
    -- explicit here because the book-facing filtration stores finiteness.
    [Valuation.IsRankOneDiscrete v.toValuation]
    [Finite (chapter02DecompositionGroup K v)] :
    Chapter02LowerFiltration (chapter02DecompositionGroup K v) where
  group := chapter02LowerGroupNat K v
  normal := by
    intro n
    sorry
  descending := by
    intro n
    sorry
  eventually_trivial := by
    sorry
  displacement := chapter02Displacement K v
  displacement_one := chapter02Displacement_one K v
  lower_mem_iff := by
    intro σ hσ n
    exact chapter02_lower_group_mem_iff_displacement K v σ hσ n

end

end LastLib.Book03RamificationTheory.Chapter02
