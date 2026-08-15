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
  displacement_nonnegative : ∀ σ : G, (0 : WithTop ℤ) ≤ displacement σ
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
  cases F
  cases F'
  simp only [Chapter02LowerFiltration.mk.injEq]
  exact ⟨funext hgroup, hdisp⟩

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
  simp [chapter02IntegerLowerGroup]

theorem chapter02IntegerLowerGroup_of_nonnegative
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) {i : ℤ} (hi : 0 ≤ i) :
    chapter02IntegerLowerGroup F i = F.group i.toNat := by
  simp [chapter02IntegerLowerGroup, hi]

theorem chapter02IntegerLowerGroup_succ_le
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) (i : ℤ) (hi : -1 ≤ i) :
    chapter02IntegerLowerGroup F (i + 1) ≤
      chapter02IntegerLowerGroup F i := by
  by_cases h : i < 0
  · have hi' : i = -1 := by omega
    subst i
    simp [chapter02IntegerLowerGroup]
  · have h0 : 0 ≤ i := le_of_not_gt h
    simp only [chapter02IntegerLowerGroup]
    rw [if_neg (by omega : ¬ i + 1 < 0), if_neg h]
    have hnat : (i + 1).toNat = i.toNat + 1 := by omega
    rw [hnat]
    exact F.descending i.toNat

theorem chapter02IntegerLowerGroup_anti
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) {i j : ℤ}
    (hi : -1 ≤ i) (hij : i ≤ j) :
    chapter02IntegerLowerGroup F j ≤ chapter02IntegerLowerGroup F i := by
  by_cases h : i < 0
  · have hi' : i = -1 := by omega
    subst i
    simp [chapter02IntegerLowerGroup]
  · have hi0 : 0 ≤ i := le_of_not_gt h
    have hj0 : 0 ≤ j := by omega
    simp only [chapter02IntegerLowerGroup, if_neg h, if_neg (by omega : ¬ j < 0)]
    have hnat : i.toNat ≤ j.toNat := by omega
    have hanti : ∀ a b : ℕ, a ≤ b → F.group b ≤ F.group a := by
      intro a b hab
      induction hab with
      | refl => exact le_rfl
      | @step b hab ih =>
        exact (F.descending b).trans ih
    exact hanti i.toNat j.toNat hnat

theorem chapter02IntegerLowerGroup_normal
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) (i : ℤ) :
    (chapter02IntegerLowerGroup F i).Normal := by
  by_cases h : i < 0 <;> simp [chapter02IntegerLowerGroup, h, F.normal]

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
  classical
  let A := v.toValuation.valuationSubring
  let f : A → WithTop ℤ :=
    fun x => v ((σ : Gal(L / K)) (x : L) - (x : L))
  let S : Set (WithTop ℤ) := Set.range f
  have hσ' : (σ : Gal(L / K)) ≠ 1 := by
    intro h
    apply hσ
    apply Subtype.ext
    exact h
  have h_exists : ∃ x : A,
      (σ : Gal(L / K)) (x : L) - (x : L) ≠ 0 := by
    obtain ⟨y, hy⟩ : ∃ y : L, (σ : Gal(L / K)) y ≠ y := by
      by_contra h
      apply hσ'
      ext y
      by_contra hy'
      exact h ⟨y, hy'⟩
    rcases A.mem_or_inv_mem' y with hyA | hyA
    · refine ⟨⟨y, hyA⟩, ?_⟩
      intro hzero
      apply hy
      exact sub_eq_zero.mp hzero
    · refine ⟨⟨y⁻¹, hyA⟩, ?_⟩
      intro hzero
      apply hy
      have hinv := congrArg (fun z : L => z⁻¹) (sub_eq_zero.mp hzero)
      simpa using hinv
  obtain ⟨x, hxne⟩ := h_exists
  have hnonneg (y : A) : 0 ≤ f y := by
    have hyA : (((σ • y : A) - y : A) : L) ∈ A :=
      (σ • y : A) - y |>.property
    have hyv : v.toValuation (((σ • y : A) - y : A) : L) ≤ 1 :=
      (Valuation.mem_valuationSubring_iff (v.toValuation) _).mp hyA
    have hval (z : WithTop ℤ) :
        Multiplicative.ofAdd (OrderDual.toDual z) ≤
            (1 : Multiplicative (WithTop ℤ)ᵒᵈ) ↔ 0 ≤ z := by
      change Multiplicative.ofAdd (OrderDual.toDual z) ≤
          Multiplicative.ofAdd (OrderDual.toDual (0 : WithTop ℤ)) ↔ 0 ≤ z
      rw [Multiplicative.ofAdd_le, OrderDual.toDual_le_toDual]
    have hnonneg' := (hval _).mp hyv
    change 0 ≤ v (((σ • y : A) - y : A) : L) at hnonneg'
    have hsmul : ((σ • y : A) : L) = (σ : Gal(L / K)) (y : L) := rfl
    have hsub : (((σ • y : A) - y : A) : L) =
        (σ : Gal(L / K)) (y : L) - (y : L) := by
      change ((σ • y : A) : L) - (y : L) = _
      rw [hsmul]
    rw [hsub] at hnonneg'
    simpa [f] using hnonneg'
  have hS_nonempty : S.Nonempty := by
    exact ⟨f 0, ⟨0, rfl⟩⟩
  have hS_bdd : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro z ⟨y, rfl⟩
    exact hnonneg y
  have hS_not_top : ¬S ⊆ ({⊤} : Set (WithTop ℤ)) := by
    intro htop
    have htop' : f x = ⊤ := by
      simpa using htop ⟨x, rfl⟩
    exact (v.ne_top_iff.mpr hxne) htop'
  have hT_nonempty : ((fun z : ℤ => (z : WithTop ℤ)) ⁻¹' S).Nonempty := by
    obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.mp
      (v.ne_top_iff.mpr hxne)
    refine ⟨z, ?_⟩
    exact ⟨x, hz.symm⟩
  have hT_bdd : BddBelow ((fun z : ℤ => (z : WithTop ℤ)) ⁻¹' S) := by
    refine ⟨0, ?_⟩
    intro z hz
    have hz' : (0 : WithTop ℤ) ≤ (z : WithTop ℤ) := by
      rcases hz with ⟨y, hy⟩
      simpa [hy] using hnonneg y
    simpa using (WithTop.coe_le_coe.mp hz')
  have hSinf : sInf S =
      ((sInf ((fun z : ℤ => (z : WithTop ℤ)) ⁻¹' S) : ℤ) : WithTop ℤ) := by
    exact WithTop.sInf_eq hS_not_top hS_bdd
  obtain ⟨y, hy⟩ := Int.csInf_mem hT_nonempty hT_bdd
  refine ⟨y, ?_, ?_⟩
  · rw [chapter02Displacement, if_neg hσ]
    simpa [f, S] using hy.trans hSinf.symm
  · rw [chapter02Displacement, if_neg hσ]
    rw [hSinf]
    simp [S]

/-- The displacement and congruence descriptions of the lower groups agree. -/
theorem chapter02_lower_group_mem_iff_congruence
    (K : Type u) {L : Type u} [Field K] [Field L] [Algebra K L]
    (v : AddValuation L (WithTop ℤ))
    (i : ℤ) (σ : chapter02DecompositionGroup K v) :
    σ ∈ chapter02LowerGroup K v i ↔ chapter02HigherCongruence K v i σ := by
  by_cases hi : i < 0
  · simp [chapter02LowerGroup, chapter02HigherCongruence, hi]
  · simp only [chapter02LowerGroup, chapter02HigherCongruence, if_neg hi]
    change LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05HigherCongruence
      v.toValuation.valuationSubring (i.toNat + 1) σ ↔
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05HigherCongruence
        v.toValuation.valuationSubring (i.toNat + 1) σ
    rfl

theorem chapter02_lower_group_of_nonnegative
    (K : Type u) {L : Type u} [Field K] [Field L] [Algebra K L]
    (v : AddValuation L (WithTop ℤ)) {i : ℤ} (hi : 0 ≤ i) :
    chapter02LowerGroup K v i = chapter02LowerGroupNat K v i.toNat := by
  simp [chapter02LowerGroup, chapter02LowerGroupNat, hi]

theorem chapter02_lower_group_of_negative
    (K : Type u) {L : Type u} [Field K] [Field L] [Algebra K L]
    (v : AddValuation L (WithTop ℤ)) {i : ℤ} (hi : i < 0) :
    chapter02LowerGroup K v i = ⊤ := by
  simp [chapter02LowerGroup, hi]

theorem chapter02_higher_congruence_of_nonnegative
    (K : Type u) {L : Type u} [Field K] [Field L] [Algebra K L]
    (v : AddValuation L (WithTop ℤ)) {i : ℤ} (hi : 0 ≤ i)
    (σ : chapter02DecompositionGroup K v) :
    chapter02HigherCongruence K v i σ ↔
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05HigherCongruence
        v.toValuation.valuationSubring (i.toNat + 1) σ := by
  simp [chapter02HigherCongruence, hi]

theorem chapter02_higher_congruence_of_negative
    (K : Type u) {L : Type u} [Field K] [Field L] [Algebra K L]
    (v : AddValuation L (WithTop ℤ)) {i : ℤ} (hi : i < 0)
    (σ : chapter02DecompositionGroup K v) :
    chapter02HigherCongruence K v i σ := by
  simp [chapter02HigherCongruence, hi]

/-- The lower-group membership criterion in terms of `i_G`. -/
theorem chapter02_lower_group_mem_iff_displacement
    (K : Type u) {L : Type u} [Field K] [Field L] [Algebra K L]
    (v : AddValuation L (WithTop ℤ))
    [Valuation.IsRankOneDiscrete v.toValuation]
    (hnormalized : Function.Surjective v)
    (σ : chapter02DecompositionGroup K v) (hσ : σ ≠ 1) (n : ℕ) :
    σ ∈ chapter02LowerGroup K v n ↔
      ((n + 1 : ℕ) : WithTop ℤ) ≤ chapter02Displacement K v σ := by
  classical
  let A := v.toValuation.valuationSubring
  let w := v.toValuation
  have hval (z : WithTop ℤ) :
      Multiplicative.ofAdd (OrderDual.toDual z) ≤
          (1 : Multiplicative (WithTop ℤ)ᵒᵈ) ↔ 0 ≤ z := by
    change Multiplicative.ofAdd (OrderDual.toDual z) ≤
        Multiplicative.ofAdd (OrderDual.toDual (0 : WithTop ℤ)) ↔ 0 ≤ z
    rw [Multiplicative.ofAdd_le, OrderDual.toDual_le_toDual]
  have hval_lt (z : WithTop ℤ) :
      Multiplicative.ofAdd (OrderDual.toDual z) <
          (1 : Multiplicative (WithTop ℤ)ᵒᵈ) ↔ 0 < z := by
    change Multiplicative.ofAdd (OrderDual.toDual z) <
        Multiplicative.ofAdd (OrderDual.toDual (0 : WithTop ℤ)) ↔ 0 < z
    rw [Multiplicative.ofAdd_lt, OrderDual.toDual_lt_toDual]
  have hpos_one : ∀ z : WithTop ℤ, 0 < z → (1 : WithTop ℤ) ≤ z := by
    intro z hz
    induction z using WithTop.recTopCoe with
    | top => exact le_top
    | coe z =>
        apply WithTop.coe_le_coe.mpr
        rw [WithTop.coe_pos] at hz
        omega
  have hsub_nonneg : ∀ {z : WithTop ℤ},
      (1 : WithTop ℤ) ≤ z → (0 : WithTop ℤ) ≤ z - 1 := by
    intro z hz
    induction z using WithTop.recTopCoe with
    | top => simp
    | coe z =>
        change (0 : WithTop ℤ) ≤ (↑(z - 1) : WithTop ℤ)
        have hz' : (1 : ℤ) ≤ z := by
          exact_mod_cast hz
        have : (0 : ℤ) ≤ z - 1 := sub_nonneg.mpr hz'
        exact_mod_cast this
  have hsub_nonneg' : ∀ {a b : WithTop ℤ},
      b ≤ a → (0 : WithTop ℤ) ≤ a - b := by
    intro a b hab
    induction a using WithTop.recTopCoe with
    | top => simp
    | coe a =>
        induction b using WithTop.recTopCoe with
        | top => simp at hab
        | coe b =>
            change (0 : WithTop ℤ) ≤ (↑(a - b) : WithTop ℤ)
            apply WithTop.coe_le_coe.mpr
            apply sub_nonneg.mpr
            exact WithTop.coe_le_coe.mp hab
  obtain ⟨πL, hπL⟩ := hnormalized 1
  have hπA : πL ∈ A := by
    apply (Valuation.mem_valuationSubring_iff w πL).2
    apply (hval _).2
    change 0 ≤ v πL
    simp [hπL]
  let π : A := ⟨πL, hπA⟩
  have hπval : v (π : L) = 1 := hπL
  have hπne : (π : L) ≠ 0 := by
    intro hzero
    have hzero' := hπval
    rw [hzero, AddValuation.map_zero] at hzero'
    simp at hzero'
  have hπI : π ∈ IsLocalRing.maximalIdeal A := by
    apply (Valuation.mem_maximalIdeal_iff L w).2
    apply (hval_lt _).2
    change 0 < v (π : L)
    simp [hπval]
  have hpowval (m : ℕ) : v ((π : L) ^ m) = (m : WithTop ℤ) := by
    rw [AddValuation.map_pow, hπval]
    simp
  have hIval (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A) :
      (1 : WithTop ℤ) ≤ v (a : L) := by
    apply hpos_one
    apply (hval_lt _).mp
    exact (Valuation.mem_maximalIdeal_iff L w).mp ha
  have hIeq : IsLocalRing.maximalIdeal A = Ideal.span ({π} : Set A) := by
    apply le_antisymm
    · intro a ha
      apply Ideal.mem_span_singleton.mpr
      let y : L := (a : L) / (π : L)
      have hyval : 0 ≤ v y := by
        dsimp [y]
        rw [AddValuation.map_div, hπval]
        exact hsub_nonneg (hIval a ha)
      have hyA : y ∈ A := by
        apply (Valuation.mem_valuationSubring_iff w y).2
        exact (hval _).2 hyval
      refine ⟨⟨y, hyA⟩, ?_⟩
      apply Subtype.ext
      dsimp [y]
      field_simp
    · exact Ideal.span_le.mpr (by
        intro x hx
        have hx' : x = π := by simpa using hx
        simpa [hx'] using hπI)
  have hmem_val (m : ℕ) (x : A) :
      x ∈ (IsLocalRing.maximalIdeal A) ^ m ↔
        (m : WithTop ℤ) ≤ v (x : L) := by
    rw [hIeq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, rfl⟩
      have hyval : 0 ≤ v (y : L) := by
        exact (hval _).mp (Valuation.mem_valuationSubring_iff w y |>.mp y.property)
      change (m : WithTop ℤ) ≤ v ((π : L) ^ m * (y : L))
      rw [AddValuation.map_mul, hpowval]
      exact le_add_of_nonneg_right hyval
    · intro hx
      let y : L := (x : L) / (π : L) ^ m
      have hyval : 0 ≤ v y := by
        dsimp [y]
        rw [AddValuation.map_div, hpowval]
        exact hsub_nonneg' hx
      have hyA : y ∈ A := by
        apply (Valuation.mem_valuationSubring_iff w y).2
        exact (hval _).2 hyval
      refine ⟨⟨y, hyA⟩, ?_⟩
      apply Subtype.ext
      dsimp [y]
      field_simp
  change σ ∈
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05RamificationGroup
        K A (n + 1) ↔ _
  change LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05HigherCongruence
      A (n + 1) σ ↔ _
  constructor
  · intro hσ'
    rw [chapter02Displacement, if_neg hσ]
    apply le_csInf
    · exact ⟨v ((σ : Gal(L / K)) (0 : L) - (0 : L)), ⟨0, rfl⟩⟩
    · intro b hb
      rcases hb with ⟨x, rfl⟩
      exact (hmem_val (n + 1) ((σ • x : A) - x)).mp (hσ' x)
  · intro hdisp x
    apply (hmem_val (n + 1) ((σ • x : A) - x)).2
    have hdiff_nonneg (y : A) :
        (0 : WithTop ℤ) ≤ v ((σ : Gal(L / K)) (y : L) - (y : L)) := by
      have hyA : (((σ • y : A) - y : A) : L) ∈ A :=
        (σ • y : A) - y |>.property
      have hyv :=
        (hval _).mp ((Valuation.mem_valuationSubring_iff w _).mp hyA)
      change 0 ≤ v (((σ • y : A) - y : A) : L) at hyv
      have hsmul : ((σ • y : A) : L) =
          (σ : Gal(L / K)) (y : L) := rfl
      have hsub : (((σ • y : A) - y : A) : L) =
          (σ : Gal(L / K)) (y : L) - (y : L) := by
        change ((σ • y : A) : L) - (y : L) = _
        rw [hsmul]
      rw [hsub] at hyv
      exact hyv
    have hBdd :
        BddBelow (Set.range (fun y : A =>
          v ((σ : Gal(L / K)) (y : L) - (y : L)))) := by
      refine ⟨0, ?_⟩
      rintro z ⟨y, rfl⟩
      exact hdiff_nonneg y
    have hle : chapter02Displacement K v σ ≤
        v ((σ : Gal(L / K)) (x : L) - (x : L)) := by
      rw [chapter02Displacement, if_neg hσ]
      exact csInf_le hBdd ⟨x, rfl⟩
    exact hdisp.trans hle

/- The identity has displacement `+∞`, so the displacement criterion also
   applies to it.  Keeping this all-elements bridge alongside the nonidentity
   theorem preserves the book's literal set-membership formulation without
   changing the narrower API used by the canonical filtration structure. -/
theorem chapter02_lower_group_mem_iff_displacement_all
    (K : Type u) {L : Type u} [Field K] [Field L] [Algebra K L]
    (v : AddValuation L (WithTop ℤ))
    [Valuation.IsRankOneDiscrete v.toValuation]
    (hnormalized : Function.Surjective v)
    (σ : chapter02DecompositionGroup K v) (n : ℕ) :
    σ ∈ chapter02LowerGroup K v n ↔
      ((n + 1 : ℕ) : WithTop ℤ) ≤ chapter02Displacement K v σ := by
  by_cases hσ : σ = 1
  · subst σ
    simp [chapter02Displacement]
  · exact chapter02_lower_group_mem_iff_displacement K v hnormalized σ hσ n

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
  classical
  let A := v.toValuation.valuationSubring
  have hnonneg (x : A) : 0 ≤ v ((σ : Gal(L / K)) (x : L) - (x : L)) := by
    have hxA : (((σ • x : A) - x : A) : L) ∈ A :=
      (σ • x : A) - x |>.property
    have hxv : v.toValuation (((σ • x : A) - x : A) : L) ≤ 1 :=
      (Valuation.mem_valuationSubring_iff (v.toValuation) _).mp hxA
    have hval (z : WithTop ℤ) :
        Multiplicative.ofAdd (OrderDual.toDual z) ≤
            (1 : Multiplicative (WithTop ℤ)ᵒᵈ) ↔ 0 ≤ z := by
      change Multiplicative.ofAdd (OrderDual.toDual z) ≤
          Multiplicative.ofAdd (OrderDual.toDual (0 : WithTop ℤ)) ↔ 0 ≤ z
      rw [Multiplicative.ofAdd_le, OrderDual.toDual_le_toDual]
    have hxnonneg := (hval _).mp hxv
    change 0 ≤ v (((σ • x : A) - x : A) : L) at hxnonneg
    have hsmul : ((σ • x : A) : L) = (σ : Gal(L / K)) (x : L) := rfl
    have hsub : (((σ • x : A) - x : A) : L) =
        (σ : Gal(L / K)) (x : L) - (x : L) := by
      change ((σ • x : A) : L) - (x : L) = _
      rw [hsmul]
    rw [hsub] at hxnonneg
    exact hxnonneg
  have hnotpos : ¬ ∀ x : A, 0 < v ((σ : Gal(L / K)) (x : L) - (x : L)) := by
    intro hpos
    exact hσ ((
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.inertia_iff_positive_valuation_displacement
        v σ).2 hpos)
  push Not at hnotpos
  obtain ⟨x, hx⟩ := hnotpos
  exact ⟨x, le_antisymm hx (hnonneg x)⟩

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
  obtain ⟨x, hx, hfinite⟩ := chapter02Displacement_attained_of_ne_one K v σ hσ
  refine ⟨?_, hfinite⟩
  have hpos :=
    (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.inertia_iff_positive_valuation_displacement
      v σ).mp hσI x
  rw [← hx]
  exact hpos

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
  simp [chapter02LowerGroup]

/-- A convenient book-facing name for the monogenic integral presentation. -/
def chapter02IntegralRingGeneratedByUniformizer
    {C A : Type*} [CommRing C] [CommRing A] [Algebra C A]
    (π : A) : Prop :=
  Algebra.adjoin C ({π} : Set A) = ⊤

/- DEPENDENCY_GUESS: The preceding chapter's tame character package is not
   present in this checkout.  The fixed coefficient ring and its generation by
   a uniformizer below are the minimal local interface needed for the
   uniformizer-displacement lemma. -/
/-- Under the displayed integral-generation hypothesis, the minimum can be
tested on a uniformizer in the separable-residue case. -/
theorem chapter02_displacement_eq_uniformizer
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    [Valuation.IsRankOneDiscrete vK.toValuation]
    [Valuation.IsRankOneDiscrete vL.toValuation]
    (_hext : vK.IsEquiv (vL.comap (algebraMap K L)))
    (π : vL.toValuation.valuationSubring)
    (_hπ : vL.toValuation.IsUniformizer (π : L))
    (C : Type*) [CommRing C]
    [Algebra C vL.toValuation.valuationSubring]
    [Algebra (IsLocalRing.ResidueField vK.toValuation.valuationSubring)
      (IsLocalRing.ResidueField vL.toValuation.valuationSubring)]
    (_hseparable : Algebra.IsSeparable
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
  classical
  let A := vL.toValuation.valuationSubring
  let c : WithTop ℤ :=
    vL ((σ : Gal(L / K)) (π : L) - (π : L))
  have hnonneg (x : A) : 0 ≤ vL (x : L) := by
    have hxA : (x : L) ∈ A := x.property
    have hxv : vL.toValuation (x : L) ≤ 1 :=
      (Valuation.mem_valuationSubring_iff (vL.toValuation) _).mp hxA
    have hval (z : WithTop ℤ) :
        Multiplicative.ofAdd (OrderDual.toDual z) ≤
            (1 : Multiplicative (WithTop ℤ)ᵒᵈ) ↔ 0 ≤ z := by
      change Multiplicative.ofAdd (OrderDual.toDual z) ≤
          Multiplicative.ofAdd (OrderDual.toDual (0 : WithTop ℤ)) ↔ 0 ≤ z
      rw [Multiplicative.ofAdd_le, OrderDual.toDual_le_toDual]
    have hxnonneg := (hval _).mp hxv
    change 0 ≤ vL (x : L) at hxnonneg
    exact hxnonneg
  have hdisp_nonneg (x : A) :
      0 ≤ vL ((σ : Gal(L / K)) (x : L) - (x : L)) := by
    have hsub :
        (((σ • x : A) - x : A) : L) =
          (σ : Gal(L / K)) (x : L) - (x : L) := by
      change ((σ • x : A) : L) - (x : L) = _
      have hsmul : ((σ • x : A) : L) =
          (σ : Gal(L / K)) (x : L) := rfl
      rw [hsmul]
    rw [← hsub]
    exact hnonneg ((σ • x : A) - x)
  have hBdd :
      BddBelow (Set.range (fun x : A =>
        vL ((σ : Gal(L / K)) (x : L) - (x : L)))) := by
    refine ⟨0, ?_⟩
    intro b hb
    rcases hb with ⟨x, rfl⟩
    exact hdisp_nonneg x
  have hP : ∀ x : A, c ≤ vL ((σ : Gal(L / K)) (x : L) - (x : L)) := by
    intro x
    let P : A → Prop :=
      fun z => c ≤ vL ((σ : Gal(L / K)) (z : L) - (z : L))
    have hxgen : x ∈ Algebra.adjoin C ({π} : Set A) := by
      rw [hgen]
      trivial
    have hPx : P x := by
      refine Algebra.adjoin_induction (R := C) (s := ({π} : Set A))
        (p := fun z _ => P z) ?_ ?_ ?_ ?_ hxgen
      · intro z hz
        have hz' : z = π := Set.mem_singleton_iff.mp hz
        subst z
        exact le_rfl
      · intro r
        have hfixA := hfixed σ hσI r
        have hfix : (σ : Gal(L / K)) ((algebraMap C A r : A) : L) =
            ((algebraMap C A r : A) : L) := by
          have hfix' := congrArg (fun z : A => (z : L)) hfixA
          change (σ : Gal(L / K)) ((algebraMap C A r : A) : L) =
            ((algebraMap C A r : A) : L) at hfix'
          exact hfix'
        change c ≤ vL ((σ : Gal(L / K)) ((algebraMap C A r : A) : L) -
          ((algebraMap C A r : A) : L))
        rw [hfix]
        simp
      · intro z w hz hw hzp hwp
        dsimp [P] at hzp hwp ⊢
        have heq :
            (σ : Gal(L / K)) ((z + w : A) : L) - ((z + w : A) : L) =
              ((σ : Gal(L / K)) (z : L) - (z : L)) +
                ((σ : Gal(L / K)) (w : L) - (w : L)) := by
          simp [map_add]
          ring
        change c ≤ vL ((σ : Gal(L / K)) ((z + w : A) : L) -
          ((z + w : A) : L))
        rw [heq]
        exact le_trans (le_min hzp hwp) (vL.map_add _ _)
      · intro z w hz hw hzp hwp
        dsimp [P] at hzp hwp ⊢
        have heq :
            (σ : Gal(L / K)) ((z * w : A) : L) - ((z * w : A) : L) =
              (σ : Gal(L / K)) (z : L) *
                  ((σ : Gal(L / K)) (w : L) - (w : L)) +
                (w : L) *
                  ((σ : Gal(L / K)) (z : L) - (z : L)) := by
          simp [map_mul]
          ring
        have hterm1 :
            c ≤ vL ((σ : Gal(L / K)) (z : L) *
              ((σ : Gal(L / K)) (w : L) - (w : L))) := by
          rw [vL.map_mul]
          have hsz : 0 ≤ vL ((σ : Gal(L / K)) (z : L)) := by
            have hsz' := hnonneg (σ • z)
            have hsmul : ((σ • z : A) : L) =
                (σ : Gal(L / K)) (z : L) := rfl
            rw [hsmul] at hsz'
            exact hsz'
          calc
            c ≤ vL ((σ : Gal(L / K)) (w : L) - (w : L)) := hwp
            _ = 0 + vL ((σ : Gal(L / K)) (w : L) - (w : L)) := by
              rw [zero_add]
            _ ≤ vL ((σ : Gal(L / K)) (z : L)) +
                vL ((σ : Gal(L / K)) (w : L) - (w : L)) := by
              exact add_le_add_left hsz _
        have hterm2 :
            c ≤ vL ((w : L) *
              ((σ : Gal(L / K)) (z : L) - (z : L))) := by
          rw [vL.map_mul]
          calc
            c ≤ vL ((σ : Gal(L / K)) (z : L) - (z : L)) := hzp
            _ = vL ((σ : Gal(L / K)) (z : L) - (z : L)) + 0 := by
              rw [add_zero]
            _ ≤ vL (w : L) +
                vL ((σ : Gal(L / K)) (z : L) - (z : L)) := by
              have hsw : 0 ≤ vL (w : L) := hnonneg w
              have haux := add_le_add_left hsw
                (vL ((σ : Gal(L / K)) (z : L) - (z : L)))
              simpa [zero_add] using haux
        change c ≤ vL ((σ : Gal(L / K)) ((z * w : A) : L) -
          ((z * w : A) : L))
        rw [heq]
        exact le_trans (le_min hterm1 hterm2) (vL.map_add _ _)
    exact hPx
  rw [chapter02Displacement, if_neg hσ]
  apply le_antisymm
  · have hπmem :
        vL ((σ : Gal(L / K)) (π : L) - (π : L)) ∈
          Set.range (fun x : A =>
            vL ((σ : Gal(L / K)) (x : L) - (x : L))) :=
      ⟨π, rfl⟩
    exact csInf_le hBdd hπmem
  · apply le_csInf
    · exact ⟨vL ((σ : Gal(L / K)) (π : L) - (π : L)),
        ⟨π, rfl⟩⟩
    · intro b hb
      rcases hb with ⟨x, rfl⟩
      simpa [c] using hP x

/-- The canonical lower filtration attached to a finite Galois valuation branch. -/
def chapter02CanonicalLowerFiltration
    (K : Type u) {L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : AddValuation L (WithTop ℤ))
    -- The finite Galois hypothesis normally supplies this instance; it is
    -- explicit here because the book-facing filtration stores finiteness.
    [Valuation.IsRankOneDiscrete v.toValuation]
    [Finite (chapter02DecompositionGroup K v)]
    (hnormalized : Function.Surjective v) :
    Chapter02LowerFiltration (chapter02DecompositionGroup K v) where
  group := chapter02LowerGroupNat K v
  normal := by
    intro n
    refine ⟨?_⟩
    intro h hh g
    change ∀ x : v.toValuation.valuationSubring,
      (g * h * g⁻¹) • x - x ∈
        (IsLocalRing.maximalIdeal v.toValuation.valuationSubring) ^ (n + 1)
    intro x
    have hmem := hh (g⁻¹ • x)
    have hmem' := (
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.decomposition_group_preserves_maximal_ideal_powers
        v.toValuation.valuationSubring g (n + 1)
        (h • (g⁻¹ • x) - (g⁻¹ • x))).mp hmem
    have heq : (g * h * g⁻¹) • x - x =
        g • (h • (g⁻¹ • x) - (g⁻¹ • x)) := by
      rw [mul_smul, mul_smul, smul_sub, smul_smul]
      simp
    rw [heq]
    exact hmem'
  descending := by
    intro n
    exact
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05RamificationGroup_succ_le
        (A := v.toValuation.valuationSubring) (n + 1)
  eventually_trivial := by
    classical
    have hI :
        (⨅ r : ℕ, (IsLocalRing.maximalIdeal v.toValuation.valuationSubring) ^ r) =
          (⊥ : Ideal v.toValuation.valuationSubring) := by
      exact Ideal.iInf_pow_eq_bot_of_isLocalRing
        (IsLocalRing.maximalIdeal v.toValuation.valuationSubring)
        ((IsLocalRing.maximalIdeal.isMaximal _).ne_top)
    have hnotall (σ : chapter02DecompositionGroup K v) (hσ : σ ≠ 1) :
        ¬ ∀ n : ℕ, σ ∈ chapter02LowerGroupNat K v n := by
      intro hall
      have hσ' : (σ : Gal(L / K)) ≠ 1 := by
        intro h
        apply hσ
        apply Subtype.ext
        exact h
      obtain ⟨y, hy⟩ : ∃ y : L, (σ : Gal(L / K)) y ≠ y := by
        by_contra h
        apply hσ'
        ext y
        by_contra hy'
        exact h ⟨y, hy'⟩
      obtain ⟨x, hxne⟩ :
          ∃ x : v.toValuation.valuationSubring,
            (σ : Gal(L / K)) (x : L) - (x : L) ≠ 0 := by
        rcases v.toValuation.valuationSubring.mem_or_inv_mem' y with hyA | hyA
        · refine ⟨⟨y, hyA⟩, ?_⟩
          intro hzero
          apply hy
          exact sub_eq_zero.mp hzero
        · refine ⟨⟨y⁻¹, hyA⟩, ?_⟩
          intro hzero
          apply hy
          have hinv := congrArg (fun z : L => z⁻¹) (sub_eq_zero.mp hzero)
          simpa using hinv
      have hdall (r : ℕ) :
          ((σ • x : v.toValuation.valuationSubring) - x :
            v.toValuation.valuationSubring) ∈
            (IsLocalRing.maximalIdeal v.toValuation.valuationSubring) ^ r := by
        cases r with
        | zero => simp
        | succ n =>
            have hh := hall n
            change LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05HigherCongruence
              v.toValuation.valuationSubring (n + 1) σ at hh
            exact hh x
      have hdi :
          ((σ • x : v.toValuation.valuationSubring) - x :
            v.toValuation.valuationSubring) ∈
            ⨅ r : ℕ, (IsLocalRing.maximalIdeal v.toValuation.valuationSubring) ^ r :=
        (Ideal.mem_iInf).2 hdall
      rw [hI] at hdi
      have hzero :
          ((σ • x : v.toValuation.valuationSubring) - x :
            v.toValuation.valuationSubring) = 0 :=
        Ideal.mem_bot.mp hdi
      apply hxne
      have hzero' := congrArg (fun z : v.toValuation.valuationSubring => (z : L)) hzero
      have hsmul : ((σ • x : v.toValuation.valuationSubring) : L) =
          (σ : Gal(L / K)) (x : L) := rfl
      change ((σ • x : v.toValuation.valuationSubring) : L) - (x : L) = 0 at hzero'
      rw [hsmul] at hzero'
      exact hzero'
    have hanti : ∀ a b : ℕ, a ≤ b →
        chapter02LowerGroupNat K v b ≤ chapter02LowerGroupNat K v a := by
      intro a b hab
      induction hab with
      | refl => exact le_rfl
      | @step b hab ih =>
          exact
            (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05RamificationGroup_succ_le
              (A := v.toValuation.valuationSubring) (b + 1)).trans ih
    let f : chapter02DecompositionGroup K v → ℕ := fun σ =>
      if hσ : σ = 1 then 0 else
        Classical.choose (not_forall.mp (hnotall σ hσ))
    have hf_spec (σ : chapter02DecompositionGroup K v) (hσ : σ ≠ 1) :
        σ ∉ chapter02LowerGroupNat K v (f σ) := by
      dsimp [f]
      split
      · contradiction
      · exact Classical.choose_spec (not_forall.mp (hnotall σ hσ))
    have hsne : (Finset.univ.image f).Nonempty := by
      refine ⟨f 1, ?_⟩
      exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
    let N : ℕ := (Finset.univ.image f).max' hsne
    refine ⟨N, ?_⟩
    intro n hn
    apply le_antisymm
    · intro σ hσn
      have hfN : f σ ≤ N := by
        exact Finset.le_max' _ _
          (Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, rfl⟩)
      by_cases hσ : σ = 1
      · simp [hσ]
      · exfalso
        exact hf_spec σ hσ (hanti (f σ) n (hfN.trans hn) hσn)
    · exact bot_le
  displacement := chapter02Displacement K v
  displacement_one := chapter02Displacement_one K v
  displacement_nonnegative := by
    intro σ
    by_cases hσ : σ = 1
    · simp [chapter02Displacement, hσ]
    · rw [chapter02Displacement, if_neg hσ]
      have hnonneg (x : v.toValuation.valuationSubring) :
          0 ≤ v ((σ : Gal(L / K)) (x : L) - (x : L)) := by
        have hxA : (((σ • x : v.toValuation.valuationSubring) - x :
            v.toValuation.valuationSubring) : L) ∈ v.toValuation.valuationSubring :=
          (σ • x : v.toValuation.valuationSubring) - x |>.property
        have hxv : v.toValuation (((σ • x : v.toValuation.valuationSubring) - x :
            v.toValuation.valuationSubring) : L) ≤ 1 :=
          (Valuation.mem_valuationSubring_iff (v.toValuation) _).mp hxA
        have hval (z : WithTop ℤ) :
            Multiplicative.ofAdd (OrderDual.toDual z) ≤
                (1 : Multiplicative (WithTop ℤ)ᵒᵈ) ↔ 0 ≤ z := by
          change Multiplicative.ofAdd (OrderDual.toDual z) ≤
              Multiplicative.ofAdd (OrderDual.toDual (0 : WithTop ℤ)) ↔ 0 ≤ z
          rw [Multiplicative.ofAdd_le, OrderDual.toDual_le_toDual]
        have hxnonneg := (hval _).mp hxv
        change 0 ≤ v (((σ • x : v.toValuation.valuationSubring) - x :
          v.toValuation.valuationSubring) : L) at hxnonneg
        have hsmul : ((σ • x : v.toValuation.valuationSubring) : L) =
            (σ : Gal(L / K)) (x : L) := rfl
        have hsub : (((σ • x : v.toValuation.valuationSubring) - x :
            v.toValuation.valuationSubring) : L) =
            (σ : Gal(L / K)) (x : L) - (x : L) := by
          change ((σ • x : v.toValuation.valuationSubring) : L) - (x : L) = _
          rw [hsmul]
        rw [hsub] at hxnonneg
        exact hxnonneg
      apply le_csInf
      · exact ⟨v ((σ : Gal(L / K)) (0 : L) - (0 : L)), ⟨0, rfl⟩⟩
      · intro b hb
        rcases hb with ⟨x, rfl⟩
        exact hnonneg x
  lower_mem_iff := by
    intro σ hσ n
    exact chapter02_lower_group_mem_iff_displacement K v hnormalized σ hσ n

end

end LastLib.Book03RamificationTheory.Chapter02
