import LastLib.Book03RamificationTheory.Chapter03.Dependencies
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.Section02FrobeniusInAnUnramifiedExtension
import Mathlib.FieldTheory.Galois.Basic

namespace LastLib.Book03RamificationTheory.Chapter03

noncomputable section

open scoped BigOperators Pointwise

/-! ## 3.1. Unramified extensions -/

/-
The local data used for the unramified calculation.  `decomposition_top`
records the single-branch/local-field situation in which the source writes
the decomposition group as the full Galois group; faithful reduction is the
intrinsic unramified condition needed for `G_0 = 1`. -/
structure Chapter03UnramifiedGaloisData
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] where
  valuationRing : ValuationSubring L
  decomposition_top :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
        K valuationRing = ⊤
  reduction_faithful :
    Function.Injective
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05ResidueAction
        K valuationRing)

theorem chapter03_unramified_inertia_is_trivial
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (D : Chapter03UnramifiedGaloisData K L) :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05InertiaGroup
        K D.valuationRing = ⊥ := by
  rw [LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.inertia_group_is_residue_action_kernel]
  ext σ
  constructor
  · intro hσ
    change LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05ResidueAction
      K D.valuationRing σ = 1 at hσ
    have hσone : σ = 1 := D.reduction_faithful
      (hσ.trans (map_one _).symm)
    simp [hσone]
  · intro hσ
    have hσone : σ = 1 := by simpa using hσ
    rw [hσone]
    simp

theorem chapter03_unramified_reduction_has_no_positive_ramification
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (D : Chapter03UnramifiedGaloisData K L) :
    chapter03GaloisLowerGroup K D.valuationRing (-1) = ⊤ ∧
      chapter03GaloisLowerGroup K D.valuationRing 0 = ⊥ ∧
      (∀ i : ℤ, 0 < i → chapter03GaloisLowerGroup K D.valuationRing i = ⊥) := by
  have hinertia := chapter03_unramified_inertia_is_trivial D
  have hzero : chapter03GaloisLowerGroup K D.valuationRing 0 = ⊥ := by
    rw [chapter03GaloisLowerGroup_zero_eq_inertia]
    simpa [LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05InertiaGroupInG] using
      congrArg
        (fun H : Subgroup
            (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
              K D.valuationRing) => H.map (Subgroup.subtype _)) hinertia
  have hram : ∀ n : ℕ,
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05RamificationGroup
          K D.valuationRing (n + 1) = ⊥ := by
    intro n
    induction n with
    | zero =>
        exact (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FirstRamificationGroup_eq_inertia
          (A := D.valuationRing)).trans hinertia
    | succ n ih =>
        apply le_antisymm
        · rw [show n + 1 + 1 = (n + 1) + 1 by omega]
          exact (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05RamificationGroup_succ_le
            D.valuationRing (n + 1)).trans_eq ih
        · exact bot_le
  refine ⟨chapter03GaloisLowerGroup_neg_one K D.valuationRing D.decomposition_top,
    hzero, ?_⟩
  intro i hi
  rw [chapter03GaloisLowerGroup, if_neg (by omega), hram i.toNat]
  exact Subgroup.map_bot _

theorem chapter03_unramified_lower_groups
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (D : Chapter03UnramifiedGaloisData K L) :
    chapter03GaloisLowerGroup K D.valuationRing (-1) = ⊤ ∧
      chapter03GaloisLowerGroup K D.valuationRing 0 = ⊥ := by
  have h := chapter03_unramified_reduction_has_no_positive_ramification D
  exact ⟨h.1, h.2.1⟩

/- Arithmetic Frobenius is recorded at the residue-visible, `-1` level. -/
theorem chapter03_unramified_arithmetic_frobenius_at_minus_one
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Fintype k] [Finite l] [Algebra K L] [Algebra k l]
    [Algebra.IsAlgebraic k l] [FiniteDimensional K L]
    [FiniteDimensional k l] [IsGalois K L] [IsGalois k l]
    (D : Chapter03UnramifiedGaloisData K L)
    (R : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.Chapter06UnramifiedGaloisReduction
      K L k l)
    (hdegree : 1 < Module.finrank k l) :
    (∀ σ : Gal(L / K),
        ∃ n : ℤ,
          (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.chapter06UnramifiedArithmeticFrobenius
            R) ^ n = σ) ∧
      chapter03GaloisLowerGroup K D.valuationRing (-1) = ⊤ ∧
      chapter03GaloisLowerGroup K D.valuationRing 0 ≠ ⊤ := by
  have hgen : ∀ σ : Gal(L / K),
      ∃ n : ℤ,
        (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.chapter06UnramifiedArithmeticFrobenius
          R) ^ n = σ := by
    intro σ
    exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.chapter06_unramified_arithmetic_frobenius_generates
      R σ
  have hres_ne :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.chapter06ArithmeticFrobenius
        k l ≠ 1 := by
    intro h
    have hord :=
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.chapter06_arithmetic_frobenius_order
        k l (Module.finrank k l) rfl
    rw [h] at hord
    have hfin : Module.finrank k l = 1 := by simpa using hord.symm
    omega
  have hlift_ne :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.chapter06UnramifiedArithmeticFrobenius
          R ≠ 1 := by
    intro h
    apply hres_ne
    simpa [LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.chapter06UnramifiedArithmeticFrobenius] using
      congrArg R.reduction h
  have hzero : chapter03GaloisLowerGroup K D.valuationRing 0 = ⊥ := by
    rw [chapter03GaloisLowerGroup_zero_eq_inertia]
    simpa [LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05InertiaGroupInG] using
      congrArg
        (fun H : Subgroup
            (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
              K D.valuationRing) => H.map (Subgroup.subtype _))
        (chapter03_unramified_inertia_is_trivial D)
  have hnotop : chapter03GaloisLowerGroup K D.valuationRing 0 ≠ ⊤ := by
    intro htop
    have hmem :
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.chapter06UnramifiedArithmeticFrobenius
            R ∈ (⊥ : Subgroup (Gal(L / K))) := by
      rw [← hzero, htop]
      trivial
    apply hlift_ne
    simpa using hmem
  exact ⟨hgen, chapter03GaloisLowerGroup_neg_one K D.valuationRing D.decomposition_top,
    hnotop⟩

end
end LastLib.Book03RamificationTheory.Chapter03
