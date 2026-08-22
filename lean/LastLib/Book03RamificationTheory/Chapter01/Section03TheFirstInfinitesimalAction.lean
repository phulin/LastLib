import LastLib.Book03RamificationTheory.Chapter01.Section02InertiaRevisited
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.Section05MonogenicityAndResidueGenerators

namespace LastLib.Book03RamificationTheory.Chapter01

noncomputable section

open scoped BigOperators WithZero

/-! ## 1.3. The first infinitesimal action -/

/-- A ratio witness for the action on a chosen uniformizer. -/
structure Chapter01UniformizerRatioWitness
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (π : A)
    (I : Subgroup (chapter01DecompositionGroup K A)) where
  ratio : I → Aˣ
  relation : ∀ σ : I,
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05ValuationRingAction
        K A (σ : chapter01DecompositionGroup K A) π =
      (ratio σ : A) * π

/-- The explicit uniformizer-ratio existence interface. -/
theorem chapter01_uniformizer_ratio_exists_for_valuation
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vL : Valuation L ℤᵐ⁰) [IsDiscreteValuationRing vL.valuationSubring]
    (π : vL.valuationSubring) (hπ : chapter01IsUniformizer vL π)
    (σ : chapter01InertiaGroup K vL.valuationSubring) :
    ∃ c : vL.valuationSubringˣ,
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05ValuationRingAction
          K vL.valuationSubring
          (σ : chapter01DecompositionGroup K vL.valuationSubring) π =
        (c : vL.valuationSubring) * π := by
  have hπirr : Irreducible (π : vL.valuationSubring) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
    exact hπ.2
  have hσirr : Irreducible
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05ValuationRingAction
        K vL.valuationSubring
        (σ : chapter01DecompositionGroup K vL.valuationSubring) π) := by
    exact hπirr.map
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05ValuationRingAction
        K vL.valuationSubring (σ : chapter01DecompositionGroup K vL.valuationSubring))
  have hassoc : Associated
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05ValuationRingAction
        K vL.valuationSubring
        (σ : chapter01DecompositionGroup K vL.valuationSubring) π)
      (π : vL.valuationSubring) := by
    exact IsDiscreteValuationRing.associated_of_irreducible
      vL.valuationSubring hσirr hπirr
  rcases hassoc.symm with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  rw [← hu, mul_comm]

/-- A chosen unit ratio `σ(π)/π` for an inertial automorphism. -/
noncomputable def chapter01UniformizerRatio
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vL : Valuation L ℤᵐ⁰) [IsDiscreteValuationRing vL.valuationSubring]
    (π : vL.valuationSubring) (hπ : chapter01IsUniformizer vL π)
    (σ : chapter01InertiaGroup K vL.valuationSubring) :
    vL.valuationSubringˣ :=
  Classical.choose (chapter01_uniformizer_ratio_exists_for_valuation vL π hπ σ)

@[simp] theorem chapter01UniformizerRatio_relation
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vL : Valuation L ℤᵐ⁰) [IsDiscreteValuationRing vL.valuationSubring]
    (π : vL.valuationSubring) (hπ : chapter01IsUniformizer vL π)
    (σ : chapter01InertiaGroup K vL.valuationSubring) :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05ValuationRingAction
        K vL.valuationSubring
        (σ : chapter01DecompositionGroup K vL.valuationSubring) π =
      (chapter01UniformizerRatio vL π hπ σ : vL.valuationSubring) * π := by
  exact Classical.choose_spec
    (chapter01_uniformizer_ratio_exists_for_valuation vL π hπ σ)

/-- The residue of the uniformizer ratio. -/
def chapter01UniformizerRatioResidue
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vL : Valuation L ℤᵐ⁰) [IsDiscreteValuationRing vL.valuationSubring]
    (π : vL.valuationSubring) (hπ : chapter01IsUniformizer vL π) :
    chapter01InertiaGroup K vL.valuationSubring →
      (chapter01ResidueField vL)ˣ :=
  fun σ => Units.map (IsLocalRing.residue vL.valuationSubring).toMonoidHom
    (chapter01UniformizerRatio vL π hπ σ)

/-- The tame character on the first infinitesimal layer. -/
noncomputable def chapter01TameCharacter
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vL : Valuation L ℤᵐ⁰) [IsDiscreteValuationRing vL.valuationSubring]
    (π : vL.valuationSubring) (hπ : chapter01IsUniformizer vL π) :
    chapter01InertiaGroup K vL.valuationSubring →*
      (chapter01ResidueField vL)ˣ := by
  refine
    { toFun := chapter01UniformizerRatioResidue vL π hπ
      map_one' := ?_
      map_mul' := ?_ }
  · apply Units.ext
    change IsLocalRing.residue vL.valuationSubring
      (chapter01UniformizerRatio vL π hπ 1) = 1
    have hrel := chapter01UniformizerRatio_relation (K := K) (L := L) vL π hπ
      (1 : chapter01InertiaGroup K vL.valuationSubring)
    have hratio :
        chapter01UniformizerRatio (K := K) (L := L) vL π hπ
            (1 : chapter01InertiaGroup K vL.valuationSubring) = 1 := by
      apply Units.ext
      dsimp
      change π = (chapter01UniformizerRatio vL π hπ
        (1 : chapter01InertiaGroup K vL.valuationSubring) :
          vL.valuationSubring) * π at hrel
      apply (mul_right_cancel₀ (M₀ := vL.valuationSubring) hπ.1)
      simpa using hrel.symm
    rw [hratio]
    rfl
  · intro σ τ
    apply Units.ext
    change IsLocalRing.residue vL.valuationSubring
        (chapter01UniformizerRatio vL π hπ (σ * τ)) =
      IsLocalRing.residue vL.valuationSubring
        ((chapter01UniformizerRatio vL π hπ σ : vL.valuationSubring) *
          (chapter01UniformizerRatio vL π hπ τ : vL.valuationSubring))
    have hσ := chapter01UniformizerRatio_relation (K := K) (L := L) vL π hπ σ
    have hτ := chapter01UniformizerRatio_relation (K := K) (L := L) vL π hπ τ
    have hστ := chapter01UniformizerRatio_relation (K := K) (L := L) vL π hπ (σ * τ)
    change (σ : chapter01DecompositionGroup K vL.valuationSubring) • π =
      (chapter01UniformizerRatio vL π hπ σ : vL.valuationSubring) * π at hσ
    change (τ : chapter01DecompositionGroup K vL.valuationSubring) • π =
      (chapter01UniformizerRatio vL π hπ τ : vL.valuationSubring) * π at hτ
    change (σ * τ : chapter01DecompositionGroup K vL.valuationSubring) • π =
      (chapter01UniformizerRatio vL π hπ (σ * τ) : vL.valuationSubring) * π at hστ
    have hratio :
        (chapter01UniformizerRatio vL π hπ (σ * τ) : vL.valuationSubring) =
          ((σ : chapter01DecompositionGroup K vL.valuationSubring) •
            (chapter01UniformizerRatio vL π hπ τ : vL.valuationSubring)) *
            (chapter01UniformizerRatio vL π hπ σ : vL.valuationSubring) := by
      apply (mul_right_cancel₀ (M₀ := vL.valuationSubring) hπ.1)
      rw [← hστ, mul_smul, hτ, smul_mul', hσ, mul_assoc]
    rw [hratio]
    simp only [map_mul]
    rw [mul_comm]
    have hres := chapter01_residue_action_commutes_with_reduction
      (K := K) (L := L) vL.valuationSubring
        (σ : chapter01DecompositionGroup K vL.valuationSubring)
        (chapter01UniformizerRatio vL π hπ τ : vL.valuationSubring)
    change IsLocalRing.residue vL.valuationSubring
        ((σ : chapter01DecompositionGroup K vL.valuationSubring) •
          (chapter01UniformizerRatio vL π hπ τ : vL.valuationSubring)) = _ at hres
    change IsLocalRing.residue vL.valuationSubring
        (chapter01UniformizerRatio vL π hπ σ : vL.valuationSubring) *
          IsLocalRing.residue vL.valuationSubring
            ((σ : chapter01DecompositionGroup K vL.valuationSubring) •
              (chapter01UniformizerRatio vL π hπ τ : vL.valuationSubring)) = _
    rw [hres]
    rw [(chapter01_inertia_mem_iff_residue_fixed vL.valuationSubring
      (σ : chapter01DecompositionGroup K vL.valuationSubring)).mp σ.property]

@[simp] theorem chapter01TameCharacter_apply
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vL : Valuation L ℤᵐ⁰) [IsDiscreteValuationRing vL.valuationSubring]
    (π : vL.valuationSubring) (hπ : chapter01IsUniformizer vL π)
    (σ : chapter01InertiaGroup K vL.valuationSubring) :
    chapter01TameCharacter vL π hπ σ =
      Units.map (IsLocalRing.residue vL.valuationSubring).toMonoidHom
        (chapter01UniformizerRatio vL π hπ σ) := by
  rfl

/-- Changing a uniformizer changes its ratio by `σ(u)/u`; its residue is one. -/
theorem chapter01_uniformizer_change_ratio_residue
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vL : Valuation L ℤᵐ⁰) [IsDiscreteValuationRing vL.valuationSubring]
    (π π' : vL.valuationSubring)
    (hπ : chapter01IsUniformizer vL π)
    (hπ' : chapter01IsUniformizer vL π')
    (u : vL.valuationSubringˣ)
    (hchange : π' = (u : vL.valuationSubring) * π)
    (σ : chapter01InertiaGroup K vL.valuationSubring) :
    chapter01TameCharacter vL π' hπ' σ =
      chapter01TameCharacter vL π hπ σ := by
  apply Units.ext
  change IsLocalRing.residue vL.valuationSubring
      (chapter01UniformizerRatio vL π' hπ' σ) =
    IsLocalRing.residue vL.valuationSubring
      (chapter01UniformizerRatio vL π hπ σ)
  have hσ := chapter01UniformizerRatio_relation (K := K) (L := L) vL π hπ σ
  have hσ' := chapter01UniformizerRatio_relation (K := K) (L := L) vL π' hπ' σ
  change (σ : chapter01DecompositionGroup K vL.valuationSubring) • π =
    (chapter01UniformizerRatio vL π hπ σ : vL.valuationSubring) * π at hσ
  change (σ : chapter01DecompositionGroup K vL.valuationSubring) • π' =
    (chapter01UniformizerRatio vL π' hπ' σ : vL.valuationSubring) * π' at hσ'
  have hσ'' :
      (σ : chapter01DecompositionGroup K vL.valuationSubring) •
          ((u : vL.valuationSubring) * π) =
        (chapter01UniformizerRatio vL π' hπ' σ : vL.valuationSubring) *
          ((u : vL.valuationSubring) * π) := by
    calc
      (σ : chapter01DecompositionGroup K vL.valuationSubring) •
          ((u : vL.valuationSubring) * π) =
        (σ : chapter01DecompositionGroup K vL.valuationSubring) • π' :=
          congrArg (fun x : vL.valuationSubring =>
            (σ : chapter01DecompositionGroup K vL.valuationSubring) • x)
            hchange.symm
      _ = (chapter01UniformizerRatio vL π' hπ' σ : vL.valuationSubring) * π' := hσ'
      _ = (chapter01UniformizerRatio vL π' hπ' σ : vL.valuationSubring) *
          ((u : vL.valuationSubring) * π) :=
        congrArg (fun x : vL.valuationSubring =>
          (chapter01UniformizerRatio vL π' hπ' σ : vL.valuationSubring) * x)
          hchange
  have hratio :
      (chapter01UniformizerRatio vL π' hπ' σ : vL.valuationSubring) *
          (u : vL.valuationSubring) =
        ((σ : chapter01DecompositionGroup K vL.valuationSubring) •
          (u : vL.valuationSubring)) *
          (chapter01UniformizerRatio vL π hπ σ : vL.valuationSubring) := by
    apply (mul_right_cancel₀ (M₀ := vL.valuationSubring) hπ.1)
    rw [smul_mul', hσ] at hσ''
    simpa [mul_assoc] using hσ''.symm
  have hres := congrArg (IsLocalRing.residue vL.valuationSubring) hratio
  simp only [map_mul] at hres
  have hres_u := chapter01_residue_action_commutes_with_reduction
    (K := K) (L := L) vL.valuationSubring
      (σ : chapter01DecompositionGroup K vL.valuationSubring)
      (u : vL.valuationSubring)
  change IsLocalRing.residue vL.valuationSubring
      ((σ : chapter01DecompositionGroup K vL.valuationSubring) •
        (u : vL.valuationSubring)) = _ at hres_u
  rw [(chapter01_inertia_mem_iff_residue_fixed vL.valuationSubring
    (σ : chapter01DecompositionGroup K vL.valuationSubring)).mp σ.property] at hres_u
  rw [hres_u] at hres
  apply (mul_right_cancel₀ (M₀ := chapter01ResidueField vL)
    (Units.map (IsLocalRing.residue vL.valuationSubring).toMonoidHom u).ne_zero)
  simpa [mul_comm] using hres

/-- The tame character is intrinsic to the extension, not to the chosen
uniformizer. -/
theorem chapter01_tame_character_is_intrinsic
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vL : Valuation L ℤᵐ⁰) [IsDiscreteValuationRing vL.valuationSubring]
    (π π' : vL.valuationSubring)
    (hπ : chapter01IsUniformizer vL π)
    (hπ' : chapter01IsUniformizer vL π') :
    chapter01TameCharacter (K := K) vL π hπ =
      chapter01TameCharacter (K := K) vL π' hπ' := by
  have hπirr : Irreducible (π : vL.valuationSubring) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
    exact hπ.2
  have hπ'irr : Irreducible (π' : vL.valuationSubring) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
    exact hπ'.2
  have hassoc : Associated (π' : vL.valuationSubring) (π : vL.valuationSubring) :=
    IsDiscreteValuationRing.associated_of_irreducible
      vL.valuationSubring hπ'irr hπirr
  rcases hassoc.symm with ⟨u, hu⟩
  have hchange : π' = (u : vL.valuationSubring) * π := by
    rw [← hu, mul_comm]
  apply MonoidHom.ext
  intro σ
  exact (chapter01_uniformizer_change_ratio_residue vL π π' hπ hπ' u hchange σ).symm

/-
The next structure records the integral-model part of the source's maximal
unramified-stage argument.  `A₀` is the chosen integral model of the
unramified field, while `k` and `l` are its displayed residue fields.
-/
-- SOURCE_ISSUE: The source says residue separability alone gives the
-- monogenic presentation `B = 𝓞_{K₀}[π_L]`.  Immediate/separable defect
-- extensions over imperfect residue fields show that a defectless (for
-- example perfect-residue) hypothesis is also needed for this conclusion.
-- LOCAL_DEPENDENCY_GUESS: the preceding chapter's maximal-unramified package
-- supplies the identification of `A₀` with `𝓞_{K₀}` and of `B` with the
-- integral closure in `L`; this chapter only needs the monogenic interface.
structure Chapter01MaximalUnramifiedMonogenicPresentation
    (A₀ B k l : Type*) [CommRing A₀] [CommRing B]
    [Field k] [Field l] [Algebra A₀ B] [Algebra k l]
    (π : B) where
  residue_separable : Algebra.IsSeparable k l
  integral_generator :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08MonogenicBy A₀ B π

@[simp] theorem chapter01_maximal_unramified_monogenic_ring_eq_adjoin
    {A₀ B k l : Type*} [CommRing A₀] [CommRing B]
    [Field k] [Field l] [Algebra A₀ B] [Algebra k l]
    (π : B)
    (_P : Chapter01MaximalUnramifiedMonogenicPresentation A₀ B k l π) :
    Algebra.adjoin A₀ ({π} : Set B) = ⊤ := by
  exact _P.integral_generator.2

/-- The canonical maximal-unramified stage package, specialized to the
defectless perfect-residue interface used by the preceding book. -/
theorem chapter01_separable_residue_has_clean_unramified_stage
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsLocalHom (algebraMap A B)] [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [Module.Finite A B]
    [Module.IsTorsionFree A B] [FaithfulSMul A B]
    [IsIntegralClosure B A L]
    [Module.Finite
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.chapter09BaseResidueField A)
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.chapter09ExtensionResidueField B)]
    [LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.Chapter09FiniteLocalExtension
      A B K L]
    [PerfectField
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.chapter09BaseResidueField A)]
    (hresidue_separable : Algebra.IsSeparable
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.chapter09BaseResidueField A)
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.chapter09ExtensionResidueField B)) :
    Nonempty
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.Chapter09Corollary92Data A B K L) := by
  exact
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.chapter09_corollary_92
      A B K L hresidue_separable

/-- The congruence modulo `𝔪²` which defines the first positive lower group. -/
def chapter01FirstInfinitesimalCongruence
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vL : Valuation L ℤᵐ⁰) (π : vL.valuationSubring)
    (σ : chapter01InertiaGroup K vL.valuationSubring) : Prop :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05ValuationRingAction
      K vL.valuationSubring
      (σ : chapter01DecompositionGroup K vL.valuationSubring) π - π ∈
    (IsLocalRing.maximalIdeal vL.valuationSubring) ^ 2

/-- The character kernel is the first infinitesimal congruence kernel. -/
theorem chapter01_tame_character_mem_kernel_iff
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vL : Valuation L ℤᵐ⁰) [IsDiscreteValuationRing vL.valuationSubring]
    (π : vL.valuationSubring) (hπ : chapter01IsUniformizer vL π)
    (σ : chapter01InertiaGroup K vL.valuationSubring) :
    σ ∈ (chapter01TameCharacter vL π hπ).ker ↔
      chapter01FirstInfinitesimalCongruence vL π σ := by
  change (chapter01TameCharacter vL π hπ σ = 1) ↔
    chapter01FirstInfinitesimalCongruence vL π σ
  have hratio := chapter01UniformizerRatio_relation (K := K) (L := L) vL π hπ σ
  change (σ : chapter01DecompositionGroup K vL.valuationSubring) • π =
    (chapter01UniformizerRatio vL π hπ σ : vL.valuationSubring) * π at hratio
  have hchar :
      chapter01TameCharacter vL π hπ σ = 1 ↔
        IsLocalRing.residue vL.valuationSubring
          (chapter01UniformizerRatio vL π hπ σ) = 1 := by
    rw [chapter01TameCharacter_apply]
    constructor
    · intro h
      have h' := congrArg (fun z : (chapter01ResidueField vL)ˣ =>
        (z : chapter01ResidueField vL)) h
      simpa using h'
    · intro h
      apply Units.ext
      exact h
  have hresiff :
      IsLocalRing.residue vL.valuationSubring
          (chapter01UniformizerRatio vL π hπ σ) = 1 ↔
        (chapter01UniformizerRatio vL π hπ σ : vL.valuationSubring) - 1 ∈
          IsLocalRing.maximalIdeal vL.valuationSubring := by
    constructor
    · intro h
      apply (IsLocalRing.residue_eq_zero_iff _).mp
      rw [map_sub, h, map_one, sub_self]
    · intro h
      have hz := (IsLocalRing.residue_eq_zero_iff _).mpr h
      apply sub_eq_zero.mp
      simpa only [map_sub, map_one] using hz
  have hmul_mem_iff (x : vL.valuationSubring) :
      x * π ∈ (IsLocalRing.maximalIdeal vL.valuationSubring) ^ 2 ↔
        x ∈ IsLocalRing.maximalIdeal vL.valuationSubring := by
    have hmax : IsLocalRing.maximalIdeal vL.valuationSubring =
        Ideal.span ({π} : Set vL.valuationSubring) := hπ.2
    rw [hmax, Ideal.span_singleton_pow]
    constructor
    · intro hx
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hx
      apply Ideal.mem_span_singleton.mpr
      refine ⟨c, ?_⟩
      apply (mul_left_cancel₀ (M₀ := vL.valuationSubring) hπ.1)
      simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using hc
    · intro hx
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hx
      apply Ideal.mem_span_singleton.mpr
      refine ⟨c, ?_⟩
      rw [hc]
      ring
  unfold chapter01FirstInfinitesimalCongruence
  change (chapter01TameCharacter vL π hπ σ = 1) ↔
    ((σ : chapter01DecompositionGroup K vL.valuationSubring) • π - π ∈
      (IsLocalRing.maximalIdeal vL.valuationSubring) ^ 2)
  rw [hratio, show
      (chapter01UniformizerRatio vL π hπ σ : vL.valuationSubring) * π - π =
        ((chapter01UniformizerRatio vL π hπ σ : vL.valuationSubring) - 1) * π by ring]
  exact hchar.trans (hresiff.trans (hmul_mem_iff _).symm)

/-- The zero lower group is inertia. -/
theorem chapter01_lower_ramification_group_zero_eq_inertia
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) :
    chapter01LowerRamificationGroup K A 0 = chapter01InertiaGroup K A := by
  change
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05RamificationGroup K A 1 = _
  exact
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FirstRamificationGroup_eq_inertia A

/-- Lower ramification groups descend with the index. -/
theorem chapter01_lower_ramification_group_succ_le
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (i : ℕ) :
    chapter01LowerRamificationGroup K A (i + 1) ≤
      chapter01LowerRamificationGroup K A i := by
  change
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05RamificationGroup
        K A (i + 1 + 1) ≤
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05RamificationGroup
        K A (i + 1)
  simpa [Nat.add_assoc] using
    (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05RamificationGroup_succ_le
      A (i + 1))

/-- Under residue separability, the character kernel is wild inertia. -/
theorem chapter01_tame_character_kernel_eq_wild_inertia
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vK : Valuation K ℤᵐ⁰)
    (vL : Valuation L ℤᵐ⁰) [IsDiscreteValuationRing vL.valuationSubring]
    (hplace : chapter01SamePlace vK vL)
    [Algebra (chapter01ResidueField vK) (chapter01ResidueField vL)]
    (π : vL.valuationSubring) (hπ : chapter01IsUniformizer vL π)
    (hresidue_separable :
      Algebra.IsSeparable (chapter01ResidueField vK)
        (chapter01ResidueField vL)) :
    (chapter01TameCharacter vL π hπ).ker =
      (chapter01WildInertiaGroup K vL.valuationSubring).comap
        (chapter01InertiaGroup K vL.valuationSubring).subtype := by
  sorry

/-- The cotangent line is the finite-precision object on which the first
infinitesimal scalar action is read. -/
def chapter01FirstInfinitesimalScalarAction
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vL : Valuation L ℤᵐ⁰) [IsDiscreteValuationRing vL.valuationSubring]
    (π : vL.valuationSubring) (hπ : chapter01IsUniformizer vL π) :
    chapter01InertiaGroup K vL.valuationSubring →
      (chapter01ResidueField vL →+ chapter01ResidueField vL) :=
  fun σ =>
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10ResiduePowerScaling
      vL.valuationSubring
      (chapter01UniformizerRatio vL π hπ σ) 1

/-- In uniformizer coordinates, the first infinitesimal action is multiplication
by the residue of the ratio. -/
theorem chapter01_first_infinitesimal_scalar_formula
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vL : Valuation L ℤᵐ⁰) [IsDiscreteValuationRing vL.valuationSubring]
    (π : vL.valuationSubring) (hπ : chapter01IsUniformizer vL π)
    (σ : chapter01InertiaGroup K vL.valuationSubring)
    (a : chapter01ResidueField vL) :
    chapter01FirstInfinitesimalScalarAction vL π hπ σ a =
      (chapter01TameCharacter vL π hπ σ : chapter01ResidueField vL) * a := by
  change ((IsLocalRing.residue vL.valuationSubring
      (chapter01UniformizerRatio vL π hπ σ)) ^ 1) * a = _
  simp [chapter01TameCharacter_apply]

end

end LastLib.Book03RamificationTheory.Chapter01
