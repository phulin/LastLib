import LastLib.Book03RamificationTheory.Chapter02.Section02BasicGroupProperties
import Mathlib.GroupTheory.Sylow
import Mathlib.RingTheory.AdicCompletion.Basic

namespace LastLib.Book03RamificationTheory.Chapter02

noncomputable section

open scoped BigOperators Pointwise

universe u

/-! ## 2.3. The tame character -/

/-- The successive lower layer, with the subgroup inclusion made explicit. -/
theorem chapter02_lower_layer_normal
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) (i : ℕ) :
    ((F.group (i + 1)).subgroupOf (F.group i)).Normal := by
  apply (Subgroup.normal_subgroupOf_iff (F.descending i)).2
  intro h k hh hk
  exact (F.normal (i + 1)).conj_mem h hh k

instance chapter02LowerLayerNormalInstance
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) (i : ℕ) :
    ((F.group (i + 1)).subgroupOf (F.group i)).Normal :=
  chapter02_lower_layer_normal F i

def chapter02LowerLayer
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) (i : ℕ) : Type _ := by
  letI : ((F.group (i + 1)).subgroupOf (F.group i)).Normal :=
    chapter02_lower_layer_normal F i
  exact F.group i ⧸ (F.group (i + 1)).subgroupOf (F.group i)

instance chapter02LowerLayerGroup
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) (i : ℕ) :
    Group (chapter02LowerLayer F i) := by
  letI : ((F.group (i + 1)).subgroupOf (F.group i)).Normal :=
    chapter02_lower_layer_normal F i
  change Group (F.group i ⧸ (F.group (i + 1)).subgroupOf (F.group i))
  infer_instance

/-- The tame inertia quotient `G₀/G₁`. -/
abbrev chapter02TameLayer
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) : Type _ :=
  chapter02LowerLayer F 0

/-- The wild inertia subgroup at positive depth. -/
def chapter02WildGroup
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) : Subgroup G :=
  F.group 1

/-- The positive-depth wild subgroup viewed as a subgroup of inertia. -/
def chapter02WildSubgroupInInertia
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) : Subgroup (F.group 0) :=
  (F.group 1).subgroupOf (F.group 0)

/-- The residue quotient `G/G₀`. -/
def chapter02ResidueQuotient
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) : Type _ := by
  letI : (F.group 0).Normal := F.normal 0
  exact G ⧸ F.group 0

instance chapter02ResidueQuotientGroup
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) : Group (chapter02ResidueQuotient F) := by
  letI : (F.group 0).Normal := F.normal 0
  change Group (G ⧸ F.group 0)
  infer_instance

/- The preceding chapter's `K₀` is represented here by the coefficient ring
   `C`; the structure records exactly the uniformizer, integral generation,
   and pointwise inertia fixing used in the uniformizer argument.  The
   monogenic presentation is explicit because residue separability alone does
   not rule out defect over an imperfect residue field. -/
structure Chapter02UnramifiedUniformizerPresentation
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (C : Type*) [CommRing C] [Algebra C A]
    (π : A) where
  /-- The named generator is a generator of the maximal ideal of `A`. -/
  uniformizer :
    IsLocalRing.maximalIdeal A = Ideal.span ({π} : Set A)
  integral_generation :
    chapter02IntegralRingGeneratedByUniformizer (C := C) (A := A) π
  inertia_fixes_coefficients :
    ∀ σ : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05InertiaGroup K A,
      ∀ c : C,
      σ • algebraMap C A c = algebraMap C A c

theorem chapter02_inertial_precision_two_iff_uniformizer
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (C : Type*) [CommRing C] [Algebra C A]
    (π : A) (P : Chapter02UnramifiedUniformizerPresentation K L A C π)
    (σ : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup K A)
    (hσI : σ ∈ LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05InertiaGroup K A) :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05HigherCongruence A 2 σ ↔
      (σ • π - π) ∈ (IsLocalRing.maximalIdeal A) ^ 2 := by
  let I : Ideal A := IsLocalRing.maximalIdeal A
  constructor
  · intro hσ
    exact hσ π
  · intro hπ
    change ∀ x : A, (σ • x - x) ∈ I ^ 2
    have hcoeff (c : C) :
        (σ • algebraMap C A c - algebraMap C A c) ∈ I ^ 2 := by
      have hfix := P.inertia_fixes_coefficients ⟨σ, hσI⟩ c
      have hzero : σ • algebraMap C A c - algebraMap C A c = 0 := by
        change (⟨σ, hσI⟩ :
          LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05InertiaGroup K A) •
            algebraMap C A c - algebraMap C A c = 0
        rw [hfix, sub_self]
      rw [hzero]
      exact (I ^ 2).zero_mem
    have hx : ∀ x : A, x ∈ Algebra.adjoin C ({π} : Set A) →
        (σ • x - x) ∈ I ^ 2 := by
      intro x hx
      refine Algebra.adjoin_induction (s := ({π} : Set A))
        (p := fun y _ => (σ • y - y) ∈ I ^ 2) ?_ ?_ ?_ ?_ hx
      · intro y hy
        have hy' : y = π := by simpa using hy
        subst y
        simpa [I] using hπ
      · intro c
        exact hcoeff c
      · intro y z hy hz hy' hz'
        have heq : σ • (y + z) - (y + z) =
            (σ • y - y) + (σ • z - z) := by
          rw [smul_add]
          ring
        rw [heq]
        exact (I ^ 2).add_mem hy' hz'
      · intro y z hy hz hy' hz'
        have heq : σ • (y * z) - (y * z) =
            y * (σ • z - z) + (σ • y - y) * (σ • z) := by
          simp [smul_mul']
          ring
        rw [heq]
        exact (I ^ 2).add_mem
          ((I ^ 2).mul_mem_left y hz')
          ((I ^ 2).mul_mem_right (σ • z) hy')
    intro x
    apply hx x
    rw [P.integral_generation]
    trivial

private theorem chapter02_uniformizer_ratio_exists
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (vL : AddValuation L (WithTop ℤ))
    [Valuation.IsRankOneDiscrete vL.toValuation]
    (π : vL.toValuation.valuationSubring)
    (hπ : vL.toValuation.IsUniformizer π)
    (σ : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05InertiaGroup
      K vL.toValuation.valuationSubring) :
    ∃ c : vL.toValuation.valuationSubringˣ,
      σ • π = (c : vL.toValuation.valuationSubring) * π := by
  let e : RingAut vL.toValuation.valuationSubring :=
    MulSemiringAction.toRingAut _ _ σ
  have hmap :
      (IsLocalRing.maximalIdeal vL.toValuation.valuationSubring).map e =
        IsLocalRing.maximalIdeal vL.toValuation.valuationSubring :=
    IsLocalRing.map_ringEquiv_maximalIdeal e
  have hgen :
      IsLocalRing.maximalIdeal vL.toValuation.valuationSubring =
        Ideal.span ({e π} : Set vL.toValuation.valuationSubring) := by
    calc
      IsLocalRing.maximalIdeal vL.toValuation.valuationSubring =
          (IsLocalRing.maximalIdeal vL.toValuation.valuationSubring).map e :=
        hmap.symm
      _ = (Ideal.span ({π} : Set vL.toValuation.valuationSubring)).map e := by
        rw [hπ.is_generator]
      _ = Ideal.span ({e π} : Set vL.toValuation.valuationSubring) := by
        rw [Ideal.map_span]
        simp
  have hπ' : vL.toValuation.IsUniformizer (e π) :=
    Valuation.isUniformizer_of_maximalIdeal_eq_span vL.toValuation hgen
  obtain ⟨c, hc⟩ := Valuation.associated_of_isUniformizer hπ hπ'
  refine ⟨c, ?_⟩
  simpa [e, mul_comm] using hc.symm

/- Chapter 1 supplies a concrete `θ₀` for its valuation-specific interface.
   The structure below is the necessary bridge to an abstract lower
   filtration: it keeps the source map and its exact kernel explicit, while
   the quotient lift supplies the induced map on `G₀/G₁`. -/
structure Chapter02TameCharacterData
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) (l : Type*) [Field l] where
  thetaZero : F.group 0 →* lˣ
  thetaZero_kernel :
    MonoidHom.ker thetaZero =
      (F.group 1).subgroupOf (F.group 0)

/- The quotient lift is a genuine construction once the kernel equality
   supplied by `θ₀` is known. -/
noncomputable def chapter02TameCharacterOfKernel
    {G : Type u} [Group G] [Finite G]
    {F : Chapter02LowerFiltration G} {l : Type*} [Field l]
    (thetaZero : F.group 0 →* lˣ)
    (hker : MonoidHom.ker thetaZero =
      (F.group 1).subgroupOf (F.group 0)) :
    chapter02TameLayer F →* lˣ := by
  letI : ((F.group 1).subgroupOf (F.group 0)).Normal :=
    chapter02_lower_layer_normal F 0
  exact QuotientGroup.lift
    ((F.group 1).subgroupOf (F.group 0)) thetaZero (by
      intro σ hσ
      change thetaZero σ = 1
      have hσ' : σ ∈ MonoidHom.ker thetaZero := by
        rw [hker]
        exact hσ
      exact hσ')

noncomputable def chapter02TameCharacter
    {G : Type u} [Group G] [Finite G]
    {F : Chapter02LowerFiltration G} {l : Type*} [Field l]
    (D : Chapter02TameCharacterData F l) :
    chapter02TameLayer F →* lˣ :=
  chapter02TameCharacterOfKernel D.thetaZero D.thetaZero_kernel

/-- The tame character is injective on the tame inertia quotient. -/
theorem chapter02_tame_character_injective
    {G : Type u} [Group G] [Finite G]
    {F : Chapter02LowerFiltration G} {l : Type*} [Field l]
    (D : Chapter02TameCharacterData F l) :
    Function.Injective (chapter02TameCharacter D) := by
  let N := (F.group 1).subgroupOf (F.group 0)
  let : N.Normal := chapter02_lower_layer_normal F 0
  have hN : N ≤ D.thetaZero.ker := by
    change (F.group 1).subgroupOf (F.group 0) ≤ D.thetaZero.ker
    rw [D.thetaZero_kernel]
  change Function.Injective
    (QuotientGroup.lift N D.thetaZero hN)
  apply (QuotientGroup.injective_lift_iff N D.thetaZero hN).2
  exact D.thetaZero_kernel.symm

theorem chapter02_tame_character_factorization
    {G : Type u} [Group G] [Finite G]
    {F : Chapter02LowerFiltration G} {l : Type*} [Field l]
    (D : Chapter02TameCharacterData F l) (σ : F.group 0) :
    chapter02TameCharacter D
        (QuotientGroup.mk' ((F.group 1).subgroupOf (F.group 0)) σ) =
      D.thetaZero σ := by
  let N := (F.group 1).subgroupOf (F.group 0)
  let : N.Normal := chapter02_lower_layer_normal F 0
  have hN : N ≤ D.thetaZero.ker := by
    change (F.group 1).subgroupOf (F.group 0) ≤ D.thetaZero.ker
    rw [D.thetaZero_kernel]
  change QuotientGroup.lift N D.thetaZero hN (QuotientGroup.mk' N σ) = D.thetaZero σ
  exact QuotientGroup.lift_mk' N hN σ

/-- A finite subgroup of a field's multiplicative group is cyclic. -/
theorem chapter02_tame_layer_is_cyclic
    {G : Type u} [Group G] [Finite G]
    {F : Chapter02LowerFiltration G} {l : Type*} [Field l]
    (D : Chapter02TameCharacterData F l) :
    IsCyclic (chapter02TameLayer F) := by
  let : ((F.group 1).subgroupOf (F.group 0)).Normal :=
    chapter02_lower_layer_normal F 0
  let : Finite (chapter02TameLayer F) := by
    change Finite (F.group 0 ⧸ (F.group 1).subgroupOf (F.group 0))
    infer_instance
  exact isCyclic_of_injective_ringHom
    ((Units.coeHom l).comp (chapter02TameCharacter D))
    (Units.val_injective.comp (chapter02_tame_character_injective D))

/-- The tame layer has order prime to the positive residue characteristic. -/
theorem chapter02_tame_layer_order_coprime
    {G : Type u} [Group G] [Finite G]
    {F : Chapter02LowerFiltration G} {l : Type*} [Field l]
    (p : ℕ) [Fact p.Prime] [CharP l p]
    (D : Chapter02TameCharacterData F l) :
    Nat.Coprime (Nat.card (chapter02TameLayer F)) p := by
  let : ((F.group 1).subgroupOf (F.group 0)).Normal :=
    chapter02_lower_layer_normal F 0
  let : Finite (chapter02TameLayer F) := by
    change Finite (F.group 0 ⧸ (F.group 1).subgroupOf (F.group 0))
    infer_instance
  rw [Nat.coprime_comm, (Fact.out : p.Prime).coprime_iff_not_dvd]
  intro hpdiv
  have hcyc : IsCyclic (chapter02TameLayer F) :=
    chapter02_tame_layer_is_cyclic D
  obtain ⟨g, hg⟩ := hcyc.exists_ofOrder_eq_natCard
  let f : chapter02TameLayer F →* lˣ := chapter02TameCharacter D
  have hf : Function.Injective f := chapter02_tame_character_injective D
  have horder0 : orderOf g ≠ 0 := by
    rw [hg]
    exact Nat.ne_of_gt Nat.card_pos
  have hpdiv' : p ∣ orderOf g := by
    rw [hg]
    exact hpdiv
  have hpow : orderOf (g ^ (Nat.card (chapter02TameLayer F) / p)) = p := by
    simpa [hg] using (orderOf_pow_orderOf_div horder0 hpdiv')
  let u : lˣ := f (g ^ (Nat.card (chapter02TameLayer F) / p))
  have hpow' : orderOf u = p := by
    rw [orderOf_injective f hf]
    exact hpow
  have hroot (u : lˣ) (hu : u ^ p = 1) : u = 1 := by
    apply Units.val_injective
    have hu' : (u : l) ^ (p ^ 1 * 1) = 1 := by
      simpa [Units.val_pow_eq_pow_val] using congrArg Units.val hu
    have hv := (ExpChar.pow_prime_pow_mul_eq_one_iff p 1 1 (u : l)).mp hu'
    simpa using hv
  have hu : u ^ p = 1 := by
    have hu' : u ^ orderOf u = 1 := pow_orderOf_eq_one u
    rw [hpow'] at hu'
    exact hu'
  have hpone : p = 1 := by
    have hpone' := hpow'.symm
    rw [hroot u hu] at hpone'
    simpa using hpone'
  exact (Fact.out : p.Prime).ne_one hpone

/- The cyclicity conclusion concerns inertia modulo wild inertia, not
   inertia itself.  No splitting or abelianity of the wild extension is
   included in this interface. -/

/-- The canonical tame character data exists once the valuation branch is
    supplied with its clean unramified--uniformizer presentation.

    The residue-field algebra is deliberately the one induced by the
    valuation extension (`Valuation.HasExtension`), rather than an unrelated
    algebra instance.  The coefficient ring and uniformizer are explicit
    because the uniformizer precision argument needs the actual integral
    presentation, not just its numerical invariants. -/
theorem chapter02_canonical_tame_character_data_exists
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    [Valuation.IsRankOneDiscrete vK.toValuation]
    [Valuation.IsRankOneDiscrete vL.toValuation]
    [Finite (chapter02DecompositionGroup K vL)]
    (hnormalized : Function.Surjective vL)
    [Valuation.HasExtension vK.toValuation vL.toValuation]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.toValuation.valuationSubring)
      vK.toValuation.valuationSubring)
    [FiniteDimensional (IsLocalRing.ResidueField vK.toValuation.valuationSubring)
      (IsLocalRing.ResidueField vL.toValuation.valuationSubring)]
    (C : Type*) [CommRing C]
    [Algebra C vL.toValuation.valuationSubring]
    (π : vL.toValuation.valuationSubring)
    (hpresentation :
      Chapter02UnramifiedUniformizerPresentation
        K L vL.toValuation.valuationSubring C π)
    (hseparable : Algebra.IsSeparable
      (IsLocalRing.ResidueField vK.toValuation.valuationSubring)
      (IsLocalRing.ResidueField vL.toValuation.valuationSubring)) :
    Nonempty
      (Chapter02TameCharacterData
        (chapter02CanonicalLowerFiltration K vL hnormalized)
        (IsLocalRing.ResidueField vL.toValuation.valuationSubring)) := by
  have _ := hcomplete
  have _ := hseparable
  let A := vL.toValuation.valuationSubring
  let D := chapter02DecompositionGroup K vL
  let F := chapter02CanonicalLowerFiltration K vL hnormalized
  have hπ : vL.toValuation.IsUniformizer π := by
    exact Valuation.isUniformizer_of_maximalIdeal_eq_span vL.toValuation
      hpresentation.uniformizer
  have hσI (σ : F.group 0) :
      (σ : D) ∈
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05InertiaGroup
          K A := by
    rw [← chapter02_lower_group_zero_eq_inertia K vL]
    exact σ.property
  let iσ (σ : F.group 0) :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05InertiaGroup K A :=
    ⟨(σ : D), hσI σ⟩
  let ratio (σ : F.group 0) : Aˣ :=
    Classical.choose (chapter02_uniformizer_ratio_exists K L vL π hπ (iσ σ))
  have ratio_spec (σ : F.group 0) :
      (σ : D) • π = (ratio σ : A) * π := by
    simpa [ratio, iσ, D, A] using
      (Classical.choose_spec
        (chapter02_uniformizer_ratio_exists K L vL π hπ (iσ σ)))
  have hπA : π ≠ 0 := by
    intro h
    apply hπ.ne_zero
    exact congrArg (fun x : vL.toValuation.valuationSubring => (x : L)) h
  have hmul_iff (d : A) :
      d ∈ IsLocalRing.maximalIdeal A ↔
        d * π ∈ (IsLocalRing.maximalIdeal A) ^ 2 := by
    constructor
    · intro hd
      have hπmem : π ∈ IsLocalRing.maximalIdeal A := by
        rw [hpresentation.uniformizer]
        exact Ideal.mem_span_singleton_self π
      rw [pow_two]
      exact Ideal.mul_mem_mul hd hπmem
    · intro hdp
      change d * π ∈
        (IsLocalRing.maximalIdeal vL.toValuation.valuationSubring) ^ 2 at hdp
      rw [hpresentation.uniformizer, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton'] at hdp
      change d ∈ IsLocalRing.maximalIdeal vL.toValuation.valuationSubring
      rw [hpresentation.uniformizer, Ideal.mem_span_singleton']
      obtain ⟨a, ha⟩ := hdp
      have hcancel : a * π = d := by
        apply mul_right_cancel₀ hπA
        calc
          (a * π) * π = a * π ^ 2 := by ring
          _ = d * π := ha
      exact ⟨a, hcancel⟩
  let theta : F.group 0 →* (IsLocalRing.ResidueField A)ˣ := by
    refine
      { toFun := fun σ =>
          Units.map (IsLocalRing.residue A).toMonoidHom (ratio σ)
        map_one' := ?_
        map_mul' := ?_ }
    · have hratio := ratio_spec (1 : F.group 0)
      have hratio' : (ratio (1 : F.group 0) : A) = 1 := by
        apply mul_right_cancel₀ hπA
        simpa using hratio.symm
      apply Units.ext
      change IsLocalRing.residue A (ratio (1 : F.group 0) : A) = 1
      rw [hratio']
      rfl
    · intro σ τ
      apply Units.ext
      change IsLocalRing.residue A (ratio (σ * τ) : A) =
        IsLocalRing.residue A ((ratio σ : A) * (ratio τ : A))
      have hcomp :
          (ratio (σ * τ) : A) * π =
            ((σ : D) • (ratio τ : A)) * (ratio σ : A) * π := by
        calc
          (ratio (σ * τ) : A) * π = (σ * τ : D) • π :=
            (ratio_spec (σ * τ)).symm
          _ = (σ : D) • ((τ : D) • π) := by rw [mul_smul]
          _ = (σ : D) • ((ratio τ : A) * π) := by rw [ratio_spec τ]
          _ = ((σ : D) • (ratio τ : A)) * ((σ : D) • π) := by
            rw [smul_mul']
          _ = ((σ : D) • (ratio τ : A)) * (ratio σ : A) * π := by
            rw [ratio_spec σ]
            ring
      have hratio :
          (ratio (σ * τ) : A) =
            ((σ : D) • (ratio τ : A)) * (ratio σ : A) :=
        mul_right_cancel₀ hπA hcomp
      have hfix :
          IsLocalRing.residue A ((σ : D) • (ratio τ : A)) =
            IsLocalRing.residue A (ratio τ : A) := by
        rw [LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.residue_action_commutes_with_reduction]
        exact
          (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.inertia_mem_iff_residue_fixed
            A (σ : D)).mp (hσI σ) _
      rw [hratio, map_mul, hfix, map_mul, mul_comm]
  have hker : theta.ker = (F.group 1).subgroupOf (F.group 0) := by
    ext σ
    constructor
    · intro hσ
      change theta σ = 1 at hσ
      have hres : IsLocalRing.residue A (ratio σ : A) = 1 := by
        have h := congrArg Units.val hσ
        simpa [theta] using h
      have hunit : (ratio σ : A) - 1 ∈ IsLocalRing.maximalIdeal A := by
        apply (IsLocalRing.residue_eq_zero_iff _).mp
        simp [map_sub, hres]
      change (σ : D) ∈ F.group 1
      change LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05HigherCongruence
        A 2 (σ : D)
      apply
        (chapter02_inertial_precision_two_iff_uniformizer
          K L A C π hpresentation (σ : D) (hσI σ)).mpr
      have hdiff_eq : (σ : D) • π - π =
          ((ratio σ : A) - 1) * π := by
        rw [ratio_spec σ]
        ring
      have hmul := (hmul_iff ((ratio σ : A) - 1)).mp hunit
      rw [hdiff_eq]
      exact hmul
    · intro hσ
      change (σ : D) ∈ F.group 1 at hσ
      change LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05HigherCongruence
        A 2 (σ : D) at hσ
      have hdiff :=
        (chapter02_inertial_precision_two_iff_uniformizer
          K L A C π hpresentation (σ : D) (hσI σ)).mp hσ
      have hmul : ((ratio σ : A) - 1) * π ∈
          (IsLocalRing.maximalIdeal A) ^ 2 := by
        have hdiff_eq : (σ : D) • π - π =
            ((ratio σ : A) - 1) * π := by
          rw [ratio_spec σ]
          ring
        rw [← hdiff_eq]
        exact hdiff
      have hunit : (ratio σ : A) - 1 ∈ IsLocalRing.maximalIdeal A :=
        (hmul_iff ((ratio σ : A) - 1)).mpr hmul
      apply MonoidHom.mem_ker.mpr
      apply Units.ext
      change IsLocalRing.residue A (ratio σ : A) = 1
      have hzero : IsLocalRing.residue A ((ratio σ : A) - 1) = 0 :=
        (IsLocalRing.residue_eq_zero_iff _).2 hunit
      simpa [map_sub] using sub_eq_zero.mp hzero
  exact ⟨{ thetaZero := by simpa [F, A] using theta
           thetaZero_kernel := by simpa [F, A] using hker }⟩

/-- The first positive group is normal in the ambient group. -/
theorem chapter02_wild_group_normal
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) :
    (chapter02WildGroup F).Normal := by
  exact F.normal 1

/-- A finite filtration with `p`-group positive layers has `p`-group wild part. -/
theorem chapter02_wild_group_is_p_group
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) (p : ℕ) [Fact p.Prime]
    (hlayers : ∀ i : ℕ, 1 ≤ i → IsPGroup p (chapter02LowerLayer F i)) :
    IsPGroup p (chapter02WildGroup F) := by
  obtain ⟨N, hN⟩ := F.eventually_trivial
  have hbase : F.group (N + 1) = ⊥ := hN (N + 1) (by omega)
  have hdown : ∀ d : ℕ, ∀ i : ℕ, i + d = N + 1 → 1 ≤ i →
      IsPGroup p (F.group i) := by
    intro d
    induction d with
    | zero =>
        intro i hEq hi
        have hiEq : i = N + 1 := by omega
        subst i
        rw [hbase]
        exact IsPGroup.of_bot
    | succ d ih =>
        intro i hEq hi
        have hEq' : (i + 1) + d = N + 1 := by omega
        have hnext : IsPGroup p (F.group (i + 1)) :=
          ih (i + 1) hEq' (by omega)
        let H : Subgroup (F.group i) :=
          (F.group (i + 1)).subgroupOf (F.group i)
        let : H.Normal := by
          dsimp [H]
          exact chapter02_lower_layer_normal F i
        let : Finite (chapter02LowerLayer F i) := by
          change Finite (F.group i ⧸ H)
          infer_instance
        have hcard : Nat.card (F.group i) =
            Nat.card (chapter02LowerLayer F i) * Nat.card (F.group (i + 1)) := by
          change Nat.card (F.group i) =
            Nat.card ((F.group i) ⧸ H) * Nat.card (F.group (i + 1))
          have heq : Nat.card H = Nat.card (F.group (i + 1)) :=
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe (F.descending i)).toEquiv
          rw [Subgroup.card_eq_card_quotient_mul_card_subgroup H, heq]
        obtain ⟨a, ha⟩ := (hlayers i hi).exists_card_eq
        obtain ⟨b, hb⟩ := hnext.exists_card_eq
        apply IsPGroup.of_card
        rw [hcard, ha, hb, pow_add]
  have hresult := hdown N 1 (by omega) (by omega)
  change IsPGroup p (F.group 1)
  exact hresult

/-- The lower-layer quotient accounts for the order of inertia. -/
theorem chapter02_inertia_order_factorization
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) :
    Nat.card (F.group 0) =
      Nat.card (chapter02TameLayer F) * Nat.card (chapter02WildGroup F) := by
  let H : Subgroup (F.group 0) := (F.group 1).subgroupOf (F.group 0)
  let : H.Normal := by
    dsimp [H]
    exact chapter02_lower_layer_normal F 0
  change Nat.card (F.group 0) =
    Nat.card ((F.group 0) ⧸ H) * Nat.card (F.group 1)
  have heq : Nat.card H = Nat.card (F.group 1) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (F.descending 0)).toEquiv
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup H, heq]

/-- The ramification index represented by the inertia group in this profile. -/
def chapter02RamificationIndex
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) : ℕ :=
  Nat.card (F.group 0)

theorem chapter02_ramification_index_eq_tame_mul_wild
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) :
    chapter02RamificationIndex F =
      Nat.card (chapter02TameLayer F) * Nat.card (chapter02WildGroup F) := by
  exact chapter02_inertia_order_factorization F

def chapter02TameOrder
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) : ℕ :=
  Nat.card (chapter02TameLayer F)

def chapter02WildOrder
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) : ℕ :=
  Nat.card (chapter02WildGroup F)

theorem chapter02_inertia_order_eq_tame_mul_wild
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) :
    Nat.card (F.group 0) = chapter02TameOrder F * chapter02WildOrder F := by
  exact chapter02_inertia_order_factorization F

/-- A finite wild group has prime-power order. -/
theorem chapter02_wild_order_is_prime_power
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) (p : ℕ) [Fact p.Prime]
    (hwild : IsPGroup p (chapter02WildGroup F)) :
    ∃ n : ℕ, chapter02WildOrder F = p ^ n := by
  change ∃ n : ℕ, Nat.card (chapter02WildGroup F) = p ^ n
  exact hwild.exists_card_eq

/- The ambient wild subgroup and its copy inside inertia have the same
   cardinality.  This bridge lets the canonical p-group result feed the
   Sylow statement, whose Sylow groups live in the inertia subgroup. -/
theorem chapter02_wild_subgroup_in_inertia_is_p_group
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) (p : ℕ) [Fact p.Prime]
    (hwild : IsPGroup p (chapter02WildGroup F)) :
    IsPGroup p (chapter02WildSubgroupInInertia F) := by
  let W : Subgroup (F.group 0) := chapter02WildSubgroupInInertia F
  have hcard : Nat.card W = Nat.card (chapter02WildGroup F) := by
    change Nat.card ((F.group 1).subgroupOf (F.group 0)) = Nat.card (F.group 1)
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (F.descending 0)).toEquiv
  obtain ⟨n, hn⟩ := hwild.exists_card_eq
  apply IsPGroup.of_card
  rw [hcard, hn]

/-- The wild subgroup is the unique subgroup of inertia of the Sylow order. -/
theorem chapter02_wild_group_unique_sylow
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) (p : ℕ) [Fact p.Prime]
    (htame : Nat.Coprime (Nat.card (chapter02TameLayer F)) p)
    (hwild : IsPGroup p (chapter02WildGroup F)) :
    ∀ P : Sylow p (F.group 0),
      (P : Subgroup (F.group 0)) = chapter02WildSubgroupInInertia F := by
  let W : Subgroup (F.group 0) := chapter02WildSubgroupInInertia F
  let : W.Normal := by
    change ((F.group 1).subgroupOf (F.group 0)).Normal
    exact chapter02_lower_layer_normal F 0
  have hwild' : IsPGroup p W :=
    chapter02_wild_subgroup_in_inertia_is_p_group F p hwild
  have hindex : W.index = Nat.card (chapter02TameLayer F) := by
    change W.index = Nat.card ((F.group 0) ⧸ W)
    rw [Subgroup.index_eq_card]
  have hnot : ¬ p ∣ W.index := by
    rw [hindex]
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp htame.symm
  let P0 : Sylow p (F.group 0) := hwild'.toSylow hnot
  intro P
  have hle : W ≤ (P : Subgroup (F.group 0)) :=
    IsPGroup.le_sylow_of_normal hwild' P
  have hle' : (P0 : Subgroup (F.group 0)) ≤ (P : Subgroup (F.group 0)) := by
    simpa [P0] using hle
  have heq : (P : Subgroup (F.group 0)) = (P0 : Subgroup (F.group 0)) :=
    P0.is_maximal' P.isPGroup' hle'
  simpa [P0, W] using heq

/-- If every positive layer is trivial, the wild factor is trivial. -/
theorem chapter02_wild_group_eq_bot_of_trivial_positive_layers
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G)
    (htrivial : ∀ i : ℕ, 1 ≤ i → Subsingleton (chapter02LowerLayer F i)) :
    chapter02WildGroup F = ⊥ := by
  have hstep : ∀ i : ℕ, 1 ≤ i → F.group i = F.group (i + 1) := by
    intro i hi
    let : ((F.group (i + 1)).subgroupOf (F.group i)).Normal :=
      chapter02_lower_layer_normal F i
    let : Subsingleton (chapter02LowerLayer F i) := htrivial i hi
    have htop : (F.group (i + 1)).subgroupOf (F.group i) = ⊤ :=
      QuotientGroup.subsingleton_iff.mp
        (inferInstance : Subsingleton (chapter02LowerLayer F i))
    exact le_antisymm (Subgroup.subgroupOf_eq_top.mp htop) (F.descending i)
  obtain ⟨N, hN⟩ := F.eventually_trivial
  have hbase : F.group (N + 1) = ⊥ := hN (N + 1) (by omega)
  have hdown : ∀ d : ℕ, ∀ i : ℕ, i + d = N + 1 → 1 ≤ i →
      F.group i = ⊥ := by
    intro d
    induction d with
    | zero =>
        intro i hEq hi
        have hiEq : i = N + 1 := by omega
        subst i
        exact hbase
    | succ d ih =>
        intro i hEq hi
        have hEq' : (i + 1) + d = N + 1 := by omega
        have hnext : F.group (i + 1) = ⊥ :=
          ih (i + 1) hEq' (by omega)
        exact (hstep i hi).trans hnext
  have hresult := hdown N 1 (by omega) (by omega)
  change F.group 1 = ⊥
  exact hresult

/-- A filtration with trivial positive layers has trivial wild order. -/
theorem chapter02_wild_order_eq_one_of_trivial_positive_layers
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G)
    (htrivial : ∀ i : ℕ, 1 ≤ i → Subsingleton (chapter02LowerLayer F i)) :
    chapter02WildOrder F = 1 := by
  change Nat.card (chapter02WildGroup F) = 1
  rw [chapter02_wild_group_eq_bot_of_trivial_positive_layers F htrivial]
  simp

end

end LastLib.Book03RamificationTheory.Chapter02
