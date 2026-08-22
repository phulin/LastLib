import LastLib.Book05LocalClassFieldTheory.Chapter08.Section04UnitAndRamificationTheorem

namespace LastLib.Book05LocalClassFieldTheory.Chapter08

noncomputable section

open scoped IsMulCommutative Pointwise

/-! ## 8.5. Conductors -/

def chapter08ExtensionConductorExists
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) : Prop :=
  ∃ n : ℕ, chapter08UnitFiltration vK n ≤ chapter08NormSubgroup K L

def chapter08ExtensionConductor
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (h : chapter08ExtensionConductorExists (K := K) (L := L) vK) : ℕ :=
  by
    classical
    exact Nat.find h

theorem chapter08_extension_conductor_exists_of_unit_ramification_input
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))] [CommGroup (Gal(L / K))]
    (X : Chapter08FiniteLocalExtensionData K L)
    (F : Chapter08RamificationFiltration (Gal(L / K)))
    (P : Chapter08UnitRamificationInput X F) :
    chapter08ExtensionConductorExists (K := K) (L := L) X.base.valuation := by
  classical
  change ∃ n : ℕ, chapter08UnitFiltration X.base.valuation n ≤ chapter08NormSubgroup K L
  obtain ⟨n, hn⟩ : ∃ n : ℕ, chapter08UpperGroup F n = ⊥ := by
    obtain ⟨b, hb⟩ := F.lower_eventually_trivial
    have hbij' :
        Function.Bijective
          (LastLib.Book03RamificationTheory.Chapter05.chapter05HerbrandFunction F) :=
      P.upper_bijective
    have hstrict :=
      (LastLib.Book03RamificationTheory.Chapter05.chapter05_herbrand_function_is_continuous_increasing_piecewise_linear
        F).2.1
    have hb0 : (0 : ℝ) ≤ (b : ℝ) := by
      exact_mod_cast Nat.zero_le b
    have hbm : (-1 : ℝ) ≤ (b : ℝ) := by
      linarith
    have hblt : (-1 : ℝ) < (b : ℝ) := by
      linarith
    have hφ : (-1 : ℝ) ≤ chapter08HerbrandFunction F (b : ℝ) := by
      change (-1 : ℝ) ≤
        LastLib.Book03RamificationTheory.Chapter05.chapter05HerbrandFunction F (b : ℝ)
      have hlt :
          LastLib.Book03RamificationTheory.Chapter05.chapter05HerbrandFunction F (-1 : ℝ) <
            LastLib.Book03RamificationTheory.Chapter05.chapter05HerbrandFunction F (b : ℝ) :=
        hstrict (a := (-1 : ℝ)) (b := (b : ℝ)) (by simp) hbm hblt
      rw [LastLib.Book03RamificationTheory.Chapter05.chapter05_herbrand_function_neg_one F] at hlt
      linarith
    obtain ⟨n, hn⟩ := exists_nat_ge (chapter08HerbrandFunction F (b : ℝ))
    refine ⟨n, ?_⟩
    have hbot :
        chapter08UpperGroup F (chapter08HerbrandFunction F (b : ℝ)) = ⊥ := by
      rw [chapter08UpperGroup,
        LastLib.Book03RamificationTheory.Chapter05.chapter05_upper_group_eq_lower_at_inverse
          F hφ]
      change F.lowerGroup
        (LastLib.Book03RamificationTheory.Chapter05.chapter05HerbrandInverse F
          (LastLib.Book03RamificationTheory.Chapter05.chapter05HerbrandFunction F (b : ℝ))) = ⊥
      rw [LastLib.Book03RamificationTheory.Chapter05.chapter05_herbrand_inverse_left_inverse
        F hbij' (b : ℝ)]
      exact hb b le_rfl
    have hanti :=
      LastLib.Book03RamificationTheory.Chapter05.chapter05_upper_filtration_antitone F hbij'
    apply bot_unique
    calc
      chapter08UpperGroup F (n : ℝ) ≤
          chapter08UpperGroup F (chapter08HerbrandFunction F (b : ℝ)) :=
        hanti hn
      _ = ⊥ := hbot
  have hU := P.units_norm_from_fixed_field n
  rw [hn] at hU
  rw [show
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FixedField
          (K := K) (L := L) (⊥ : Subgroup (Gal(L / K))) =
        (⊤ : IntermediateField K L) by simp] at hU
  have hnormtop :
      chapter08NormSubgroup K (⊤ : IntermediateField K L) =
        chapter08NormSubgroup K L := by
    ext x
    constructor
    · intro hx
      rcases (LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05_mem_normSubgroup_iff
        K (⊤ : IntermediateField K L) x).mp hx with ⟨y, hy⟩
      apply (LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05_mem_normSubgroup_iff
        K L x).mpr
      let e : (⊤ : IntermediateField K L) ≃ₐ[K] L := IntermediateField.topEquiv
      let y' : Lˣ := Units.map e.toRingEquiv.toMonoidHom y
      refine ⟨y', ?_⟩
      apply Units.ext
      dsimp [y', LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05NormMap,
        LastLib.Book05LocalClassFieldTheory.Chapter03.chapter03NormUnit]
      change Algebra.norm K (e (y : (⊤ : IntermediateField K L))) = (x : K)
      rw [Algebra.norm_eq_of_algEquiv e]
      exact congrArg Units.val hy
    · intro hx
      rcases (LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05_mem_normSubgroup_iff
        K L x).mp hx with ⟨y, hy⟩
      apply (LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05_mem_normSubgroup_iff
        K (⊤ : IntermediateField K L) x).mpr
      let e : (⊤ : IntermediateField K L) ≃ₐ[K] L := IntermediateField.topEquiv
      let y' : (⊤ : IntermediateField K L)ˣ :=
        Units.map e.symm.toRingEquiv.toMonoidHom y
      refine ⟨y', ?_⟩
      apply Units.ext
      dsimp [y', LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05NormMap,
        LastLib.Book05LocalClassFieldTheory.Chapter03.chapter03NormUnit]
      change Algebra.norm K (e.symm (y : L)) = (x : K)
      rw [Algebra.norm_eq_of_algEquiv e.symm]
      exact congrArg Units.val hy
  refine ⟨n, ?_⟩
  rw [← hnormtop]
  exact hU

theorem chapter08_extension_conductor_spec
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (h : chapter08ExtensionConductorExists (K := K) (L := L) vK) :
    chapter08UnitFiltration vK
        (chapter08ExtensionConductor (K := K) (L := L) vK h) ≤
      chapter08NormSubgroup K L := by
  classical
  exact Nat.find_spec h

theorem chapter08_extension_conductor_minimal
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (h : chapter08ExtensionConductorExists (K := K) (L := L) vK) (n : ℕ)
    (hn : chapter08UnitFiltration vK n ≤ chapter08NormSubgroup K L) :
    chapter08ExtensionConductor (K := K) (L := L) vK h ≤ n := by
  classical
  exact Nat.find_min' h hn

def chapter08RamificationConductorExists
    {G : Type*} [Group G] [Finite G]
    (F : Chapter08RamificationFiltration G) : Prop :=
  ∃ n : ℕ, chapter08UpperGroup F n = ⊥

def chapter08RamificationConductor
    {G : Type*} [Group G] [Finite G]
    (F : Chapter08RamificationFiltration G)
    (h : chapter08RamificationConductorExists F) : ℕ :=
  by
    classical
    exact Nat.find h

theorem chapter08_ramification_conductor_exists
    {G : Type*} [Group G] [Finite G]
    (F : Chapter08RamificationFiltration G)
    (hbij : Function.Bijective (chapter08HerbrandFunction F)) :
    chapter08RamificationConductorExists F := by
  classical
  obtain ⟨b, hb⟩ := F.lower_eventually_trivial
  have hbij' :
      Function.Bijective
        (LastLib.Book03RamificationTheory.Chapter05.chapter05HerbrandFunction F) := hbij
  have hstrict :=
    (LastLib.Book03RamificationTheory.Chapter05.chapter05_herbrand_function_is_continuous_increasing_piecewise_linear
      F).2.1
  have hb0 : (0 : ℝ) ≤ (b : ℝ) := by
    exact_mod_cast Nat.zero_le b
  have hbm : (-1 : ℝ) ≤ (b : ℝ) := by
    linarith
  have hblt : (-1 : ℝ) < (b : ℝ) := by
    linarith
  have hφ : (-1 : ℝ) ≤ chapter08HerbrandFunction F (b : ℝ) := by
    change (-1 : ℝ) ≤
      LastLib.Book03RamificationTheory.Chapter05.chapter05HerbrandFunction F (b : ℝ)
    have hlt :
        LastLib.Book03RamificationTheory.Chapter05.chapter05HerbrandFunction F (-1 : ℝ) <
          LastLib.Book03RamificationTheory.Chapter05.chapter05HerbrandFunction F (b : ℝ) :=
      hstrict (a := (-1 : ℝ)) (b := (b : ℝ)) (by simp) hbm hblt
    rw [LastLib.Book03RamificationTheory.Chapter05.chapter05_herbrand_function_neg_one F] at hlt
    linarith
  obtain ⟨n, hn⟩ := exists_nat_ge (chapter08HerbrandFunction F (b : ℝ))
  refine ⟨n, ?_⟩
  have hbot :
      chapter08UpperGroup F (chapter08HerbrandFunction F (b : ℝ)) = ⊥ := by
    rw [chapter08UpperGroup,
      LastLib.Book03RamificationTheory.Chapter05.chapter05_upper_group_eq_lower_at_inverse
        F hφ]
    change F.lowerGroup
      (LastLib.Book03RamificationTheory.Chapter05.chapter05HerbrandInverse F
        (LastLib.Book03RamificationTheory.Chapter05.chapter05HerbrandFunction F (b : ℝ))) = ⊥
    rw [LastLib.Book03RamificationTheory.Chapter05.chapter05_herbrand_inverse_left_inverse
      F hbij' (b : ℝ)]
    exact hb b le_rfl
  have hanti :=
    LastLib.Book03RamificationTheory.Chapter05.chapter05_upper_filtration_antitone F hbij'
  apply bot_unique
  calc
    chapter08UpperGroup F (n : ℝ) ≤
        chapter08UpperGroup F (chapter08HerbrandFunction F (b : ℝ)) :=
      hanti hn
    _ = ⊥ := hbot

theorem chapter08_ramification_conductor_spec
    {G : Type*} [Group G] [Finite G]
    (F : Chapter08RamificationFiltration G)
    (h : chapter08RamificationConductorExists F) :
    chapter08UpperGroup F (chapter08RamificationConductor F h) = ⊥ := by
  classical
  exact Nat.find_spec h

theorem chapter08_extension_conductor_eq_ramification_conductor
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (X : Chapter08FiniteLocalExtensionData K L)
    (D : Chapter08FiniteReciprocityData K L)
    (F : Chapter08RamificationFiltration (Gal(L / K)))
    (P : Chapter08UnitRamificationInput X F)
    (hunit : chapter08ExtensionConductorExists (K := K) (L := L) X.base.valuation)
    (hram : chapter08RamificationConductorExists F) :
    chapter08ExtensionConductor (K := K) (L := L) X.base.valuation hunit =
      chapter08RamificationConductor F hram := by
  classical
  let nu : ℕ :=
    chapter08ExtensionConductor (K := K) (L := L) X.base.valuation hunit
  let nr : ℕ := chapter08RamificationConductor F hram
  have hnu_spec :
      chapter08UnitFiltration X.base.valuation nu ≤ chapter08NormSubgroup K L := by
    exact chapter08_extension_conductor_spec X.base.valuation hunit
  have hnr_spec : chapter08UpperGroup F nr = ⊥ := by
    exact chapter08_ramification_conductor_spec F hram
  have hnr_unit :
      chapter08UnitFiltration X.base.valuation nr ≤ chapter08NormSubgroup K L := by
    intro x hx
    have hxupper :
        chapter08FiniteReciprocityMap D x ∈ chapter08UpperGroup F nr := by
      rw [← chapter08_unit_and_upper_ramification X D F P nr]
      exact ⟨x, hx, rfl⟩
    rw [hnr_spec] at hxupper
    change chapter08FiniteReciprocityMap D x = 1 at hxupper
    rw [← chapter08FiniteReciprocityMap_kernel D]
    exact hxupper
  have hnu_le_nr : nu ≤ nr := by
    exact chapter08_extension_conductor_minimal X.base.valuation hunit nr hnr_unit
  have hnr_upper :
      chapter08UpperGroup F nu = ⊥ := by
    have hmap := chapter08_unit_and_upper_ramification X D F P nu
    apply bot_unique
    rw [← hmap]
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hxnorm : x ∈ chapter08NormSubgroup K L := hnu_spec hx
    rw [← chapter08FiniteReciprocityMap_kernel D] at hxnorm
    exact hxnorm
  have hnr_le_nu : nr ≤ nu := by
    exact Nat.find_min' hram hnr_upper
  exact Nat.le_antisymm hnu_le_nr hnr_le_nu

theorem chapter08_extension_conductor_zero_iff_unramified
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (X : Chapter08FiniteLocalExtensionData K L)
    (D : Chapter08FiniteReciprocityData K L)
    (F : Chapter08RamificationFiltration (Gal(L / K)))
    (P : Chapter08UnitRamificationInput X F)
    (hunit : chapter08ExtensionConductorExists (K := K) (L := L) X.base.valuation) :
    chapter08ExtensionConductor (K := K) (L := L) X.base.valuation hunit = 0 ↔
      chapter08FiniteUnramified X := by
  sorry

def chapter08TamelyRamified
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (X : Chapter08FiniteLocalExtensionData K L) : Prop :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05TameAtResidueCharacteristic
    X.ramificationIndex (chapter08ResidueCharacteristic X.base.valuation)

def chapter08WildlyRamified
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (X : Chapter08FiniteLocalExtensionData K L) : Prop :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05WildAtResidueCharacteristic
    X.ramificationIndex (chapter08ResidueCharacteristic X.base.valuation)

def chapter08NontrivialRamification
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (X : Chapter08FiniteLocalExtensionData K L) : Prop :=
  chapter08FiniteInertia X ≠ ⊥

private theorem chapter08_tame_principal_units_are_norm_units
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (X : Chapter08FiniteLocalExtensionData K L)
    (htame : chapter08TamelyRamified X) :
    chapter08UnitFiltration X.base.valuation 1 ≤
      chapter08NormUnitSubgroup X.base.valuation X.valuation := by
  classical
  let A := X.base.valuation.toValuation.valuationSubring
  let _ : Finite (Chapter08ResidueField X.base.valuation) :=
    X.base.localField.2
  let _ : Fintype (Chapter08ResidueField X.base.valuation) :=
    Fintype.ofFinite _
  let _ : Valuation.IsRankOneDiscrete X.base.valuation.toValuation :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08_rank_one_discrete_of_add_valuation
      X.base.valuation X.base.localField.1.1
  let _ : Nontrivial
      (MonoidWithZeroHom.valueGroup (.ofClass X.base.valuation.toValuation)) :=
    ⟨⟨Valuation.IsRankOneDiscrete.generator' X.base.valuation.toValuation, 1,
      ne_of_lt (Valuation.IsRankOneDiscrete.generator'_lt_one
        X.base.valuation.toValuation)⟩⟩
  have hDVR : IsDiscreteValuationRing A := by
    change IsDiscreteValuationRing X.base.valuation.toValuation.valuationSubring
    infer_instance
  have hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A :=
    X.base.localField.1.2
  let p := chapter08ResidueCharacteristic X.base.valuation
  have hp : Nat.Prime p := CharP.prime_ringChar _
  have hcop : Nat.Coprime X.ramificationIndex p := by
    exact htame
  have heunit :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Chapter10IntegerIsUnit
        A X.ramificationIndex := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit
      (X.ramificationIndex : A)).mp
    intro hzero
    have hcast :
        (X.ramificationIndex : Chapter08ResidueField X.base.valuation) = 0 := by
      change IsLocalRing.residue A (X.ramificationIndex : A) = 0
      simpa using hzero
    have hdiv : p ∣ X.ramificationIndex :=
      (CharP.cast_eq_zero_iff (Chapter08ResidueField X.base.valuation) p
        X.ramificationIndex).mp hcast
    exact (hp.coprime_iff_not_dvd.mp (Nat.coprime_comm.mp hcop)) hdiv
  obtain ⟨e, hepow⟩ :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10_principal_unit_power_isomorphism
      A X.ramificationIndex heunit hcomplete hDVR
  let N₀ : Subgroup (chapter08UnitFiltration X.base.valuation 0) :=
    (chapter08NormUnitSubgroup X.base.valuation X.valuation).comap
      (chapter08UnitFiltration X.base.valuation 0).subtype
  have hindex : N₀.index = X.ramificationIndex := by
    dsimp [N₀]
    exact chapter08_unit_norm_index_eq_ramification_index X
  intro x hx
  change x ∈
    (Chapter08RingUnitFiltration X.base.valuation 1).map
      (chapter08RingUnitInclusion X.base.valuation) at hx
  rcases hx with ⟨u, hu, hux⟩
  let u₁ : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10UnitFiltration
      A 1 := ⟨u, hu⟩
  let v₁ := e.symm u₁
  have hvpow : v₁ ^ X.ramificationIndex = u₁ := by
    have h := e.apply_symm_apply u₁
    rw [hepow] at h
    exact h
  have hvpow' :
      (chapter08RingUnitInclusion X.base.valuation (v₁ : Aˣ)) ^
          X.ramificationIndex = x := by
    rw [← map_pow]
    have hinc := congrArg
      (fun w : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10UnitFiltration
          A 1 =>
        chapter08RingUnitInclusion X.base.valuation (w : Aˣ)) hvpow
    exact hinc.trans hux
  have hv1 : (v₁ : Aˣ) ∈ Chapter08RingUnitFiltration X.base.valuation 1 := by
    exact v₁.property
  have hv0 : (v₁ : Aˣ) ∈ Chapter08RingUnitFiltration X.base.valuation 0 := by
    exact (LastLib.Book05LocalClassFieldTheory.Chapter02.chapter02_unit_filtration_descending
      X.base.valuation 0) hv1
  have hv0' :
      chapter08RingUnitInclusion X.base.valuation (v₁ : Aˣ) ∈
        chapter08UnitFiltration X.base.valuation 0 := by
    exact ⟨v₁, hv0, rfl⟩
  let z : chapter08UnitFiltration X.base.valuation 0 :=
    ⟨chapter08RingUnitInclusion X.base.valuation (v₁ : Aˣ), hv0'⟩
  have hz : (z : Kˣ) ^ N₀.index ∈
      chapter08NormUnitSubgroup X.base.valuation X.valuation :=
    N₀.pow_index_mem z
  rw [hindex] at hz
  rw [← hvpow']
  exact hz

theorem chapter08_nontrivial_tame_conductor_one
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (X : Chapter08FiniteLocalExtensionData K L)
    (D : Chapter08FiniteReciprocityData K L)
    (F : Chapter08RamificationFiltration (Gal(L / K)))
    (P : Chapter08UnitRamificationInput X F)
    (hunit : chapter08ExtensionConductorExists (K := K) (L := L) X.base.valuation)
    (htame : chapter08TamelyRamified X)
    (hnontrivial : chapter08NontrivialRamification X) :
    chapter08ExtensionConductor (K := K) (L := L) X.base.valuation hunit = 1 := by
  have hU1norm := chapter08_tame_principal_units_are_norm_units X htame
  have hU1 :
      chapter08UnitFiltration X.base.valuation 1 ≤
        chapter08NormSubgroup K L :=
    hU1norm.trans
      (chapter08_norm_unit_subgroup_le_norm_subgroup
        X.base.valuation X.valuation)
  let n := chapter08ExtensionConductor (K := K) (L := L)
    X.base.valuation hunit
  have hnle : n ≤ 1 := by
    exact chapter08_extension_conductor_minimal X.base.valuation hunit 1 hU1
  have hnzero : n ≠ 0 := by
    intro hn
    have hspec :
        chapter08UnitFiltration X.base.valuation n ≤
          chapter08NormSubgroup K L :=
      chapter08_extension_conductor_spec X.base.valuation hunit
    have hI : chapter08FiniteInertia X = ⊥ := by
      apply bot_unique
      rw [← chapter08_finite_reciprocity_units_eq_inertia X D]
      intro y hy
      rcases hy with ⟨u, hu, rfl⟩
      have hun : u ∈ chapter08UnitFiltration X.base.valuation n := by
        rw [hn]
        exact hu
      have hunorm := hspec hun
      rw [← chapter08FiniteReciprocityMap_kernel D] at hunorm
      exact hunorm
    exact hnontrivial hI
  have hnge : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hnzero
  exact Nat.le_antisymm hnle hnge

theorem chapter08_wild_conductor_at_least_two
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (X : Chapter08FiniteLocalExtensionData K L)
    (D : Chapter08FiniteReciprocityData K L)
    (F : Chapter08RamificationFiltration (Gal(L / K)))
    (P : Chapter08UnitRamificationInput X F)
    (hunit : chapter08ExtensionConductorExists (K := K) (L := L) X.base.valuation)
    (hwild : chapter08WildlyRamified X) :
    2 ≤ chapter08ExtensionConductor (K := K) (L := L) X.base.valuation hunit := by
  sorry

/- A character correspondence is the finite-level form of transporting a
   character through reciprocity. -/
structure Chapter08CharacterCorrespondence
    {K L : Type} {A : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    [CommGroup A] (D : Chapter08FiniteReciprocityData K L) where
  multiplicative : Kˣ →* A
  galois : Gal(L / K) →* A
  compatibility : galois.comp (chapter08FiniteReciprocityMap D) = multiplicative

theorem chapter08_character_correspondence_is_finite_order
    {K L : Type} {A : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    [CommGroup A]
    (D : Chapter08FiniteReciprocityData K L)
    (C : Chapter08CharacterCorrespondence (A := A) D) :
    chapter08FiniteOrderCharacter C.multiplicative := by
  change (Set.range C.multiplicative).Finite
  have hrecip :
      (Set.range (chapter08FiniteReciprocityMap D)).Finite := by
    exact Set.finite_univ.subset (Set.range_subset_iff.mpr (fun _ => Set.mem_univ _))
  have hcomp :
      (Set.range (C.galois.comp (chapter08FiniteReciprocityMap D))).Finite := by
    change (Set.range (C.galois ∘ chapter08FiniteReciprocityMap D)).Finite
    rw [Set.range_comp]
    exact hrecip.image C.galois
  rw [← C.compatibility]
  exact hcomp

theorem chapter08_character_conductor_spec
    {K A : Type*} [Field K] [CommGroup A]
    (vK : AddValuation K (WithTop ℤ)) (χ : Kˣ →* A)
    (hχ : chapter08ConductorExists vK χ) :
    ∀ x ∈ chapter08UnitFiltration vK (chapter08Conductor vK χ hχ),
      χ x = 1 := by
  classical
  exact Nat.find_spec hχ

theorem chapter08_character_conductor_minimal
    {K A : Type*} [Field K] [CommGroup A]
    (vK : AddValuation K (WithTop ℤ)) (χ : Kˣ →* A)
    (hχ : chapter08ConductorExists vK χ) (n : ℕ)
    (hn : ∀ x ∈ chapter08UnitFiltration vK n, χ x = 1) :
    chapter08Conductor vK χ hχ ≤ n := by
  classical
  exact Nat.find_min' hχ hn

theorem chapter08_character_conductor_matches_galois_character_conductor
    {K L : Type} {A : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    [CommGroup A]
    (X : Chapter08FiniteLocalExtensionData K L)
    (D : Chapter08FiniteReciprocityData K L)
    (F : Chapter08RamificationFiltration (Gal(L / K)))
    (P : Chapter08UnitRamificationInput X F)
    (C : Chapter08CharacterCorrespondence (A := A) D)
    (hχ : chapter08ConductorExists X.base.valuation C.multiplicative)
    (hρ : chapter08GaloisConductorExists F C.galois) :
      chapter08Conductor X.base.valuation C.multiplicative hχ =
      chapter08GaloisConductor F C.galois hρ := by
  classical
  let d : DecidablePred (fun n : ℕ =>
      ∀ g ∈ chapter08UpperGroup F n, C.galois g = 1) :=
    fun n => Classical.propDecidable _
  apply Nat.le_antisymm
  · apply chapter08_character_conductor_minimal X.base.valuation C.multiplicative hχ
      (chapter08GaloisConductor F C.galois hρ)
    intro x hx
    have hxupper :
        chapter08FiniteReciprocityMap D x ∈
          chapter08UpperGroup F
            (chapter08GaloisConductor F C.galois hρ) := by
      rw [← chapter08_unit_and_upper_ramification X D F P _]
      exact ⟨x, hx, rfl⟩
    have hgalois :
        C.galois (chapter08FiniteReciprocityMap D x) = 1 :=
      (show ∀ g ∈ chapter08UpperGroup F
          (chapter08GaloisConductor F C.galois hρ), C.galois g = 1 from by
        simpa [d, chapter08GaloisConductor] using
          (@Nat.find_spec _ d hρ))
        _ hxupper
    have hcompat :
        C.galois (chapter08FiniteReciprocityMap D x) = C.multiplicative x := by
      simpa [MonoidHom.comp_apply] using
        congrArg (fun f : Kˣ →* A => f x) C.compatibility
    exact hcompat.symm.trans hgalois
  · have hmin : Nat.find hρ ≤
        chapter08Conductor X.base.valuation C.multiplicative hχ := by
      apply @Nat.find_min' _ d hρ
      intro g hg
      rw [← chapter08_unit_and_upper_ramification X D F P _] at hg
      rcases hg with ⟨x, hx, rfl⟩
      have hspec := chapter08_character_conductor_spec
        X.base.valuation C.multiplicative hχ x hx
      have hcompat :
          C.galois (chapter08FiniteReciprocityMap D x) = C.multiplicative x := by
        simpa [MonoidHom.comp_apply] using
          congrArg (fun f : Kˣ →* A => f x) C.compatibility
      exact hcompat.trans hspec
    simpa [d, chapter08GaloisConductor] using hmin

theorem chapter08_character_unramified_iff_conductor_zero
    {K L : Type} {A : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    [CommGroup A]
    (X : Chapter08FiniteLocalExtensionData K L)
    (D : Chapter08FiniteReciprocityData K L)
    (F : Chapter08RamificationFiltration (Gal(L / K)))
    (P : Chapter08UnitRamificationInput X F)
    (C : Chapter08CharacterCorrespondence (A := A) D)
    (hχ : chapter08ConductorExists X.base.valuation C.multiplicative) :
    chapter08Conductor X.base.valuation C.multiplicative hχ = 0 ↔
      ∀ g ∈ chapter08FiniteInertia X, C.galois g = 1 := by
  have _hP := P
  constructor
  · intro hzero g hg
    rw [← chapter08_finite_reciprocity_units_eq_inertia X D] at hg
    rcases hg with ⟨x, hx, rfl⟩
    have hx' : x ∈ chapter08UnitFiltration X.base.valuation
        (chapter08Conductor X.base.valuation C.multiplicative hχ) := by
      simpa [hzero] using hx
    have hspec := chapter08_character_conductor_spec
      X.base.valuation C.multiplicative hχ x hx'
    have hcompat :
        C.galois (chapter08FiniteReciprocityMap D x) = C.multiplicative x := by
      simpa [MonoidHom.comp_apply] using
        congrArg (fun f : Kˣ →* A => f x) C.compatibility
    exact hcompat.trans hspec
  · intro htrivial
    apply Nat.eq_zero_of_le_zero
    apply chapter08_character_conductor_minimal X.base.valuation C.multiplicative hχ
      0
    intro x hx
    have hg :
        chapter08FiniteReciprocityMap D x ∈ chapter08FiniteInertia X := by
      rw [← chapter08_finite_reciprocity_units_eq_inertia X D]
      exact ⟨x, hx, rfl⟩
    have hcompat :
        C.galois (chapter08FiniteReciprocityMap D x) = C.multiplicative x := by
      simpa [MonoidHom.comp_apply] using
        congrArg (fun f : Kˣ →* A => f x) C.compatibility
    exact hcompat.symm.trans (htrivial _ hg)

end

end LastLib.Book05LocalClassFieldTheory.Chapter08
