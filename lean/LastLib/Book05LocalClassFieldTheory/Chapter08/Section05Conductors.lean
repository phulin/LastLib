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
    [FiniteDimensional K L] [IsGalois K L]
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
  sorry

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
  sorry

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
  sorry

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
  sorry

end

end LastLib.Book05LocalClassFieldTheory.Chapter08
