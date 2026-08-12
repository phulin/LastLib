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
  sorry

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
  sorry

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
  sorry

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
