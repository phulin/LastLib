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
   `C`; the structure records exactly the two properties used in the
   uniformizer argument: integral generation and pointwise inertia fixing. -/
structure Chapter02UnramifiedUniformizerPresentation
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (C : Type*) [CommRing C] [Algebra C A]
    (π : A) where
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
  sorry

/- DEPENDENCY_GUESS: The map called `θ₀` in Section 1.3 is not available in
   this checkout.  The structure below keeps its source and kernel explicit,
   while the quotient lift supplies the canonical induced map. -/
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
  sorry

theorem chapter02_tame_character_factorization
    {G : Type u} [Group G] [Finite G]
    {F : Chapter02LowerFiltration G} {l : Type*} [Field l]
    (D : Chapter02TameCharacterData F l) (σ : F.group 0) :
    chapter02TameCharacter D
        (QuotientGroup.mk' ((F.group 1).subgroupOf (F.group 0)) σ) =
      D.thetaZero σ := by
  sorry

/-- A finite subgroup of a field's multiplicative group is cyclic. -/
theorem chapter02_tame_layer_is_cyclic
    {G : Type u} [Group G] [Finite G]
    {F : Chapter02LowerFiltration G} {l : Type*} [Field l]
    (D : Chapter02TameCharacterData F l) :
    IsCyclic (chapter02TameLayer F) := by
  sorry

/-- The tame layer has order prime to the positive residue characteristic. -/
theorem chapter02_tame_layer_order_coprime
    {G : Type u} [Group G] [Finite G]
    {F : Chapter02LowerFiltration G} {l : Type*} [Field l]
    (p : ℕ) [Fact p.Prime] [CharP l p]
    (D : Chapter02TameCharacterData F l) :
    Nat.Coprime (Nat.card (chapter02TameLayer F)) p := by
  sorry

/- The cyclicity conclusion concerns inertia modulo wild inertia, not
   inertia itself.  No splitting or abelianity of the wild extension is
   included in this interface. -/

/- DEPENDENCY_GUESS: The canonical construction of `θ₀` needs the preceding
   maximal-unramified-subextension and uniformizer package.  The hypotheses
   below expose the finite, complete, discrete, residue-separable situation
   in which that package is expected to supply the data. -/
theorem chapter02_canonical_tame_character_data_exists
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    [Valuation.IsRankOneDiscrete vK.toValuation]
    [Valuation.IsRankOneDiscrete vL.toValuation]
    [Finite (chapter02DecompositionGroup K vL)]
    (hext : vK.IsEquiv (vL.comap (algebraMap K L)))
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.toValuation.valuationSubring)
      vK.toValuation.valuationSubring)
    [Algebra (IsLocalRing.ResidueField vK.toValuation.valuationSubring)
      (IsLocalRing.ResidueField vL.toValuation.valuationSubring)]
    [FiniteDimensional (IsLocalRing.ResidueField vK.toValuation.valuationSubring)
      (IsLocalRing.ResidueField vL.toValuation.valuationSubring)]
    (hseparable : Algebra.IsSeparable
      (IsLocalRing.ResidueField vK.toValuation.valuationSubring)
      (IsLocalRing.ResidueField vL.toValuation.valuationSubring)) :
    Nonempty
      (Chapter02TameCharacterData
        (chapter02CanonicalLowerFiltration K vL)
        (IsLocalRing.ResidueField vL.toValuation.valuationSubring)) := by
  sorry

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
  sorry

/-- The lower-layer quotient accounts for the order of inertia. -/
theorem chapter02_inertia_order_factorization
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) :
    Nat.card (F.group 0) =
      Nat.card (chapter02TameLayer F) * Nat.card (chapter02WildGroup F) := by
  sorry

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
  sorry

/-- The wild subgroup is the unique subgroup of inertia of the Sylow order. -/
theorem chapter02_wild_group_unique_sylow
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) (p : ℕ) [Fact p.Prime]
    (htame : Nat.Coprime (Nat.card (chapter02TameLayer F)) p)
    (hwild : IsPGroup p (chapter02WildSubgroupInInertia F)) :
    ∀ P : Sylow p (F.group 0),
      (P : Subgroup (F.group 0)) = chapter02WildSubgroupInInertia F := by
  sorry

/-- If every positive layer is trivial, the wild factor is trivial. -/
theorem chapter02_wild_group_eq_bot_of_trivial_positive_layers
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G)
    (htrivial : ∀ i : ℕ, 1 ≤ i → Subsingleton (chapter02LowerLayer F i)) :
    chapter02WildGroup F = ⊥ := by
  sorry

/-- In the characteristic-zero convention `p = 1`, the wild order is one. -/
theorem chapter02_char_zero_wild_order_eq_one
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G)
    (htrivial : ∀ i : ℕ, 1 ≤ i → Subsingleton (chapter02LowerLayer F i)) :
    chapter02WildOrder F = 1 := by
  sorry

end

end LastLib.Book03RamificationTheory.Chapter02
