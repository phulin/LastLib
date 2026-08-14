import LastLib.Book03RamificationTheory.Chapter02.Section03TheTameCharacter
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

namespace LastLib.Book03RamificationTheory.Chapter02

noncomputable section

open scoped BigOperators Pointwise

universe u

/-! ## 2.4. Higher graded pieces -/

/--
The coefficient package obtained from a chosen uniformizer at a positive lower
level.  The zero criterion is coordinate-independent, while the additive law
records the first-order composition calculation.
-/
structure Chapter02HigherCoefficientData
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) (l : Type*) [Field l] (i : ℕ) where
  coefficient : F.group i → l
  coefficient_zero_iff :
    ∀ σ, coefficient σ = 0 ↔ (σ : G) ∈ F.group (i + 1)
  coefficient_mul :
    ∀ σ τ, coefficient (σ * τ) = coefficient σ + coefficient τ

theorem chapter02_higher_coefficient_vanishing_invariant
    {G : Type u} [Group G] [Finite G]
    {F : Chapter02LowerFiltration G} {l : Type*} [Field l] (i : ℕ)
    (c c' : F.group i → l) (a : l) (ha : a ≠ 0)
    (hscale : ∀ σ, c' σ = a * c σ) :
    ∀ σ, c σ = 0 ↔ c' σ = 0 := by
  sorry

/-- The coefficient homomorphism before passing to the lower quotient. -/
def chapter02HigherCoefficientHom
    {G : Type u} [Group G] [Finite G]
    {F : Chapter02LowerFiltration G} {l : Type*} [Field l] (i : ℕ)
    (D : Chapter02HigherCoefficientData F l i) :
    F.group i →* Multiplicative l where
  toFun σ := Multiplicative.ofAdd (D.coefficient σ)
  map_one' := by
    sorry
  map_mul' σ τ := by
    change Multiplicative.ofAdd (D.coefficient (σ * τ)) =
      Multiplicative.ofAdd (D.coefficient σ) * Multiplicative.ofAdd (D.coefficient τ)
    simp [D.coefficient_mul]

/-- The higher coefficient map on `Gᵢ/Gᵢ₊₁`. -/
def chapter02HigherLayerCharacter
    {G : Type u} [Group G] [Finite G]
    {F : Chapter02LowerFiltration G} {l : Type*} [Field l] (i : ℕ)
    (D : Chapter02HigherCoefficientData F l i) :
    chapter02LowerLayer F i →* Multiplicative l := by
  letI : ((F.group (i + 1)).subgroupOf (F.group i)).Normal :=
    chapter02_lower_layer_normal F i
  exact QuotientGroup.lift
    ((F.group (i + 1)).subgroupOf (F.group i))
    (chapter02HigherCoefficientHom i D) (by
      intro σ hσ
      change D.coefficient σ = 0
      apply (D.coefficient_zero_iff σ).2
      exact hσ)

/-- The higher coefficient map, viewed as an additive map. -/
def chapter02HigherLayerAdditiveMap
    {G : Type u} [Group G] [Finite G]
    {F : Chapter02LowerFiltration G} {l : Type*} [Field l] (i : ℕ)
    (D : Chapter02HigherCoefficientData F l i) :
    Additive (chapter02LowerLayer F i) →+ l where
  toFun σ := Multiplicative.toAdd (chapter02HigherLayerCharacter i D σ)
  map_zero' := by
    sorry
  map_add' σ τ := by
    sorry

theorem chapter02_higher_layer_character_injective
    {G : Type u} [Group G] [Finite G]
    {F : Chapter02LowerFiltration G} {l : Type*} [Field l] (i : ℕ)
    (D : Chapter02HigherCoefficientData F l i) :
    Function.Injective (chapter02HigherLayerCharacter i D) := by
  intro σ τ hστ
  sorry

theorem chapter02_higher_layer_additive_map_injective
    {G : Type u} [Group G] [Finite G]
    {F : Chapter02LowerFiltration G} {l : Type*} [Field l] (i : ℕ)
    (D : Chapter02HigherCoefficientData F l i) :
    Function.Injective (chapter02HigherLayerAdditiveMap i D) := by
  sorry

/-- The image of a positive layer in the additive residue field. -/
def chapter02HigherLayerImage
    {G : Type u} [Group G] [Finite G]
    {F : Chapter02LowerFiltration G} {l : Type*} [Field l] (i : ℕ)
    (D : Chapter02HigherCoefficientData F l i) : AddSubgroup l :=
  (chapter02HigherLayerAdditiveMap i D).range

/-- A positive graded piece is elementary abelian when it embeds in `l⁺`. -/
def chapter02HigherLayerIsElementaryAbelian
    {G : Type u} [Group G] [Finite G]
    {F : Chapter02LowerFiltration G} {l : Type*} [Field l]
    (p i : ℕ) [CharP l p]
    (D : Chapter02HigherCoefficientData F l i) : Prop :=
  1 ≤ i ∧ IsPGroup p (chapter02LowerLayer F i) ∧
    Nonempty
      (Additive (chapter02LowerLayer F i) ≃+ chapter02HigherLayerImage i D)

/-- Every positive graded piece is an elementary abelian `p`-group. -/
theorem chapter02_higher_layer_is_elementary_abelian
    {G : Type u} [Group G] [Finite G]
    {F : Chapter02LowerFiltration G} {l : Type*} [Field l]
    (p i : ℕ) [Fact p.Prime] [CharP l p]
    (hi : 1 ≤ i) (D : Chapter02HigherCoefficientData F l i) :
    chapter02HigherLayerIsElementaryAbelian p i D := by
  sorry

/-- The intrinsic target for the coefficient map. -/
abbrev chapter02IntrinsicHigherTarget
    (l M N : Type*) [Field l]
    [AddCommGroup M] [AddCommGroup N]
    [Module l M] [Module l N] : Type _ :=
  M →ₗ[l] N

/-- If both graded modules are one-dimensional, their `l`-linear Hom-space is one-dimensional. -/
theorem chapter02_intrinsic_higher_target_finrank_one
    (l M N : Type*) [Field l]
    [AddCommGroup M] [AddCommGroup N]
    [Module l M] [Module l N]
    [FiniteDimensional l M] [FiniteDimensional l N]
    (hM : Module.finrank l M = 1) (hN : Module.finrank l N = 1) :
    Module.finrank l (chapter02IntrinsicHigherTarget l M N) = 1 := by
  sorry

/- The intrinsic target is only a one-dimensional residue-field Hom-space;
   this does not assert that every additive subspace occurs or that the
   successive extensions of the filtration split. -/

/- DEPENDENCY_GUESS: The residue-field linearization and the chosen
   uniformizer presentation from the preceding chapter are represented by the
   coefficient data below until those declarations are reconciled globally. -/
/-- The canonical higher coefficient package exists in the defectless,
separable-residue case. -/
theorem chapter02_canonical_higher_coefficient_data_exists
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
    [PerfectField (IsLocalRing.ResidueField vK.toValuation.valuationSubring)]
    [Algebra (IsLocalRing.ResidueField vK.toValuation.valuationSubring)
      (IsLocalRing.ResidueField vL.toValuation.valuationSubring)]
    [FiniteDimensional (IsLocalRing.ResidueField vK.toValuation.valuationSubring)
      (IsLocalRing.ResidueField vL.toValuation.valuationSubring)]
    (hseparable : Algebra.IsSeparable
      (IsLocalRing.ResidueField vK.toValuation.valuationSubring)
      (IsLocalRing.ResidueField vL.toValuation.valuationSubring))
    (i : ℕ) (hi : 1 ≤ i) :
    Nonempty
      (Chapter02HigherCoefficientData
        (chapter02CanonicalLowerFiltration K vL)
        (IsLocalRing.ResidueField vL.toValuation.valuationSubring) i) := by
  sorry

/- The canonical coefficient packages are the missing assembly step between
   the graded-piece calculation and the book's assertion about wild inertia.
   Keeping these consequences explicit prevents users from having to rebuild
   the infinite family of positive layers at every application. -/
/-- The canonical positive subgroup is a `p`-group in residue characteristic `p`. -/
theorem chapter02_canonical_wild_group_is_p_group
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
    [PerfectField (IsLocalRing.ResidueField vK.toValuation.valuationSubring)]
    [Algebra (IsLocalRing.ResidueField vK.toValuation.valuationSubring)
      (IsLocalRing.ResidueField vL.toValuation.valuationSubring)]
    [FiniteDimensional (IsLocalRing.ResidueField vK.toValuation.valuationSubring)
      (IsLocalRing.ResidueField vL.toValuation.valuationSubring)]
    (hseparable : Algebra.IsSeparable
      (IsLocalRing.ResidueField vK.toValuation.valuationSubring)
      (IsLocalRing.ResidueField vL.toValuation.valuationSubring))
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField vL.toValuation.valuationSubring) p] :
    IsPGroup p
      (chapter02WildGroup (chapter02CanonicalLowerFiltration K vL)) := by
  sorry

/-- In residue characteristic zero the canonical positive subgroup is trivial. -/
theorem chapter02_canonical_wild_group_eq_bot_of_char_zero
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
    [PerfectField (IsLocalRing.ResidueField vK.toValuation.valuationSubring)]
    [Algebra (IsLocalRing.ResidueField vK.toValuation.valuationSubring)
      (IsLocalRing.ResidueField vL.toValuation.valuationSubring)]
    [FiniteDimensional (IsLocalRing.ResidueField vK.toValuation.valuationSubring)
      (IsLocalRing.ResidueField vL.toValuation.valuationSubring)]
    (hseparable : Algebra.IsSeparable
      (IsLocalRing.ResidueField vK.toValuation.valuationSubring)
      (IsLocalRing.ResidueField vL.toValuation.valuationSubring))
    [CharZero (IsLocalRing.ResidueField vL.toValuation.valuationSubring)] :
    chapter02WildGroup (chapter02CanonicalLowerFiltration K vL) = ⊥ := by
  sorry

/-- Positive layers in characteristic zero are trivial. -/
theorem chapter02_higher_layer_subsingleton_of_char_zero
    {G : Type u} [Group G] [Finite G]
    {F : Chapter02LowerFiltration G} {l : Type*} [Field l] [CharZero l]
    (i : ℕ) (hi : 1 ≤ i)
    (D : Chapter02HigherCoefficientData F l i) :
    Subsingleton (chapter02LowerLayer F i) := by
  sorry

/-- The characteristic-zero positive subgroup is trivial. -/
theorem chapter02_char_zero_positive_group_eq_bot
    {G : Type u} [Group G] [Finite G]
    {F : Chapter02LowerFiltration G} {l : Type*} [Field l] [CharZero l]
    (hdata : ∀ i : ℕ, 1 ≤ i →
      Nonempty (Chapter02HigherCoefficientData F l i)) :
    chapter02WildGroup F = ⊥ := by
  apply chapter02_wild_group_eq_bot_of_trivial_positive_layers F
  intro i hi
  exact chapter02_higher_layer_subsingleton_of_char_zero i hi
    (hdata i hi).some

end

end LastLib.Book03RamificationTheory.Chapter02
