import LastLib.Book03RamificationTheory.Chapter02.Section03TheTameCharacter
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter05.Section01SuccessivePrecision
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
  /-- Higher coefficient data is only defined on a positive lower layer. -/
  positive : 1 ≤ i
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
  intro σ
  rw [hscale σ]
  constructor
  · intro h
    simp [h]
  · intro h
    exact (mul_eq_zero.mp h).resolve_left ha

/-- The coefficient homomorphism before passing to the lower quotient. -/
def chapter02HigherCoefficientHom
    {G : Type u} [Group G] [Finite G]
    {F : Chapter02LowerFiltration G} {l : Type*} [Field l] (i : ℕ)
    (D : Chapter02HigherCoefficientData F l i) :
    F.group i →* Multiplicative l where
  toFun σ := Multiplicative.ofAdd (D.coefficient σ)
  map_one' := by
    have hzero : D.coefficient (1 : F.group i) = 0 :=
      (D.coefficient_zero_iff (1 : F.group i)).2
        (F.group (i + 1)).one_mem
    simp [hzero]
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
    change Multiplicative.toAdd (chapter02HigherLayerCharacter i D 1) = 0
    simp
  map_add' σ τ := by
    change chapter02LowerLayer F i at σ τ
    change Multiplicative.toAdd
        (chapter02HigherLayerCharacter i D (σ * τ)) =
      Multiplicative.toAdd (chapter02HigherLayerCharacter i D σ) +
        Multiplicative.toAdd (chapter02HigherLayerCharacter i D τ)
    rw [map_mul]
    rfl

theorem chapter02_higher_layer_character_injective
    {G : Type u} [Group G] [Finite G]
    {F : Chapter02LowerFiltration G} {l : Type*} [Field l] (i : ℕ)
    (D : Chapter02HigherCoefficientData F l i) :
    Function.Injective (chapter02HigherLayerCharacter i D) := by
  let N := (F.group (i + 1)).subgroupOf (F.group i)
  let : N.Normal := chapter02_lower_layer_normal F i
  let f := chapter02HigherCoefficientHom i D
  have hN : N ≤ f.ker := by
    intro σ hσ
    change Multiplicative.ofAdd (D.coefficient σ) = 1
    have hzero : D.coefficient σ = 0 :=
      (D.coefficient_zero_iff σ).2 hσ
    simp [hzero]
  have hker : N = f.ker := by
    ext σ
    constructor
    · intro hσ
      exact hN hσ
    · intro hσ
      change Multiplicative.ofAdd (D.coefficient σ) = 1 at hσ
      have hzero : D.coefficient σ = 0 := by simpa using hσ
      exact (D.coefficient_zero_iff σ).1 hzero
  change Function.Injective (QuotientGroup.lift N f hN)
  exact (QuotientGroup.injective_lift_iff N f hN).2 hker

theorem chapter02_higher_layer_additive_map_injective
    {G : Type u} [Group G] [Finite G]
    {F : Chapter02LowerFiltration G} {l : Type*} [Field l] (i : ℕ)
    (D : Chapter02HigherCoefficientData F l i) :
    Function.Injective (chapter02HigherLayerAdditiveMap i D) := by
  intro σ τ hστ
  change chapter02LowerLayer F i at σ τ
  change Multiplicative.toAdd (chapter02HigherLayerCharacter i D σ) =
      Multiplicative.toAdd (chapter02HigherLayerCharacter i D τ) at hστ
  apply chapter02_higher_layer_character_injective i D
  exact Multiplicative.toAdd.injective hστ

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
  have hcharall : ∀ x : Multiplicative l, x ^ p = 1 := by
    intro x
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow]
    change p • (x.toAdd : l) = 0
    rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  have hP : IsPGroup p (chapter02LowerLayer F i) := by
    intro σ
    refine ⟨1, ?_⟩
    simp only [pow_one]
    apply chapter02_higher_layer_character_injective i D
    rw [map_pow, map_one]
    exact hcharall _
  refine ⟨hi, hP, ?_⟩
  exact ⟨AddMonoidHom.ofInjective
    (chapter02_higher_layer_additive_map_injective i D)⟩

/-- Positive layers in characteristic zero are trivial. -/
theorem chapter02_higher_layer_subsingleton_of_char_zero
    {G : Type u} [Group G] [Finite G]
    {F : Chapter02LowerFiltration G} {l : Type*} [Field l] [CharZero l]
    (i : ℕ) (_hi : 1 ≤ i)
    (D : Chapter02HigherCoefficientData F l i) :
    Subsingleton (chapter02LowerLayer F i) := by
  let f := chapter02HigherLayerAdditiveMap i D
  let : Finite (chapter02LowerLayer F i) := by
    change Finite (F.group i ⧸ (F.group (i + 1)).subgroupOf (F.group i))
    infer_instance
  let : Finite (Additive (chapter02LowerLayer F i)) := by
    exact Finite.of_injective
      (fun σ : Additive (chapter02LowerLayer F i) => (σ : chapter02LowerLayer F i))
      (fun _ _ h => h)
  let : Finite (chapter02HigherLayerImage i D) := by
    exact Finite.of_surjective f.rangeRestrict
      (AddMonoidHom.rangeRestrict_surjective f)
  have hzero (x : chapter02HigherLayerImage i D) : x = 0 := by
    obtain ⟨n, hn, hnx⟩ := (isAddTorsion_of_finite x).exists_nsmul_eq_zero
    apply Subtype.ext
    have hnx' := congrArg
      (fun y : chapter02HigherLayerImage i D => (y : l)) hnx
    change n • (x : l) = 0 at hnx'
    rw [nsmul_eq_mul] at hnx'
    exact (mul_eq_zero.mp hnx').resolve_left (Nat.cast_ne_zero.mpr hn.ne')
  constructor
  intro σ τ
  have hσ := hzero (f.rangeRestrict σ)
  have hτ := hzero (f.rangeRestrict τ)
  apply chapter02_higher_layer_additive_map_injective i D
  exact Subtype.ext_iff.mp (hσ.trans hτ.symm)

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
  rw [Module.finrank_linearMap, hM, hN]

/- The intrinsic target is only a one-dimensional residue-field Hom-space;
   this does not assert that every additive subspace occurs or that the
   successive extensions of the filtration split. -/

private theorem chapter02_canonical_action_deepens
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (vL : AddValuation L (WithTop ℤ))
    [Valuation.IsRankOneDiscrete vL.toValuation]
    [Finite (chapter02DecompositionGroup K vL)]
    (hnormalized : Function.Surjective vL)
    (m : ℕ) (g : chapter02DecompositionGroup K vL)
    (hg : g ∈ (chapter02CanonicalLowerFiltration K vL hnormalized).group m) :
    ∀ r : ℕ, ∀ x : vL.toValuation.valuationSubring,
      x ∈ (IsLocalRing.maximalIdeal vL.toValuation.valuationSubring) ^ r →
        g • x - x ∈
          (IsLocalRing.maximalIdeal vL.toValuation.valuationSubring) ^ (m + r) := by
  let A := vL.toValuation.valuationSubring
  let I : Ideal A := IsLocalRing.maximalIdeal A
  have hcong (r : ℕ) (g : chapter02DecompositionGroup K vL)
      (hg : g ∈ (chapter02CanonicalLowerFiltration K vL hnormalized).group r)
      (x : A) : g • x - x ∈ I ^ (r + 1) := by
    change LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05HigherCongruence
      A (r + 1) g at hg
    exact hg x
  have hpres (g : chapter02DecompositionGroup K vL) (r : ℕ) (x : A)
      (hx : x ∈ I ^ r) : g • x ∈ I ^ r := by
    exact
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.decomposition_group_preserves_maximal_ideal_powers
        A g r x).mp hx
  intro r
  induction r with
  | zero =>
      intro x hx
      have hx' := hcong m g hg x
      simpa using Ideal.pow_le_pow_right (Nat.le_succ m) hx'
  | succ r ih =>
      intro x hx
      rw [I.pow_succ] at hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro a ha b hb
        have hga : g • a ∈ I ^ r := by
          exact hpres g r a ha
        have hterm1 :
            g • a * (g • b - b) ∈ I ^ (m + (r + 1)) := by
          rw [show m + (r + 1) = r + (m + 1) by omega,
            Ideal.IsTwoSided.pow_add r (m + 1)]
          exact Ideal.mul_mem_mul hga (hcong m g hg b)
        have hterm2 :
            b * (g • a - a) ∈ I ^ (m + (r + 1)) := by
          rw [show m + (r + 1) = (m + r) + 1 by omega, I.pow_succ]
          exact Ideal.mul_mem_mul_rev (ih a ha) hb
        have heq : g • (a * b) - (a * b) =
            g • a * (g • b - b) + b * (g • a - a) := by
          simp [smul_mul']
          ring
        rw [heq]
        exact (I ^ (m + (r + 1))).add_mem hterm1 hterm2
      · intro x y hx hy
        have heq : g • (x + y) - (x + y) =
            (g • x - x) + (g • y - y) := by
          simp [smul_add]
          ring
        rw [heq]
        exact (I ^ (m + (r + 1))).add_mem hx hy

/-- A clean valuation presentation supplies the higher coefficient package.

    The two displayed zero criteria are kept in the constructor interface:
    one is tested on the chosen uniformizer and the other on every integral
    element.  The latter is what identifies the coefficient kernel with the
    next lower group.  The additive composition law is included explicitly
    as well, although it is also a field of `D`, so later layer arguments can
    consume the resulting `Chapter02HigherCoefficientData` directly. -/
theorem chapter02_higher_coefficient_data_of_canonical_presentation
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
      (IsLocalRing.ResidueField vL.toValuation.valuationSubring))
    (i : ℕ) (hi : 1 ≤ i) :
    ∃ D : Chapter02HigherCoefficientData
        (chapter02CanonicalLowerFiltration K vL hnormalized)
        (IsLocalRing.ResidueField vL.toValuation.valuationSubring) i,
      (∀ σ,
        D.coefficient σ = 0 ↔
          ((σ : chapter02DecompositionGroup K vL) • π - π) ∈
            (IsLocalRing.maximalIdeal vL.toValuation.valuationSubring) ^ (i + 2)) ∧
      (∀ σ,
        D.coefficient σ = 0 ↔
          ∀ x : vL.toValuation.valuationSubring,
            ((σ : chapter02DecompositionGroup K vL) • x - x) ∈
              (IsLocalRing.maximalIdeal vL.toValuation.valuationSubring) ^ (i + 2)) ∧
      (∀ σ τ,
        D.coefficient (σ * τ) = D.coefficient σ + D.coefficient τ) := by
  have _ := hcomplete
  have _ := hseparable
  let A := vL.toValuation.valuationSubring
  let D := chapter02DecompositionGroup K vL
  let F := chapter02CanonicalLowerFiltration K vL hnormalized
  let I : Ideal A := IsLocalRing.maximalIdeal A
  let n := i + 1
  have hπ : vL.toValuation.IsUniformizer π := by
    exact Valuation.isUniformizer_of_maximalIdeal_eq_span vL.toValuation
      hpresentation.uniformizer
  have hπirr : Irreducible (π : A) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer (R := A) π).2
      hpresentation.uniformizer
  let layerRep (σ : F.group i) :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter05.chapterGradedPiece A n :=
    Submodule.Quotient.mk
      (p := LastLib.Book01ValuationsDVRsAndCompletions.Chapter05.chapterGradedPieceDenominator
        A n)
      ⟨(σ : D) • π - π, by
        change ((σ : D) • π - π) ∈ I ^ n
        have hσ := σ.property
        change LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05HigherCongruence
          A (i + 1) (σ : D) at hσ
        exact hσ π⟩
  have hbij : Function.Bijective
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter05.chapterLayerResidueLinearMap
        (A := A) π hπirr n) := by
    change Function.Bijective
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter05.chapterLayerMultiplicationMap
        (A := A) π hπirr n)
    exact
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter05.chapterLayerMultiplicationMap_bijective
        (A := A) π hπirr n
  let layerEquiv := LinearEquiv.ofBijective
    (LastLib.Book01ValuationsDVRsAndCompletions.Chapter05.chapterLayerResidueLinearMap
      (A := A) π hπirr n) hbij
  let coefficient (σ : F.group i) :
      IsLocalRing.ResidueField A := layerEquiv.symm (layerRep σ)
  have hlayerRep_zero (σ : F.group i) :
      layerRep σ = 0 ↔ ((σ : D) • π - π) ∈ I ^ (n + 1) := by
    dsimp [layerRep]
    rw [Submodule.Quotient.mk_eq_zero]
    rfl
  have hcoeffzero_layer (σ : F.group i) :
      coefficient σ = 0 ↔ layerRep σ = 0 := by
    constructor
    · intro h
      have h' := congrArg layerEquiv h
      simpa [coefficient] using h'
    · intro h
      simp [coefficient, h]
  have hgroup0' : ∀ j : ℕ, F.group j ≤ F.group 0 := by
    intro j
    induction j with
    | zero => exact le_rfl
    | succ j ih => exact (F.descending j).trans ih
  have hgroup0 : F.group i ≤ F.group 0 := hgroup0' i
  have hσI (σ : F.group i) :
      (σ : D) ∈
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05InertiaGroup
          K A := by
    rw [← chapter02_lower_group_zero_eq_inertia K vL]
    exact hgroup0 σ.property
  have hpi_all (σ : F.group i) :
      ((σ : D) • π - π) ∈ I ^ (i + 2) ↔
        ∀ x : A, ((σ : D) • x - x) ∈ I ^ (i + 2) := by
    constructor
    · intro hπdiff
      have hcoeff (c : C) :
          ((σ : D) • algebraMap C A c - algebraMap C A c) ∈ I ^ (i + 2) := by
        have hfix := hpresentation.inertia_fixes_coefficients
          ⟨(σ : D), hσI σ⟩ c
        have hzero :
            (σ : D) • algebraMap C A c - algebraMap C A c = 0 := by
          change (⟨(σ : D), hσI σ⟩ :
            LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05InertiaGroup
              K A) • algebraMap C A c - algebraMap C A c = 0
          rw [hfix, sub_self]
        rw [hzero]
        exact (I ^ (i + 2)).zero_mem
      have hx : ∀ x : A, x ∈ Algebra.adjoin C ({π} : Set A) →
          ((σ : D) • x - x) ∈ I ^ (i + 2) := by
        intro x hx
        refine Algebra.adjoin_induction (s := ({π} : Set A))
          (p := fun y _ => ((σ : D) • y - y) ∈ I ^ (i + 2)) ?_ ?_ ?_ ?_ hx
        · intro y hy
          have hy' : y = π := by simpa using hy
          subst y
          exact hπdiff
        · intro c
          exact hcoeff c
        · intro y z hy hz hy' hz'
          have heq : (σ : D) • (y + z) - (y + z) =
              ((σ : D) • y - y) + ((σ : D) • z - z) := by
            rw [smul_add]
            ring
          rw [heq]
          exact (I ^ (i + 2)).add_mem hy' hz'
        · intro y z hy hz hy' hz'
          have heq : (σ : D) • (y * z) - (y * z) =
              y * ((σ : D) • z - z) +
                ((σ : D) • y - y) * ((σ : D) • z) := by
            simp [smul_mul']
            ring
          rw [heq]
          exact (I ^ (i + 2)).add_mem
            ((I ^ (i + 2)).mul_mem_left y hz')
            ((I ^ (i + 2)).mul_mem_right ((σ : D) • z) hy')
      intro x
      apply hx x
      rw [hpresentation.integral_generation]
      trivial
    · intro hall
      exact hall π
  have hcoeffzero_pi (σ : F.group i) :
      coefficient σ = 0 ↔ ((σ : D) • π - π) ∈ I ^ (i + 2) := by
    exact (hcoeffzero_layer σ).trans (by simpa [n] using hlayerRep_zero σ)
  have hnext (σ : F.group i) :
      coefficient σ = 0 ↔ (σ : D) ∈ F.group (i + 1) := by
    constructor
    · intro h
      have hπdiff := (hcoeffzero_pi σ).1 h
      have hall := (hpi_all σ).mp hπdiff
      change LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05HigherCongruence
        A (i + 2) (σ : D)
      exact hall
    · intro h
      apply (hcoeffzero_pi σ).2
      apply (hpi_all σ).2
      have h' := h
      change LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05HigherCongruence
        A (i + 2) (σ : D) at h'
      exact h'
  have hrep_add (σ τ : F.group i) :
      layerRep (σ * τ) = layerRep σ + layerRep τ := by
    have hτmem : ((τ : D) • π - π) ∈ I ^ n := by
      have hτ := τ.property
      change LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05HigherCongruence
        A (i + 1) (τ : D) at hτ
      exact hτ π
    have hdeep :
        (σ : D) • ((τ : D) • π - π) - ((τ : D) • π - π) ∈
          I ^ (i + n) := by
      exact chapter02_canonical_action_deepens K L vL hnormalized i
        (σ : D) σ.property n ((τ : D) • π - π) hτmem
    have hdeep' :
        (σ : D) • ((τ : D) • π - π) - ((τ : D) • π - π) ∈ I ^ (n + 1) := by
      exact (Ideal.pow_le_pow_right (by omega)) hdeep
    apply (Submodule.Quotient.eq
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter05.chapterGradedPieceDenominator
        A n)).2
    change ((↑(σ * τ) : D) • π - π) -
        (((σ : D) • π - π) + ((τ : D) • π - π)) ∈ I ^ (n + 1)
    have hdelta_mul :
        ((↑(σ * τ) : D) • π - π) =
          (σ : D) • ((τ : D) • π - π) + ((σ : D) • π - π) := by
      change ((σ : D) * (τ : D)) • π - π = _
      rw [mul_smul, smul_sub]
      ring
    rw [hdelta_mul]
    have heq :
        (σ : D) • ((τ : D) • π - π) - ((τ : D) • π - π) =
          ((σ : D) • ((τ : D) • π - π) + ((σ : D) • π - π)) -
            (((σ : D) • π - π) + ((τ : D) • π - π)) := by
      ring
    rw [← heq]
    exact hdeep'
  have hcoeff_add (σ τ : F.group i) :
      coefficient (σ * τ) = coefficient σ + coefficient τ := by
    have h := congrArg layerEquiv.symm (hrep_add σ τ)
    simpa [coefficient] using h
  let data : Chapter02HigherCoefficientData F (IsLocalRing.ResidueField A) i :=
    { positive := hi
      coefficient := coefficient
      coefficient_zero_iff := by
        intro σ
        exact hnext σ
      coefficient_mul := by
        intro σ τ
        exact hcoeff_add σ τ }
  refine ⟨data, ?_, ?_, ?_⟩
  · intro σ
    change coefficient σ = 0 ↔ ((σ : D) • π - π) ∈ I ^ (i + 2)
    exact hcoeffzero_pi σ
  · intro σ
    change coefficient σ = 0 ↔
      ∀ x : A, ((σ : D) • x - x) ∈ I ^ (i + 2)
    exact (hcoeffzero_pi σ).trans (hpi_all σ)
  · intro σ τ
    change coefficient (σ * τ) = coefficient σ + coefficient τ
    exact hcoeff_add σ τ

/-- The canonical higher coefficient package exists in the clean,
    separable-residue presentation. -/
theorem chapter02_canonical_higher_coefficient_data_exists
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
      (IsLocalRing.ResidueField vL.toValuation.valuationSubring))
    (i : ℕ) (hi : 1 ≤ i) :
    Nonempty
      (Chapter02HigherCoefficientData
        (chapter02CanonicalLowerFiltration K vL hnormalized)
        (IsLocalRing.ResidueField vL.toValuation.valuationSubring) i) := by
  obtain ⟨D, _, _, _⟩ :=
    chapter02_higher_coefficient_data_of_canonical_presentation
      K L vK vL hnormalized hcomplete C π hpresentation hseparable i hi
  exact ⟨D⟩

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
      (IsLocalRing.ResidueField vL.toValuation.valuationSubring))
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField vL.toValuation.valuationSubring) p] :
    IsPGroup p
      (chapter02WildGroup (chapter02CanonicalLowerFiltration K vL hnormalized)) := by
  apply chapter02_wild_group_is_p_group
  intro i hi
  obtain ⟨D⟩ :=
    chapter02_canonical_higher_coefficient_data_exists
      K L vK vL hnormalized hcomplete C π hpresentation hseparable i hi
  exact (chapter02_higher_layer_is_elementary_abelian p i hi D).2.1

/-- In residue characteristic zero the canonical positive subgroup is trivial. -/
theorem chapter02_canonical_wild_group_eq_bot_of_char_zero
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
      (IsLocalRing.ResidueField vL.toValuation.valuationSubring))
    [CharZero (IsLocalRing.ResidueField vL.toValuation.valuationSubring)] :
    chapter02WildGroup (chapter02CanonicalLowerFiltration K vL hnormalized) = ⊥ := by
  apply chapter02_wild_group_eq_bot_of_trivial_positive_layers
  intro i hi
  obtain ⟨D⟩ :=
    chapter02_canonical_higher_coefficient_data_exists
      K L vK vL hnormalized hcomplete C π hpresentation hseparable i hi
  exact chapter02_higher_layer_subsingleton_of_char_zero i hi D

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
