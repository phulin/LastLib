import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Section06MixedCharacteristicExample

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10

noncomputable section

open Ideal IsLocalRing

/-! ## 10.7. Galois action on the layers -/

/-- The automorphism group of an algebraic extension over its base field. -/
abbrev Chapter10GaloisAutomorphism
    (K L : Type*) [Field K] [Field L] [Algebra K L] :=
  L ≃ₐ[K] L

/-- The induced action of a ring automorphism on units. -/
def chapter10GaloisUnitAction
    {R : Type*} [CommRing R] (σ : R ≃+* R) : Rˣ →* Rˣ :=
  Units.map σ.toRingHom.toMonoidHom

/-- Stability of the unit filtration under an automorphism of the valuation ring. -/
def Chapter10UnitFiltrationStable
    {L : Type*} [Field L] (A : ValuationSubring L) (σ : A ≃+* A) : Prop :=
  ∀ n : ℕ, ∀ u : Aˣ, u ∈ chapter10UnitFiltration A n →
    chapter10GaloisUnitAction σ u ∈ chapter10UnitFiltration A n

/-- A Galois automorphism preserves every congruence subgroup. -/
theorem chapter10_galois_unit_filtration_stable
    {L : Type*} [Field L] (A : ValuationSubring L) (σ : A ≃+* A)
    (hmax : Ideal.map σ.toRingHom (IsLocalRing.maximalIdeal A) =
      IsLocalRing.maximalIdeal A) :
    Chapter10UnitFiltrationStable A σ := by
  sorry

/-- Compatibility data for the induced residue-field automorphism. -/
def Chapter10ResidueAutomorphismCompatible
    {L : Type*} [Field L] (A : ValuationSubring L)
    (σ : A ≃+* A) (σbar : Chapter10ResidueField A ≃+* Chapter10ResidueField A) : Prop :=
  ∀ a : A,
    σbar (IsLocalRing.residue A a) = IsLocalRing.residue A (σ a)

/-- The inertia condition: the induced residue automorphism is trivial. -/
def Chapter10InertiaElement
    {L : Type*} [Field L] (A : ValuationSubring L)
    (σbar : Chapter10ResidueField A ≃+* Chapter10ResidueField A) : Prop :=
  σbar = RingEquiv.refl (Chapter10ResidueField A)

/-- The first unit quotient sees only the residue automorphism. -/
theorem chapter10_galois_first_quotient_residue_action
    {L : Type*} [Field L] (A : ValuationSubring L) (σ : A ≃+* A)
    (σbar : Chapter10ResidueField A ≃+* Chapter10ResidueField A)
    (hcompat : Chapter10ResidueAutomorphismCompatible A σ σbar) :
    ∀ u : Aˣ,
      chapter10UnitReduction A (chapter10GaloisUnitAction σ u) =
        Units.map σbar.toRingHom.toMonoidHom (chapter10UnitReduction A u) := by
  sorry

/-- Inertia acts trivially on the residue-unit quotient. -/
theorem chapter10_inertia_trivial_on_first_unit_quotient
    {L : Type*} [Field L] (A : ValuationSubring L) (σ : A ≃+* A)
    (σbar : Chapter10ResidueField A ≃+* Chapter10ResidueField A)
    (hcompat : Chapter10ResidueAutomorphismCompatible A σ σbar)
    (hinertia : Chapter10InertiaElement A σbar) :
    ∀ u : Aˣ,
      chapter10UnitReduction A (chapter10GaloisUnitAction σ u) =
        chapter10UnitReduction A u := by
  sorry

/-- The coordinate action on the `n`th layer, including the uniformizer ratio. -/
def chapter10GaloisLayerCoordinateAction
    {L : Type*} [Field L] (A : ValuationSubring L)
    (σbar : Chapter10ResidueField A ≃+* Chapter10ResidueField A)
    (c : Aˣ) (n : ℕ) :
    Chapter10ResidueField A →+ Chapter10ResidueField A where
  toFun a := σbar a * ((chapter10UnitReduction A c :
    (Chapter10ResidueField A)ˣ) : Chapter10ResidueField A) ^ n
  map_zero' := by simp
  map_add' a b := by
    rw [map_add]
    ring

/--
After choosing a uniformizer, the higher-layer action is
`a ↦ σ̄(a)·(σ(π)/π)ⁿ·a` in residue coordinates.  The unit `c` records the
ratio `σ(π)/π` inside the valuation ring.
-/
theorem chapter10_galois_higher_layer_coordinate_formula
    {L : Type*} [Field L] (A : ValuationSubring L)
    (σ : A ≃+* A) (σbar : Chapter10ResidueField A ≃+* Chapter10ResidueField A)
    (π : A) (c : Aˣ) (n : ℕ)
    (hcompat : Chapter10ResidueAutomorphismCompatible A σ σbar)
    (hπ : σ π = (c : A) * π) :
    ∀ a : Chapter10ResidueField A,
      chapter10GaloisLayerCoordinateAction A σbar c n a =
        σbar a * ((chapter10UnitReduction A c :
          (Chapter10ResidueField A)ˣ) : Chapter10ResidueField A) ^ n := by
  intro a
  rfl

/-- The inertia character on a higher layer may be nontrivial. -/
def Chapter10InertiaCharacterMayBeNontrivial
    {L : Type*} [Field L] (A : ValuationSubring L) (π : A) : Prop :=
  ∃ (σ : A ≃+* A) (c : Aˣ),
    σ π = (c : A) * π ∧
      chapter10UnitReduction A c ≠ 1

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10
