import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter05.Section03MorphismsAndExactSequences

/-!
# 5.4 Base change and transitivity

The base-change layer makes the changed cover and its canonical right-algebra structure explicit.
The transitivity layer records the two-stage comparison data for a faithfully flat tower.
-/

open CategoryTheory
open TensorProduct
open scoped TensorProduct

universe u

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter05

noncomputable section

section BaseChange

variable {A B A' : Type u} [CommRing A] [CommRing B] [CommRing A']
  [Algebra A B] [Algebra A A']

abbrev baseChangedRing : Type u := B ⊗[A] A'

/-- The canonical `A'`-algebra structure on `B ⊗[A] A'`, using the right factor. -/
noncomputable abbrev baseChangeAlgebra : Algebra A' (baseChangedRing (A := A) (B := B) (A' := A') ) :=
  Algebra.TensorProduct.rightAlgebra

@[simp]
theorem baseChangeAlgebra_map_apply (a' : A') :
    letI : Algebra A' (baseChangedRing (A := A) (B := B) (A' := A')) := baseChangeAlgebra
    algebraMap A' (baseChangedRing (A := A) (B := B) (A' := A')) a' = 1 ⊗ₜ[A] a' := by
  rfl

/-- The scalar extension of a descended `A`-module to the new base `A'`. -/
noncomputable def baseChangedModule (M : ModuleCat A) : ModuleCat A' :=
  (ModuleCat.extendScalars (algebraMap A A')).obj M

noncomputable def baseChangedInvariantModule (D : DescentDatum A B) : ModuleCat A' :=
  baseChangedModule (invariantModuleCat D)

/-- Base change once more along the new faithfully flat cover
`A' → B ⊗[A] A'`. -/
noncomputable def baseChangedCoverModule (M : ModuleCat A') :
    ModuleCat (baseChangedRing (A := A) (B := B) (A' := A')) := by
  letI : Algebra A' (baseChangedRing (A := A) (B := B) (A' := A')) := baseChangeAlgebra
  exact
    (ModuleCat.extendScalars
      (algebraMap A' (baseChangedRing (A := A) (B := B) (A' := A')))).obj M

/-- The type of descent data for the base-changed cover.  The right-algebra instance is local in
Mathlib, so it is installed in the dependent result type. -/
noncomputable abbrev BaseChangedDescentDatum : Type _ :=
  letI : Algebra A' (baseChangedRing (A := A) (B := B) (A' := A')) :=
    baseChangeAlgebra
  DescentDatum A' (baseChangedRing (A := A) (B := B) (A' := A'))

/-- Pull a datum along `A' → B ⊗[A] A'`, with the two structural maps of the base-changed
Čech nerve.  The canonical datum on the scalar extension of the invariant module is exposed
separately below. -/
noncomputable def pulledDescentDatum (D : DescentDatum A B) :
    BaseChangedDescentDatum (A := A) (B := B) (A' := A') := by
  sorry

/-- The canonical datum on the scalar extension of the descended module. -/
noncomputable def canonicalBaseChangedDescentDatum (D : DescentDatum A B) :
    BaseChangedDescentDatum (A := A) (B := B) (A' := A') := by
  letI : Algebra A' (baseChangedRing (A := A) (B := B) (A' := A')) := baseChangeAlgebra
  exact
    (descentComparison A' (baseChangedRing (A := A) (B := B) (A' := A'))).obj
      (baseChangedModule (invariantModuleCat D))

theorem pulledDescentDatum_is_canonically_effective
    [Module.FaithfullyFlat A B] (D : DescentDatum A B) :
    Nonempty
      (pulledDescentDatum (A := A) (B := B) (A' := A') D ≅
        canonicalBaseChangedDescentDatum (A := A) (B := B) (A' := A') D) := by
  sorry

theorem baseChange_of_invariant_module
    [Module.FaithfullyFlat A B] (D : DescentDatum A B) :
    Nonempty
      (baseChangedInvariantModule (A := A) (B := B) (A' := A') D ≅
        letI : Algebra A' (baseChangedRing (A := A) (B := B) (A' := A')) := baseChangeAlgebra
        invariantModuleCat (pulledDescentDatum (A := A) (B := B) (A' := A') D)) := by
  sorry

theorem flat_base_change_preserves_invariant_equalizer_after_base_change
    [Module.FaithfullyFlat A B] [Module.Flat A A'] (D : DescentDatum A B) :
    Nonempty
      (baseChangedInvariantModule (A := A) (B := B) (A' := A') D ≅
        letI : Algebra A' (baseChangedRing (A := A) (B := B) (A' := A')) := baseChangeAlgebra
        invariantModuleCat (pulledDescentDatum (A := A) (B := B) (A' := A') D)) := by
  exact baseChange_of_invariant_module D

theorem uniqueness_after_faithfullyFlat_baseChange [Module.FaithfullyFlat A A']
    {M N : ModuleCat A}
    (e : (descentComparison A A').obj M ≅ (descentComparison A A').obj N) :
    Nonempty (M ≅ N) := by
  let hEq : (descentComparison A A').IsEquivalence :=
    faithfullyFlat_module_descent_of_instance (A := A) (B := A')
  let hFF : (descentComparison A A').FullyFaithful :=
    { preimage := fun f => (hEq.full.map_surjective f).choose
      map_preimage := fun f => (hEq.full.map_surjective f).choose_spec
      preimage_map := fun f =>
        hEq.faithful.map_injective ((hEq.full.map_surjective
          ((descentComparison A A').map f)).choose_spec) }
  exact ⟨hFF.preimageIso e⟩

theorem uniqueness_after_faithfullyFlat_cover_baseChange [Module.FaithfullyFlat A B]
    {M N : ModuleCat A'}
    (e :
      letI : Algebra A' (baseChangedRing (A := A) (B := B) (A' := A')) := baseChangeAlgebra
      (descentComparison A' (baseChangedRing (A := A) (B := B) (A' := A'))).obj M ≅
        (descentComparison A' (baseChangedRing (A := A) (B := B) (A' := A'))).obj N) :
    Nonempty (M ≅ N) := by
  let _ : Algebra A' (baseChangedRing (A := A) (B := B) (A' := A')) := baseChangeAlgebra
  have hff : RingHom.FaithfullyFlat
      (algebraMap A' (baseChangedRing (A := A) (B := B) (A' := A'))) := by
    have hAB : RingHom.FaithfullyFlat (algebraMap A B) :=
      RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
    apply RingHom.FaithfullyFlat.isStableUnderBaseChange
      (R := A) (S := B) (R' := A')
      (S' := baseChangedRing (A := A) (B := B) (A' := A'))
    exact hAB
  let hEq : (descentComparison A'
      (baseChangedRing (A := A) (B := B) (A' := A'))).IsEquivalence :=
    faithfullyFlat_module_descent hff
  let hFF : (descentComparison A'
      (baseChangedRing (A := A) (B := B) (A' := A'))).FullyFaithful :=
    { preimage := fun f => (hEq.full.map_surjective f).choose
      map_preimage := fun f => (hEq.full.map_surjective f).choose_spec
      preimage_map := fun f =>
        hEq.faithful.map_injective ((hEq.full.map_surjective
          ((descentComparison A'
            (baseChangedRing (A := A) (B := B) (A' := A'))).map f)).choose_spec) }
  exact ⟨hFF.preimageIso e⟩

end BaseChange

section Transitivity

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C]

/-- The hypothesis that both stages of a faithfully flat scalar tower are faithfully flat. -/
def TowerFaithfullyFlat [_tower : IsScalarTower A B C] : Prop :=
  RingHom.FaithfullyFlat (algebraMap A B) ∧
    RingHom.FaithfullyFlat (algebraMap B C)

theorem tower_composite_faithfullyFlat [tower : IsScalarTower A B C]
    (h : TowerFaithfullyFlat (A := A) (B := B) (C := C)) :
    RingHom.FaithfullyFlat (algebraMap A C) := by
  rw [IsScalarTower.algebraMap_eq A B C]
  exact RingHom.FaithfullyFlat.stableUnderComposition (algebraMap A B) (algebraMap B C) h.1 h.2

/-- Restriction of a `C`-module descent datum from the `A`-nerve to the intermediate `B`-nerve.

This is pullback along the canonical map from the `A`-overlap to the `B`-overlap, so it only
requires the scalar tower. Faithful flatness is needed later for effectivity, not for restriction. -/
noncomputable def restrictDescentDatumToIntermediate
    [tower : IsScalarTower A B C]
    (D : DescentDatum.{u, u} A C) :
    DescentDatum.{u, u} B C := by
  sorry

theorem remaining_compatibility_descends_by_fullFaithfulness
    [tower : IsScalarTower A B C]
    (h : TowerFaithfullyFlat (A := A) (B := B) (C := C))
    (D : DescentDatum.{u, u} A C) (N : ModuleCat.{u, u} B)
    (E : DescentDatum.{u, u} B C)
    (hE : Nonempty (E ≅ restrictDescentDatumToIntermediate D))
    (hN : Nonempty (((descentComparison B C).obj N) ≅ E)) :
    ∃ (M : ModuleCat.{u, u} A) (F : DescentDatum.{u, u} A B),
      Nonempty (((descentComparison A B).obj M) ≅ F) ∧
        Nonempty (((descentComparison A C).obj M) ≅ D) ∧
        Nonempty (F.A ≅ N) ∧
        Nonempty (((descentComparison B C).obj F.A) ≅ E) := by
  sorry

end Transitivity

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter05
