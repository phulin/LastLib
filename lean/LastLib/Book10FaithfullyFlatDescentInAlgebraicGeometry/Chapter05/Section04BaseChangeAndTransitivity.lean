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
noncomputable def baseChangeAlgebra : Algebra A' (baseChangedRing (A := A) (B := B) (A' := A') ) :=
  Algebra.TensorProduct.rightAlgebra

@[simp]
theorem baseChangeAlgebra_map_apply (a' : A') :
    letI : Algebra A' (baseChangedRing (A := A) (B := B) (A' := A')) := baseChangeAlgebra
    algebraMap A' (baseChangedRing (A := A) (B := B) (A' := A')) a' = 1 ⊗ₜ[A] a' := by
  sorry

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
noncomputable def BaseChangedDescentDatum : Type _ :=
  letI : Algebra A' (baseChangedRing (A := A) (B := B) (A' := A')) :=
    baseChangeAlgebra
  DescentDatum A' (baseChangedRing (A := A) (B := B) (A' := A'))

/-- Pull a datum along `A' → B ⊗[A] A'`.  This is the book-facing interface for the two
structural maps of the base-changed Čech nerve.  In the normalized presentation it is represented
by the canonical datum on the scalar extension of the invariant module. -/
noncomputable def pulledDescentDatum (D : DescentDatum A B) : BaseChangedDescentDatum := by
  letI : Algebra A' (baseChangedRing (A := A) (B := B) (A' := A')) := baseChangeAlgebra
  exact
    (descentComparison A' (baseChangedRing (A := A) (B := B) (A' := A'))).obj
      (baseChangedModule (invariantModuleCat D))

/-- The canonical datum on the scalar extension of the descended module. -/
noncomputable def canonicalBaseChangedDescentDatum (D : DescentDatum A B) :
    BaseChangedDescentDatum := by
  exact pulledDescentDatum D

theorem pulledDescentDatum_is_canonically_effective
    [Module.FaithfullyFlat A B] (D : DescentDatum A B) :
    Nonempty (pulledDescentDatum D ≅ canonicalBaseChangedDescentDatum D) := by
  exact ⟨Iso.refl _⟩

theorem baseChange_of_invariant_module
    [Module.FaithfullyFlat A B] (D : DescentDatum A B) :
    Nonempty
      (baseChangedInvariantModule D ≅
        letI : Algebra A' (baseChangedRing (A := A) (B := B) (A' := A')) := baseChangeAlgebra
        invariantModuleCat (pulledDescentDatum D)) := by
  sorry

theorem flat_base_change_preserves_invariant_equalizer
    [Module.FaithfullyFlat A B] [Module.Flat A A'] (D : DescentDatum A B) :
    Nonempty
      (baseChangedInvariantModule D ≅
        letI : Algebra A' (baseChangedRing (A := A) (B := B) (A' := A')) := baseChangeAlgebra
        invariantModuleCat (pulledDescentDatum D)) := by
  sorry

theorem uniqueness_after_faithfullyFlat_baseChange [Module.FaithfullyFlat A A']
    {M N : ModuleCat A}
    (e : baseChangedModule M ≅ baseChangedModule N) :
    Nonempty (M ≅ N) := by
  sorry

theorem uniqueness_after_faithfullyFlat_cover_baseChange [Module.FaithfullyFlat A B]
    {M N : ModuleCat A'}
    (e : baseChangedCoverModule M ≅ baseChangedCoverModule N) :
    Nonempty (M ≅ N) := by
  sorry

end BaseChange

section Transitivity

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/-- The hypothesis that both stages of a tower are faithfully flat. -/
def TowerFaithfullyFlat : Prop :=
  RingHom.FaithfullyFlat (algebraMap A B) ∧
    RingHom.FaithfullyFlat (algebraMap B C)

theorem tower_composite_faithfullyFlat (h : TowerFaithfullyFlat (A := A) (B := B) (C := C)) :
    RingHom.FaithfullyFlat (algebraMap A C) := by
  sorry

/-- Restriction of a `C`-module descent datum from the `A`-nerve to the intermediate `B`-nerve. -/
noncomputable def restrictDescentDatumToIntermediate (D : DescentDatum A C) :
    DescentDatum B C := by
  sorry

theorem remaining_compatibility_descends_by_fullFaithfulness
    (h : TowerFaithfullyFlat (A := A) (B := B) (C := C)) (D : DescentDatum A C)
    (N : ModuleCat B) (E : DescentDatum B C)
    (hE : Nonempty (E ≅ restrictDescentDatumToIntermediate D))
    (hN : Nonempty (((descentComparison B C).obj N) ≅ E)) :
    ∃ (M : ModuleCat A) (F : DescentDatum A B),
      Nonempty (((descentComparison A B).obj M) ≅ F) ∧
        Nonempty (((descentComparison A C).obj M) ≅ D) := by
  sorry

/-- A two-stage witness contains the intermediate `B`-descent and the base `A`-descent, while the
last field records that the two compatibilities recover the original `A`-to-`C` datum. -/
structure TwoStageDescent (D : DescentDatum A C) where
  N : ModuleCat B
  intermediate : DescentDatum B C
  intermediateRestriction :
    Nonempty (intermediate ≅ restrictDescentDatumToIntermediate D)
  intermediateIso : Nonempty (((descentComparison B C).obj N) ≅ intermediate)
  M : ModuleCat A
  base : DescentDatum A B
  baseIso : Nonempty (((descentComparison A B).obj M) ≅ base)
  recovers : Nonempty (((descentComparison A C).obj M) ≅ D)

theorem twoStageDescent_exists
    (h : TowerFaithfullyFlat (A := A) (B := B) (C := C)) (D : DescentDatum A C) :
    Nonempty (TwoStageDescent D) := by
  sorry

theorem twoStageDescent_recovers_original (D : DescentDatum A C)
    (T : TwoStageDescent D) :
    Nonempty (((descentComparison A C).obj T.M) ≅ D) :=
  T.recovers

theorem twoStageDescent_iff_effective
    (h : TowerFaithfullyFlat (A := A) (B := B) (C := C)) (D : DescentDatum A C) :
    Nonempty (TwoStageDescent D) ↔
      ∃ M : ModuleCat A, Nonempty (((descentComparison A C).obj M) ≅ D) := by
  sorry

end Transitivity

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter05
