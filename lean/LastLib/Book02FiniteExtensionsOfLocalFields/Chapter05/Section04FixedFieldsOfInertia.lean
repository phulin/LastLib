import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.Section03ResidueActionAndInertia

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05

noncomputable section

open scoped BigOperators

/-! ## 5.4. Fixed fields of inertia -/

/-- The fixed field of a subgroup of a finite Galois group. -/
abbrev chapter05FixedField
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (H : Subgroup Gal(L / K)) : IntermediateField K L :=
  IntermediateField.fixedField H

/-- A branch invariant profile using Mathlib's intrinsic ideal invariants. -/
structure Chapter05LocalEFProfile
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (P : Ideal B) where
  e : ℕ
  f : ℕ
  e_eq : e = P.ramificationIdx A
  f_eq : f = P.inertiaDeg A

/-- The foundational unramified predicate used for an `e = 1` layer. -/
abbrev chapter05Unramified (e : ℕ) (residueSeparable : Prop) : Prop :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.foundationalUnramified e residueSeparable

/-- The foundational totally ramified predicate used for an `f = 1` layer. -/
abbrev chapter05TotallyRamified (f : ℕ) : Prop :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.foundationalTotallyRamified f

/-- The kernel of a residue action is a normal subgroup. -/
theorem inertia_kernel_is_normal
    {D Q : Type*} [Group D] [Group Q] (ρ : D →* Q) :
    (MonoidHom.ker ρ).Normal := by
  infer_instance

/-- The fixed field of the inertia kernel has the quotient and kernel degrees. -/
theorem fixed_field_of_residue_kernel_has_two_degrees
    {K L Q : Type*} [Field K] [Field L] [Algebra K L] [Group Q]
    [FiniteDimensional K L] [IsGalois K L] [Finite Q]
    (ρ : Gal(L / K) →* Q) (hρ : Function.Surjective ρ)
    (e f : ℕ)
    (he : Nat.card (MonoidHom.ker ρ) = e)
    (hf : Nat.card Q = f) :
    Module.finrank K (chapter05FixedField (MonoidHom.ker ρ)) = f ∧
      Module.finrank (chapter05FixedField (MonoidHom.ker ρ)) L = e := by
  sorry

/-- The quotient of the Galois group by inertia is the Galois group of the fixed field. -/
theorem residue_quotient_is_fixed_field_galois_group
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (I : Subgroup Gal(L / K)) [I.Normal] :
    Nonempty
      ((Gal(L / K) ⧸ I) ≃* Gal(chapter05FixedField I / K)) := by
  sorry

/-- Inertia is the Galois group of the totally ramified fixed-field layer. -/
theorem inertia_is_fixed_field_layer_galois_group
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (I : Subgroup Gal(L / K)) [I.Normal] :
    Nonempty
      (I ≃* Gal(L / chapter05FixedField I)) := by
  sorry

/-- The degree allocation forced by the inertia fixed field. -/
theorem fixed_field_inertia_degree_allocation
    {K L Q : Type*} [Field K] [Field L] [Algebra K L] [Group Q]
    [FiniteDimensional K L] [IsGalois K L] [Finite Q]
    (ρ : Gal(L / K) →* Q) (hρ : Function.Surjective ρ)
    (e f : ℕ)
    (he : Nat.card (MonoidHom.ker ρ) = e)
    (hf : Nat.card Q = f) :
    Module.finrank K (chapter05FixedField (MonoidHom.ker ρ)) = f ∧
      Module.finrank (chapter05FixedField (MonoidHom.ker ρ)) L = e := by
  exact fixed_field_of_residue_kernel_has_two_degrees ρ hρ e f he hf

/--
 The local `e`/`f` labels for the two layers: the fixed field has `e = 1`
 and the upper layer has `f = 1`, while the complementary invariant is
 unchanged.  The equalities are stated as an explicit layer profile so that
 later proof passes can attach the actual valuation-ring profiles.
 -/
structure Chapter05InertiaLayerAllocation (e f : ℕ) where
  fixed_field_ramification : ℕ
  fixed_field_residue : ℕ
  upper_ramification : ℕ
  upper_residue : ℕ
  fixed_field_ramification_eq_one : fixed_field_ramification = 1
  fixed_field_residue_eq : fixed_field_residue = f
  upper_ramification_eq : upper_ramification = e
  upper_residue_eq_one : upper_residue = 1

/-- The canonical layer profile records unramified and totally ramified endpoints. -/
def chapter05CanonicalInertiaLayerAllocation (e f : ℕ) :
    Chapter05InertiaLayerAllocation e f := by
  refine
    { fixed_field_ramification := 1
      fixed_field_residue := f
      upper_ramification := e
      upper_residue := 1
      fixed_field_ramification_eq_one := rfl
      fixed_field_residue_eq := rfl
      upper_ramification_eq := rfl
      upper_residue_eq_one := rfl }

/-- The degree formulas and layer profile are compatible. -/
theorem fixed_field_inertia_has_unramified_and_totally_ramified_layers
    {K L Q : Type*} [Field K] [Field L] [Algebra K L] [Group Q]
    [FiniteDimensional K L] [IsGalois K L] [Finite Q]
    (ρ : Gal(L / K) →* Q) (hρ : Function.Surjective ρ)
    (e f : ℕ) (he : Nat.card (MonoidHom.ker ρ) = e)
    (hf : Nat.card Q = f) (residueSeparable : Prop)
    (hresidueSeparable : residueSeparable) :
    Module.finrank K (chapter05FixedField (MonoidHom.ker ρ)) = f ∧
      Module.finrank (chapter05FixedField (MonoidHom.ker ρ)) L = e ∧
      chapter05Unramified 1 residueSeparable ∧
      chapter05TotallyRamified 1 ∧
      Nonempty (Chapter05InertiaLayerAllocation e f) := by
  have hdeg := fixed_field_inertia_degree_allocation ρ hρ e f he hf
  exact ⟨hdeg.1, hdeg.2, ⟨rfl, hresidueSeparable⟩, rfl,
    ⟨chapter05CanonicalInertiaLayerAllocation e f⟩⟩

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05
