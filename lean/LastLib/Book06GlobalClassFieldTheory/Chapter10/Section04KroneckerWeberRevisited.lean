import LastLib.Book06GlobalClassFieldTheory.Chapter10.Dependencies
import LastLib.Book06GlobalClassFieldTheory.Chapter10.Section02ConnectedComponentOfTheIdeleClassGroup

namespace LastLib.Book06GlobalClassFieldTheory.Chapter10

noncomputable section

open CategoryTheory
open Opposite

universe u v

/-!
## 10.4. Kronecker--Weber revisited
-/

/- LOCAL_DEPENDENCY_GUESS: the roots of unity in a chosen abelian closure are
the canonical cyclotomic generators. -/
structure Chapter10CyclotomicTowerData
    (Qab : Type u) [Field Qab] [Algebra ℚ Qab] [IsGalois ℚ Qab] where
  rootOfUnity : Chapter10PositiveNatural → Qab
  primitive_root : ∀ m, IsPrimitiveRoot (rootOfUnity m) m.1
  /-- The chosen primitive roots form a compatible cyclotomic tower. -/
  rootOfUnity_compat :
    ∀ {m n : Chapter10PositiveNatural}, n.1 ∣ m.1 →
      rootOfUnity m ^ (m.1 / n.1) = rootOfUnity n

namespace Chapter10CyclotomicTowerData

variable {Qab : Type u} [Field Qab] [Algebra ℚ Qab] [IsGalois ℚ Qab]

/-- The finite Galois field denoted by `ℚ(ζ_m)` in the chosen closure. -/
noncomputable def cyclotomicField
    (D : Chapter10CyclotomicTowerData Qab)
    (m : Chapter10PositiveNatural) :
    FiniteGaloisIntermediateField ℚ Qab :=
  FiniteGaloisIntermediateField.adjoin ℚ {D.rootOfUnity m}

theorem rootOfUnity_mem_cyclotomicField
    (D : Chapter10CyclotomicTowerData Qab)
    (m : Chapter10PositiveNatural) :
    D.rootOfUnity m ∈ (D.cyclotomicField m).toIntermediateField := by
  sorry

/- The compatibility of the selected roots also makes the generated fields a
cofinal directed tower, rather than merely a family of unrelated finite
extensions. -/
theorem cyclotomicField_mono_of_dvd
    (D : Chapter10CyclotomicTowerData Qab)
    {m n : Chapter10PositiveNatural} (h : n.1 ∣ m.1) :
    D.cyclotomicField n ≤ D.cyclotomicField m := by
  sorry

end Chapter10CyclotomicTowerData

structure Chapter10KroneckerWeberData
    (Qab : Type u) [Field Qab] [Algebra ℚ Qab] [IsGalois ℚ Qab] where
  closure : Chapter10AbelianClosureData ℚ Qab
  cyclotomic : Chapter10CyclotomicTowerData Qab
  complexConjugation : Gal(Qab / ℚ)
  complexConjugation_on_roots :
    ∀ m, complexConjugation (cyclotomic.rootOfUnity m) =
      (cyclotomic.rootOfUnity m)⁻¹

def chapter10CyclotomicFieldUnion
    {Qab : Type u} [Field Qab] [Algebra ℚ Qab] [IsGalois ℚ Qab]
    (D : Chapter10CyclotomicTowerData Qab) : Set Qab :=
  {x | ∃ m, x ∈ (D.cyclotomicField m).toIntermediateField}

/- The Kronecker--Weber assertion is kept as a theorem rather than built into
the definition of the cyclotomic tower. -/
theorem chapter10_kronecker_weber_finite_containment
    {Qab : Type u} [Field Qab] [Algebra ℚ Qab] [IsGalois ℚ Qab]
    (D : Chapter10KroneckerWeberData Qab)
    (L : FiniteGaloisIntermediateField ℚ Qab)
    (hL : chapter10IsAbelianFiniteGaloisExtension L) :
    ∃ m, L ≤ D.cyclotomic.cyclotomicField m := by
  sorry

theorem chapter10_Q_ab_eq_union_cyclotomic
    {Qab : Type u} [Field Qab] [Algebra ℚ Qab] [IsGalois ℚ Qab]
    (D : Chapter10KroneckerWeberData Qab) :
    chapter10CyclotomicFieldUnion D.cyclotomic = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  obtain ⟨L, hL, hx⟩ := D.closure.finite_abelian_subextension x
  obtain ⟨m, hm⟩ := chapter10_kronecker_weber_finite_containment D L hL
  exact ⟨m, hm hx⟩

/-- The cyclotomic Galois action, written as the inverse limit of the unit
groups `(ℤ/mℤ)ˣ`. -/
noncomputable def chapter10CyclotomicGaloisUnitEquiv
    {Qab : Type u} [Field Qab] [Algebra ℚ Qab] [IsGalois ℚ Qab]
    (D : Chapter10KroneckerWeberData Qab) :
    Gal(Qab / ℚ) ≃ₜ* chapter10CyclotomicUnitInverseLimit := by
  sorry

/- The coordinate interpretation is the bridge from the abstract inverse
limit to the chosen roots of unity.  The representative `val` is harmless
because the root has order `m.1`. -/
noncomputable def chapter10CyclotomicProfiniteFunctor :
    Chapter10PositiveNaturalᵒᵖ ⥤ ProfiniteGrp :=
  chapter10CyclotomicUnitFunctor ⋙ forget₂ FiniteGrp ProfiniteGrp

noncomputable def chapter10CyclotomicCoordinate
    (m : Chapter10PositiveNatural) :
    (chapter10CyclotomicProfiniteFunctor.obj (Opposite.op m) : Type) ≃*
      (ZMod m.1)ˣ := by
  change (ZMod m.1)ˣ ≃* (ZMod m.1)ˣ
  exact MulEquiv.refl _

noncomputable def chapter10CyclotomicExponent
    {Qab : Type u} [Field Qab] [Algebra ℚ Qab] [IsGalois ℚ Qab]
    (D : Chapter10KroneckerWeberData Qab)
    (σ : Gal(Qab / ℚ)) (m : Chapter10PositiveNatural) : ℕ := by
  letI : NeZero m.1 := ⟨Nat.ne_of_gt m.2⟩
  exact ((chapter10CyclotomicCoordinate m
    ((chapter10CyclotomicGaloisUnitEquiv D σ).val (Opposite.op m)) :
      (ZMod m.1)ˣ) : ZMod m.1).val

theorem chapter10CyclotomicGaloisUnitEquiv_root_action
    {Qab : Type u} [Field Qab] [Algebra ℚ Qab] [IsGalois ℚ Qab]
    (D : Chapter10KroneckerWeberData Qab) (σ : Gal(Qab / ℚ))
    (m : Chapter10PositiveNatural) :
    σ (D.cyclotomic.rootOfUnity m) =
      D.cyclotomic.rootOfUnity m ^ chapter10CyclotomicExponent D σ m := by
  sorry

theorem chapter10_Q_ab_galois_group_is_profinite_units
    {Qab : Type u} [Field Qab] [Algebra ℚ Qab] [IsGalois ℚ Qab]
    (D : Chapter10KroneckerWeberData Qab) :
    Nonempty (Gal(Qab / ℚ) ≃ₜ* chapter10CyclotomicUnitInverseLimit) :=
  ⟨chapter10CyclotomicGaloisUnitEquiv D⟩

theorem chapter10_complex_conjugation_corresponds_to_minus_one
    {Qab : Type u} [Field Qab] [Algebra ℚ Qab] [IsGalois ℚ Qab]
    (D : Chapter10KroneckerWeberData Qab) :
    chapter10CyclotomicGaloisUnitEquiv D D.complexConjugation =
      chapter10CyclotomicMinusOne := by
  sorry

theorem chapter10_positive_real_component_of_CQ_in_global_kernel
    {C : Type u} {Qab : Type v} [CommGroup C] [TopologicalSpace C] [T2Space C]
    [IsTopologicalGroup C] [Field Qab] [Algebra ℚ Qab] [IsGalois ℚ Qab]
    (T : Chapter10IdeleClassTopologyData C)
    (F : Chapter10FiniteArtinFamily C ℚ Qab)
    (R : Chapter10FiniteReciprocityData F) :
    T.positiveRealComponent ≤ (chapter10GlobalArtinMap F).ker := by
  simpa only [← chapter10_globalArtinMap_kernel_eq_identityComponent T F R] using
    (chapter10_positiveRealComponent_le_identityComponent T)

theorem chapter10_ray_class_field_union_replaces_cyclotomic_union
    {K : Type u} {Kab : Type v} [Field K] [NumberField K] [Field Kab]
    [Algebra K Kab] [IsGalois K Kab]
    (A : Chapter10AbelianClosureData K Kab)
    (R : Chapter10RayClassFieldSystem K Kab) :
    chapter10RayClassFieldUnion R = Set.univ :=
  chapter10RayClassFieldUnion_eq_univ A R

theorem chapter10_every_finite_abelian_extension_is_in_a_ray_class_field
    {K : Type u} {Kab : Type v} [Field K] [NumberField K] [Field Kab]
    [Algebra K Kab] [IsGalois K Kab]
    (R : Chapter10RayClassFieldSystem K Kab)
    (L : FiniteGaloisIntermediateField K Kab)
    (hL : chapter10IsAbelianFiniteGaloisExtension L) :
    ∃ m, L ≤ R.rayField m :=
  R.contains_every_finite_abelian L hL

/- SOURCE_NOTE: the sentence that no equally elementary roots-of-unity family
works for a general number field is a qualitative warning, not a standalone
mathematical assertion. The precise replacement is the ray-class-field union
and conductor containment theorems above. -/

end

end LastLib.Book06GlobalClassFieldTheory.Chapter10
