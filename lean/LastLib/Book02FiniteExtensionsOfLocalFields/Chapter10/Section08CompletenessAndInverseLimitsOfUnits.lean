import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Section01WhyUnitsNeedTheirOwnFiltration
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Section03HigherQuotientsAreAdditiveResidueFields

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10

noncomputable section

set_option maxHeartbeats 800000

open Ideal IsLocalRing

/-! ## 10.8. Completeness and inverse limits of units -/

/-- Reduction from precision `n+1` to precision `n`. -/
noncomputable def chapter10PrecisionRingTransition
    (A : Type*) [CommRing A] [IsLocalRing A] (n : ℕ) :
    Chapter10PrecisionQuotient A (n + 1) →+*
      Chapter10PrecisionQuotient A n := by
  exact Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (Nat.le_succ n))

/-- The induced transition map on finite-precision unit groups. -/
def chapter10PrecisionUnitTransition
    (A : Type*) [CommRing A] [IsLocalRing A] (n : ℕ) :
    (Chapter10PrecisionQuotient A (n + 1))ˣ →*
      (Chapter10PrecisionQuotient A n)ˣ :=
  Units.map (chapter10PrecisionRingTransition A n).toMonoidHom

/-- An opaque name for a finite-precision unit group, avoiding quotient unfolding in families. -/
def Chapter10PrecisionUnitGroup
    (A : Type*) [CommRing A] [IsLocalRing A] (n : ℕ) : Type _ :=
  (Chapter10PrecisionQuotient A (n + 1))ˣ

instance chapter10PrecisionUnitGroupGroup
    (A : Type*) [CommRing A] [IsLocalRing A] (n : ℕ) :
    Group (Chapter10PrecisionUnitGroup A n) := by
  change Group ((Chapter10PrecisionQuotient A (n + 1))ˣ)
  infer_instance

/-- The abstract transition used by the inverse-limit interface. -/
noncomputable def chapter10AbstractPrecisionUnitTransition
    (A : Type*) [CommRing A] [IsLocalRing A] (n : ℕ) :
    Chapter10PrecisionUnitGroup A (n + 1) →*
      Chapter10PrecisionUnitGroup A n := by
  change (Chapter10PrecisionQuotient A (n + 2))ˣ →*
    (Chapter10PrecisionQuotient A (n + 1))ˣ
  exact chapter10PrecisionUnitTransition A (n + 1)

/-- A compatible family of units in all finite congruence quotients. -/
def Chapter10CompatibleUnitFamily
    (A : Type*) [CommRing A] [IsLocalRing A] :
    Subgroup (∀ n : ℕ, Chapter10PrecisionUnitGroup A n) where
  carrier := {x | ∀ n,
    chapter10AbstractPrecisionUnitTransition A n (x (n + 1)) = x n}
  one_mem' := by
    intro n
    simp
  mul_mem' := by
    intro x y hxy hy n
    change chapter10AbstractPrecisionUnitTransition A n
        (x (n + 1) * y (n + 1)) = x n * y n
    rw [map_mul, hxy n, hy n]
  inv_mem' := by
    intro x hxy n
    change chapter10AbstractPrecisionUnitTransition A n
        ((x (n + 1))⁻¹) = (x n)⁻¹
    rw [map_inv, hxy n]

/-- The inverse-limit group of finite-precision units. -/
abbrev Chapter10AdicUnitInverseLimit
    (A : Type*) [CommRing A] [IsLocalRing A] : Type _ :=
  Chapter10CompatibleUnitFamily A

/-- The canonical compatible family attached to a ring unit. -/
noncomputable def chapter10UnitToAdicInverseLimit
    (A : Type*) [CommRing A] [IsLocalRing A] :
    Aˣ →* Chapter10AdicUnitInverseLimit A := by
  let q : ∀ n : ℕ, Aˣ →* Chapter10PrecisionUnitGroup A n :=
    fun n => Units.map
      (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ (n + 1))).toMonoidHom
  have hcompat : ∀ (u : Aˣ) (n : ℕ),
      chapter10AbstractPrecisionUnitTransition A n (q (n + 1) u) = q n u := by
    intro u n
    apply Units.ext
    change (chapter10PrecisionRingTransition A (n + 1))
        (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ (n + 1 + 1))
          (u : A)) =
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ (n + 1)) (u : A)
    rw [chapter10PrecisionRingTransition, Ideal.Quotient.factor_mk]
  refine
    { toFun := fun u => ⟨fun n => q n u, fun n => hcompat u n⟩
      map_one' := by
        ext n
        exact (q n).map_one
      map_mul' := by
        intro u v
        ext n
        exact (q n).map_mul u v }

private noncomputable def chapter10CompatibleRingUnitMap
    {L : Type*} [Field L] (A : ValuationSubring L) :
    (LastLib.Book01ValuationsDVRsAndCompletions.Chapter08.Chapter08CompatibleFamily A
      (IsLocalRing.maximalIdeal A))ˣ →*
      Chapter10AdicUnitInverseLimit A := by
  sorry

private noncomputable def chapter10CompatibleRingUnitUnmap
    {L : Type*} [Field L] (A : ValuationSubring L) :
    Chapter10AdicUnitInverseLimit A →*
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter08.Chapter08CompatibleFamily A
        (IsLocalRing.maximalIdeal A))ˣ := by
  sorry

/-- Completeness identifies ring units with the inverse limit of their reductions. -/
theorem chapter10_complete_units_inverse_limit
    {L : Type*} [Field L] (A : ValuationSubring L)
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hDVR : IsDiscreteValuationRing A) :
    ∃ e : Aˣ ≃* Chapter10AdicUnitInverseLimit A,
      ∀ u, e u = chapter10UnitToAdicInverseLimit A u := by
  sorry

/-- The finite-precision quotients of the principal-unit group. -/
abbrev Chapter10PrincipalUnitPrecisionQuotient
    (A : Type*) [CommRing A] [IsLocalRing A] (n : ℕ) : Type _ :=
  chapter10UnitFiltration A 1 ⧸
    (chapter10UnitFiltration A (n + 1)).subgroupOf (chapter10UnitFiltration A 1)

/-- Reduction between successive principal-unit precision quotients. -/
noncomputable def chapter10PrincipalUnitTransition
    (A : Type*) [CommRing A] [IsLocalRing A] (n : ℕ) :
    Chapter10PrincipalUnitPrecisionQuotient A (n + 1) →*
      Chapter10PrincipalUnitPrecisionQuotient A n := by
  exact QuotientGroup.map
    ((chapter10UnitFiltration A (n + 2)).subgroupOf
      (chapter10UnitFiltration A 1))
    ((chapter10UnitFiltration A (n + 1)).subgroupOf
      (chapter10UnitFiltration A 1))
    (MonoidHom.id _) (by
      intro u hu
      change (u : Aˣ) ∈ chapter10UnitFiltration A (n + 1)
      exact (chapter10_unit_filtration_descending A (n + 1)) hu)

/-- An opaque name for a principal-unit precision quotient. -/
def Chapter10PrincipalUnitPrecisionGroup
    (A : Type*) [CommRing A] [IsLocalRing A] (n : ℕ) : Type _ :=
  Chapter10PrincipalUnitPrecisionQuotient A n

instance chapter10PrincipalUnitPrecisionGroupGroup
    (A : Type*) [CommRing A] [IsLocalRing A] (n : ℕ) :
    Group (Chapter10PrincipalUnitPrecisionGroup A n) := by
  change Group (Chapter10PrincipalUnitPrecisionQuotient A n)
  infer_instance

/-- The abstract transition used by the principal-unit inverse-limit interface. -/
noncomputable def chapter10AbstractPrincipalUnitTransition
    (A : Type*) [CommRing A] [IsLocalRing A] (n : ℕ) :
    Chapter10PrincipalUnitPrecisionGroup A (n + 1) →*
      Chapter10PrincipalUnitPrecisionGroup A n := by
  change Chapter10PrincipalUnitPrecisionQuotient A (n + 1) →*
    Chapter10PrincipalUnitPrecisionQuotient A n
  exact chapter10PrincipalUnitTransition A n

/-- A compatible family of principal units modulo every deeper subgroup. -/
def Chapter10CompatiblePrincipalUnitFamily
    (A : Type*) [CommRing A] [IsLocalRing A] :
    Subgroup (∀ n : ℕ, Chapter10PrincipalUnitPrecisionGroup A n) where
  carrier := {x | ∀ n,
    chapter10AbstractPrincipalUnitTransition A n (x (n + 1)) = x n}
  one_mem' := by
    intro n
    simp
  mul_mem' := by
    intro x y hxy hy n
    change chapter10AbstractPrincipalUnitTransition A n
        (x (n + 1) * y (n + 1)) = x n * y n
    rw [map_mul, hxy n, hy n]
  inv_mem' := by
    intro x hxy n
    change chapter10AbstractPrincipalUnitTransition A n
        ((x (n + 1))⁻¹) = (x n)⁻¹
    rw [map_inv, hxy n]

/-- The inverse-limit type for principal units. -/
abbrev Chapter10PrincipalUnitInverseLimit
    (A : Type*) [CommRing A] [IsLocalRing A] : Type _ :=
  Chapter10CompatiblePrincipalUnitFamily A

/- The canonical family of principal-unit reductions. -/
noncomputable def chapter10PrincipalUnitToAdicInverseLimit
    (A : Type*) [CommRing A] [IsLocalRing A] :
    chapter10UnitFiltration A 1 →*
      Chapter10PrincipalUnitInverseLimit A := by
  let q : ∀ n : ℕ,
      chapter10UnitFiltration A 1 →*
        Chapter10PrincipalUnitPrecisionGroup A n :=
    fun n => QuotientGroup.mk'
      ((chapter10UnitFiltration A (n + 1)).subgroupOf
        (chapter10UnitFiltration A 1))
  have hcompat : ∀ (u : chapter10UnitFiltration A 1) (n : ℕ),
      chapter10AbstractPrincipalUnitTransition A n (q (n + 1) u) =
        q n u := by
    intro u n
    rfl
  refine
    { toFun := fun u => ⟨fun n => q n u, hcompat u⟩
      map_one' := by
        ext n
        exact (q n).map_one
      map_mul' := by
        intro u v
        ext n
        exact (q n).map_mul u v }

/-- Completeness identifies principal units with their compatible finite layers. -/
theorem chapter10_complete_principal_units_inverse_limit
    {L : Type*} [Field L] (A : ValuationSubring L)
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hDVR : IsDiscreteValuationRing A) :
    ∃ e : chapter10UnitFiltration A 1 ≃*
        Chapter10PrincipalUnitInverseLimit A,
      ∀ u, e u = chapter10PrincipalUnitToAdicInverseLimit A u := by
  sorry

/-- Finite residue fields make every finite-precision quotient finite. -/
theorem chapter10_finite_residue_finite_precision_quotients
    {L : Type*} [Field L] (A : ValuationSubring L)
    [Finite (Chapter10ResidueField A)] (n : ℕ)
    (hDVR : IsDiscreteValuationRing A) :
    Finite (Chapter10PrecisionQuotient A (n + 1)) := by
  let _ : IsDiscreteValuationRing A := hDVR
  let _ : Finite (A ⧸ IsLocalRing.maximalIdeal A) := by
    change Finite (Chapter10ResidueField A)
    infer_instance
  exact Ideal.finite_quotient_pow
    (IsPrincipalIdealRing.principal (IsLocalRing.maximalIdeal A)).fg (n + 1)

/-- Under the adic topology, finite residue fields make the unit group compact. -/
theorem chapter10_finite_residue_unit_group_compact
    {L : Type*} [Field L] (A : ValuationSubring L)
    [UniformSpace Aˣ] [IsTopologicalGroup Aˣ] [CompleteSpace Aˣ]
    [T2Space Aˣ] [Finite (Chapter10ResidueField A)]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hDVR : IsDiscreteValuationRing A)
    (htop : Chapter10UnitFiltrationNeighborhoodBasis
      (chapter10UnitFiltration A)) :
    Chapter10CompactUnitGroup (G := Aˣ) := by
  sorry

/-- Each congruence subgroup is compact and open in the finite-residue case. -/
theorem chapter10_finite_residue_unit_filtration_compact_open
    {L : Type*} [Field L] (A : ValuationSubring L)
    [UniformSpace Aˣ] [IsTopologicalGroup Aˣ] [CompleteSpace Aˣ]
    [T2Space Aˣ] [Finite (Chapter10ResidueField A)]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hDVR : IsDiscreteValuationRing A)
    (htop : Chapter10UnitFiltrationNeighborhoodBasis
      (chapter10UnitFiltration A)) :
    ∀ n : ℕ,
      IsCompact (chapter10UnitFiltration A n : Set Aˣ) ∧
        IsOpen (chapter10UnitFiltration A n : Set Aˣ) := by
  sorry

/-- The valuation direction is discrete and is the only noncompact direction. -/
def Chapter10LocallyCompactButNotCompact
    (G : Type*) [TopologicalSpace G] : Prop :=
  LocallyCompactSpace G ∧ ¬ IsCompact (Set.univ : Set G)

/-- With finite residue field, a complete valued field is locally compact but not compact. -/
theorem chapter10_finite_residue_local_compactness
    {L : Type*} [Field L] (A : ValuationSubring L)
    [UniformSpace Lˣ] [IsTopologicalGroup Lˣ] [CompleteSpace Lˣ]
    [T2Space Lˣ] [Finite (Chapter10ResidueField A)]
    [Valuation.IsRankOneDiscrete A.valuation]
    (π : A) (hπ : Chapter10Uniformizer A π)
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hDVR : IsDiscreteValuationRing A)
    (htop : Chapter10UnitFiltrationNeighborhoodBasis
      (chapter10FieldUnitFiltration A)) :
    Chapter10LocallyCompactButNotCompact Lˣ := by
  sorry

/-- An infinite residue-unit quotient obstructs compactness of the unit group. -/
theorem chapter10_infinite_residue_prevents_unit_compactness
    {L : Type*} [Field L] (A : ValuationSubring L)
    [TopologicalSpace Aˣ] [TopologicalSpace (Chapter10ResidueField A)ˣ]
    [Infinite (Chapter10ResidueField A)]
    (hquotient_discrete :
      ∀ s : Set (Chapter10ResidueField A)ˣ,
        IsOpen s)
    (hresidue_surjective : Function.Surjective (chapter10UnitReduction A))
    (hresidue_continuous : Continuous (chapter10UnitReduction A)) :
    ¬ Chapter10CompactUnitGroup (G := Aˣ) := by
  classical
  intro hcompact
  let _ : CompactSpace Aˣ := ⟨hcompact⟩
  let _ : DiscreteTopology (Chapter10ResidueField A)ˣ :=
    ⟨eq_bot_of_singletons_open (fun x => hquotient_discrete {x})⟩
  have hrange : IsCompact (Set.range (chapter10UnitReduction A)) := by
    simpa only [Set.image_univ, hresidue_surjective.range_eq] using
      (isCompact_univ.image hresidue_continuous)
  have hfinite : (Set.range (chapter10UnitReduction A)).Finite :=
    hrange.finite_of_discrete
  have huniv : (Set.univ : Set (Chapter10ResidueField A)ˣ).Finite := by
    simpa only [hresidue_surjective.range_eq] using hfinite
  let _ : Finite (Chapter10ResidueField A)ˣ :=
    Finite.of_finite_univ huniv
  let f : Chapter10ResidueField A →
      (Chapter10ResidueField A)ˣ ⊕ Unit :=
    fun x => if hx : x = 0 then Sum.inr () else Sum.inl (Units.mk0 x hx)
  have hf : Function.Injective f := by
    intro x y hxy
    by_cases hx : x = 0 <;> by_cases hy : y = 0
    · simp [hx, hy]
    · simp [f, hx, hy] at hxy
    · simp [f, hx, hy] at hxy
    · have hunit : Units.mk0 x hx = Units.mk0 y hy := by
        simpa [f, hx, hy] using hxy
      exact congrArg Units.val hunit
  have hfinite_residue : Finite (Chapter10ResidueField A) := by
    exact Finite.of_injective f hf
  let _ : Finite (Chapter10ResidueField A) := hfinite_residue
  exact not_finite (Chapter10ResidueField A)

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10
