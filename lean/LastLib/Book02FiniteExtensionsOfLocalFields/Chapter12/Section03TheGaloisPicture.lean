import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12.Section02TheSeparabilityMap

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12

noncomputable section

open scoped BigOperators

universe u

/-! ## 12.3. The Galois picture -/

/--
The reduction datum behind the decomposition/inertia exact sequence.  The
reduction homomorphism is kept explicit: constructing it from quotient
valuation rings is a later compatibility theorem, while this interface
records its kernel, surjectivity, and the normal inertia subgroup.
-/
structure Chapter12GaloisReductionData
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [FiniteDimensional K L] [IsGalois K L]
    [Algebra (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [FiniteDimensional (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)] where
  reduction :
    Gal(L / K) →* Gal(IsLocalRing.ResidueField vL.valuationSubring /
      IsLocalRing.ResidueField vK.valuationSubring)
  inertia : Subgroup (Gal(L / K))
  inertia_normal : inertia.Normal
  reduction_surjective : Function.Surjective reduction
  reduction_kernel : reduction.ker = inertia
  valuation_unique :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.hasUniqueValuationExtension vK L

/-- The kernel/surjectivity form of the displayed exact sequence `1 → I → G → Gal(l/k) → 1`. -/
def chapter12GaloisReductionExactSequence
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [FiniteDimensional K L] [IsGalois K L]
    [Algebra (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [FiniteDimensional (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    (d : Chapter12GaloisReductionData vK vL) : Prop :=
  d.reduction.ker = d.inertia ∧ Function.Surjective d.reduction

/-- Book 2, §12.3: the reduction datum is an exact sequence. -/
theorem galois_reduction_is_exact
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [FiniteDimensional K L] [IsGalois K L]
    [Algebra (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [FiniteDimensional (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    (d : Chapter12GaloisReductionData vK vL) :
    chapter12GaloisReductionExactSequence vK vL d := by
  exact ⟨d.reduction_kernel, d.reduction_surjective⟩

instance chapter12GaloisInertiaNormal
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [FiniteDimensional K L] [IsGalois K L]
    [Algebra (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [FiniteDimensional (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    (d : Chapter12GaloisReductionData vK vL) : d.inertia.Normal :=
  d.inertia_normal

/-- The fixed field of inertia, i.e. the maximal unramified intermediate field. -/
noncomputable def inertiaFixedField
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [FiniteDimensional K L] [IsGalois K L]
    [Algebra (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [FiniteDimensional (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    (d : Chapter12GaloisReductionData vK vL) : IntermediateField K L :=
  IntermediateField.fixedField d.inertia

/-- The group-theoretic predicate expressing that an intermediate field is unramified. -/
def chapter12UnramifiedIntermediateField
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [FiniteDimensional K L] [IsGalois K L]
    [Algebra (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [FiniteDimensional (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    (d : Chapter12GaloisReductionData vK vL) (M : IntermediateField K L) : Prop :=
  d.inertia ≤ M.fixingSubgroup

/-- The arithmetic Frobenius `x ↦ x ^ #k` for a finite-field extension. -/
noncomputable def arithmeticFrobenius
    {k l : Type u} [Field k] [Field l] [Algebra k l]
    [Finite k] [Algebra.IsAlgebraic k l] : Gal(l / k) :=
  letI := Fintype.ofFinite k
  FiniteField.frobeniusAlgEquivOfAlgebraic k l

/-- The geometric Frobenius convention, inverse to arithmetic Frobenius. -/
noncomputable def geometricFrobenius
    {k l : Type u} [Field k] [Field l] [Algebra k l]
    [Finite k] [Algebra.IsAlgebraic k l] : Gal(l / k) :=
  (arithmeticFrobenius (k := k) (l := l))⁻¹

/-- Book 2, §12.3: completeness gives uniqueness of the valuation extension. -/
theorem complete_galois_extension_has_unique_valuation
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring) :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.hasUniqueValuationExtension vK L := by
  sorry

/-- Book 2, §12.3: the decomposition/inertia reduction has the exact quotient. -/
theorem galois_reduction_has_exact_quotient
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [FiniteDimensional K L] [IsGalois K L]
    [Algebra (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [FiniteDimensional (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    (d : Chapter12GaloisReductionData vK vL) :
    Nonempty
      (Gal(L / K) ⧸ d.inertia ≃*
        Gal(IsLocalRing.ResidueField vL.valuationSubring /
          IsLocalRing.ResidueField vK.valuationSubring)) := by
  sorry

/-- Book 2, §§12.2–12.3: the exact quotient has order equal to the residue degree. -/
theorem galois_reduction_quotient_order_is_residue_degree
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [FiniteDimensional K L] [IsGalois K L]
    [Algebra (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [FiniteDimensional (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    (d : Chapter12GaloisReductionData vK vL) :
    Nat.card (Gal(L / K) ⧸ d.inertia) =
      Module.finrank (IsLocalRing.ResidueField vK.valuationSubring)
        (IsLocalRing.ResidueField vL.valuationSubring) := by
  sorry

/-- Book 2, §12.3: fixed field of inertia is maximal among unramified fields. -/
theorem inertia_fixed_field_is_maximal_unramified
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [FiniteDimensional K L] [IsGalois K L]
    [Algebra (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [FiniteDimensional (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    (d : Chapter12GaloisReductionData vK vL) :
    chapter12UnramifiedIntermediateField vK vL d (inertiaFixedField vK vL d) ∧
      ∀ M : IntermediateField K L,
        chapter12UnramifiedIntermediateField vK vL d M →
          M ≤ inertiaFixedField vK vL d := by
  sorry

/-- Book 2, §12.3: the fixed-field diagram sits between the two endpoints. -/
theorem inertia_fixed_field_has_field_inclusions
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [FiniteDimensional K L] [IsGalois K L]
    [Algebra (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [FiniteDimensional (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    (d : Chapter12GaloisReductionData vK vL) :
    (⊥ : IntermediateField K L) ≤ inertiaFixedField vK vL d ∧
      inertiaFixedField vK vL d ≤ (⊤ : IntermediateField K L) := by
  exact ⟨bot_le, le_top⟩

/-- Book 2, §12.3: finite residue Galois groups are generated by Frobenius. -/
theorem arithmetic_frobenius_generates_finite_residue_galois_group
    {k l : Type u} [Field k] [Field l] [Algebra k l]
    [Fintype k] [Finite l] [Algebra.IsAlgebraic k l] :
    Subgroup.zpowers (arithmeticFrobenius (k := k) (l := l)) =
      (⊤ : Subgroup (Gal(l / k))) := by
  sorry

/-- Book 2, §12.3: a finite-residue Frobenius lift determines an inertia coset. -/
theorem ramified_frobenius_lifts_to_a_coset
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [FiniteDimensional K L] [IsGalois K L]
    [Algebra (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [FiniteDimensional (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [Fintype (IsLocalRing.ResidueField vK.valuationSubring)]
    [Finite (IsLocalRing.ResidueField vL.valuationSubring)]
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    (d : Chapter12GaloisReductionData vK vL) :
    ∃ σ : Gal(L / K),
      d.reduction σ = arithmeticFrobenius
        (k := IsLocalRing.ResidueField vK.valuationSubring)
        (l := IsLocalRing.ResidueField vL.valuationSubring) := by
  sorry

/-- Book 2, §12.3: any two such lifts represent the same quotient coset. -/
theorem ramified_frobenius_lifts_have_the_same_inertia_coset
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [FiniteDimensional K L] [IsGalois K L]
    [Algebra (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [FiniteDimensional (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [Fintype (IsLocalRing.ResidueField vK.valuationSubring)]
    [Finite (IsLocalRing.ResidueField vL.valuationSubring)]
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    (d : Chapter12GaloisReductionData vK vL)
    (σ τ : Gal(L / K))
    (hσ : d.reduction σ = arithmeticFrobenius
      (k := IsLocalRing.ResidueField vK.valuationSubring)
      (l := IsLocalRing.ResidueField vL.valuationSubring))
    (hτ : d.reduction τ = arithmeticFrobenius
      (k := IsLocalRing.ResidueField vK.valuationSubring)
      (l := IsLocalRing.ResidueField vL.valuationSubring)) :
    QuotientGroup.mk' d.inertia σ = QuotientGroup.mk' d.inertia τ := by
  sorry

/-- Book 2, §12.3: when inertia is trivial, Frobenius is an actual generator. -/
theorem unramified_frobenius_is_an_actual_generator
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [FiniteDimensional K L] [IsGalois K L]
    [Algebra (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [FiniteDimensional (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [Fintype (IsLocalRing.ResidueField vK.valuationSubring)]
    [Finite (IsLocalRing.ResidueField vL.valuationSubring)]
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    (d : Chapter12GaloisReductionData vK vL)
    (hinertia : d.inertia = ⊥) :
    ∃ σ : Gal(L / K),
      d.reduction σ = arithmeticFrobenius
        (k := IsLocalRing.ResidueField vK.valuationSubring)
        (l := IsLocalRing.ResidueField vL.valuationSubring) ∧
      Subgroup.zpowers σ = (⊤ : Subgroup (Gal(L / K))) := by
  sorry

/-- Book 2, §12.3: geometric Frobenius is the inverse convention. -/
theorem geometric_frobenius_is_the_inverse
    {k l : Type u} [Field k] [Field l] [Algebra k l]
    [Finite k] [Algebra.IsAlgebraic k l] :
    geometricFrobenius (k := k) (l := l) =
      (arithmeticFrobenius (k := k) (l := l))⁻¹ := by
  rfl

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12
