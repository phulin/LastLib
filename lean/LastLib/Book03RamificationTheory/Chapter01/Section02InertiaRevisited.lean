import LastLib.Book03RamificationTheory.Chapter01.Section01TheQuestionLeftByInertia
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.Section04FixedFieldsOfInertia

namespace LastLib.Book03RamificationTheory.Chapter01

noncomputable section

open scoped BigOperators WithZero

/-! ## 1.2. Inertia revisited -/

/-- The canonical residue action has inertia as its kernel. -/
theorem chapter01_inertia_group_is_residue_action_kernel
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) :
    chapter01InertiaGroup K A =
      MonoidHom.ker (chapter01ResidueAction K A) := by
  exact
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.inertia_group_is_residue_action_kernel A

/-- Kernel membership is exactly invisibility on every residue class. -/
theorem chapter01_inertia_mem_iff_residue_fixed
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (σ : chapter01DecompositionGroup K A) :
    σ ∈ chapter01InertiaGroup K A ↔
      ∀ x : IsLocalRing.ResidueField A,
        chapter01ResidueAction K A σ x = x := by
  exact
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.inertia_mem_iff_residue_fixed A σ

/-- Reduction commutes with the action on the valuation ring. -/
theorem chapter01_residue_action_commutes_with_reduction
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (σ : chapter01DecompositionGroup K A) (x : A) :
    IsLocalRing.residue A (σ • x) =
      chapter01ResidueAction K A σ (IsLocalRing.residue A x) := by
  exact
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.residue_action_commutes_with_reduction A σ x

/-- The abstract exact-sequence interface used for residue reduction. -/
structure Chapter01ResidueGaloisReduction
    (G Q : Type*) [Group G] [Group Q]
    (I : Subgroup G) [I.Normal] where
  reduction : G →* Q
  surjective : Function.Surjective reduction
  kernel_eq_inertia : MonoidHom.ker reduction = I

/-- A surjective residue reduction gives the displayed exact sequence. -/
theorem chapter01_residue_action_exact_sequence
    {D Q : Type*} [Group D] [Group Q]
    (ρ : D →* Q) (hρ : Function.Surjective ρ) :
    Function.MulExact (Subgroup.subtype (MonoidHom.ker ρ)) ρ ∧
      Function.Surjective ρ := by
  exact
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.residue_action_exact_sequence ρ hρ

/-- The order formula for the kernel of a finite exact residue sequence. -/
theorem chapter01_residue_exact_sequence_cardinality
    {D Q : Type*} [Group D] [Group Q] [Finite D] [Finite Q]
    (ρ : D →* Q) (hρ : Function.Surjective ρ) :
    Nat.card D = Nat.card (MonoidHom.ker ρ) * Nat.card Q := by
  exact
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.residue_exact_sequence_cardinality ρ hρ

/-- If the total finite group has degree `e*f` and the residue quotient has
order `f`, the inertia kernel has order `e`. -/
theorem chapter01_kernel_card_eq_degree_factor
    {D Q : Type*} [Group D] [Group Q] [Finite D] [Finite Q]
    (ρ : D →* Q) (hρ : Function.Surjective ρ)
    (e f : ℕ) (hD : Nat.card D = e * f)
    (hQ : Nat.card Q = f) :
    Nat.card (MonoidHom.ker ρ) = e := by
  sorry

/-- The preceding kernel calculation applies to any chosen inertia subgroup
identified as the kernel of residue reduction. -/
theorem chapter01_inertia_order_eq_ramification_index
    {D Q : Type*} [Group D] [Group Q] [Finite D] [Finite Q]
    (I : Subgroup D) (ρ : D →* Q) (hρ : Function.Surjective ρ)
    (hkernel : I = MonoidHom.ker ρ) (e f : ℕ)
    (hD : Nat.card D = e * f) (hQ : Nat.card Q = f) :
    Nat.card I = e := by
  rw [hkernel]
  exact chapter01_kernel_card_eq_degree_factor ρ hρ e f hD hQ

/-- Completeness, normalized uniqueness, and residue separability make the
residue action over the base residue field surjective. -/
theorem chapter01_residue_action_over_base_surjective
    {F E Γ : Type*} [Field F] [Field E] [Algebra F E]
    [LinearOrderedCommGroupWithZero Γ] [FiniteDimensional F E]
    [IsGalois F E]
    (v : Valuation F Γ) [Valuation.IsRankOneDiscrete v]
    (w : Valuation E Γ) [Valuation.IsRankOneDiscrete w]
    (hext : v.IsEquiv (w.comap (algebraMap F E)))
    [Valuation.HasExtension v w]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal v.valuationSubring) v.valuationSubring)
    (hunique :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05UniqueNormalizedValuationExtension
        v w)
    [FiniteDimensional (IsLocalRing.ResidueField v.valuationSubring)
      (IsLocalRing.ResidueField w.valuationSubring)]
    [Normal (IsLocalRing.ResidueField v.valuationSubring)
      (IsLocalRing.ResidueField w.valuationSubring)]
    (hbase : ∀ σ : chapter01DecompositionGroup F w.valuationSubring, ∀ x :
      IsLocalRing.ResidueField v.valuationSubring,
      chapter01ResidueAction F w.valuationSubring σ
          (algebraMap (IsLocalRing.ResidueField v.valuationSubring)
            (IsLocalRing.ResidueField w.valuationSubring) x) =
        algebraMap (IsLocalRing.ResidueField v.valuationSubring)
          (IsLocalRing.ResidueField w.valuationSubring) x)
    (hseparable : Algebra.IsSeparable
      (IsLocalRing.ResidueField v.valuationSubring)
      (IsLocalRing.ResidueField w.valuationSubring)) :
    Function.Surjective
      (chapter01ResidueActionOverBase F w.valuationSubring
        (IsLocalRing.ResidueField v.valuationSubring) hbase) := by
  exact
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.residue_action_surjective_when_residue_separable
      v w hext hcomplete hunique hbase hseparable

/-- With a finite Galois residue extension, the surjective residue action can
be expressed with target `Gal(l/k)`, yielding the source's exact sequence. -/
theorem chapter01_separable_residue_reduction_exists
    {F E Γ : Type*} [Field F] [Field E] [Algebra F E]
    [LinearOrderedCommGroupWithZero Γ] [FiniteDimensional F E]
    [IsGalois F E]
    (v : Valuation F Γ) [Valuation.IsRankOneDiscrete v]
    (w : Valuation E Γ) [Valuation.IsRankOneDiscrete w]
    (hext : v.IsEquiv (w.comap (algebraMap F E)))
    [Valuation.HasExtension v w]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal v.valuationSubring) v.valuationSubring)
    (hunique :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05UniqueNormalizedValuationExtension
        v w)
    [FiniteDimensional (IsLocalRing.ResidueField v.valuationSubring)
      (IsLocalRing.ResidueField w.valuationSubring)]
    [Normal (IsLocalRing.ResidueField v.valuationSubring)
      (IsLocalRing.ResidueField w.valuationSubring)]
    (hbase : ∀ σ : chapter01DecompositionGroup F w.valuationSubring, ∀ x :
      IsLocalRing.ResidueField v.valuationSubring,
      chapter01ResidueAction F w.valuationSubring σ
          (algebraMap (IsLocalRing.ResidueField v.valuationSubring)
            (IsLocalRing.ResidueField w.valuationSubring) x) =
        algebraMap (IsLocalRing.ResidueField v.valuationSubring)
          (IsLocalRing.ResidueField w.valuationSubring) x)
    (hseparable : Algebra.IsSeparable
      (IsLocalRing.ResidueField v.valuationSubring)
      (IsLocalRing.ResidueField w.valuationSubring))
    [IsGalois
      (IsLocalRing.ResidueField v.valuationSubring)
      (IsLocalRing.ResidueField w.valuationSubring)] :
    ∃ ρ : chapter01DecompositionGroup F w.valuationSubring →*
        Gal(IsLocalRing.ResidueField w.valuationSubring /
          IsLocalRing.ResidueField v.valuationSubring),
      Function.Surjective ρ ∧
        MonoidHom.ker ρ = chapter01InertiaGroup F w.valuationSubring := by
  sorry

/-!
The next statement is the corrected form of the source's “fixed field of
inertia is maximal unramified” assertion.  The local-ring presentation keeps
the actual branch ideals and the maximal-unramified predicate, while perfect
base residue fields provide the standard defectless hypothesis.
-/

theorem chapter01_inertia_fixed_field_is_maximal_unramified
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsLocalHom (algebraMap A B)] [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [Module.Finite A B]
    [Module.IsTorsionFree A B] [FaithfulSMul A B]
    [IsIntegralClosure B A L]
    [Module.Finite (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField B)]
    [LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.Chapter09FiniteLocalExtension
      A B K L]
    [IsGalois K L] [PerfectField (IsLocalRing.ResidueField A)] :
    ∃ I : Subgroup (chapter01GaloisGroup K L),
      Nonempty
        (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.Chapter09GaloisInertiaIdentification
          A B K L I) := by
  exact
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.chapter09_galois_inertia_fixed_field
      A B K L

/-- The fixed field of inertia carries the quotient Galois group. -/
theorem chapter01_residue_quotient_is_fixed_field_galois_group
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (I : Subgroup (chapter01GaloisGroup K L)) [I.Normal] :
    Nonempty
      ((chapter01GaloisGroup K L ⧸ I) ≃*
        Gal(chapter01FixedField I / K)) := by
  exact
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.residue_quotient_is_fixed_field_galois_group I

/-- The inertia subgroup is the Galois group over its fixed field. -/
theorem chapter01_inertia_is_fixed_field_layer_galois_group
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (I : Subgroup (chapter01GaloisGroup K L)) :
    Nonempty (I ≃* Gal(L / chapter01FixedField I)) := by
  exact
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.inertia_is_fixed_field_layer_galois_group I

/-- The inseparable residue warning: residue automorphisms need not count the
whole residue degree. -/
theorem chapter01_inseparable_residue_automorphisms_do_not_recover_degree
    {k l : Type*} [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l] (hinsep : ¬Algebra.IsSeparable k l) :
    Nat.card (Gal(l / k)) < Module.finrank k l := by
  exact
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.inseparable_residue_automorphism_group_is_strictly_smaller
      hinsep

/-- Arithmetic and geometric Frobenius are inverse conventions. -/
theorem chapter01_geometric_frobenius_is_inverse
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l] :
    chapter01GeometricFrobenius k l = (chapter01ArithmeticFrobenius k l)⁻¹ := by
  exact
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.chapter06_geometric_frobenius_is_inverse k l

/-- A ramified residue Frobenius specifies a coset, not a preferred lift. -/
theorem chapter01_frobenius_coset_nonempty
    {G H : Type*} [Group G] [Group H]
    (I : Subgroup G) [I.Normal]
    (D : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.Chapter06RamifiedGaloisReduction
      G H I) (φ : H) :
    (chapter01ArithmeticFrobeniusCoset I D φ).Nonempty := by
  exact
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.chapter06_arithmetic_frobenius_coset_nonempty
      I D φ

/-- Two lifts of the same residue Frobenius differ by inertia. -/
theorem chapter01_frobenius_lifts_differ_by_inertia
    {G H : Type*} [Group G] [Group H]
    (I : Subgroup G) [I.Normal]
    (D : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.Chapter06RamifiedGaloisReduction
      G H I) (φ : H)
    {g h : G} (hg : g ∈ chapter01ArithmeticFrobeniusCoset I D φ)
    (hh : h ∈ chapter01ArithmeticFrobeniusCoset I D φ) :
    ∃ i : I, h = g * i := by
  exact
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.chapter06_frobenius_lifts_differ_by_inertia
      I D φ hg hh

/-- If inertia is nontrivial, the residue Frobenius coset has no unique lift. -/
theorem chapter01_frobenius_has_no_distinguished_lift
    {G H : Type*} [Group G] [Group H]
    (I : Subgroup G) [I.Normal]
    (D : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.Chapter06RamifiedGaloisReduction
      G H I) (φ : H)
    (hI : ∃ i : I, (i : G) ≠ 1) :
    ¬∃! g : G, g ∈ chapter01ArithmeticFrobeniusCoset I D φ := by
  exact
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.chapter06_ramified_frobenius_has_no_distinguished_lift
      I D φ hI

end

end LastLib.Book03RamificationTheory.Chapter01
