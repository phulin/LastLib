import LastLib.Book05LocalClassFieldTheory.Chapter10.Dependencies
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

namespace LastLib.Book05LocalClassFieldTheory.Chapter10

noncomputable section

/-! ## 10.4. Formal-module layers -/

noncomputable def chapter10TorsionNormSubgroup
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    {Ω : Type*} [Field Ω] [Algebra K Ω]
    (T : Chapter10FormalTorsionSystem D Ω) (n : ℕ) : Subgroup Kˣ := by
  letI : FiniteDimensional K (T.torsionField n) := T.finite n
  exact chapter10NormSubgroup K (T.torsionField n)

abbrev Chapter10TorsionNormQuotient
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    {Ω : Type*} [Field Ω] [Algebra K Ω]
    (T : Chapter10FormalTorsionSystem D Ω) (n : ℕ) : Type _ :=
  Kˣ ⧸ chapter10TorsionNormSubgroup D T n

def chapter10TorsionValueUnitSubgroup
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    (n : ℕ) : Subgroup Kˣ :=
  chapter10ValueUnitSubgroup D D.uniformizer 1 n

/- LOCAL_DEPENDENCY_GUESS: this is the finite-level norm calculation attached
   to the formal-module torsion field. -/
theorem chapter10_formal_torsion_norm_group
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    {Ω : Type*} [Field Ω] [Algebra K Ω]
    (T : Chapter10FormalTorsionSystem D Ω) (n : ℕ) (hn : 1 ≤ n) :
    chapter10TorsionNormSubgroup D T n =
      chapter10TorsionValueUnitSubgroup D n := by
  sorry

theorem chapter10_formal_torsion_norm_quotient_equiv
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    {Ω : Type*} [Field Ω] [Algebra K Ω]
    (T : Chapter10FormalTorsionSystem D Ω) (n : ℕ) (hn : 1 ≤ n) :
    Nonempty
      ((Chapter10TorsionNormQuotient D T n) ≃*
        Chapter10UnitQuotient D.valuation n) := by
  sorry

theorem chapter10_formal_torsion_precision_unit_equiv
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    [Fintype (Chapter10ResidueField D.valuation)]
    (n : ℕ) (hn : 1 ≤ n) :
    Nonempty
      (Chapter10UnitQuotient D.valuation n ≃*
        (Chapter10PrecisionQuotient D.valuation n)ˣ) := by
  classical
  let A := Chapter10ValuationRing D.valuation
  have hmax : IsLocalRing.maximalIdeal A ≠ (⊤ : Ideal A) :=
    (inferInstance : (IsLocalRing.maximalIdeal A).IsMaximal).ne_top
  have hpow_ne : (IsLocalRing.maximalIdeal A) ^ n ≠ (⊤ : Ideal A) := by
    intro hpow
    apply hmax
    exact (Ideal.pow_eq_top_iff.mp hpow).resolve_right (Nat.ne_of_gt hn)
  let _ : Nontrivial (A ⧸ (IsLocalRing.maximalIdeal A) ^ n) :=
    Ideal.Quotient.nontrivial_iff.mpr hpow_ne
  let _ : IsLocalRing (A ⧸ (IsLocalRing.maximalIdeal A) ^ n) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  let _ : IsLocalHom
      (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n)) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let f : Aˣ →* (Chapter10PrecisionQuotient D.valuation n)ˣ :=
    Units.map
      (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n)).toMonoidHom
  have hsurj : Function.Surjective f := by
    exact IsLocalRing.surjective_units_map_of_local_ringHom
      (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n))
      Ideal.Quotient.mk_surjective inferInstance
  have hker : f.ker = Chapter10UnitFiltration D.valuation n := by
    ext u
    constructor
    · intro hu
      change f u = 1 at hu
      have hv := congrArg Units.val hu
      change Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n)
          (u : A) = 1 at hv
      change (u : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ n
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub]
      exact sub_eq_zero.mpr hv
    · intro hu
      apply MonoidHom.mem_ker.mpr
      apply Units.ext
      change Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n) (u : A) = 1
      rw [← sub_eq_zero]
      change Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n)
          ((u : A) - 1) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hu
  exact ⟨QuotientGroup.liftEquiv
    (Chapter10UnitFiltration D.valuation n) hsurj hker.symm⟩

theorem chapter10_formal_torsion_extension_degree
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    {Ω : Type*} [Field Ω] [Algebra K Ω]
    (T : Chapter10FormalTorsionSystem D Ω) (n : ℕ) (hn : 1 ≤ n)
    [Fintype (Chapter10ResidueField D.valuation)] :
    Module.finrank K (T.torsionField n) =
      (Fintype.card (Chapter10ResidueField D.valuation) - 1) *
        Fintype.card (Chapter10ResidueField D.valuation) ^ (n - 1) := by
  sorry

theorem chapter10_formal_torsion_norm_quotient_card
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    {Ω : Type*} [Field Ω] [Algebra K Ω]
    (T : Chapter10FormalTorsionSystem D Ω) (n : ℕ) (hn : 1 ≤ n)
    [Fintype (Chapter10ResidueField D.valuation)] :
    Nat.card (Chapter10TorsionNormQuotient D T n) =
      (Fintype.card (Chapter10ResidueField D.valuation) - 1) *
        Fintype.card (Chapter10ResidueField D.valuation) ^ (n - 1) := by
  sorry

/- At level one the formal torsion field contains every finite tame abelian
   totally ramified subextension whose degree divides `q - 1`. -/
theorem chapter10_formal_level_one_captures_tame_abelian_inertia
    {K M : Type*} [Field K] [Field M] [Algebra K M]
    [FiniteDimensional K M] [Algebra.IsSeparable K M]
    (D : Chapter10LocalFieldProfile K)
    {Ω : Type*} [Field Ω] [Algebra K Ω]
    (T : Chapter10FormalTorsionSystem D Ω)
    (vM : AddValuation M (WithTop ℤ))
    (hM : Chapter10TotallyRamifiedValuedExtension D.valuation vM 1)
    (hgal : IsGalois K M)
    (habelian : ∀ σ τ : Gal(M / K), σ * τ = τ * σ)
    [Fintype (Chapter10ResidueField D.valuation)]
    (hdegree : Module.finrank K M ∣
      Fintype.card (Chapter10ResidueField D.valuation) - 1) :
    Nonempty (M →ₐ[K] T.torsionField 1) := by
  sorry

/- Each positive unit layer is an additive residue-field layer. -/
theorem chapter10_formal_unit_layer_is_additive_residue_field
    {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ))
    (n : ℕ) (hn : 0 < n) :
    Nonempty
      (Chapter10UnitFiltration v n ⧸
      (Chapter10UnitFiltration v (n + 1)).subgroupOf
            (Chapter10UnitFiltration v n) ≃*
        Multiplicative (Chapter10ResidueField v)) := by
  sorry

theorem chapter10_formal_unit_layer_card
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    [Fintype (Chapter10ResidueField D.valuation)] (n : ℕ) (hn : 0 < n) :
    Nat.card
        (Chapter10UnitFiltration D.valuation n ⧸
        (Chapter10UnitFiltration D.valuation (n + 1)).subgroupOf
            (Chapter10UnitFiltration D.valuation n)) =
      Fintype.card (Chapter10ResidueField D.valuation) := by
  let A := Chapter10ValuationRing D.valuation
  obtain ⟨π, hπirr⟩ := IsDiscreteValuationRing.exists_irreducible A
  let hπ : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Chapter10Uniformizer A π :=
    ⟨hπirr.ne_zero, hπirr.maximalIdeal_eq⟩
  let e : Multiplicative (Chapter10ResidueField D.valuation) ≃*
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Chapter10UnitLayerQuotient A n :=
    MulEquiv.ofBijective
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10UniformizerLayerCoordinate
        A π hπ n hn)
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10_uniformizer_layer_coordinate_bijective
        A π hπ n hn)
  change Nat.card
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Chapter10UnitLayerQuotient A n) =
    Fintype.card (Chapter10ResidueField D.valuation)
  calc
    Nat.card
        (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Chapter10UnitLayerQuotient A n) =
        Nat.card (Multiplicative (Chapter10ResidueField D.valuation)) :=
      Nat.card_congr e.symm.toEquiv
    Nat.card (Multiplicative (Chapter10ResidueField D.valuation)) =
        Fintype.card (Chapter10ResidueField D.valuation) := by
      simp [Nat.card_eq_fintype_card]

theorem chapter10_formal_torsion_layers_are_totally_ramified
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    {Ω : Type*} [Field Ω] [Algebra K Ω]
    (T : Chapter10FormalTorsionSystem D Ω) (n : ℕ) (hn : 1 ≤ n)
    [Fintype (Chapter10ResidueField D.valuation)] :
    ∃ vL : AddValuation (T.torsionField n) (WithTop ℤ),
      Chapter10TotallyRamifiedValuedExtension
        D.valuation vL
        ((Fintype.card (Chapter10ResidueField D.valuation) - 1) *
          Fintype.card (Chapter10ResidueField D.valuation) ^ (n - 1)) := by
  sorry

/- Proposition 10.1: arithmetic reciprocity acts by the inverse formal-unit
   label, with the inverse reduced in the finite quotient `Oˣ/Uⁿ`. -/
theorem chapter10_artin_action_on_formal_torsion
    {K : Type} [Field K] (D : Chapter10LocalFieldProfile K)
    {Ω : Type} [Field Ω] [Algebra K Ω]
    (T : Chapter10FormalTorsionSystem D Ω) (n : ℕ) (hn : 1 ≤ n)
    [FiniteDimensional K (T.torsionField n)]
    [IsAbelianGalois K (T.torsionField n)]
    [Fintype (Gal(T.torsionField n / K))]
    (A : Chapter10NormalizedFiniteArtinMap K (T.torsionField n))
    (u : Chapter10RingUnitGroup D.valuation) :
    A.artin.reciprocity (chapter10RingUnitInField D.valuation u)
        (T.primitivePoint n) =
      T.formalAction n
        (QuotientGroup.mk'
          (Chapter10UnitFiltration D.valuation n) u⁻¹)
        (T.primitivePoint n) := by
  sorry

theorem chapter10_artin_and_torsion_labelings_differ_by_inversion
    {K : Type} [Field K] (D : Chapter10LocalFieldProfile K)
    {Ω : Type} [Field Ω] [Algebra K Ω]
    (T : Chapter10FormalTorsionSystem D Ω) (n : ℕ) (hn : 1 ≤ n)
    [FiniteDimensional K (T.torsionField n)]
    [IsAbelianGalois K (T.torsionField n)]
    [Fintype (Gal(T.torsionField n / K))]
    (A : Chapter10NormalizedFiniteArtinMap K (T.torsionField n)) :
    ∀ u : Chapter10RingUnitGroup D.valuation,
      A.artin.reciprocity (chapter10RingUnitInField D.valuation u) =
        T.torsionLabel n
          (QuotientGroup.mk'
            (Chapter10UnitFiltration D.valuation n) u⁻¹) := by
  sorry

theorem chapter10_artin_of_uniformizer_on_formal_torsion
    {K : Type} [Field K] (D : Chapter10LocalFieldProfile K)
    {Ω : Type} [Field Ω] [Algebra K Ω]
    (T : Chapter10FormalTorsionSystem D Ω) (n : ℕ) (hn : 1 ≤ n)
    [FiniteDimensional K (T.torsionField n)]
    [IsAbelianGalois K (T.torsionField n)]
    [Fintype (Gal(T.torsionField n / K))]
    (A : Chapter10NormalizedFiniteArtinMap K (T.torsionField n)) :
    A.artin.reciprocity D.uniformizer = 1 := by
  apply (MonoidHom.mem_ker).mp
  rw [A.artin.kernel_eq_norm]
  change D.uniformizer ∈ chapter10TorsionNormSubgroup D T n
  rw [chapter10_formal_torsion_norm_group D T n hn]
  apply (chapter10_mem_value_unit_subgroup_iff D D.uniformizer 1 n D.uniformizer).2
  refine ⟨1, ⟨1, (Chapter10FieldUnitFiltration D.valuation n).one_mem⟩, ?_⟩
  simp

/- The source's `\mathbb Q_p` specialization uses the multiplicative formal
   group and writes the inverse unit in the exponent modulo `p^n`.  This
   predicate records that reduction without choosing a representative of the
   finite quotient. -/
def chapter10PadicUnitExponentRepresentative
    (p n : ℕ) [Fact p.Prime] (u : (ℤ_[p])ˣ) (r : ℕ) : Prop :=
  ∃ z : ℤ_[p],
    ((u⁻¹ : (ℤ_[p])ˣ) : ℤ_[p]) - (r : ℤ_[p]) =
      (p : ℤ_[p]) ^ n * z

/- The cyclotomic example is stated at the same finite-reciprocity level as
   Proposition 10.1.  The primitive-root and generation hypotheses identify
   the chosen cyclotomic level, while the representative predicate makes the
   exponent convention explicit. -/
theorem chapter10_padic_cyclotomic_reciprocity_action
    {p n : ℕ} [Fact p.Prime] {L : Type} [Field L]
    [Algebra (ℚ_[p]) L] [FiniteDimensional (ℚ_[p]) L]
    [IsAbelianGalois (ℚ_[p]) L] [Fintype (Gal(L / ℚ_[p]))]
    (A : Chapter10NormalizedFiniteArtinMap (ℚ_[p]) L)
    (ζ : L) (hn : 0 < n)
    (hprimitive : IsPrimitiveRoot ζ (p ^ n))
    (hgenerates : Algebra.adjoin (ℚ_[p]) ({ζ} : Set L) = ⊤) :
    ∀ u : (ℤ_[p])ˣ, ∃ r : ℕ,
      chapter10PadicUnitExponentRepresentative p n u r ∧
        A.artin.reciprocity
            (Units.map (algebraMap (ℤ_[p]) (ℚ_[p])).toMonoidHom u) ζ =
          ζ ^ r := by
  sorry

end

end LastLib.Book05LocalClassFieldTheory.Chapter10
