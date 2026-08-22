import LastLib.Book05LocalClassFieldTheory.Chapter02.Dependencies
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Section02TheFirstQuotient

namespace LastLib.Book05LocalClassFieldTheory.Chapter02

noncomputable section

open Function Ideal IsLocalRing
open Filter Topology
open scoped BigOperators Pointwise Topology

/-! ## 2.1. Separating magnitude from units -/

/- `Function.MulExact` records equality of the image of the first map with the
   kernel of the second.  Surjectivity is listed separately because it is the
   final `→ 0` condition in the displayed short exact sequence. -/
structure Chapter02ValuationCoordinateData
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) where
  valuation : Kˣ →* Multiplicative ℤ
  exact : chapter02ValuationExactSequence v valuation

theorem chapter02_valuation_exact_sequence
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ))
    (d : Chapter02ValuationCoordinateData v) :
    Function.Injective (chapter02UnitInclusion v) ∧
      Function.MulExact (chapter02UnitInclusion v) d.valuation ∧
      Function.Surjective d.valuation := by
  exact d.exact

theorem chapter02_valuation_sequence_is_injective_on_units
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) :
    Function.Injective (chapter02UnitInclusion v) := by
  intro x y h
  apply Units.ext
  apply Subtype.ext
  exact congrArg Units.val h

/- LOCAL_DEPENDENCY_GUESS: the normalized valuation-coordinate homomorphism is
   supplied by the earlier DVR decomposition interface. -/
theorem chapter02_valuation_coordinate_exists
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ))
    (hlocal : Chapter02LocalField v) :
    Nonempty (Chapter02ValuationCoordinateData v) := by
  classical
  obtain ⟨π, hπ0, hπ, hvalues⟩ := hlocal.1.1
  have unit_val (u : Kˣ) : ∃ z : ℤ, v (u : K) = (z : WithTop ℤ) :=
    hvalues (u : K) (Units.ne_zero u)
  let valInt : Kˣ → ℤ := fun u => Classical.choose (unit_val u)
  have valInt_spec (u : Kˣ) : v (u : K) = (valInt u : WithTop ℤ) :=
    Classical.choose_spec (unit_val u)
  have hpow (z : ℤ) : v (π ^ z) = (z : WithTop ℤ) := by
    cases z with
    | ofNat n =>
        change v (π ^ (n : ℤ)) = (n : WithTop ℤ)
        rw [zpow_natCast]
        rw [v.map_pow, hπ]
        simp
    | negSucc n =>
        rw [zpow_negSucc, v.map_inv, v.map_pow, hπ]
        simp [Int.negSucc_eq]
  let ν : Kˣ →* Multiplicative ℤ :=
    { toFun := fun u => Multiplicative.ofAdd (valInt u)
      map_one' := by
        change valInt (1 : Kˣ) = 0
        apply WithTop.coe_injective
        rw [← valInt_spec]
        change v (1 : K) = 0
        rw [v.map_one]
      map_mul' := by
        intro u w
        change valInt (u * w) = valInt u + valInt w
        apply WithTop.coe_injective
        have huv : ((u * w : Kˣ) : K) = (u : K) * (w : K) := rfl
        calc
          (valInt (u * w) : WithTop ℤ) = v ((u * w : Kˣ) : K) :=
            (valInt_spec (u * w)).symm
          _ = v (u : K) + v (w : K) := by rw [huv, v.map_mul]
          _ = (valInt u : WithTop ℤ) + (valInt w : WithTop ℤ) := by
            rw [valInt_spec, valInt_spec] }
  let hvint : v.toValuation.Integers (Chapter02ValuationRing v) :=
    Valuation.valuationSubring.integers v.toValuation
  refine ⟨⟨ν, ?_⟩⟩
  change Function.Injective (chapter02UnitInclusion v) ∧
    Function.MulExact (chapter02UnitInclusion v) ν ∧
      Function.Surjective ν
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    apply Units.ext
    apply Subtype.ext
    exact congrArg (fun z : Kˣ => (z : K)) hab
  · intro u
    constructor
    · intro hu
      have huvint : valInt u = 0 := by
        change Multiplicative.ofAdd (valInt u) = Multiplicative.ofAdd 0 at hu
        exact Multiplicative.ofAdd.injective hu
      have huval : v (u : K) = 0 := by
        rw [valInt_spec, huvint]
        simp
      let a0 : Chapter02ValuationRing v :=
        ⟨(u : K), by
          change 0 ≤ v (u : K)
          rw [huval]⟩
      have haunit : IsUnit a0 := by
        apply hvint.isUnit_iff_valuation_eq_one.mpr
        change v (u : K) = 0
        exact huval
      obtain ⟨a, ha⟩ := haunit
      refine ⟨a, ?_⟩
      apply Units.ext
      change ((a : Chapter02ValuationRing v) : K) = (u : K)
      simpa [a0] using congrArg (fun z : Chapter02ValuationRing v => (z : K)) ha
    · rintro ⟨a, rfl⟩
      have hav : v ((chapter02UnitInclusion v a : Kˣ) : K) = 0 := by
        change v ((a : Chapter02ValuationRing v) : K) = 0
        exact hvint.valuation_unit a
      have havint : valInt (chapter02UnitInclusion v a) = 0 := by
        apply WithTop.coe_injective
        rw [← valInt_spec, hav]
        simp
      simp [ν, havint]
  · intro z
    let u : Kˣ :=
      Units.mk0 (π ^ (Multiplicative.toAdd z))
        (zpow_ne_zero _ hπ0)
    refine ⟨u, ?_⟩
    have huvint : valInt u = Multiplicative.toAdd z := by
      apply WithTop.coe_injective
      rw [← valInt_spec]
      change v (π ^ (Multiplicative.toAdd z)) = _
      exact hpow (Multiplicative.toAdd z)
    change Multiplicative.ofAdd (valInt u) = z
    rw [huvint]
    simp

theorem chapter02_valuation_sequence_splits
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ))
    (d : Chapter02ValuationCoordinateData v) (π : Kˣ)
    (hπ : d.valuation π = Multiplicative.ofAdd 1) :
    Function.RightInverse (chapter02UniformizerSection π) d.valuation := by
  intro z
  change d.valuation (π ^ (Multiplicative.toAdd z)) = z
  rw [map_zpow, hπ]
  rw [← ofAdd_toAdd z]
  rw [← ofAdd_zsmul]
  simp

theorem chapter02_valuation_unit_decomposition
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ))
    (d : Chapter02ValuationCoordinateData v) (π : Kˣ)
    (hπ : d.valuation π = Multiplicative.ofAdd 1)
    (_huniformizer : chapter02IsUniformizerUnit v π) :
    (∀ x : K, x ≠ 0 →
      ∃ n : ℤ, ∃ u : Chapter02UnitGroup v,
      x = ((π : Kˣ) : K) ^ n * ((u : Chapter02UnitGroup v) : K)) ∧
      Nonempty
        (Kˣ ≃* (Multiplicative ℤ × Chapter02UnitGroup v)) := by
  classical
  have hval_zpow (n : ℤ) :
      d.valuation (π ^ n) = Multiplicative.ofAdd n := by
    rw [map_zpow, hπ]
    rw [← ofAdd_zsmul]
    simp
  have hker_unit (u : Chapter02UnitGroup v) :
      d.valuation (chapter02UnitInclusion v u) = 1 :=
    (d.exact.2.1 _).mpr ⟨u, rfl⟩
  have hincval (u : Chapter02UnitGroup v) :
      ((chapter02UnitInclusion v u : Kˣ) : K) =
        ((u : Chapter02UnitGroup v) : K) := rfl
  have factorization (x : K) (hx : x ≠ 0) :
      ∃ n : ℤ, ∃ u : Chapter02UnitGroup v,
        x = ((π : Kˣ) : K) ^ n * ((u : Chapter02UnitGroup v) : K) := by
    let xunit : Kˣ := Units.mk0 x hx
    let n : ℤ := Multiplicative.toAdd (d.valuation xunit)
    let q : Kˣ := xunit * (π ^ n)⁻¹
    have hqval : d.valuation q = 1 := by
      dsimp [q]
      rw [map_mul, map_inv, hval_zpow, ofAdd_toAdd]
      exact mul_inv_cancel _
    have hqker : q ∈ d.valuation.ker := MonoidHom.mem_ker.mpr hqval
    have hqrange : q ∈ (chapter02UnitInclusion v).range := by
      rw [← (MonoidHom.mulExact_iff.mp d.exact.2.1)]
      exact hqker
    obtain ⟨u, hu⟩ := hqrange
    have hxu : xunit = π ^ n * chapter02UnitInclusion v u := by
      calc
        xunit = (xunit * (π ^ n)⁻¹) * π ^ n := by group
        _ = chapter02UnitInclusion v u * π ^ n := by
          change q * π ^ n = _
          rw [hu.symm]
        _ = π ^ n * chapter02UnitInclusion v u := by ac_rfl
    refine ⟨n, u, ?_⟩
    have hxu' := congrArg Units.val hxu
    simpa [Units.val_mul, hincval, xunit, Units.val_zpow_eq_zpow_val] using hxu'
  have normal_form (x : Kˣ) :
      ∃ n : ℤ, ∃ u : Chapter02UnitGroup v,
        (x : K) = ((π : Kˣ) : K) ^ n * ((u : Chapter02UnitGroup v) : K) ∧
          ∀ m : ℤ, ∀ w : Chapter02UnitGroup v,
            (x : K) = ((π : Kˣ) : K) ^ m * ((w : Chapter02UnitGroup v) : K) →
              m = n ∧ w = u := by
    obtain ⟨n, u, hfactor⟩ := factorization (x : K) x.ne_zero
    have hxu : x = π ^ n * chapter02UnitInclusion v u := by
      apply Units.ext
      simpa [Units.val_mul, hincval, Units.val_zpow_eq_zpow_val] using hfactor
    refine ⟨n, u, hfactor, ?_⟩
    intro m w hmw
    have hmw' : x = π ^ m * chapter02UnitInclusion v w := by
      apply Units.ext
      simpa [Units.val_mul, hincval, Units.val_zpow_eq_zpow_val] using hmw
    have hcoord_m : d.valuation x = d.valuation (π ^ m) := by
      calc
        d.valuation x = d.valuation (π ^ m * chapter02UnitInclusion v w) :=
          congrArg d.valuation hmw'
        _ = d.valuation (π ^ m) := by rw [map_mul, hker_unit, mul_one]
    have hcoord_n : d.valuation x = d.valuation (π ^ n) := by
      calc
        d.valuation x = d.valuation (π ^ n * chapter02UnitInclusion v u) :=
          congrArg d.valuation hxu
        _ = d.valuation (π ^ n) := by rw [map_mul, hker_unit, mul_one]
    have hmnval : d.valuation (π ^ m) = d.valuation (π ^ n) :=
      hcoord_m.symm.trans hcoord_n
    have hmnval' : Multiplicative.ofAdd m = Multiplicative.ofAdd n :=
      (hval_zpow m).symm.trans (hmnval.trans (hval_zpow n))
    have hmn : m = n := Multiplicative.ofAdd.injective hmnval'
    have hunit : chapter02UnitInclusion v w =
        chapter02UnitInclusion v u := by
      apply mul_left_cancel (a := π ^ n)
      rw [hmn] at hmw'
      exact hmw'.symm.trans hxu
    exact ⟨hmn, chapter02_valuation_sequence_is_injective_on_units v hunit⟩
  constructor
  · exact factorization
  · choose n u hfactor hunique using normal_form
    let f : Kˣ →* (Multiplicative ℤ × Chapter02UnitGroup v) :=
      { toFun := fun x => (Multiplicative.ofAdd (n x), u x)
        map_one' := by
          have h := hunique 1 0 1 (by simp)
          apply Prod.ext
          · change n 1 = 0
            exact h.1.symm
          · exact h.2.symm
        map_mul' := by
          intro x y
          have hxy :
              ((x * y : Kˣ) : K) =
                ((π : Kˣ) : K) ^ (n x + n y) *
                  (((u x * u y : Chapter02UnitGroup v) : K)) := by
            change (x : K) * (y : K) = _
            rw [hfactor x, hfactor y]
            simp only [Units.val_mul]
            calc
              ((π : Kˣ) : K) ^ n x * ((u x : Chapter02UnitGroup v) : K) *
                    (((π : Kˣ) : K) ^ n y * ((u y : Chapter02UnitGroup v) : K)) =
                  (((π : Kˣ) : K) ^ n x * ((π : Kˣ) : K) ^ n y) *
                    (((u x : Chapter02UnitGroup v) : K) *
                      ((u y : Chapter02UnitGroup v) : K)) := by ring
              _ = ((π : Kˣ) : K) ^ (n x + n y) *
                    (((u x * u y : Chapter02UnitGroup v) : K)) := by
                rw [← zpow_add₀ (Units.ne_zero π)]
                rfl
          have h := hunique (x * y) (n x + n y) (u x * u y) hxy
          apply Prod.ext
          · change n (x * y) = n x + n y
            exact h.1.symm
          · exact h.2.symm }
    let g : (Multiplicative ℤ × Chapter02UnitGroup v) →* Kˣ :=
      { toFun := fun z =>
          Units.mk0
            (((π : Kˣ) : K) ^ (Multiplicative.toAdd z.1) *
              ((z.2 : Chapter02UnitGroup v) : K)) (by
                have hz : ((z.2 : Chapter02UnitGroup v) : K) ≠ 0 := by
                  intro hz
                  apply z.2.ne_zero
                  apply Subtype.ext
                  exact hz
                exact mul_ne_zero (zpow_ne_zero _ (Units.ne_zero π)) hz)
        map_one' := by
          apply Units.ext
          simp
        map_mul' := by
          intro z w
          apply Units.ext
          change
            ((π : Kˣ) : K) ^
                (Multiplicative.toAdd z.1 + Multiplicative.toAdd w.1) *
                (((z.2 * w.2 : Chapter02UnitGroup v) : K)) =
              (((π : Kˣ) : K) ^ (Multiplicative.toAdd z.1) *
                ((z.2 : Chapter02UnitGroup v) : K)) *
                (((π : Kˣ) : K) ^ (Multiplicative.toAdd w.1) *
                  ((w.2 : Chapter02UnitGroup v) : K))
          rw [zpow_add₀ (Units.ne_zero π)]
          simp only [Units.val_mul]
          change
            ((π : Kˣ) : K) ^ (Multiplicative.toAdd z.1) *
                ((π : Kˣ) : K) ^ (Multiplicative.toAdd w.1) *
                (((z.2 : Chapter02UnitGroup v) : K) *
                  ((w.2 : Chapter02UnitGroup v) : K)) = _
          ring }
    have hfg : ∀ x : Kˣ, g (f x) = x := by
      intro x
      apply Units.ext
      change ((π : Kˣ) : K) ^ n x * ((u x : Chapter02UnitGroup v) : K) = (x : K)
      exact (hfactor x).symm
    have hgf : ∀ z : Multiplicative ℤ × Chapter02UnitGroup v, f (g z) = z := by
      intro z
      have hz :
          ((g z : Kˣ) : K) =
            ((π : Kˣ) : K) ^ (Multiplicative.toAdd z.1) *
              ((z.2 : Chapter02UnitGroup v) : K) := by
        rfl
      have h := hunique (g z) (Multiplicative.toAdd z.1) z.2 hz
      apply Prod.ext
      · change n (g z) = Multiplicative.toAdd z.1
        exact h.1.symm
      · exact h.2.symm
    let e : Kˣ ≃* (Multiplicative ℤ × Chapter02UnitGroup v) :=
      { toFun := fun x => f x
        invFun := fun z => g z
        left_inv := hfg
        right_inv := hgf
        map_mul' := by
          intro x y
          exact f.map_mul x y }
    exact ⟨e⟩

/- The choice of a uniformizer is not canonical.  The following bridge keeps
   the change-of-coordinate statement explicit instead of identifying two
   splittings definitionally. -/
theorem chapter02_uniformizer_change_is_unit_change
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ))
    (π π' : Kˣ) (u : Chapter02UnitGroup v)
    (_hπ : chapter02IsUniformizerUnit v π)
    (_hπ' : chapter02IsUniformizerUnit v π')
    (hchange : (π' : K) = (chapter02UnitInclusion v u : Kˣ) * π) :
    ∀ z : ℤ, ∃ w : Chapter02UnitGroup v,
      ((π' : Kˣ) : K) ^ z =
        ((chapter02UnitInclusion v w : Kˣ) : K) * ((π : Kˣ) : K) ^ z := by
  intro z
  refine ⟨u ^ z, ?_⟩
  rw [hchange, mul_zpow]
  have hmapval :
      ((chapter02UnitInclusion v (u ^ z) : Kˣ) : K) =
        ((chapter02UnitInclusion v u : Kˣ) : K) ^ z := by
    simpa only [Units.val_zpow_eq_zpow_val] using
      congrArg Units.val ((chapter02UnitInclusion v).map_zpow u z)
  rw [hmapval]

theorem chapter02_unit_filtration_zero
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) :
    Chapter02UnitFiltration v 0 = ⊤ := by
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10_unit_filtration_zero
    (Chapter02ValuationRing v)

theorem chapter02_unit_filtration_mem_iff
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ) (u : Chapter02UnitGroup v) :
    u ∈ Chapter02UnitFiltration v n ↔
      (u : Chapter02ValuationRing v) - 1 ∈
        (IsLocalRing.maximalIdeal (Chapter02ValuationRing v)) ^ n := Iff.rfl

theorem chapter02_mem_valuation_ideal_power_set_iff
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ) (x : K) :
    x ∈ chapter02ValuationIdealPowerSet v n ↔
      ∃ y : Chapter02ValuationRing v,
        y ∈ (IsLocalRing.maximalIdeal (Chapter02ValuationRing v)) ^ n ∧
          x = (y : K) := Iff.rfl

theorem chapter02_mem_principal_unit_set_iff
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ) (x : K) :
    x ∈ chapter02PrincipalUnitSet v n ↔
      ∃ y : Chapter02ValuationRing v,
        y ∈ (IsLocalRing.maximalIdeal (Chapter02ValuationRing v)) ^ n ∧
          x = 1 + (y : K) := Iff.rfl

theorem chapter02_mem_field_unit_set_iff
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ) (x : K) :
    x ∈ chapter02FieldUnitSet v n ↔
      ∃ u : chapter02FieldUnitFiltration v n,
        x = ((u : Kˣ) : K) := Iff.rfl

theorem chapter02_unit_filtration_inverse
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ)
    {u : Chapter02UnitGroup v} (hu : u ∈ Chapter02UnitFiltration v n) :
    u⁻¹ ∈ Chapter02UnitFiltration v n := by
  exact (Chapter02UnitFiltration v n).inv_mem hu

theorem chapter02_unit_filtration_descending
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) :
    ∀ n : ℕ, Chapter02UnitFiltration v (n + 1) ≤
      Chapter02UnitFiltration v n := by
  intro n
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10_unit_filtration_descending
    (Chapter02ValuationRing v) n

theorem chapter02_unit_filtration_first_quotient
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) :
    Nonempty
      ((Chapter02UnitGroup v ⧸ Chapter02UnitFiltration v 1) ≃*
        (Chapter02ResidueField v)ˣ) := by
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10_first_unit_quotient_equiv_residue_units
      (Chapter02ValuationRing v)

theorem chapter02_unit_filtration_higher_quotient
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ) (hn : 1 ≤ n)
    (hDVR : IsDiscreteValuationRing (Chapter02ValuationRing v)) :
    Nonempty
      ((Chapter02UnitFiltration v n ⧸
          (Chapter02UnitFiltration v (n + 1)).subgroupOf
            (Chapter02UnitFiltration v n)) ≃*
        Multiplicative (Chapter02ResidueField v)) := by
  classical
  let A := Chapter02ValuationRing v
  let _ : IsDiscreteValuationRing A := hDVR
  obtain ⟨π, hπirr⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hπ : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Chapter10Uniformizer A π :=
    ⟨hπirr.ne_zero, hπirr.maximalIdeal_eq⟩
  have hn' : 0 < n := by omega
  let f :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10UniformizerLayerCoordinate
      A π hπ n hn'
  have hf : Function.Bijective f :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10_uniformizer_layer_coordinate_bijective
      A π hπ n hn'
  exact ⟨(MulEquiv.ofBijective f hf).symm⟩

theorem chapter02_unit_filtration_is_compact_open
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ))
    [UniformSpace (Chapter02UnitGroup v)]
    [IsTopologicalGroup (Chapter02UnitGroup v)]
    [CompleteSpace (Chapter02UnitGroup v)]
    [T2Space (Chapter02UnitGroup v)]
    [Finite (Chapter02ResidueField v)]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal (Chapter02ValuationRing v))
      (Chapter02ValuationRing v))
    (hDVR : IsDiscreteValuationRing (Chapter02ValuationRing v))
    (hbasis : Chapter02UnitFiltrationNeighborhoodBasis v) :
    ∀ n : ℕ,
      IsCompact (Chapter02UnitFiltration v n : Set (Chapter02UnitGroup v)) ∧
        IsOpen (Chapter02UnitFiltration v n : Set (Chapter02UnitGroup v)) := by
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10_finite_residue_unit_filtration_compact_open
    (Chapter02ValuationRing v) hcomplete hDVR hbasis

theorem chapter02_unit_group_is_compact
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ))
    [UniformSpace (Chapter02UnitGroup v)]
    [IsTopologicalGroup (Chapter02UnitGroup v)]
    [CompleteSpace (Chapter02UnitGroup v)]
    [T2Space (Chapter02UnitGroup v)]
    [Finite (Chapter02ResidueField v)]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal (Chapter02ValuationRing v))
      (Chapter02ValuationRing v))
    (hDVR : IsDiscreteValuationRing (Chapter02ValuationRing v))
    (hbasis : Chapter02UnitFiltrationNeighborhoodBasis v) :
    IsCompact (Set.univ : Set (Chapter02UnitGroup v)) := by
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10_finite_residue_unit_group_compact
    (Chapter02ValuationRing v) hcomplete hDVR hbasis

theorem chapter02_unit_filtration_is_neighborhood_basis
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ))
    [TopologicalSpace (Chapter02UnitGroup v)]
    (hbasis : Chapter02UnitFiltrationNeighborhoodBasis v) :
    (∀ n : ℕ,
      IsOpen (Chapter02UnitFiltration v n : Set (Chapter02UnitGroup v))) ∧
      ∀ s ∈ 𝓝 (1 : Chapter02UnitGroup v), ∃ n,
        (Chapter02UnitFiltration v n : Set (Chapter02UnitGroup v)) ⊆ s := by
  exact hbasis

theorem chapter02_unit_filtration_separated
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ))
    (hseparated : ∀ x : Chapter02ValuationRing v,
      (∀ n : ℕ, x ∈
        (IsLocalRing.maximalIdeal (Chapter02ValuationRing v)) ^ n) → x = 0) :
    ⨅ n : ℕ, Chapter02UnitFiltration v n = ⊥ := by
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10_unit_filtration_separated
    (Chapter02ValuationRing v) hseparated

theorem chapter02_unit_group_inverse_limit
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ))
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal (Chapter02ValuationRing v))
      (Chapter02ValuationRing v))
    (hDVR : IsDiscreteValuationRing (Chapter02ValuationRing v)) :
    Nonempty
      (Chapter02UnitGroup v ≃* Chapter02UnitInverseLimit v) := by
  let _ : IsDiscreteValuationRing (Chapter02ValuationRing v) := hDVR
  exact ⟨(LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10_complete_units_inverse_limit
    (Chapter02ValuationRing v) hcomplete).choose⟩

theorem chapter02_inverse_limit_family_is_transition_compatible
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ))
    (x : Chapter02UnitInverseLimit v) (n : ℕ) :
    chapter02PrecisionUnitTransition v n (x.1 (n + 1)) = x.1 n := by
  exact x.2 n

end

end LastLib.Book05LocalClassFieldTheory.Chapter02
