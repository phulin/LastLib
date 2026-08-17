import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Dependencies
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Section02TheFirstQuotient
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter05.Section03FractionalIdealsAndPrecision
import Mathlib.GroupTheory.Index

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10

noncomputable section

open Ideal IsLocalRing

/-! ## 10.3. Higher quotients are additive residue fields -/

/-- The canonical higher layer is an additive group viewed multiplicatively. -/
theorem chapter10_higher_unit_layer_is_additive
    {L : Type*} [Field L] (A : ValuationSubring L) (n : ℕ) (hn : 0 < n) :
    ∃ e : Multiplicative
        (Chapter10IdealLayer A (IsLocalRing.maximalIdeal A) n) ≃*
        Chapter10UnitLayerQuotient A n,
      ∀ u : chapter10UnitFiltration A n,
        e (Multiplicative.ofAdd
          (Submodule.Quotient.mk
            (p := chapter10IdealLayerDenominator A
              (IsLocalRing.maximalIdeal A) n)
            (⟨((u : Aˣ) : A) - 1, u.property⟩ :
              (IsLocalRing.maximalIdeal A ^ n : Ideal A)))) =
          QuotientGroup.mk'
            ((chapter10UnitFiltration A (n + 1)).subgroupOf
              (chapter10UnitFiltration A n)) u := by
  classical
  let φ : Additive (chapter10UnitFiltration A n) →+
      Chapter10IdealLayer A (IsLocalRing.maximalIdeal A) n :=
    { toFun := fun u =>
        Submodule.Quotient.mk
          (p := chapter10IdealLayerDenominator A (IsLocalRing.maximalIdeal A) n)
          (⟨(((Additive.toMul u : chapter10UnitFiltration A n) : Aˣ) : A) - 1,
            (Additive.toMul u).property⟩ :
            (IsLocalRing.maximalIdeal A ^ n : Ideal A))
      map_zero' := by
        apply (Submodule.Quotient.mk_eq_zero _).2
        simp [chapter10IdealLayerDenominator]
      map_add' := by
        intro u v
        apply (Submodule.Quotient.eq _).2
        change _ ∈ (IsLocalRing.maximalIdeal A) ^ (n + 1)
        simp only [Submodule.coe_sub, Submodule.coe_add, Submodule.subtype_apply]
        rw [toMul_add]
        have huv :
            (((Additive.toMul u * Additive.toMul v : chapter10UnitFiltration A n) : Aˣ) : A) =
              (((Additive.toMul u : chapter10UnitFiltration A n) : Aˣ) : A) *
                (((Additive.toMul v : chapter10UnitFiltration A n) : Aˣ) : A) := by
          rfl
        rw [huv]
        have hpow : (IsLocalRing.maximalIdeal A) ^ n *
            (IsLocalRing.maximalIdeal A) ^ n ≤
            (IsLocalRing.maximalIdeal A) ^ (n + 1) := by
          calc
            (IsLocalRing.maximalIdeal A) ^ n *
                (IsLocalRing.maximalIdeal A) ^ n =
              (IsLocalRing.maximalIdeal A) ^ (n + n) :=
                (Ideal.IsTwoSided.pow_add
                  (I := IsLocalRing.maximalIdeal A) n n).symm
            _ ≤ (IsLocalRing.maximalIdeal A) ^ (n + 1) :=
              Ideal.pow_le_pow_right (by omega)
        have hprod :
            ((((Additive.toMul u : chapter10UnitFiltration A n) : Aˣ) : A) - 1) *
                ((((Additive.toMul v : chapter10UnitFiltration A n) : Aˣ) : A) - 1) ∈
              (IsLocalRing.maximalIdeal A) ^ (n + 1) := by
          exact hpow (Ideal.mul_mem_mul (Additive.toMul u).property
            (Additive.toMul v).property)
        (convert hprod using 1; ring) }
  let ψ : chapter10UnitFiltration A n →*
      Multiplicative (Chapter10IdealLayer A (IsLocalRing.maximalIdeal A) n) :=
    AddMonoidHom.toMultiplicativeRight φ
  have hker : ψ.ker =
      (chapter10UnitFiltration A (n + 1)).subgroupOf
        (chapter10UnitFiltration A n) := by
    ext u
    constructor
    · intro hu
      have hu' : φ (Additive.ofMul u) = 0 := by
        simpa [ψ] using hu
      change ((u : Aˣ) : A) - 1 ∈
        (IsLocalRing.maximalIdeal A) ^ (n + 1)
      have hu'' :
          Submodule.Quotient.mk
              (p := chapter10IdealLayerDenominator A
                (IsLocalRing.maximalIdeal A) n)
              (⟨((u : Aˣ) : A) - 1, u.property⟩ :
                (IsLocalRing.maximalIdeal A ^ n : Ideal A)) = 0 := by
        change Submodule.Quotient.mk
            (p := chapter10IdealLayerDenominator A
              (IsLocalRing.maximalIdeal A) n)
            (⟨((u : Aˣ) : A) - 1, u.property⟩ :
              (IsLocalRing.maximalIdeal A ^ n : Ideal A)) = 0 at hu'
        exact hu'
      have hmem := (Submodule.Quotient.mk_eq_zero _).mp hu''
      change ((u : Aˣ) : A) - 1 ∈
        (IsLocalRing.maximalIdeal A) ^ (n + 1) at hmem
      exact hmem
    · intro hu
      change ((u : Aˣ) : A) - 1 ∈
        (IsLocalRing.maximalIdeal A) ^ (n + 1) at hu
      apply MonoidHom.mem_ker.mpr
      change φ (Additive.ofMul u) = 0
      change Submodule.Quotient.mk
          (p := chapter10IdealLayerDenominator A
            (IsLocalRing.maximalIdeal A) n)
          (⟨((u : Aˣ) : A) - 1, u.property⟩ :
            (IsLocalRing.maximalIdeal A ^ n : Ideal A)) = 0
      apply (Submodule.Quotient.mk_eq_zero _).2
      simpa [chapter10IdealLayerDenominator] using hu
  have hsurj : Function.Surjective ψ := by
    intro z
    let q : Chapter10IdealLayer A (IsLocalRing.maximalIdeal A) n :=
      Multiplicative.toAdd z
    obtain ⟨r, hrq⟩ := Submodule.Quotient.mk_surjective _ q
    have hp : (IsLocalRing.maximalIdeal A) ^ n ≤
        IsLocalRing.maximalIdeal A := by
      simpa [pow_one] using
        (Ideal.pow_le_pow_right (I := IsLocalRing.maximalIdeal A) hn)
    have hrmax : (r : A) ∈ IsLocalRing.maximalIdeal A := hp r.property
    have hnegmax : -(r : A) ∈ IsLocalRing.maximalIdeal A :=
      (IsLocalRing.maximalIdeal A).neg_mem hrmax
    have hneg : -(r : A) ∈ nonunits A :=
      (IsLocalRing.mem_maximalIdeal (-(r : A))).1 hnegmax
    have hu : IsUnit (1 + (r : A)) := by
      have h := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
        (-(r : A)) hneg
      (convert h using 1; ring)
    let w : Aˣ := hu.unit
    have hw : (w : A) - 1 = (r : A) := by
      dsimp [w]
      ring
    have hwmem : (w : A) - 1 ∈
        (IsLocalRing.maximalIdeal A) ^ n := by
      rw [hw]
      exact r.property
    let u : chapter10UnitFiltration A n := ⟨w, hwmem⟩
    refine ⟨u, ?_⟩
    have hφq : φ (Additive.ofMul u) = q := by
      rw [← hrq]
      change Submodule.Quotient.mk
          (⟨((u : Aˣ) : A) - 1, u.property⟩ :
            (IsLocalRing.maximalIdeal A ^ n : Ideal A)) =
        Submodule.Quotient.mk r
      apply (Submodule.Quotient.eq _).2
      change ((u : Aˣ) : A) - 1 - (r : A) ∈
        (IsLocalRing.maximalIdeal A) ^ (n + 1)
      rw [show (u : Aˣ) = w by rfl, hw]
      simp
    change φ (Additive.ofMul u) = q
    exact hφq
  let eMul := QuotientGroup.liftEquiv
    ((chapter10UnitFiltration A (n + 1)).subgroupOf
      (chapter10UnitFiltration A n)) hsurj hker.symm
  refine ⟨eMul.symm, ?_⟩
  intro u
  apply eMul.injective
  rw [eMul.apply_symm_apply]
  unfold eMul
  simp [ψ, φ]
  rfl

/-- The error in multiplying `1+x` and `1+y` is one layer deeper. -/
theorem chapter10_higher_layer_multiplication_linearizes
    {L : Type*} [Field L] (A : ValuationSubring L) (n : ℕ) (hn : 0 < n)
    (x y : A)
    (hx : x ∈ (IsLocalRing.maximalIdeal A) ^ n)
    (hy : y ∈ (IsLocalRing.maximalIdeal A) ^ n) :
    x * y ∈ (IsLocalRing.maximalIdeal A) ^ (n + 1) ∧
      (1 + x) * (1 + y) - (1 + (x + y)) ∈
        (IsLocalRing.maximalIdeal A) ^ (n + 1) := by
  constructor
  · have hpow :
        (IsLocalRing.maximalIdeal A) ^ n *
            (IsLocalRing.maximalIdeal A) ^ n ≤
          (IsLocalRing.maximalIdeal A) ^ (n + 1) := by
      calc
        (IsLocalRing.maximalIdeal A) ^ n *
            (IsLocalRing.maximalIdeal A) ^ n =
          (IsLocalRing.maximalIdeal A) ^ (n + n) :=
            (Ideal.IsTwoSided.pow_add
              (I := IsLocalRing.maximalIdeal A) n n).symm
        _ ≤ (IsLocalRing.maximalIdeal A) ^ (n + 1) :=
          Ideal.pow_le_pow_right (by omega)
    exact hpow (Ideal.mul_mem_mul hx hy)
  · convert (show x * y ∈ (IsLocalRing.maximalIdeal A) ^ (n + 1) from by
      have hpow :
          (IsLocalRing.maximalIdeal A) ^ n *
              (IsLocalRing.maximalIdeal A) ^ n ≤
            (IsLocalRing.maximalIdeal A) ^ (n + 1) := by
        calc
          (IsLocalRing.maximalIdeal A) ^ n *
              (IsLocalRing.maximalIdeal A) ^ n =
            (IsLocalRing.maximalIdeal A) ^ (n + n) :=
              (Ideal.IsTwoSided.pow_add
                (I := IsLocalRing.maximalIdeal A) n n).symm
          _ ≤ (IsLocalRing.maximalIdeal A) ^ (n + 1) :=
            Ideal.pow_le_pow_right (by omega)
      exact hpow (Ideal.mul_mem_mul hx hy)) using 1; ring

/-- Multiplication by a residue scalar on the `n`th additive layer. -/
def chapter10ResiduePowerScaling
    {L : Type*} [Field L] (A : ValuationSubring L) (u : Aˣ) (n : ℕ) :
    Chapter10ResidueField A →+ Chapter10ResidueField A where
  toFun a := ((chapter10UnitReduction A u) ^ n : Chapter10ResidueField A) * a
  map_zero' := by simp
  map_add' a b := by simp [mul_add]

/- The coordinate map itself depends on the chosen uniformizer; its existence
   is the noncanonical part of the layer identification. -/
noncomputable def chapter10UniformizerLayerCoordinate
    {L : Type*} [Field L] (A : ValuationSubring L)
    [IsDiscreteValuationRing A] (π : A)
    (hπ : Chapter10Uniformizer A π) (n : ℕ) (hn : 0 < n) :
    Multiplicative (Chapter10ResidueField A) →*
      Chapter10UnitLayerQuotient A n := by
  let hπ' : Irreducible π :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer (R := A) π).2 hπ.2
  let e : Multiplicative
      (Chapter10IdealLayer A (IsLocalRing.maximalIdeal A) n) ≃*
        Chapter10UnitLayerQuotient A n :=
    Classical.choose (chapter10_higher_unit_layer_is_additive A n hn)
  let g :=
    (LastLib.Book01ValuationsDVRsAndCompletions.Chapter05.chapterLayerMultiplicationMap
      (A := A) π hπ' n)
  let f : Chapter10ResidueField A →+
      Chapter10IdealLayer A (IsLocalRing.maximalIdeal A) n := by
    exact
      { toFun := fun a => g a
        map_zero' := by exact g.map_zero
        map_add' := by intro a b; exact g.map_add a b }
  exact e.toMonoidHom.comp (AddMonoidHom.toMultiplicativeRight f)

/-- The uniformizer coordinate identifies the residue field with the unit layer. -/
theorem chapter10_uniformizer_layer_coordinate_bijective
    {L : Type*} [Field L] (A : ValuationSubring L)
    [IsDiscreteValuationRing A] (π : A)
    (hπ : Chapter10Uniformizer A π) (n : ℕ) (hn : 0 < n) :
    Function.Bijective
      (chapter10UniformizerLayerCoordinate A π hπ n hn) := by
  classical
  dsimp [chapter10UniformizerLayerCoordinate]
  apply Function.Bijective.comp
  · exact (Classical.choose (chapter10_higher_unit_layer_is_additive A n hn)).bijective
  · let g :=
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter05.chapterLayerMultiplicationMap
        (A := A) π
        ((IsDiscreteValuationRing.irreducible_iff_uniformizer (R := A) π).2 hπ.2) n)
    have hg : Function.Bijective g :=
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter05.chapterLayerMultiplicationMap_bijective
        (A := A) π
        ((IsDiscreteValuationRing.irreducible_iff_uniformizer (R := A) π).2 hπ.2) n
    constructor
    · intro x y hxy
      exact hg.1 hxy
    · intro z
      obtain ⟨x, hx⟩ := hg.2 (Multiplicative.toAdd z)
      refine ⟨Multiplicative.ofAdd x, ?_⟩
      exact hx

/-- A change `π ↦ uπ` rescales the `n`th coordinate by the residue of `uⁿ`. -/
theorem chapter10_uniformizer_change_rescales_layer
    {L : Type*} [Field L] (A : ValuationSubring L)
    [IsDiscreteValuationRing A]
    (π π' : A) (u : Aˣ) (n : ℕ) (hn : 0 < n)
    (hπ : Chapter10Uniformizer A π)
    (hπ' : Chapter10Uniformizer A π')
    (hchange : π' = (u : A) * π) :
    ∀ a : Chapter10ResidueField A,
      chapter10UniformizerLayerCoordinate A π' hπ' n hn (Multiplicative.ofAdd a) =
        chapter10UniformizerLayerCoordinate A π hπ n hn
          (Multiplicative.ofAdd (chapter10ResiduePowerScaling A u n a)) := by
  intro a
  classical
  dsimp [chapter10UniformizerLayerCoordinate]
  congr 1
  change
    (LastLib.Book01ValuationsDVRsAndCompletions.Chapter05.chapterLayerMultiplicationMap
      (A := A) π'
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer (R := A) π').2 hπ'.2) n) a =
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter05.chapterLayerMultiplicationMap
        (A := A) π
        ((IsDiscreteValuationRing.irreducible_iff_uniformizer (R := A) π).2 hπ.2) n)
        ((chapter10ResiduePowerScaling A u n) a)
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [LastLib.Book01ValuationsDVRsAndCompletions.Chapter05.chapterLayerMultiplicationMap_apply
    (A := A) π' ((IsDiscreteValuationRing.irreducible_iff_uniformizer (R := A) π').2 hπ'.2) n r]
  change
    (LastLib.Book01ValuationsDVRsAndCompletions.Chapter05.chapterLayerRepresentative
      (A := A) π'
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer (R := A) π').2 hπ'.2) n r) =
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter05.chapterLayerMultiplicationMap
        (A := A) π
        ((IsDiscreteValuationRing.irreducible_iff_uniformizer (R := A) π).2 hπ.2) n)
        (Ideal.Quotient.mk _ (((u : A) ^ n) * r))
  rw [LastLib.Book01ValuationsDVRsAndCompletions.Chapter05.chapterLayerMultiplicationMap_apply
    (A := A) π
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer (R := A) π).2 hπ.2) n (((u : A) ^ n) * r)]
  apply (Submodule.Quotient.eq _).2
  change r * π' ^ n - ((u : A) ^ n * r) * π ^ n ∈
    (IsLocalRing.maximalIdeal A) ^ (n + 1)
  rw [hchange]
  simp [mul_pow]
  ring_nf
  simp

private theorem chapter10_unit_quotient_cardinality_aux
    {L : Type*} [Field L] (A : ValuationSubring L) (n : ℕ) (hn : 0 < n)
    [Fintype (Chapter10ResidueField A)]
    (hDVR : IsDiscreteValuationRing A) :
    Nat.card (Chapter10UnitRingQuotient A n) =
      (Fintype.card (Chapter10ResidueField A) - 1) *
        Fintype.card (Chapter10ResidueField A) ^ (n - 1) := by
  classical
  let _ : IsDiscreteValuationRing A := hDVR
  let q := Fintype.card (Chapter10ResidueField A)
  let U : ℕ → Subgroup Aˣ := chapter10UnitFiltration A
  obtain ⟨π, hπirr⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hπ : Chapter10Uniformizer A π := by
    refine ⟨?_, hπirr.maximalIdeal_eq⟩
    rw [hπirr.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self π
  have hdesc : ∀ {a b : ℕ}, a ≤ b → U b ≤ U a := by
    intro a b hab v hv
    change ((v : A) - 1) ∈ (IsLocalRing.maximalIdeal A) ^ b at hv
    change ((v : A) - 1) ∈ (IsLocalRing.maximalIdeal A) ^ a
    exact (Ideal.pow_le_pow_right hab) hv
  have hendpoint (j : ℕ) :
      Nat.card (Aˣ ⧸ U j) = (U j).relIndex (⊤ : Subgroup Aˣ) := by
    rw [Subgroup.relIndex_top_right, Subgroup.index_eq_card]
  have hbase : Nat.card (Aˣ ⧸ U 1) = q - 1 := by
    dsimp [U]
    obtain ⟨e⟩ := chapter10_first_unit_quotient_equiv_residue_units A
    rw [Nat.card_congr e.toEquiv]
    simpa [q, Nat.card_eq_fintype_card] using
      (Fintype.card_units (Chapter10ResidueField A))
  have hlayer (j : ℕ) (hj : 0 < j) :
      (U (j + 1)).relIndex (U j) = q := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card]
    change Nat.card (Chapter10UnitLayerQuotient A j) = q
    let f := chapter10UniformizerLayerCoordinate A π hπ j hj
    have hf : Function.Bijective f := by
      exact chapter10_uniformizer_layer_coordinate_bijective A π hπ j hj
    rw [← Nat.card_congr (Equiv.ofBijective f hf)]
    simp [q]
  have hmain : ∀ k : ℕ,
      Nat.card (Aˣ ⧸ U (k + 1)) = (q - 1) * q ^ k := by
    intro k
    induction k with
    | zero =>
        simpa using hbase
    | succ k ih =>
        have hmul := Subgroup.relIndex_mul_relIndex
          (U (k + 2)) (U (k + 1)) (⊤ : Subgroup Aˣ)
          (hdesc (by omega)) le_top
        calc
          Nat.card (Aˣ ⧸ U (k + 2)) =
              (U (k + 2)).relIndex (⊤ : Subgroup Aˣ) := hendpoint (k + 2)
          _ = (U (k + 2)).relIndex (U (k + 1)) *
                (U (k + 1)).relIndex (⊤ : Subgroup Aˣ) := hmul.symm
          _ = q * Nat.card (Aˣ ⧸ U (k + 1)) := by
            rw [hlayer (k + 1) (by omega), ← hendpoint (k + 1)]
          _ = (q - 1) * q ^ (k + 1) := by
            rw [ih]
            ring
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simpa [U, q] using hmain k

/-- The finite-precision unit quotient has set-theoretic valuation, residue,
and additive-layer coordinates; no group splitting of the successive layers
is asserted. -/
structure Chapter10UnitQuotientCoordinateProfile
    {L : Type*} [Field L] (A : ValuationSubring L) (n : ℕ) where
  equivalence :
    Chapter10FieldUnitQuotient A n ≃
        (Multiplicative ℤ ×
        ((Chapter10ResidueField A)ˣ ×
          (Fin (n - 1) → Multiplicative (Chapter10ResidueField A))))

/-- The coordinate profile asserted by the successive-layer decomposition. -/
theorem chapter10_unit_quotient_has_coordinates
    {L : Type*} [Field L] (A : ValuationSubring L) (n : ℕ) (hn : 0 < n)
    [Fintype (Chapter10ResidueField A)]
    [Valuation.IsRankOneDiscrete A.valuation]
    (hDVR : IsDiscreteValuationRing A)
    (π : A) (hπ : Chapter10Uniformizer A π) :
    Nonempty (Chapter10UnitQuotientCoordinateProfile A n) := by
  classical
  let _ : IsDiscreteValuationRing A := hDVR
  let U : ℕ → Subgroup Aˣ := chapter10UnitFiltration A
  let q := Fintype.card (Chapter10ResidueField A)
  have hqpos : 0 < q := by
    dsimp [q]
    exact Fintype.card_pos
  have hq1pos : 0 < q - 1 := by
    dsimp [q]
    rw [← Fintype.card_units]
    exact Fintype.card_pos
  let _ : Finite (Aˣ ⧸ U n) := by
    apply Nat.finite_of_card_ne_zero
    change Nat.card (Chapter10UnitRingQuotient A n) ≠ 0
    rw [chapter10_unit_quotient_cardinality_aux A n hn hDVR]
    exact Nat.mul_ne_zero (Nat.ne_of_gt hq1pos)
      (pow_ne_zero _ (Nat.ne_of_gt hqpos))
  let _ : Fintype (Aˣ ⧸ U n) := Fintype.ofFinite _
  have hring_card :
      Fintype.card (Aˣ ⧸ U n) =
        Fintype.card
          ((Chapter10ResidueField A)ˣ ×
            (Fin (n - 1) → Multiplicative (Chapter10ResidueField A))) := by
    calc
      Fintype.card (Aˣ ⧸ U n) = Nat.card (Aˣ ⧸ U n) :=
        (Nat.card_eq_fintype_card).symm
      _ = (Fintype.card (Chapter10ResidueField A) - 1) *
          Fintype.card (Chapter10ResidueField A) ^ (n - 1) := by
        simpa [U] using
          chapter10_unit_quotient_cardinality_aux A n hn hDVR
      _ = Fintype.card
          ((Chapter10ResidueField A)ˣ ×
            (Fin (n - 1) → Multiplicative (Chapter10ResidueField A))) := by
        simp [Fintype.card_units]
  let eRing : (Aˣ ⧸ U n) ≃
      ((Chapter10ResidueField A)ˣ ×
        (Fin (n - 1) → Multiplicative (Chapter10ResidueField A))) :=
    Fintype.equivOfCardEq hring_card
  let V : ℕ → Subgroup Lˣ := chapter10FieldUnitFiltration A
  have hUn0 : U n ≤ U 0 := by
    intro u hu
    change ((u : A) - 1) ∈ (IsLocalRing.maximalIdeal A) ^ n at hu
    change ((u : A) - 1) ∈ (IsLocalRing.maximalIdeal A) ^ 0
    exact (Ideal.pow_le_pow_right (Nat.zero_le n)) hu
  have hV : V n ≤ V 0 := by
    intro x hx
    change x ∈
      (chapter10UnitFiltration A n).map (Units.map A.subtype.toMonoidHom) at hx
    rcases hx with ⟨u, hu, rfl⟩
    exact ⟨u, hUn0 hu, rfl⟩
  let f : Aˣ →* V 0 :=
    { toFun := fun u =>
        ⟨Units.map A.subtype.toMonoidHom u, by
          change Units.map A.subtype.toMonoidHom u ∈
            (chapter10UnitFiltration A 0).map (Units.map A.subtype.toMonoidHom)
          refine ⟨u, ?_, rfl⟩
          simp [chapter10UnitFiltration,
            LastLib.Book01ValuationsDVRsAndCompletions.Chapter08.Chapter08UnitLayer]⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro u v
        apply Subtype.ext
        simp }
  have hf_surj : Function.Surjective f := by
    intro x
    rcases x.property with ⟨u, hu, hux⟩
    refine ⟨(u : Aˣ), ?_⟩
    apply Subtype.ext
    exact hux
  have hf_inj : Function.Injective f := by
    intro u v huv
    apply Units.ext
    apply Subtype.ext
    exact congrArg (fun x : V 0 => ((x : Lˣ) : L)) huv
  let ef : Aˣ ≃* V 0 := MulEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  let F : Aˣ →* (V 0 ⧸ (V n).subgroupOf (V 0)) :=
    (QuotientGroup.mk' ((V n).subgroupOf (V 0))).comp ef.toMonoidHom
  have hFsurj : Function.Surjective F := by
    exact (QuotientGroup.mk'_surjective _).comp ef.surjective
  have hker : F.ker = U n := by
    ext u
    constructor
    · intro hu
      change F u = 1 at hu
      have huV : (ef u : V 0) ∈ (V n).subgroupOf (V 0) :=
        (QuotientGroup.eq_one_iff _).mp hu
      change (ef u : Lˣ) ∈ V n at huV
      rcases huV with ⟨a, ha, hEq⟩
      have heq : ef u = ef (a : Aˣ) := by
        apply Subtype.ext
        change Units.map A.subtype.toMonoidHom u =
          Units.map A.subtype.toMonoidHom (a : Aˣ)
        exact hEq.symm
      rw [ef.injective heq]
      exact ha
    · intro hu
      apply MonoidHom.mem_ker.mpr
      change QuotientGroup.mk' ((V n).subgroupOf (V 0)) (ef u) = 1
      apply (QuotientGroup.eq_one_iff _).2
      change (ef u : Lˣ) ∈ V n
      change Units.map A.subtype.toMonoidHom u ∈
        (chapter10UnitFiltration A n).map (Units.map A.subtype.toMonoidHom)
      exact ⟨u, hu, rfl⟩
  let eV : (Aˣ ⧸ U n) ≃* (V 0 ⧸ (V n).subgroupOf (V 0)) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective F hFsurj)
  have hfil : V 0 = (Units.map A.subtype.toMonoidHom).range := by
    dsimp [V]
    have hU0 : chapter10UnitFiltration A 0 = (⊤ : Subgroup Aˣ) := by
      ext u
      simp [chapter10UnitFiltration,
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter08.Chapter08UnitLayer]
    rw [chapter10FieldUnitFiltration, hU0]
    ext x
    constructor
    · rintro ⟨u, -, rfl⟩
      exact ⟨u, rfl⟩
    · rintro ⟨u, rfl⟩
      exact ⟨u, trivial, rfl⟩
  let hπ' : Irreducible π :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer (R := A) π).2 hπ.2
  let eZ' :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter05.chapter_field_unit_quotient_equiv_int
      (A := A) (K := L) π hπ'
  have hZ : Nonempty (Chapter10FieldUnitQuotient A 0 ≃* Multiplicative ℤ) := by
    change Nonempty (Lˣ ⧸ V 0 ≃* Multiplicative ℤ)
    rw [hfil]
    exact ⟨eZ'⟩
  obtain ⟨eZ⟩ := hZ
  let eField : Chapter10FieldUnitQuotient A n ≃
      (Multiplicative ℤ ×
        ((Chapter10ResidueField A)ˣ ×
          (Fin (n - 1) → Multiplicative (Chapter10ResidueField A)))) :=
    (Subgroup.quotientEquivProdOfLE hV).trans
      (eZ.toEquiv.prodCongr (eV.symm.toEquiv.trans eRing))
  refine ⟨{ equivalence := ?_ }⟩
  exact eField

/-- The valuation-only quotient is the infinite cyclic magnitude coordinate. -/
theorem chapter10_field_unit_quotient_by_ring_units
    {L : Type*} [Field L] (A : ValuationSubring L)
    [Valuation.IsRankOneDiscrete A.valuation]
    (π : A) (hπ : Chapter10Uniformizer A π) :
  Nonempty (Chapter10FieldUnitQuotient A 0 ≃* Multiplicative ℤ) := by
  classical
  have hDVR : IsDiscreteValuationRing A := by
    rw [← ValuationSubring.valuationSubring_valuation A]
    infer_instance
  let _ : IsDiscreteValuationRing A := hDVR
  let hU0 : chapter10UnitFiltration A 0 = (⊤ : Subgroup Aˣ) := by
    ext u
    simp [chapter10UnitFiltration,
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter08.Chapter08UnitLayer]
  have hfil : chapter10FieldUnitFiltration A 0 =
      (Units.map A.subtype.toMonoidHom).range := by
    rw [chapter10FieldUnitFiltration, hU0]
    ext x
    constructor
    · rintro ⟨u, -, rfl⟩
      exact ⟨u, rfl⟩
    · rintro ⟨u, rfl⟩
      exact ⟨u, trivial, rfl⟩
  let hπ' : Irreducible π :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer (R := A) π).2 hπ.2
  let e :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter05.chapter_field_unit_quotient_equiv_int
      (A := A) (K := L) π hπ'
  change Nonempty (Lˣ ⧸ chapter10FieldUnitFiltration A 0 ≃* Multiplicative ℤ)
  rw [hfil]
  exact ⟨e⟩

/-- Finite residue fields give the index `(q-1)q^(n-1)` for `U⁰/Uⁿ`. -/
theorem chapter10_unit_quotient_cardinality
    {L : Type*} [Field L] (A : ValuationSubring L) (n : ℕ) (hn : 0 < n)
    [Fintype (Chapter10ResidueField A)]
    (hDVR : IsDiscreteValuationRing A) :
    Nat.card (Chapter10UnitRingQuotient A n) =
      (Fintype.card (Chapter10ResidueField A) - 1) *
        Fintype.card (Chapter10ResidueField A) ^ (n - 1) := by
  exact chapter10_unit_quotient_cardinality_aux A n hn hDVR

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10
