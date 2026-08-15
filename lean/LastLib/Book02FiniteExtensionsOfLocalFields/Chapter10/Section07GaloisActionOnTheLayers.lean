import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Dependencies

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10

noncomputable section

open Ideal IsLocalRing

private noncomputable def chapter10CanonicalHigherUnitLayerQuotientEquiv
    {L : Type*} [Field L] (A : ValuationSubring L) (n : ℕ) (hn : 0 < n) :
    Chapter10UnitLayerQuotient A n ≃*
      Multiplicative (Chapter10IdealLayer A (IsLocalRing.maximalIdeal A) n) := by
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
  exact eMul

private noncomputable def chapter10CanonicalHigherUnitLayerEquiv
    {L : Type*} [Field L] (A : ValuationSubring L) (n : ℕ) (hn : 0 < n) :
    Multiplicative (Chapter10IdealLayer A (IsLocalRing.maximalIdeal A) n) ≃*
      Chapter10UnitLayerQuotient A n :=
  (chapter10CanonicalHigherUnitLayerQuotientEquiv A n hn).symm

private theorem chapter10CanonicalHigherUnitLayerEquiv_apply
    {L : Type*} [Field L] (A : ValuationSubring L) (n : ℕ) (hn : 0 < n)
    (u : chapter10UnitFiltration A n) :
    chapter10CanonicalHigherUnitLayerEquiv A n hn
        (Multiplicative.ofAdd
          (Submodule.Quotient.mk
            (p := chapter10IdealLayerDenominator A
              (IsLocalRing.maximalIdeal A) n)
            (⟨((u : Aˣ) : A) - 1, by
              simpa [chapter10UnitFiltration, chapter10IdealUnitFiltration]
                using u.property⟩ :
              (IsLocalRing.maximalIdeal A ^ n : Ideal A)))) =
      QuotientGroup.mk'
        ((chapter10UnitFiltration A (n + 1)).subgroupOf
          (chapter10UnitFiltration A n)) u := by
  change (chapter10CanonicalHigherUnitLayerQuotientEquiv A n hn).symm _ = _
  apply (chapter10CanonicalHigherUnitLayerQuotientEquiv A n hn).injective
  rw [(chapter10CanonicalHigherUnitLayerQuotientEquiv A n hn).apply_symm_apply]
  unfold chapter10CanonicalHigherUnitLayerQuotientEquiv
  simp
  rfl

/-! ## 10.7. Galois action on the layers -/

/-- The automorphism group of an algebraic extension over its base field. -/
abbrev Chapter10GaloisAutomorphism
    (K L : Type*) [Field K] [Field L] [Algebra K L] :=
  L ≃ₐ[K] L

/-- The induced action of a ring automorphism on units. -/
def chapter10GaloisUnitAction
    {R : Type*} [CommRing R] (σ : R ≃+* R) : Rˣ →* Rˣ :=
  Units.map σ.toRingHom.toMonoidHom

/-- Stability of the unit filtration under an automorphism of the valuation ring. -/
def Chapter10UnitFiltrationStable
    {L : Type*} [Field L] (A : ValuationSubring L) (σ : A ≃+* A) : Prop :=
  ∀ n : ℕ, ∀ u : Aˣ, u ∈ chapter10UnitFiltration A n →
    chapter10GaloisUnitAction σ u ∈ chapter10UnitFiltration A n

/-- A Galois automorphism preserves every congruence subgroup. -/
theorem chapter10_galois_unit_filtration_stable
    {L : Type*} [Field L] (A : ValuationSubring L) (σ : A ≃+* A)
    (hmax : Ideal.map σ.toRingHom (IsLocalRing.maximalIdeal A) =
      IsLocalRing.maximalIdeal A) :
    Chapter10UnitFiltrationStable A σ := by
  intro n u hu
  change σ.toRingHom ((u : Aˣ) : A) - 1 ∈
    (IsLocalRing.maximalIdeal A) ^ n
  have hmap : Ideal.map σ.toRingHom
        ((IsLocalRing.maximalIdeal A) ^ n) =
      (IsLocalRing.maximalIdeal A) ^ n := by
    rw [Ideal.map_pow, hmax]
  have hu' : (u : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ n := by
    exact hu
  have hmem := Ideal.mem_map_of_mem σ.toRingHom hu'
  rw [hmap] at hmem
  simpa only [map_sub, map_one] using hmem

/-- Compatibility data for the induced residue-field automorphism. -/
def Chapter10ResidueAutomorphismCompatible
    {L : Type*} [Field L] (A : ValuationSubring L)
    (σ : A ≃+* A) (σbar : Chapter10ResidueField A ≃+* Chapter10ResidueField A) : Prop :=
  ∀ a : A,
    σbar (IsLocalRing.residue A a) = IsLocalRing.residue A (σ a)

/-- The inertia condition: the induced residue automorphism is trivial. -/
def Chapter10InertiaElement
    {L : Type*} [Field L] (A : ValuationSubring L)
    (σbar : Chapter10ResidueField A ≃+* Chapter10ResidueField A) : Prop :=
  σbar = RingEquiv.refl (Chapter10ResidueField A)

/-- The first unit quotient sees only the residue automorphism. -/
theorem chapter10_galois_first_quotient_residue_action
    {L : Type*} [Field L] (A : ValuationSubring L) (σ : A ≃+* A)
    (σbar : Chapter10ResidueField A ≃+* Chapter10ResidueField A)
    (hcompat : Chapter10ResidueAutomorphismCompatible A σ σbar) :
    ∀ u : Aˣ,
      chapter10UnitReduction A (chapter10GaloisUnitAction σ u) =
        Units.map σbar.toRingHom.toMonoidHom (chapter10UnitReduction A u) := by
  intro u
  apply Units.ext
  change IsLocalRing.residue A (σ ((u : Aˣ) : A)) =
    σbar (IsLocalRing.residue A ((u : Aˣ) : A))
  exact (hcompat ((u : Aˣ) : A)).symm

/-- Inertia acts trivially on the residue-unit quotient. -/
theorem chapter10_inertia_trivial_on_first_unit_quotient
    {L : Type*} [Field L] (A : ValuationSubring L) (σ : A ≃+* A)
    (σbar : Chapter10ResidueField A ≃+* Chapter10ResidueField A)
    (hcompat : Chapter10ResidueAutomorphismCompatible A σ σbar)
    (hinertia : Chapter10InertiaElement A σbar) :
    ∀ u : Aˣ,
      chapter10UnitReduction A (chapter10GaloisUnitAction σ u) =
        chapter10UnitReduction A u := by
  intro u
  rw [chapter10_galois_first_quotient_residue_action A σ σbar hcompat u,
    hinertia]
  rfl

/-- The coordinate action on the `n`th layer, including the uniformizer ratio. -/
def chapter10GaloisLayerCoordinateAction
    {L : Type*} [Field L] (A : ValuationSubring L)
    (σbar : Chapter10ResidueField A ≃+* Chapter10ResidueField A)
    (c : Aˣ) (n : ℕ) :
    Chapter10ResidueField A →+ Chapter10ResidueField A where
  toFun a := σbar a * ((chapter10UnitReduction A c :
    (Chapter10ResidueField A)ˣ) : Chapter10ResidueField A) ^ n
  map_zero' := by simp
  map_add' a b := by
    rw [map_add]
    ring

/- The ring automorphism induces an action on the corresponding unit-layer
   quotient once it is known to preserve the maximal ideal. -/
noncomputable def chapter10GaloisUnitLayerAction
    {L : Type*} [Field L] (A : ValuationSubring L) (σ : A ≃+* A)
    (hmax : Ideal.map σ.toRingHom (IsLocalRing.maximalIdeal A) =
      IsLocalRing.maximalIdeal A) (n : ℕ) :
    Chapter10UnitLayerQuotient A n →* Chapter10UnitLayerQuotient A n := by
  let U : Subgroup Aˣ := chapter10UnitFiltration A n
  let V : Subgroup U :=
    (chapter10UnitFiltration A (n + 1)).subgroupOf U
  let f : U →* U :=
    { toFun := fun u =>
        ⟨chapter10GaloisUnitAction σ (u : Aˣ),
          (chapter10_galois_unit_filtration_stable A σ hmax) n
            (u : Aˣ) u.property⟩
      map_one' := by
        apply Subtype.ext
        simp [chapter10GaloisUnitAction]
      map_mul' := by
        intro u v
        apply Subtype.ext
        simp [chapter10GaloisUnitAction] }
  exact QuotientGroup.map V V f (by
    intro u hu
    change chapter10GaloisUnitAction σ (u : Aˣ) ∈
      chapter10UnitFiltration A (n + 1)
    exact (chapter10_galois_unit_filtration_stable A σ hmax) (n + 1)
      (u : Aˣ) hu)

/-- An automorphism of the valuation ring acts bijectively on every unit layer. -/
theorem chapter10_galois_unit_layer_action_bijective
    {L : Type*} [Field L] (A : ValuationSubring L) (σ : A ≃+* A)
    (hmax : Ideal.map σ.toRingHom (IsLocalRing.maximalIdeal A) =
      IsLocalRing.maximalIdeal A) (n : ℕ) :
    Function.Bijective (chapter10GaloisUnitLayerAction A σ hmax n) := by
  classical
  let U : Subgroup Aˣ := chapter10UnitFiltration A n
  let V : Subgroup U :=
    (chapter10UnitFiltration A (n + 1)).subgroupOf U
  let f : U →* U :=
    { toFun := fun u =>
        ⟨chapter10GaloisUnitAction σ (u : Aˣ),
          (chapter10_galois_unit_filtration_stable A σ hmax) n
            (u : Aˣ) u.property⟩
      map_one' := by
        apply Subtype.ext
        simp [chapter10GaloisUnitAction]
      map_mul' := by
        intro u v
        apply Subtype.ext
        simp [chapter10GaloisUnitAction] }
  have hf : V ≤ V.comap f := by
    intro u hu
    change chapter10GaloisUnitAction σ (u : Aˣ) ∈
      chapter10UnitFiltration A (n + 1)
    exact (chapter10_galois_unit_filtration_stable A σ hmax) (n + 1)
      (u : Aˣ) hu
  change Function.Bijective (QuotientGroup.map V V f hf)
  have hmaxSymm :
      Ideal.map σ.symm.toRingHom (IsLocalRing.maximalIdeal A) =
        IsLocalRing.maximalIdeal A := by
    calc
      Ideal.map σ.symm.toRingHom (IsLocalRing.maximalIdeal A) =
          Ideal.map σ.symm.toRingHom
            (Ideal.map σ.toRingHom (IsLocalRing.maximalIdeal A)) := by
            rw [hmax]
      _ = IsLocalRing.maximalIdeal A := by
        exact Ideal.map_of_equiv σ
  let f' : U →* U :=
    { toFun := fun u =>
        ⟨chapter10GaloisUnitAction σ.symm (u : Aˣ),
          (chapter10_galois_unit_filtration_stable A σ.symm hmaxSymm) n
            (u : Aˣ) u.property⟩
      map_one' := by
        apply Subtype.ext
        simp [chapter10GaloisUnitAction]
      map_mul' := by
        intro u v
        apply Subtype.ext
        simp [chapter10GaloisUnitAction] }
  have hff' : Function.LeftInverse f' f := by
    intro u
    apply Subtype.ext
    change chapter10GaloisUnitAction σ.symm
        (chapter10GaloisUnitAction σ (u : Aˣ)) = (u : Aˣ)
    apply Units.ext
    change σ.symm (σ ((u : Aˣ) : A)) = ((u : Aˣ) : A)
    exact σ.symm_apply_apply _
  have hf'f : Function.LeftInverse f f' := by
    intro u
    apply Subtype.ext
    change chapter10GaloisUnitAction σ
        (chapter10GaloisUnitAction σ.symm (u : Aˣ)) = (u : Aˣ)
    apply Units.ext
    change σ (σ.symm ((u : Aˣ) : A)) = ((u : Aˣ) : A)
    exact σ.apply_symm_apply _
  have hVf : V ≤ V.comap f' := by
    intro u hu
    change chapter10GaloisUnitAction σ.symm (u : Aˣ) ∈
      chapter10UnitFiltration A (n + 1)
    exact (chapter10_galois_unit_filtration_stable A σ.symm hmaxSymm) (n + 1)
      (u : Aˣ) hu
  have hleft (x : U ⧸ V) :
      QuotientGroup.map V V f' hVf
          (QuotientGroup.map V V f hf x) = x := by
    refine QuotientGroup.induction_on x ?_
    intro u
    change QuotientGroup.mk' V (f' (f u)) = QuotientGroup.mk' V u
    rw [hff' u]
  have hright (x : U ⧸ V) :
      QuotientGroup.map V V f hf
          (QuotientGroup.map V V f' hVf x) = x := by
    refine QuotientGroup.induction_on x ?_
    intro u
    change QuotientGroup.mk' V (f (f' u)) = QuotientGroup.mk' V u
    rw [hf'f u]
  constructor
  · intro x y hxy
    calc
      x = QuotientGroup.map V V f' hVf
          (QuotientGroup.map V V f hf x) := (hleft x).symm
      _ = QuotientGroup.map V V f' hVf
          (QuotientGroup.map V V f hf y) := congrArg _ hxy
      _ = y := hleft y
  · intro y
    refine ⟨QuotientGroup.map V V f' hVf y, hright y⟩

/--
After choosing a uniformizer, the induced action on the `n`th unit layer is
`a ↦ σ̄(a)·(σ(π)/π)ⁿ` in residue coordinates.  The quotient action on the
left is the one induced by the ring automorphism, while `c` records the
ratio `σ(π)/π` inside the valuation ring.
-/
theorem chapter10_galois_higher_layer_coordinate_formula
    {L : Type*} [Field L] (A : ValuationSubring L)
    [IsDiscreteValuationRing A]
    (σ : A ≃+* A)
    (σbar : Chapter10ResidueField A ≃+* Chapter10ResidueField A)
    (π : A) (hπ : Chapter10Uniformizer A π)
    (c : Aˣ) (n : ℕ) :
    (hn : 0 < n) →
    (hmax : Ideal.map σ.toRingHom (IsLocalRing.maximalIdeal A) =
      IsLocalRing.maximalIdeal A) →
    (hcompat : Chapter10ResidueAutomorphismCompatible A σ σbar) →
    (hσπ : σ π = (c : A) * π) →
    ∃ e : Multiplicative (Chapter10ResidueField A) ≃*
        Chapter10UnitLayerQuotient A n,
      ∀ a : Chapter10ResidueField A,
        chapter10GaloisUnitLayerAction A σ hmax n
            (e (Multiplicative.ofAdd a)) =
          e (Multiplicative.ofAdd
            (chapter10GaloisLayerCoordinateAction A σbar c n a)) := by
  intro hn hmax hcompat hσπ
  classical
  let eLayer := chapter10CanonicalHigherUnitLayerEquiv A n hn
  let hπ' : Irreducible π :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer (R := A) π).2 hπ.2
  let g :=
    (LastLib.Book01ValuationsDVRsAndCompletions.Chapter05.chapterLayerMultiplicationMap
      (A := A) π hπ' n)
  let f : Additive (Multiplicative (Chapter10ResidueField A)) →+
      Chapter10IdealLayer A (IsLocalRing.maximalIdeal A) n := by
    exact
      { toFun := fun a => g a
        map_zero' := by
          exact g.map_zero
        map_add' := by
          intro a b
          exact g.map_add a b }
  let coord := eLayer.toMonoidHom.comp
    (AddMonoidHom.toMultiplicativeRight f)
  have hcoord : Function.Bijective coord :=
    by
      dsimp [coord]
      apply Function.Bijective.comp
      · exact eLayer.bijective
      · have hg : Function.Bijective g :=
          LastLib.Book01ValuationsDVRsAndCompletions.Chapter05.chapterLayerMultiplicationMap_bijective
            (A := A) π hπ' n
        constructor
        · intro x y hxy
          change g x = g y at hxy
          exact hg.1 hxy
        · intro z
          obtain ⟨x, hx⟩ := hg.2 z
          refine ⟨Multiplicative.ofAdd x, ?_⟩
          change g x = z
          exact hx
  let e : Multiplicative (Chapter10ResidueField A) ≃*
      Chapter10UnitLayerQuotient A n := MulEquiv.ofBijective coord hcoord
  refine ⟨e, ?_⟩
  intro a
  change chapter10GaloisUnitLayerAction A σ hmax n
      (eLayer (Multiplicative.ofAdd (g a))) =
    eLayer (Multiplicative.ofAdd
      (g (chapter10GaloisLayerCoordinateAction A σbar c n a)))
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
  dsimp [chapter10GaloisLayerCoordinateAction]
  change chapter10GaloisUnitLayerAction A σ hmax n
      (eLayer (Multiplicative.ofAdd
        (g (Ideal.Quotient.mk _ r)))) =
    eLayer (Multiplicative.ofAdd
      (g (σbar (IsLocalRing.residue A r) *
        (((chapter10UnitReduction A c : (Chapter10ResidueField A)ˣ) :
          Chapter10ResidueField A) ^ n))))
  have hgm : g (Ideal.Quotient.mk _ r) =
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter05.chapterLayerRepresentative
        (A := A) π hπ' n r := by
    dsimp [g]
    exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter05.chapterLayerMultiplicationMap_apply
      (A := A) π hπ' n r
  rw [hgm]
  have hxp : (r : A) * π ^ n ∈
      (IsLocalRing.maximalIdeal A) ^ n := by
    rw [hπ'.maximalIdeal_eq, Ideal.span_singleton_pow]
    exact Ideal.mul_mem_left _ r (Ideal.mem_span_singleton_self _)
  have hp_le : (IsLocalRing.maximalIdeal A) ^ n ≤
      IsLocalRing.maximalIdeal A := by
    simpa [pow_one] using
      (Ideal.pow_le_pow_right (I := IsLocalRing.maximalIdeal A) hn)
  have hxmax : (r : A) * π ^ n ∈ IsLocalRing.maximalIdeal A := hp_le hxp
  have hxneg : -((r : A) * π ^ n) ∈ nonunits A :=
    (IsLocalRing.mem_maximalIdeal (-((r : A) * π ^ n))).1
      ((IsLocalRing.maximalIdeal A).neg_mem hxmax)
  have hunit : IsUnit (1 + (r : A) * π ^ n) := by
    have h := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
      (-((r : A) * π ^ n)) hxneg
    (convert h using 1; ring)
  let w : Aˣ := hunit.unit
  have hw : (w : A) - 1 = (r : A) * π ^ n := by
    dsimp [w]
    ring
  have hwmem : (w : A) - 1 ∈
      (IsLocalRing.maximalIdeal A) ^ n := by
    rw [hw]
    exact hxp
  let u : chapter10UnitFiltration A n := ⟨w, hwmem⟩
  let q_u : Chapter10IdealLayer A (IsLocalRing.maximalIdeal A) n :=
    Submodule.Quotient.mk
      (p := chapter10IdealLayerDenominator A (IsLocalRing.maximalIdeal A) n)
      (⟨((u : Aˣ) : A) - 1, by
        simpa [chapter10UnitFiltration, chapter10IdealUnitFiltration]
          using u.property⟩ :
        (IsLocalRing.maximalIdeal A ^ n : Ideal A))
  have hrep :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter05.chapterLayerRepresentative
        (A := A) π hπ' n r = q_u := by
    dsimp [q_u]
    apply (Submodule.Quotient.eq _).2
    change (r : A) * π ^ n - (((u : Aˣ) : A) - 1) ∈
      (IsLocalRing.maximalIdeal A) ^ (n + 1)
    rw [show (u : Aˣ) = w by rfl, hw]
    simp
  have he_u : eLayer (Multiplicative.ofAdd q_u) =
      QuotientGroup.mk'
        ((chapter10UnitFiltration A (n + 1)).subgroupOf
          (chapter10UnitFiltration A n)) u := by
    exact chapter10CanonicalHigherUnitLayerEquiv_apply A n hn u
  rw [hrep, he_u]
  dsimp [chapter10GaloisUnitLayerAction]
  let uσ : chapter10UnitFiltration A n :=
    ⟨chapter10GaloisUnitAction σ (u : Aˣ),
      (chapter10_galois_unit_filtration_stable A σ hmax) n
        (u : Aˣ) u.property⟩
  change QuotientGroup.mk'
      ((chapter10UnitFiltration A (n + 1)).subgroupOf
        (chapter10UnitFiltration A n)) uσ =
    eLayer (Multiplicative.ofAdd
      (g (σbar (IsLocalRing.residue A r) *
        (((chapter10UnitReduction A c : (Chapter10ResidueField A)ˣ) :
          Chapter10ResidueField A) ^ n))))
  let xσ : A := σ r * (c : A) ^ n
  have hσval : ((uσ : Aˣ) : A) - 1 = xσ * π ^ n := by
    dsimp [uσ, chapter10GaloisUnitAction]
    rw [← map_one σ, ← map_sub]
    rw [show ((u : Aˣ) : A) - 1 = (r : A) * π ^ n by exact hw,
      map_mul, map_pow, hσπ]
    dsimp [xσ]
    ring
  have hcoord_res :
      chapter10GaloisLayerCoordinateAction A σbar c n
          (IsLocalRing.residue A r) =
        IsLocalRing.residue A xσ := by
    change σbar (IsLocalRing.residue A r) *
        (((chapter10UnitReduction A c : (Chapter10ResidueField A)ˣ) :
          Chapter10ResidueField A) ^ n) =
      IsLocalRing.residue A xσ
    rw [hcompat r]
    dsimp [xσ, chapter10UnitReduction]
    rw [map_mul, map_pow]
  dsimp [chapter10GaloisLayerCoordinateAction] at hcoord_res
  rw [hcoord_res]
  have hgmσ : g (IsLocalRing.residue A xσ) =
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter05.chapterLayerRepresentative
        (A := A) π hπ' n xσ := by
    change g (Ideal.Quotient.mk _ xσ) = _
    dsimp [g]
    exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter05.chapterLayerMultiplicationMap_apply
      (A := A) π hπ' n xσ
  rw [hgmσ]
  let q_uσ : Chapter10IdealLayer A (IsLocalRing.maximalIdeal A) n :=
    Submodule.Quotient.mk
      (p := chapter10IdealLayerDenominator A (IsLocalRing.maximalIdeal A) n)
      (⟨((uσ : Aˣ) : A) - 1, by
        simpa [chapter10UnitFiltration, chapter10IdealUnitFiltration]
          using uσ.property⟩ :
        (IsLocalRing.maximalIdeal A ^ n : Ideal A))
  have hrepσ :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter05.chapterLayerRepresentative
        (A := A) π hπ' n xσ = q_uσ := by
    dsimp [q_uσ]
    apply (Submodule.Quotient.eq _).2
    change xσ * π ^ n - (((uσ : Aˣ) : A) - 1) ∈
      (IsLocalRing.maximalIdeal A) ^ (n + 1)
    rw [hσval]
    simp
  have he_uσ : eLayer (Multiplicative.ofAdd q_uσ) =
      QuotientGroup.mk'
        ((chapter10UnitFiltration A (n + 1)).subgroupOf
          (chapter10UnitFiltration A n)) uσ := by
    exact chapter10CanonicalHigherUnitLayerEquiv_apply A n hn uσ
  rw [hrepσ, he_uσ]

/-- The inertia character on a higher layer may be nontrivial. -/
def Chapter10InertiaCharacterMayBeNontrivial
    {L : Type*} [Field L] (A : ValuationSubring L) (π : A) : Prop :=
  Chapter10Uniformizer A π ∧
    ∃ (σ : A ≃+* A) (σbar : Chapter10ResidueField A ≃+*
        Chapter10ResidueField A) (c : Aˣ),
      Ideal.map σ.toRingHom (IsLocalRing.maximalIdeal A) =
          IsLocalRing.maximalIdeal A ∧
        Chapter10ResidueAutomorphismCompatible A σ σbar ∧
        Chapter10InertiaElement A σbar ∧
        σ π = (c : A) * π ∧
        chapter10UnitReduction A c ≠ 1

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10
