import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.RegularLocalRing.Defs
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter02.Dependencies
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter02.Section01LocalEquationsModuloUnits

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter02

noncomputable section

open WithZero AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open IsLocalRing Module
open scoped AlgebraicGeometry BigOperators nonZeroDivisors

universe u v

/-!
### 2.4 Orders along a curve
-/

/- The DVR condition at closed points is the precise local consequence of the
   regular integral noetherian curve hypotheses used by the order API. -/
class Chapter02RegularIntegralNoetherianCurve (X : Scheme.{u})
    extends IsIntegral X, IsNoetherian X where
  regular_stalk : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)
  one_dimensional : ∀ x : X, Order.coheight x ≤ 1
  closedPoint_not_generic : ∀ x : X, IsClosed ({x} : Set X) →
    x ≠ genericPoint X

abbrev Chapter02ClosedPoint (X : Scheme.{u}) :=
  {x : X // IsClosed ({x} : Set X)}

theorem chapter02_closed_point_coheight_one
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (x : Chapter02ClosedPoint X) :
    Order.coheight x.1 = 1 := by
  have hlt : x.1 < (⊤ : X) := by
    apply lt_of_le_not_ge le_top
    intro h
    apply C.closedPoint_not_generic x.1 x.2
    exact (Specializes.antisymm (Scheme.le_iff_specializes.mp h)
      (genericPoint_specializes x.1)).eq
  have hpos : 0 < Order.coheight x.1 := Order.coheight_pos_of_lt_top hlt
  exact le_antisymm (C.one_dimensional x.1)
    (Order.one_le_iff_ne_zero.mpr hpos.ne')

theorem chapter02_closed_point_stalk_is_DVR
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (x : Chapter02ClosedPoint X) :
    IsDiscreteValuationRing (X.presheaf.stalk x.1) := by
  let hreg : IsRegularLocalRing (X.presheaf.stalk x.1) := C.regular_stalk x.1
  have hfin' :
      (↑(Module.finrank (ResidueField (X.presheaf.stalk x.1))
        (CotangentSpace (X.presheaf.stalk x.1))) : WithBot ℕ∞) = 1 := by
    calc
      (↑(Module.finrank (ResidueField (X.presheaf.stalk x.1))
        (CotangentSpace (X.presheaf.stalk x.1))) : WithBot ℕ∞) =
          ringKrullDim (X.presheaf.stalk x.1) :=
        (IsRegularLocalRing.iff_finrank_cotangentSpace _).mp inferInstance
      _ = Order.coheight x.1 := ringKrullDim_stalk_eq_coheight x.1
      _ = 1 := by rw [chapter02_closed_point_coheight_one X x]; rfl
  have hfin : Module.finrank (ResidueField (X.presheaf.stalk x.1))
      (CotangentSpace (X.presheaf.stalk x.1)) = 1 := by
    exact_mod_cast hfin'
  exact (IsLocalRing.finrank_CotangentSpace_eq_one_iff).mp hfin

noncomputable def chapter02OrderHom
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (x : Chapter02ClosedPoint X) :
    X.functionField →*₀ ℤᵐ⁰ :=
  X.ordHom x.1 (chapter02_closed_point_coheight_one X x)

noncomputable def chapter02OrderOfRationalFunction
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (x : Chapter02ClosedPoint X) (f : X.functionField) : ℤ :=
  X.ord f x.1

theorem chapter02_order_of_unit
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (U : X.Opens) [Nonempty U] {f : Γ(X, U)} (hf : IsUnit f)
    (x : Chapter02ClosedPoint X) (hx : x.1 ∈ U) :
    chapter02OrderOfRationalFunction X x (X.germToFunctionField U f) = 0 := by
  exact Scheme.ord_of_isUnit hf hx

theorem chapter02_order_mul
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (x : Chapter02ClosedPoint X) {f g : X.functionField}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    chapter02OrderOfRationalFunction X x (f * g) =
      chapter02OrderOfRationalFunction X x f +
        chapter02OrderOfRationalFunction X x g := by
  exact Scheme.ord_mul hf hg

theorem chapter02_order_unchanged_by_regular_unit
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (U : X.Opens) [Nonempty U] {f u : X.functionField}
    (hf : f ≠ 0) (hu : u ≠ 0)
    (hu_unit : ∃ s : Γ(X, U), IsUnit s ∧
      u = X.germToFunctionField U s) (x : Chapter02ClosedPoint X)
    (hx : x.1 ∈ U) :
    chapter02OrderOfRationalFunction X x (f * u) =
      chapter02OrderOfRationalFunction X x f := by
  obtain ⟨s, hs, rfl⟩ := hu_unit
  rw [chapter02_order_mul X x hf (by
    simp [map_ne_zero_iff, Scheme.germToFunctionField_injective, IsUnit.ne_zero hs])]
  rw [chapter02_order_of_unit X U hs x hx]
  simp

def chapter02OrderOfRationalFunctionUnit
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (x : Chapter02ClosedPoint X) : X.functionFieldˣ → ℤ :=
  fun f => chapter02OrderOfRationalFunction X x (f : X.functionField)

theorem chapter02OrderOfRationalFunctionUnit_mul
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (x : Chapter02ClosedPoint X) (f g : X.functionFieldˣ) :
    chapter02OrderOfRationalFunctionUnit X x (f * g) =
      chapter02OrderOfRationalFunctionUnit X x f +
        chapter02OrderOfRationalFunctionUnit X x g := by
  exact chapter02_order_mul X x (Units.ne_zero f) (Units.ne_zero g)

def chapter02OrderHomOnFunctionFieldUnits
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (x : Chapter02ClosedPoint X) : X.functionFieldˣ →* Multiplicative ℤ where
  toFun := fun f => Multiplicative.ofAdd (chapter02OrderOfRationalFunctionUnit X x f)
  map_one' := by
    change Multiplicative.ofAdd
      (chapter02OrderOfRationalFunction X x (1 : X.functionField)) = 1
    simp [chapter02OrderOfRationalFunction, Scheme.ord]
  map_mul' := by
    intro f g
    simpa [chapter02OrderOfRationalFunctionUnit] using
      congrArg Multiplicative.ofAdd (chapter02OrderOfRationalFunctionUnit_mul X x f g)

noncomputable def chapter02StalkAddValuation
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (x : Chapter02ClosedPoint X) :
    AddValuation (X.presheaf.stalk x.1) ℕ∞ :=
  letI := chapter02_closed_point_stalk_is_DVR X x
  IsDiscreteValuationRing.addVal (X.presheaf.stalk x.1)

theorem chapter02_stalk_addVal_uniformizer
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (x : Chapter02ClosedPoint X) {ϖ : X.presheaf.stalk x.1}
    (hϖ : Irreducible ϖ) :
    chapter02StalkAddValuation X x ϖ = 1 := by
  change @IsDiscreteValuationRing.addVal _ _ _
      (chapter02_closed_point_stalk_is_DVR X x) ϖ = 1
  exact @IsDiscreteValuationRing.addVal_uniformizer _ _ _
    (chapter02_closed_point_stalk_is_DVR X x) ϖ hϖ

noncomputable def chapter02NormalizedOrderHom
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (x : Chapter02ClosedPoint X) :
    X.functionField →*₀ ℤᵐ⁰ :=
  X.ordHom x.1 (chapter02_closed_point_coheight_one X x)

theorem chapter02_normalized_order_hom_of_unit
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (U : X.Opens) [Nonempty U] {f : Γ(X, U)} (hf : IsUnit f)
    (x : Chapter02ClosedPoint X) (hx : x.1 ∈ U) :
    chapter02NormalizedOrderHom X x (X.germToFunctionField U f) = 1 := by
  exact Scheme.ordHom_of_isUnit hf (chapter02_closed_point_coheight_one X x) hx

/- LOCAL_DEPENDENCY_GUESS: identify sections of the chosen total quotient
   sheaf with rational functions so that the canonical Mathlib order can be
   applied to a Cartier equation. -/
class Chapter02MeromorphicFunctionFieldMap (X : Scheme.{u})
    [C : Chapter02RegularIntegralNoetherianCurve X]
    [K : Chapter02MeromorphicSheaf X] where
  toFunctionField : ∀ (U : X.Opens) (_hU : Nonempty U),
    Chapter02MeromorphicSection X U →+* X.functionField
  toFunctionField_restrict : ∀ {U V : X.Opens} (h : V ≤ U)
    (hU : Nonempty U) (hV : Nonempty V)
    (s : Chapter02MeromorphicSection X U),
    toFunctionField V hV (chapter02MeromorphicRestriction X h s) =
      toFunctionField U hU s
  toFunctionField_regular : ∀ (U : X.Opens) (hU : Nonempty U) (f : Γ(X, U)),
    letI := hU
    toFunctionField U hU (chapter02RegularSectionMap X U f) =
      X.germToFunctionField U f

def chapter02MeromorphicSectionOrder
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    [K : Chapter02MeromorphicSheaf X] [F : Chapter02MeromorphicFunctionFieldMap X]
    (U : X.Opens) (hU : Nonempty U) (s : Chapter02MeromorphicSection X U)
    (x : Chapter02ClosedPoint X) : ℤ :=
  X.ord (F.toFunctionField U hU s) x.1

class Chapter02CurveCartierOrderAPI (X : Scheme.{u})
    [C : Chapter02RegularIntegralNoetherianCurve X]
    [K : Chapter02MeromorphicSheaf X]
    [F : Chapter02MeromorphicFunctionFieldMap X] where
  order : Chapter02CartierDivisor.{u, v} X → Chapter02ClosedPoint X → ℤ
  local_formula : ∀ (D : Chapter02CartierDivisor.{u, v} X)
    (x : Chapter02ClosedPoint X) (i : D.index) (_hx : x.1 ∈ D.openSet i),
      order D x = chapter02MeromorphicSectionOrder X (D.openSet i)
        ⟨⟨x.1, _hx⟩⟩ (D.equation i) x

def chapter02CartierOrder
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    [K : Chapter02MeromorphicSheaf X] [F : Chapter02MeromorphicFunctionFieldMap X]
    [A : Chapter02CurveCartierOrderAPI X]
    (D : Chapter02CartierDivisor X) (x : Chapter02ClosedPoint X) : ℤ :=
  A.order D x

theorem chapter02_cartier_order_local_formula
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    [K : Chapter02MeromorphicSheaf X] [F : Chapter02MeromorphicFunctionFieldMap X]
    [A : Chapter02CurveCartierOrderAPI X]
    (D : Chapter02CartierDivisor X) (x : Chapter02ClosedPoint X)
    (i : D.index) (hx : x.1 ∈ D.openSet i) :
    chapter02CartierOrder X D x = chapter02MeromorphicSectionOrder X (D.openSet i)
      ⟨⟨x.1, hx⟩⟩ (D.equation i) x := by
  exact A.local_formula D x i hx

theorem chapter02_cartier_order_add
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    [K : Chapter02MeromorphicSheaf X] [F : Chapter02MeromorphicFunctionFieldMap X]
    [A : Chapter02CurveCartierOrderAPI X]
    (D E : Chapter02CartierDivisor.{u, v} X) (x : Chapter02ClosedPoint X) :
    chapter02CartierOrder X (D.add E) x =
      chapter02CartierOrder X D x + chapter02CartierOrder X E x := by
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (D.cover.ge (show x.1 ∈ (⊤ : X.Opens) from trivial))
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (E.cover.ge (show x.1 ∈ (⊤ : X.Opens) from trivial))
  let p : (D.add E).index := ⟨i, j⟩
  let hD : Nonempty (D.openSet i) := ⟨⟨x.1, hi⟩⟩
  let hE : Nonempty (E.openSet j) := ⟨⟨x.1, hj⟩⟩
  let hDE : Nonempty ((D.add E).openSet p) := by
    refine ⟨⟨x.1, ?_⟩⟩
    simpa [p, Chapter02CartierDivisor.add] using (show x.1 ∈ D.openSet i ⊓ E.openSet j from ⟨hi, hj⟩)
  have hDU : (D.add E).openSet p ≤ D.openSet i := by
    simp [p, Chapter02CartierDivisor.add]
  have hEU : (D.add E).openSet p ≤ E.openSet j := by
    simp [p, Chapter02CartierDivisor.add]
  have hDi : F.toFunctionField (D.openSet i) hD
      (D.equation i : Chapter02MeromorphicSection X (D.openSet i)) ≠ 0 := by
    exact IsUnit.ne_zero ((D.equation i).isUnit.map (F.toFunctionField (D.openSet i) hD))
  have hEj : F.toFunctionField (E.openSet j) hE
      (E.equation j : Chapter02MeromorphicSection X (E.openSet j)) ≠ 0 := by
    exact IsUnit.ne_zero ((E.equation j).isUnit.map (F.toFunctionField (E.openSet j) hE))
  have hDi' : F.toFunctionField (D.openSet i ⊓ E.openSet j) hDE
      (chapter02MeromorphicRestriction X inf_le_left
        (D.equation i : Chapter02MeromorphicSection X (D.openSet i))) ≠ 0 := by
    exact IsUnit.ne_zero ((chapter02MeromorphicRestrictionUnit X inf_le_left
      (D.equation i)).isUnit.map (F.toFunctionField (D.openSet i ⊓ E.openSet j) hDE))
  have hEj' : F.toFunctionField (D.openSet i ⊓ E.openSet j) hDE
      (chapter02MeromorphicRestriction X inf_le_right
        (E.equation j : Chapter02MeromorphicSection X (E.openSet j))) ≠ 0 := by
    exact IsUnit.ne_zero ((chapter02MeromorphicRestrictionUnit X inf_le_right
      (E.equation j)).isUnit.map (F.toFunctionField (D.openSet i ⊓ E.openSet j) hDE))
  have hrestrictD := F.toFunctionField_restrict (U := D.openSet i)
    (V := D.openSet i ⊓ E.openSet j) inf_le_left hD hDE
    (D.equation i : Chapter02MeromorphicSection X (D.openSet i))
  have hrestrictE := F.toFunctionField_restrict (U := E.openSet j)
    (V := D.openSet i ⊓ E.openSet j) inf_le_right hE hDE
    (E.equation j : Chapter02MeromorphicSection X (E.openSet j))
  calc
    chapter02CartierOrder X (D.add E) x =
        chapter02MeromorphicSectionOrder X ((D.add E).openSet p) hDE
          ((D.add E).equation p) x := by
      apply chapter02_cartier_order_local_formula X (D.add E) x p
      simpa [p, Chapter02CartierDivisor.add] using
        (show x.1 ∈ D.openSet i ⊓ E.openSet j from ⟨hi, hj⟩)
    _ = chapter02MeromorphicSectionOrder X (D.openSet i) hD (D.equation i) x +
        chapter02MeromorphicSectionOrder X (E.openSet j) hE (E.equation j) x := by
      unfold chapter02MeromorphicSectionOrder
      let a := F.toFunctionField (D.openSet i ⊓ E.openSet j) hDE
        (chapter02MeromorphicRestriction X inf_le_left
          (D.equation i : Chapter02MeromorphicSection X (D.openSet i)))
      let b := F.toFunctionField (D.openSet i ⊓ E.openSet j) hDE
        (chapter02MeromorphicRestriction X inf_le_right
          (E.equation j : Chapter02MeromorphicSection X (E.openSet j)))
      have hmul : X.ord (a * b) x.1 = X.ord a x.1 + X.ord b x.1 := by
        exact chapter02_order_mul X x hDi' hEj'
      calc
        X.ord (F.toFunctionField ((D.add E).openSet p) hDE
            ((D.add E).equation p :
              Chapter02MeromorphicSection X ((D.add E).openSet p))) x.1 =
            X.ord (a * b) x.1 := by
          have hmap := (F.toFunctionField (D.openSet i ⊓ E.openSet j) hDE).map_mul
            (chapter02MeromorphicRestriction X inf_le_left
              (D.equation i : Chapter02MeromorphicSection X (D.openSet i)))
            (chapter02MeromorphicRestriction X inf_le_right
              (E.equation j : Chapter02MeromorphicSection X (E.openSet j)))
          exact congrArg (fun z => X.ord z x.1) hmap
        _ = X.ord a x.1 + X.ord b x.1 := hmul
        _ = X.ord (F.toFunctionField (D.openSet i) hD
            (D.equation i : Chapter02MeromorphicSection X (D.openSet i))) x.1 +
            X.ord (F.toFunctionField (E.openSet j) hE
              (E.equation j : Chapter02MeromorphicSection X (E.openSet j))) x.1 := by
          simpa [a, b] using congrArg₂
            (fun u v => X.ord u x.1 + X.ord v x.1) hrestrictD hrestrictE
    _ = chapter02CartierOrder X D x + chapter02CartierOrder X E x := by
      rw [← chapter02_cartier_order_local_formula X D x i hi,
        ← chapter02_cartier_order_local_formula X E x j hj]

theorem chapter02_cartier_order_neg
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    [K : Chapter02MeromorphicSheaf X] [F : Chapter02MeromorphicFunctionFieldMap X]
    [A : Chapter02CurveCartierOrderAPI X]
    (D : Chapter02CartierDivisor.{u, v} X) (x : Chapter02ClosedPoint X) :
    chapter02CartierOrder X D.neg x = -chapter02CartierOrder X D x := by
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (D.cover.ge (show x.1 ∈ (⊤ : X.Opens) from trivial))
  let hD : Nonempty (D.openSet i) := ⟨⟨x.1, hi⟩⟩
  let i' : D.neg.index := i
  let hDneg : Nonempty (D.neg.openSet i') := by
    simpa [Chapter02CartierDivisor.neg] using hD
  have hf : F.toFunctionField (D.openSet i) hD
      (D.equation i : Chapter02MeromorphicSection X (D.openSet i)) ≠ 0 := by
    exact IsUnit.ne_zero ((D.equation i).isUnit.map (F.toFunctionField (D.openSet i) hD))
  have hmap : F.toFunctionField (D.openSet i) hD
      (↑((D.equation i)⁻¹) : Chapter02MeromorphicSection X (D.openSet i)) =
      (F.toFunctionField (D.openSet i) hD
        (D.equation i : Chapter02MeromorphicSection X (D.openSet i)))⁻¹ := by
    change (Units.map (F.toFunctionField (D.openSet i) hD).toMonoidHom
      ((D.equation i)⁻¹) : X.functionField) = _
    simp
  have hzero : chapter02OrderOfRationalFunction X x (1 : X.functionField) = 0 := by
    simp [chapter02OrderOfRationalFunction, Scheme.ord]
  let a : X.functionField := F.toFunctionField (D.openSet i) hD
    (D.equation i : Chapter02MeromorphicSection X (D.openSet i))
  have ha : a ≠ 0 := by
    simpa [a] using hf
  have hinv : chapter02OrderOfRationalFunction X x (a⁻¹) =
      -chapter02OrderOfRationalFunction X x a := by
    apply eq_neg_of_add_eq_zero_left
    calc
      chapter02OrderOfRationalFunction X x (a⁻¹) +
          chapter02OrderOfRationalFunction X x a =
          chapter02OrderOfRationalFunction X x a +
            chapter02OrderOfRationalFunction X x (a⁻¹) := by
        rw [add_comm]
      _ = chapter02OrderOfRationalFunction X x (a * a⁻¹) :=
        (chapter02_order_mul X x ha (inv_ne_zero ha)).symm
      _ = chapter02OrderOfRationalFunction X x (1 : X.functionField) := by
        rw [mul_inv_cancel₀ ha]
      _ = 0 := hzero
  calc
    chapter02CartierOrder X D.neg x =
        chapter02MeromorphicSectionOrder X (D.neg.openSet i') hDneg
          (D.neg.equation i') x := by
      apply chapter02_cartier_order_local_formula X D.neg x i'
      simpa [i', Chapter02CartierDivisor.neg] using hi
    _ = -chapter02MeromorphicSectionOrder X (D.openSet i) hD
        (D.equation i) x := by
      unfold chapter02MeromorphicSectionOrder
      change chapter02OrderOfRationalFunction X x
          (F.toFunctionField (D.openSet i) hD
            (↑((D.equation i)⁻¹) :
              Chapter02MeromorphicSection X (D.openSet i))) =
        -chapter02OrderOfRationalFunction X x a
      rw [hmap]
      exact hinv
    _ = -chapter02CartierOrder X D x := by
      rw [← chapter02_cartier_order_local_formula X D x i hi]

def chapter02CartierOrderSupport
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    [K : Chapter02MeromorphicSheaf X] [F : Chapter02MeromorphicFunctionFieldMap X]
    [A : Chapter02CurveCartierOrderAPI X]
  (D : Chapter02CartierDivisor X) : Set (Chapter02ClosedPoint X) :=
  {x | chapter02CartierOrder X D x ≠ 0}

private theorem chapter02_finite_closed_subset_omitting_generic
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    {s : Set X} (hs : IsClosed s)
    (hη : genericPoint X ∉ s) : s.Finite := by
  classical
  obtain ⟨S, hSf, hSc, hSi, hsS⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible (α := X) hs
  let g : Set X → X := fun Z =>
    if hZ : Z ∈ S then (hSi Z hZ).genericPoint else genericPoint X
  have hT : (g '' S).Finite := hSf.image g
  apply hT.subset
  intro x hx
  rw [hsS] at hx
  obtain ⟨Z, hZS, hxZ⟩ := Set.mem_sUnion.mp hx
  have hgen : IsGenericPoint (g Z) Z := by
    simp only [g, hZS]
    exact (hSi Z hZS).isGenericPoint_genericPoint (hSc Z hZS)
  have hzmem : g Z ∈ Z := hgen.mem
  have hzlt : g Z < (⊤ : X) := by
    apply lt_of_le_not_ge le_top
    intro htop
    apply hη
    have htopz : g Z = (⊤ : X) :=
      (Specializes.antisymm (Scheme.le_iff_specializes.mp htop)
        (genericPoint_specializes (g Z))).eq
    have hZs : g Z ∈ s := hsS ▸ Set.mem_sUnion.mpr ⟨Z, hZS, hzmem⟩
    change (⊤ : X) ∈ s
    rw [← htopz]
    exact hZs
  have hzcoh : Order.coheight (g Z) = 1 := by
    have hpos : 0 < Order.coheight (g Z) := Order.coheight_pos_of_lt_top hzlt
    exact le_antisymm (C.one_dimensional (g Z))
      (Order.one_le_iff_ne_zero.mpr hpos.ne')
  have hxle : x ≤ g Z := Scheme.le_iff_specializes.mpr (hgen.specializes hxZ)
  have hxeq : x = g Z := by
    by_contra hne
    have hnot : ¬g Z ≤ x := by
      intro hback
      exact hne (Specializes.antisymm (Scheme.le_iff_specializes.mp hback)
        (hgen.specializes hxZ)).eq
    have hlt : x < g Z := lt_of_le_not_ge hxle hnot
    have hgt : Order.coheight (g Z) < Order.coheight x :=
      Order.coheight_strictAnti hlt (by simp [hzcoh])
    rw [hzcoh] at hgt
    exact (not_lt_of_ge (C.one_dimensional x)) hgt
  exact ⟨Z, hZS, hxeq.symm⟩

theorem chapter02_cartier_order_support_finite
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    [K : Chapter02MeromorphicSheaf X] [F : Chapter02MeromorphicFunctionFieldMap X]
    [A : Chapter02CurveCartierOrderAPI X]
    (D : Chapter02CartierDivisor X) :
    Set.Finite (chapter02CartierOrderSupport X D) := by
  classical
  have hfinite : D.support.Finite :=
    chapter02_finite_closed_subset_omitting_generic X
      (chapter02_cartier_support_closed D)
      (chapter02_cartier_support_omits_generic_point D)
  have hpre : (fun x : Chapter02ClosedPoint X => x.1) ⁻¹' D.support |>.Finite := by
    apply hfinite.preimage
    intro x hx y hy hxy
    exact Subtype.ext hxy
  refine hpre.subset ?_
  intro x hx
  change x.1 ∈ D.support
  by_contra hnot
  change ¬ (∀ i (_hx : x.1 ∈ D.openSet i),
    ¬ chapter02MeromorphicSectionIsRegularUnitAt
      (D.openSet i) (D.equation i) x.1) at hnot
  obtain ⟨i, hi⟩ := not_forall.mp hnot
  obtain ⟨hxi, hregnot⟩ := not_forall.mp hi
  have hreg := Classical.not_not.mp hregnot
  obtain ⟨V, hVle, hxV, u, hu⟩ := hreg
  let hD : Nonempty (D.openSet i) := ⟨⟨x.1, hxi⟩⟩
  let hV : Nonempty V := ⟨⟨x.1, hxV⟩⟩
  have hrestrict := F.toFunctionField_restrict (U := D.openSet i) (V := V)
    hVle hD hV (D.equation i : Chapter02MeromorphicSection X (D.openSet i))
  have hfield : F.toFunctionField (D.openSet i) hD
      (D.equation i : Chapter02MeromorphicSection X (D.openSet i)) =
      F.toFunctionField V hV
        (chapter02RegularSectionMap X V (u : Γ(X, V))) := by
    calc
      F.toFunctionField (D.openSet i) hD
          (D.equation i : Chapter02MeromorphicSection X (D.openSet i)) =
          F.toFunctionField V hV
            (chapter02MeromorphicRestriction X hVle
              (D.equation i : Chapter02MeromorphicSection X (D.openSet i))) :=
        hrestrict.symm
      _ = F.toFunctionField V hV
          (chapter02RegularSectionMap X V (u : Γ(X, V))) := by rw [hu]
  have hord0 : chapter02OrderOfRationalFunction X x
      (F.toFunctionField V hV
        (chapter02RegularSectionMap X V (u : Γ(X, V)))) = 0 := by
    rw [F.toFunctionField_regular]
    exact @chapter02_order_of_unit X C V hV (u : Γ(X, V)) u.isUnit x hxV
  have hord := chapter02_cartier_order_local_formula X D x i hxi
  unfold chapter02MeromorphicSectionOrder at hord
  change chapter02CartierOrder X D x =
    chapter02OrderOfRationalFunction X x
      (F.toFunctionField (D.openSet i) hD
        (D.equation i : Chapter02MeromorphicSection X (D.openSet i))) at hord
  rw [hfield, hord0] at hord
  exact hx hord

theorem chapter02_principal_order_support_finite
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (f : X.functionField) :
    Set.Finite {x : Chapter02ClosedPoint X |
      chapter02OrderOfRationalFunction X x f ≠ 0} := by
  classical
  by_cases hf : f = 0
  · simp [hf, chapter02OrderOfRationalFunction, Scheme.ord]
  obtain ⟨U, hUaff, f', hU, hfg, hf'unit⟩ :=
    AlgebraicGeometry.exists_isUnit_germ_eq X f hf
  have hηU : genericPoint X ∈ U := by
    apply ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
    obtain ⟨u⟩ := hU
    exact ⟨u.1, trivial, u.2⟩
  have hfinU : (U : Set X)ᶜ.Finite :=
    chapter02_finite_closed_subset_omitting_generic X
      (isClosed_compl_iff.mpr U.isOpen) (by
        intro h
        exact h hηU)
  have hpre : (fun x : Chapter02ClosedPoint X => x.1) ⁻¹' (U : Set X)ᶜ |>.Finite := by
    apply hfinU.preimage
    intro x hx y hy hxy
    exact Subtype.ext hxy
  refine hpre.subset ?_
  intro x hx
  change x.1 ∉ U
  intro hxU
  apply hx
  rw [← hfg]
  exact @chapter02_order_of_unit X C U hU f' hf'unit x hxU

def chapter02Order
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    [K : Chapter02MeromorphicSheaf X] [F : Chapter02MeromorphicFunctionFieldMap X]
    [A : Chapter02CurveCartierOrderAPI X]
    (D : Chapter02CartierDivisor X) (x : Chapter02ClosedPoint X) : ℤ :=
  chapter02CartierOrder X D x

abbrev Chapter02FormalDivisor (X : Scheme.{u})
    [_C : Chapter02RegularIntegralNoetherianCurve X] :=
  Chapter02ClosedPoint X →₀ ℤ

def chapter02PointCycle
    (X : Scheme.{u}) [_C : Chapter02RegularIntegralNoetherianCurve X]
    (x : Chapter02ClosedPoint X) (n : ℤ) : Chapter02FormalDivisor X :=
  Finsupp.single x n

noncomputable def chapter02FormalDivisorOfCartier
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    [K : Chapter02MeromorphicSheaf X] [F : Chapter02MeromorphicFunctionFieldMap X]
    [A : Chapter02CurveCartierOrderAPI X]
    (D : Chapter02CartierDivisor X) : Chapter02FormalDivisor X :=
  Finsupp.onFinset
    (Set.Finite.toFinset (chapter02_cartier_order_support_finite X D))
    (fun x => chapter02CartierOrder X D x) (by
      intro x hx
      exact (chapter02_cartier_order_support_finite X D).mem_toFinset.mpr hx)

theorem chapter02_formal_divisor_of_cartier_apply
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    [K : Chapter02MeromorphicSheaf X] [F : Chapter02MeromorphicFunctionFieldMap X]
    [A : Chapter02CurveCartierOrderAPI X]
    (D : Chapter02CartierDivisor X) (x : Chapter02ClosedPoint X) :
    chapter02FormalDivisorOfCartier X D x = chapter02CartierOrder X D x := by
  simp [chapter02FormalDivisorOfCartier]

theorem chapter02_cartier_divisor_formal_sum
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    [K : Chapter02MeromorphicSheaf X] [F : Chapter02MeromorphicFunctionFieldMap X]
    [A : Chapter02CurveCartierOrderAPI X]
    (D : Chapter02CartierDivisor X) :
    chapter02FormalDivisorOfCartier X D =
      Finset.sum (chapter02FormalDivisorOfCartier X D).support
        (fun x => chapter02PointCycle X x (chapter02Order X D x)) := by
  symm
  change Finset.sum (chapter02FormalDivisorOfCartier X D).support
      (fun x => Finsupp.single x
        (chapter02FormalDivisorOfCartier X D x)) =
    chapter02FormalDivisorOfCartier X D
  exact Finsupp.sum_single _

theorem chapter02_formal_divisor_of_cartier_add
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    [K : Chapter02MeromorphicSheaf X] [F : Chapter02MeromorphicFunctionFieldMap X]
    [A : Chapter02CurveCartierOrderAPI X]
    (D E : Chapter02CartierDivisor.{u, v} X) :
    chapter02FormalDivisorOfCartier X (D.add E) =
      chapter02FormalDivisorOfCartier X D +
        chapter02FormalDivisorOfCartier X E := by
  ext x
  simp only [chapter02_formal_divisor_of_cartier_apply, Finsupp.add_apply]
  exact chapter02_cartier_order_add X D E x

theorem chapter02_formal_divisor_of_cartier_neg
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    [K : Chapter02MeromorphicSheaf X] [F : Chapter02MeromorphicFunctionFieldMap X]
    [A : Chapter02CurveCartierOrderAPI X]
    (D : Chapter02CartierDivisor.{u, v} X) :
    chapter02FormalDivisorOfCartier X D.neg =
      -chapter02FormalDivisorOfCartier X D := by
  ext x
  simp only [chapter02_formal_divisor_of_cartier_apply, Finsupp.neg_apply]
  exact chapter02_cartier_order_neg X D x

noncomputable def chapter02PrincipalDivisor
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (f : X.functionFieldˣ) : Chapter02FormalDivisor X :=
  Finsupp.onFinset
    (Set.Finite.toFinset (chapter02_principal_order_support_finite X (f : X.functionField)))
    (fun x => chapter02OrderOfRationalFunction X x (f : X.functionField)) (by
      intro x hx
      exact (chapter02_principal_order_support_finite X (f : X.functionField)).mem_toFinset.mpr hx)

theorem chapter02_principal_divisor_apply
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (f : X.functionFieldˣ) (x : Chapter02ClosedPoint X) :
    chapter02PrincipalDivisor X f x =
      chapter02OrderOfRationalFunction X x (f : X.functionField) := by
  simp [chapter02PrincipalDivisor]

theorem chapter02_principal_divisor_mul
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (f g : X.functionFieldˣ) :
    chapter02PrincipalDivisor X (f * g) =
      chapter02PrincipalDivisor X f + chapter02PrincipalDivisor X g := by
  ext x
  simp only [chapter02_principal_divisor_apply, Finsupp.add_apply]
  exact chapter02_order_mul X x (Units.ne_zero f) (Units.ne_zero g)

theorem chapter02_principal_divisor_formal_sum
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (f : X.functionFieldˣ) :
    chapter02PrincipalDivisor X f =
      Finset.sum (chapter02PrincipalDivisor X f).support
        (fun x => chapter02PointCycle X x
          (chapter02OrderOfRationalFunction X x (f : X.functionField))) := by
  symm
  change Finset.sum (chapter02PrincipalDivisor X f).support
      (fun x => Finsupp.single x (chapter02PrincipalDivisor X f x)) =
    chapter02PrincipalDivisor X f
  exact Finsupp.sum_single _

def chapter02LinearlyEquivalent
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (D E : Chapter02FormalDivisor X) : Prop :=
  ∃ f : X.functionFieldˣ, E = D + chapter02PrincipalDivisor X f

theorem chapter02_linearly_equivalent_refl
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (D : Chapter02FormalDivisor X) :
    chapter02LinearlyEquivalent X D D := by
  refine ⟨1, ?_⟩
  ext x
  simp [chapter02_principal_divisor_apply, chapter02OrderOfRationalFunction, Scheme.ord]

theorem chapter02_linearly_equivalent_symm
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (D E : Chapter02FormalDivisor X)
    (hDE : chapter02LinearlyEquivalent X D E) :
    chapter02LinearlyEquivalent X E D := by
  rcases hDE with ⟨f, hf⟩
  have hzero : chapter02PrincipalDivisor X (1 : X.functionFieldˣ) = 0 := by
    ext x
    simp [chapter02_principal_divisor_apply, chapter02OrderOfRationalFunction, Scheme.ord]
  have hsum : chapter02PrincipalDivisor X f + chapter02PrincipalDivisor X f⁻¹ = 0 := by
    rw [← chapter02_principal_divisor_mul X f f⁻¹]
    simp [hzero]
  refine ⟨f⁻¹, ?_⟩
  rw [hf]
  calc
    D = D + 0 := (add_zero D).symm
    _ = D + (chapter02PrincipalDivisor X f + chapter02PrincipalDivisor X f⁻¹) := by
      rw [hsum]
    _ = (D + chapter02PrincipalDivisor X f) + chapter02PrincipalDivisor X f⁻¹ := by
      rw [add_assoc]

theorem chapter02_linearly_equivalent_trans
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (D E F : Chapter02FormalDivisor X)
    (hDE : chapter02LinearlyEquivalent X D E)
    (hEF : chapter02LinearlyEquivalent X E F) :
    chapter02LinearlyEquivalent X D F := by
  rcases hDE with ⟨f, hf⟩
  rcases hEF with ⟨g, hg⟩
  refine ⟨f * g, ?_⟩
  calc
    F = E + chapter02PrincipalDivisor X g := hg
    _ = (D + chapter02PrincipalDivisor X f) +
        chapter02PrincipalDivisor X g := by rw [hf]
    _ = D + (chapter02PrincipalDivisor X f +
        chapter02PrincipalDivisor X g) := by rw [add_assoc]
    _ = D + chapter02PrincipalDivisor X (f * g) := by
      rw [chapter02_principal_divisor_mul]

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter02
