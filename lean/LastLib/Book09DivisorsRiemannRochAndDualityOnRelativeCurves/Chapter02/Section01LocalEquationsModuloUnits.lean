import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter02.Dependencies

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter02

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry nonZeroDivisors

universe u v

/-!
### 2.1 Local equations modulo units
-/

def Chapter02CartierDivisor.zero {X : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X] : Chapter02CartierDivisor X where
  index := PUnit
  openSet _ := ⊤
  cover := by simp
  equation _ := 1
  equationClass _ := Quotient.mk' 1
  equationClass_eq _ := rfl
  transition _ _ := by
    refine ⟨1, ?_⟩
    simp

noncomputable def Chapter02CartierDivisor.neg {X : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X] (D : Chapter02CartierDivisor X) :
    Chapter02CartierDivisor X where
  index := D.index
  openSet := D.openSet
  cover := D.cover
  equation i := (D.equation i)⁻¹
  equationClass i := Quotient.mk' ((D.equation i)⁻¹)
  equationClass_eq i := rfl
  transition := by
    intro i j
    obtain ⟨u, hu⟩ := D.transition i j
    refine ⟨u⁻¹, ?_⟩
    rw [map_inv, hu]
    simp [chapter02MeromorphicRestrictionUnit]
    ac_rfl

private theorem chapter02_regularUnitMap_restrict {X : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X] {U V : X.Opens} (h : V ≤ U)
    (u : (Γ(X, U))ˣ) :
    chapter02RegularUnitMap X V
        (Units.map (X.presheaf.map (homOfLE h).op).hom u) =
      Units.map (K.carrier.presheaf.map (homOfLE h).op).hom
        (chapter02RegularUnitMap X U u) := by
  apply Units.ext
  exact congr($(K.regularMap.1.naturality (homOfLE h).op).hom (u : Γ(X, U)))

private theorem chapter02_meromorphicRestrictionUnit_comp {X : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X] {U V W : X.Opens}
    (hVU : V ≤ U) (hWV : W ≤ V)
    (u : (Chapter02MeromorphicSection X U)ˣ) :
    chapter02MeromorphicRestrictionUnit X hWV
        (chapter02MeromorphicRestrictionUnit X hVU u) =
      chapter02MeromorphicRestrictionUnit X (hWV.trans hVU) u := by
  apply Units.ext
  change (K.carrier.presheaf.map (homOfLE hWV).op).hom
      ((K.carrier.presheaf.map (homOfLE hVU).op).hom (u : _)) =
    (K.carrier.presheaf.map (homOfLE (hWV.trans hVU)).op).hom (u : _)
  have hle : (homOfLE hVU).op ≫ (homOfLE hWV).op =
      (homOfLE (hWV.trans hVU)).op := by
    subsingleton
  simpa only [hle, CommRingCat.comp_apply] using
    congrArg (fun z => z.hom (u : Chapter02MeromorphicSection X U))
      (Functor.map_comp K.carrier.presheaf
        (homOfLE hVU).op (homOfLE hWV).op).symm

noncomputable def Chapter02CartierDivisor.add {X : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X] (D E : Chapter02CartierDivisor X) :
    Chapter02CartierDivisor X where
  index := D.index × E.index
  openSet p := D.openSet p.1 ⊓ E.openSet p.2
  cover := by
    simpa only [D.cover, E.cover, top_inf_eq] using
      (iSup_inf_iSup (f := D.openSet) (g := E.openSet)).symm
  equation p :=
    chapter02MeromorphicRestrictionUnit X inf_le_left (D.equation p.1) *
      chapter02MeromorphicRestrictionUnit X inf_le_right (E.equation p.2)
  equationClass p := Quotient.mk'
    (chapter02MeromorphicRestrictionUnit X inf_le_left (D.equation p.1) *
      chapter02MeromorphicRestrictionUnit X inf_le_right (E.equation p.2))
  equationClass_eq p := rfl
  transition := by
    rintro ⟨i, j⟩ ⟨i', j'⟩
    obtain ⟨uD, hD⟩ := D.transition i i'
    obtain ⟨uE, hE⟩ := E.transition j j'
    have hDle :
        ((D.openSet i ⊓ E.openSet j) ⊓
            (D.openSet i' ⊓ E.openSet j')) ≤
          D.openSet i ⊓ D.openSet i' :=
      le_inf (inf_le_left.trans inf_le_left)
        (inf_le_right.trans inf_le_left)
    have hEle :
        ((D.openSet i ⊓ E.openSet j) ⊓
            (D.openSet i' ⊓ E.openSet j')) ≤
          E.openSet j ⊓ E.openSet j' :=
      le_inf (inf_le_left.trans inf_le_right)
        (inf_le_right.trans inf_le_right)
    refine ⟨Units.map (X.presheaf.map (homOfLE hDle).op).hom uD *
        Units.map (X.presheaf.map (homOfLE hEle).op).hom uE, ?_⟩
    have hDmap := chapter02_regularUnitMap_restrict hDle uD
    have hEmap := chapter02_regularUnitMap_restrict hEle uE
    rw [map_mul, hDmap, hEmap, hD, hE]
    have hDi :
        chapter02MeromorphicRestrictionUnit X hDle
            (chapter02MeromorphicRestrictionUnit X
              (show D.openSet i ⊓ D.openSet i' ≤ D.openSet i from inf_le_left)
              (D.equation i)) =
          chapter02MeromorphicRestrictionUnit X
            (show ((D.openSet i ⊓ E.openSet j) ⊓
                (D.openSet i' ⊓ E.openSet j')) ≤
                (D.openSet i ⊓ E.openSet j) from inf_le_left)
            (chapter02MeromorphicRestrictionUnit X
              (show D.openSet i ⊓ E.openSet j ≤ D.openSet i from inf_le_left)
              (D.equation i)) := by
      calc
        _ = chapter02MeromorphicRestrictionUnit X
            (hDle.trans
              (show D.openSet i ⊓ D.openSet i' ≤ D.openSet i from inf_le_left))
            (D.equation i) :=
          chapter02_meromorphicRestrictionUnit_comp
            (show D.openSet i ⊓ D.openSet i' ≤ D.openSet i from inf_le_left)
            hDle (D.equation i)
        _ = chapter02MeromorphicRestrictionUnit X
            ((show ((D.openSet i ⊓ E.openSet j) ⊓
                (D.openSet i' ⊓ E.openSet j')) ≤
                D.openSet i ⊓ E.openSet j from inf_le_left).trans
              (show D.openSet i ⊓ E.openSet j ≤ D.openSet i from inf_le_left))
            (D.equation i) := by
          congr 1
        _ = _ :=
          (chapter02_meromorphicRestrictionUnit_comp
            (show D.openSet i ⊓ E.openSet j ≤ D.openSet i from inf_le_left)
            (show ((D.openSet i ⊓ E.openSet j) ⊓
                (D.openSet i' ⊓ E.openSet j')) ≤
                D.openSet i ⊓ E.openSet j from inf_le_left)
            (D.equation i)).symm
    have hDip :
        chapter02MeromorphicRestrictionUnit X hDle
            (chapter02MeromorphicRestrictionUnit X
              (show D.openSet i ⊓ D.openSet i' ≤ D.openSet i' from inf_le_right)
              (D.equation i')) =
          chapter02MeromorphicRestrictionUnit X
            (show ((D.openSet i ⊓ E.openSet j) ⊓
                (D.openSet i' ⊓ E.openSet j')) ≤
                (D.openSet i' ⊓ E.openSet j') from inf_le_right)
            (chapter02MeromorphicRestrictionUnit X
              (show D.openSet i' ⊓ E.openSet j' ≤ D.openSet i' from inf_le_left)
              (D.equation i')) := by
      calc
        _ = chapter02MeromorphicRestrictionUnit X
            (hDle.trans
              (show D.openSet i ⊓ D.openSet i' ≤ D.openSet i' from inf_le_right))
            (D.equation i') :=
          chapter02_meromorphicRestrictionUnit_comp
            (show D.openSet i ⊓ D.openSet i' ≤ D.openSet i' from inf_le_right)
            hDle (D.equation i')
        _ = chapter02MeromorphicRestrictionUnit X
            ((show ((D.openSet i ⊓ E.openSet j) ⊓
                (D.openSet i' ⊓ E.openSet j')) ≤
                D.openSet i' ⊓ E.openSet j' from inf_le_right).trans
              (show D.openSet i' ⊓ E.openSet j' ≤ D.openSet i' from inf_le_left))
            (D.equation i') := by
          congr 1
        _ = _ :=
          (chapter02_meromorphicRestrictionUnit_comp
            (show D.openSet i' ⊓ E.openSet j' ≤ D.openSet i' from inf_le_left)
            (show ((D.openSet i ⊓ E.openSet j) ⊓
                (D.openSet i' ⊓ E.openSet j')) ≤
                D.openSet i' ⊓ E.openSet j' from inf_le_right)
            (D.equation i')).symm
    have hEj :
        chapter02MeromorphicRestrictionUnit X hEle
            (chapter02MeromorphicRestrictionUnit X
              (show E.openSet j ⊓ E.openSet j' ≤ E.openSet j from inf_le_left)
              (E.equation j)) =
          chapter02MeromorphicRestrictionUnit X
            (show ((D.openSet i ⊓ E.openSet j) ⊓
                (D.openSet i' ⊓ E.openSet j')) ≤
                (D.openSet i ⊓ E.openSet j) from inf_le_left)
            (chapter02MeromorphicRestrictionUnit X
              (show D.openSet i ⊓ E.openSet j ≤ E.openSet j from inf_le_right)
              (E.equation j)) := by
      calc
        _ = chapter02MeromorphicRestrictionUnit X
            (hEle.trans
              (show E.openSet j ⊓ E.openSet j' ≤ E.openSet j from inf_le_left))
            (E.equation j) :=
          chapter02_meromorphicRestrictionUnit_comp
            (show E.openSet j ⊓ E.openSet j' ≤ E.openSet j from inf_le_left)
            hEle (E.equation j)
        _ = chapter02MeromorphicRestrictionUnit X
            ((show ((D.openSet i ⊓ E.openSet j) ⊓
                (D.openSet i' ⊓ E.openSet j')) ≤
                D.openSet i ⊓ E.openSet j from inf_le_left).trans
              (show D.openSet i ⊓ E.openSet j ≤ E.openSet j from inf_le_right))
            (E.equation j) := by
          congr 1
        _ = _ :=
          (chapter02_meromorphicRestrictionUnit_comp
            (show D.openSet i ⊓ E.openSet j ≤ E.openSet j from inf_le_right)
            (show ((D.openSet i ⊓ E.openSet j) ⊓
                (D.openSet i' ⊓ E.openSet j')) ≤
                D.openSet i ⊓ E.openSet j from inf_le_left)
            (E.equation j)).symm
    have hEjp :
        chapter02MeromorphicRestrictionUnit X hEle
            (chapter02MeromorphicRestrictionUnit X
              (show E.openSet j ⊓ E.openSet j' ≤ E.openSet j' from inf_le_right)
              (E.equation j')) =
          chapter02MeromorphicRestrictionUnit X
            (show ((D.openSet i ⊓ E.openSet j) ⊓
                (D.openSet i' ⊓ E.openSet j')) ≤
                (D.openSet i' ⊓ E.openSet j') from inf_le_right)
            (chapter02MeromorphicRestrictionUnit X
              (show D.openSet i' ⊓ E.openSet j' ≤ E.openSet j' from inf_le_right)
              (E.equation j')) := by
      calc
        _ = chapter02MeromorphicRestrictionUnit X
            (hEle.trans
              (show E.openSet j ⊓ E.openSet j' ≤ E.openSet j' from inf_le_right))
            (E.equation j') :=
          chapter02_meromorphicRestrictionUnit_comp
            (show E.openSet j ⊓ E.openSet j' ≤ E.openSet j' from inf_le_right)
            hEle (E.equation j')
        _ = chapter02MeromorphicRestrictionUnit X
            ((show ((D.openSet i ⊓ E.openSet j) ⊓
                (D.openSet i' ⊓ E.openSet j')) ≤
                D.openSet i' ⊓ E.openSet j' from inf_le_right).trans
              (show D.openSet i' ⊓ E.openSet j' ≤ E.openSet j' from inf_le_right))
            (E.equation j') := by
          congr 1
        _ = _ :=
          (chapter02_meromorphicRestrictionUnit_comp
            (show D.openSet i' ⊓ E.openSet j' ≤ E.openSet j' from inf_le_right)
            (show ((D.openSet i ⊓ E.openSet j) ⊓
                (D.openSet i' ⊓ E.openSet j')) ≤
                D.openSet i' ⊓ E.openSet j' from inf_le_right)
            (E.equation j')).symm
    have hprodA :
        chapter02MeromorphicRestrictionUnit X
            (show ((D.openSet i ⊓ E.openSet j) ⊓
                (D.openSet i' ⊓ E.openSet j')) ≤
                D.openSet i ⊓ E.openSet j from inf_le_left)
            (chapter02MeromorphicRestrictionUnit X
              (show D.openSet i ⊓ E.openSet j ≤ D.openSet i from inf_le_left)
              (D.equation i) *
              chapter02MeromorphicRestrictionUnit X
                (show D.openSet i ⊓ E.openSet j ≤ E.openSet j from inf_le_right)
                (E.equation j)) =
          chapter02MeromorphicRestrictionUnit X
              (show ((D.openSet i ⊓ E.openSet j) ⊓
                  (D.openSet i' ⊓ E.openSet j')) ≤
                  D.openSet i ⊓ E.openSet j from inf_le_left)
              (chapter02MeromorphicRestrictionUnit X
                (show D.openSet i ⊓ E.openSet j ≤ D.openSet i from inf_le_left)
                (D.equation i)) *
            chapter02MeromorphicRestrictionUnit X
              (show ((D.openSet i ⊓ E.openSet j) ⊓
                  (D.openSet i' ⊓ E.openSet j')) ≤
                  D.openSet i ⊓ E.openSet j from inf_le_left)
              (chapter02MeromorphicRestrictionUnit X
                (show D.openSet i ⊓ E.openSet j ≤ E.openSet j from inf_le_right)
                (E.equation j)) := by
      exact (Units.map (chapter02MeromorphicRestriction X
        (show ((D.openSet i ⊓ E.openSet j) ⊓
            (D.openSet i' ⊓ E.openSet j')) ≤
            D.openSet i ⊓ E.openSet j from inf_le_left)).toMonoidHom).map_mul _ _
    have hprodAp :
        chapter02MeromorphicRestrictionUnit X
            (show ((D.openSet i ⊓ E.openSet j) ⊓
                (D.openSet i' ⊓ E.openSet j')) ≤
                D.openSet i' ⊓ E.openSet j' from inf_le_right)
            (chapter02MeromorphicRestrictionUnit X
              (show D.openSet i' ⊓ E.openSet j' ≤ D.openSet i' from inf_le_left)
              (D.equation i') *
              chapter02MeromorphicRestrictionUnit X
                (show D.openSet i' ⊓ E.openSet j' ≤ E.openSet j' from inf_le_right)
                (E.equation j')) =
          chapter02MeromorphicRestrictionUnit X
              (show ((D.openSet i ⊓ E.openSet j) ⊓
                  (D.openSet i' ⊓ E.openSet j')) ≤
                  D.openSet i' ⊓ E.openSet j' from inf_le_right)
              (chapter02MeromorphicRestrictionUnit X
                (show D.openSet i' ⊓ E.openSet j' ≤ D.openSet i' from inf_le_left)
                (D.equation i')) *
            chapter02MeromorphicRestrictionUnit X
              (show ((D.openSet i ⊓ E.openSet j) ⊓
                  (D.openSet i' ⊓ E.openSet j')) ≤
                  D.openSet i' ⊓ E.openSet j' from inf_le_right)
              (chapter02MeromorphicRestrictionUnit X
                (show D.openSet i' ⊓ E.openSet j' ≤ E.openSet j' from inf_le_right)
                (E.equation j')) := by
      exact (Units.map (chapter02MeromorphicRestriction X
        (show ((D.openSet i ⊓ E.openSet j) ⊓
            (D.openSet i' ⊓ E.openSet j')) ≤
            D.openSet i' ⊓ E.openSet j' from inf_le_right)).toMonoidHom).map_mul _ _
    simp only [map_mul, map_inv]
    change
      chapter02MeromorphicRestrictionUnit X hDle _ *
          (chapter02MeromorphicRestrictionUnit X hDle _)⁻¹ *
        (chapter02MeromorphicRestrictionUnit X hEle _ *
          (chapter02MeromorphicRestrictionUnit X hEle _)⁻¹) = _
    rw [hDi, hDip, hEj, hEjp, hprodA, hprodAp]
    simp only [mul_inv_rev]
    ac_rfl

def Chapter02CartierDivisor.IsZero {X : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X] (D : Chapter02CartierDivisor X) : Prop :=
  ∀ i, ∃ u : (Γ(X, D.openSet i))ˣ,
    chapter02RegularUnitMap X (D.openSet i) u = D.equation i

@[simp]
theorem chapter02_cartier_zero_equation {X : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X] :
    (Chapter02CartierDivisor.zero (X := X)).equation PUnit.unit = 1 := rfl

theorem chapter02_cartier_zero_is_zero {X : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X] :
    (Chapter02CartierDivisor.zero (X := X)).IsZero := by
  rintro ⟨⟩
  refine ⟨1, ?_⟩
  apply Units.ext
  simp

theorem chapter02_cartier_neg_equation {X : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X] (D : Chapter02CartierDivisor X) (i : D.index) :
    D.neg.equation i = (D.equation i)⁻¹ := by
  rfl

theorem chapter02_cartier_add_equation {X : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X] (D E : Chapter02CartierDivisor X)
    (i : D.index) (j : E.index) :
    (D.add E).equation (i, j) =
      chapter02MeromorphicRestrictionUnit X inf_le_left (D.equation i) *
        chapter02MeromorphicRestrictionUnit X inf_le_right (E.equation j) := by
  rfl

def Chapter02CartierDivisor.IsEffective {X : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X] (D : Chapter02CartierDivisor X) : Prop :=
  ∀ i, ∀ x : X, x ∈ D.openSet i →
    ∃ (V : X.Opens) (hxV : x ∈ V) (hV : V ≤ D.openSet i)
      (f : Γ(X, V)),
      chapter02RegularSectionIsRegularAt V f x hxV ∧
        chapter02RegularSectionMap X V f =
          chapter02MeromorphicRestriction X hV
            (D.equation i : Chapter02MeromorphicSection X (D.openSet i))

def Chapter02CartierDivisor.HasSignedDecomposition {X : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X]
    (D : Chapter02CartierDivisor.{u, v} X) : Prop :=
  ∃ E F : Chapter02CartierDivisor.{u, v} X,
    E.IsEffective ∧ F.IsEffective ∧ D = E.add F.neg

/- A meromorphic equation is always a unit in the meromorphic sheaf.  Its
   Cartier support is instead detected by whether it is a unit in the
   structure sheaf after restricting to a neighborhood of the point. -/
def chapter02MeromorphicSectionIsRegularUnitAt {X : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X] (U : X.Opens)
    (s : Chapter02MeromorphicSection X U) (x : X) : Prop :=
  ∃ (V : X.Opens) (hV : V ≤ U) (_hxV : x ∈ V) (u : (Γ(X, V))ˣ),
    chapter02RegularSectionMap X V (u : Γ(X, V)) =
      chapter02MeromorphicRestriction X hV s

def Chapter02CartierDivisor.support {X : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X] (D : Chapter02CartierDivisor X) : Set X :=
  {x | ∀ i (_hx : x ∈ D.openSet i),
    ¬ chapter02MeromorphicSectionIsRegularUnitAt
      (D.openSet i) (D.equation i) x}

theorem chapter02_cartier_support_closed {X : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X] [IsNoetherian X]
    (D : Chapter02CartierDivisor X) :
    IsClosed D.support := by
  classical
  rw [← isOpen_compl_iff]
  have hopen : ∀ i : D.index,
      IsOpen {x : X |
        chapter02MeromorphicSectionIsRegularUnitAt
          (D.openSet i) (D.equation i) x} := by
    intro i
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨V, hV, hxV, u, hu⟩ := hx
    refine Filter.mem_of_superset (V.isOpen.mem_nhds hxV) ?_
    intro y hy
    exact ⟨V, hV, hy, u, hu⟩
  have heq : D.supportᶜ = ⋃ i : D.index,
      (D.openSet i : Set X) ∩
        {x : X |
          chapter02MeromorphicSectionIsRegularUnitAt
            (D.openSet i) (D.equation i) x} := by
    ext x
    simp [Chapter02CartierDivisor.support]
  rw [heq]
  exact isOpen_iUnion fun i => (D.openSet i).isOpen.inter (hopen i)

theorem chapter02_cartier_support_omits_generic_point {X : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X] [IsNoetherian X] [IsIntegral X]
    (D : Chapter02CartierDivisor X) :
    genericPoint X ∉ D.support := by
  classical
  have hηcover : genericPoint X ∈ iSup D.openSet := by
    rw [D.cover]
    trivial
  obtain ⟨i, hi⟩ : ∃ i : D.index, genericPoint X ∈ D.openSet i := by
    exact Opens.mem_iSup.mp hηcover
  let U := D.openSet i
  let s : Chapter02MeromorphicSection X U := D.equation i
  obtain ⟨V0, hηV0, hV0U, a, b, hb, hs⟩ :=
    K.exists_fraction U s (genericPoint X) hi
  let U0 := V0.1
  let hU0 : Nonempty U0 := ⟨⟨genericPoint X, hηV0⟩⟩
  have hnontrivial : Nontrivial Γ(X, U0) := @Scheme.component_nontrivial X U0 hU0
  let s0 : Chapter02MeromorphicSection X U0 :=
    chapter02MeromorphicRestriction X hV0U s
  have hbnz : b ≠ 0 := by
    intro hb0
    exact @zero_notMem_nonZeroDivisors _ _ hnontrivial (hb0 ▸ hb)
  have han : a ≠ 0 := by
    intro ha
    have hzero : chapter02RegularSectionMap X U0 b = 0 := by
      have hmul := congrArg
        (fun z : Chapter02MeromorphicSection X U0 =>
          (↑((chapter02MeromorphicRestrictionUnit X hV0U (D.equation i))⁻¹) :
            Chapter02MeromorphicSection X U0) * z) hs
      have hmapzero :
          (K.regularMap.1.app (Opposite.op U0)).hom
              (0 : Γ(X, U0)) = 0 := map_zero _
      rw [ha, hmapzero, mul_zero] at hmul
      change (↑((chapter02MeromorphicRestrictionUnit X hV0U (D.equation i))⁻¹) :
          Chapter02MeromorphicSection X U0) *
          ((chapter02MeromorphicRestrictionUnit X hV0U (D.equation i) :
              Chapter02MeromorphicSection X U0) *
            (K.regularMap.1.app (Opposite.op U0)).hom b) = 0 at hmul
      rw [← mul_assoc, Units.inv_mul, one_mul] at hmul
      change (K.regularMap.1.app (Opposite.op U0)).hom b = 0
      exact hmul
    exact hbnz ((K.structureMap_injective U0)
      (hzero.trans ((chapter02RegularSectionMap X U0).map_zero).symm))
  have hbgerm : X.presheaf.germ U0 (genericPoint X) hηV0 b ≠ 0 := by
    intro h
    apply hbnz
    apply (germ_injective_of_isIntegral (X := X) (genericPoint X) hηV0)
    simpa using h
  have hagerm : X.presheaf.germ U0 (genericPoint X) hηV0 a ≠ 0 := by
    intro h
    apply han
    apply (germ_injective_of_isIntegral (X := X) (genericPoint X) hηV0)
    simpa using h
  let V := X.basicOpen (a * b)
  have hVU0 : V ≤ U0 := X.basicOpen_le (a * b)
  have hηV : genericPoint X ∈ V := by
    rw [Scheme.mem_basicOpen X (a * b) (genericPoint X) hηV0]
    rw [isUnit_iff_ne_zero]
    simpa only [map_mul] using mul_ne_zero hagerm hbgerm
  let aV : Γ(X, V) := X.presheaf.map (homOfLE hVU0).op a
  let bV : Γ(X, V) := X.presheaf.map (homOfLE hVU0).op b
  have habV : IsUnit (aV * bV) := by
    rw [← map_mul]
    exact X.toRingedSpace.isUnit_res_basicOpen (a * b)
  have haV : IsUnit aV := isUnit_of_mul_isUnit_left habV
  have hbV : IsUnit bV := isUnit_of_mul_isUnit_right habV
  have hfracV :
      chapter02MeromorphicRestriction X hVU0 s0 *
          chapter02RegularSectionMap X V bV =
        chapter02RegularSectionMap X V aV := by
    have hnat_a :
        chapter02RegularSectionMap X V aV =
          (K.carrier.presheaf.map (homOfLE hVU0).op).hom
            (chapter02RegularSectionMap X U0 a) := by
      exact congr($(K.regularMap.1.naturality (homOfLE hVU0).op).hom a)
    have hnat_b :
        chapter02RegularSectionMap X V bV =
          (K.carrier.presheaf.map (homOfLE hVU0).op).hom
            (chapter02RegularSectionMap X U0 b) := by
      exact congr($(K.regularMap.1.naturality (homOfLE hVU0).op).hom b)
    have hmap := congrArg
      (fun z => (K.carrier.presheaf.map (homOfLE hVU0).op).hom z) hs
    change (K.carrier.presheaf.map (homOfLE hVU0).op).hom
        (s0 * chapter02RegularSectionMap X U0 b) =
      (K.carrier.presheaf.map (homOfLE hVU0).op).hom
        (chapter02RegularSectionMap X U0 a) at hmap
    rw [map_mul] at hmap
    rw [← hnat_a, ← hnat_b] at hmap
    simpa [chapter02MeromorphicRestriction, map_mul] using hmap
  let uA : (Γ(X, V))ˣ := haV.unit
  let uB : (Γ(X, V))ˣ := hbV.unit
  have hVU : V ≤ U := hVU0.trans hV0U
  have hregular : chapter02MeromorphicSectionIsRegularUnitAt U s (genericPoint X) := by
    refine ⟨V, hVU, hηV, uB⁻¹ * uA, ?_⟩
    have hvB :
        (chapter02RegularUnitMap X V uB :
          Chapter02MeromorphicSection X V) =
          chapter02RegularSectionMap X V bV := by
      simp [chapter02RegularUnitMap, uB]
    have hvA :
        (chapter02RegularUnitMap X V uA :
          Chapter02MeromorphicSection X V) =
          chapter02RegularSectionMap X V aV := by
      simp [chapter02RegularUnitMap, uA]
    have hcancel :
        chapter02MeromorphicRestriction X hVU0 s0 =
          (↑((chapter02RegularUnitMap X V uB)⁻¹) :
            Chapter02MeromorphicSection X V) *
            (chapter02RegularUnitMap X V uA :
              Chapter02MeromorphicSection X V) := by
      have hfracUnits :
          chapter02MeromorphicRestriction X hVU0 s0 *
              (chapter02RegularUnitMap X V uB :
                Chapter02MeromorphicSection X V) =
            (chapter02RegularUnitMap X V uA :
              Chapter02MeromorphicSection X V) := by
        rw [hvB, hvA]
        exact hfracV
      have hmul := congrArg
        (fun z : Chapter02MeromorphicSection X V =>
          (↑((chapter02RegularUnitMap X V uB)⁻¹) :
            Chapter02MeromorphicSection X V) * z) hfracUnits
      calc
        chapter02MeromorphicRestriction X hVU0 s0 =
            chapter02MeromorphicRestriction X hVU0 s0 * 1 :=
          (mul_one _).symm
        _ = chapter02MeromorphicRestriction X hVU0 s0 *
              ((↑((chapter02RegularUnitMap X V uB)⁻¹) :
                Chapter02MeromorphicSection X V) *
                (chapter02RegularUnitMap X V uB :
                  Chapter02MeromorphicSection X V)) := by
          rw [(chapter02RegularUnitMap X V uB).inv_mul, mul_one]
        _ = (↑((chapter02RegularUnitMap X V uB)⁻¹) :
              Chapter02MeromorphicSection X V) *
              (chapter02MeromorphicRestriction X hVU0 s0 *
                (chapter02RegularUnitMap X V uB :
                  Chapter02MeromorphicSection X V)) := by
          ac_rfl
        _ = (↑((chapter02RegularUnitMap X V uB)⁻¹) :
              Chapter02MeromorphicSection X V) *
              (chapter02RegularUnitMap X V uA :
                Chapter02MeromorphicSection X V) := hmul
    change (chapter02RegularUnitMap X V (uB⁻¹ * uA) :
      Chapter02MeromorphicSection X V) = _
    rw [map_mul, map_inv]
    rw [← chapter02_meromorphicRestriction_comp (X := X) hV0U hVU0 s]
    exact hcancel.symm
  intro hηsupport
  exact hηsupport i hi hregular

theorem chapter02_regular_element_iff_injective_multiplication
    (R : Type u) [CommRing R] (f : R) :
    f ∈ nonZeroDivisors R ↔ Function.Injective (fun x : R => f * x) := by
  constructor
  · intro hf x y hxy
    exact (mul_cancel_left_mem_nonZeroDivisors hf).mp hxy
  · intro h
    rw [mem_nonZeroDivisors_iff]
    constructor
    · intro x hx
      apply h
      simpa using hx
    · intro x hx
      apply h
      simpa [mul_comm] using hx

theorem chapter02_nonzero_divisor_not_component
    (R : Type u) [CommRing R] (f : R)
    (hf : f ∈ nonZeroDivisors R) :
    ∀ x : R, f * x = 0 → x = 0 := by
  intro x hx
  exact (chapter02_regular_element_iff_injective_multiplication R f).mp hf
    (by simpa using hx)

/- The following are book-facing descriptions of the two standard total
   quotient-ring special cases.  The actual sheaf-level comparison is left in
   `Chapter02MeromorphicSheaf`, with restriction compatibility made explicit
   there. -/
def Chapter02MeromorphicSheaf.IsConstantOnNonemptyOpens {X : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X] [IsIntegral X] : Prop :=
  ∀ U : X.Opens, Nonempty U →
    Nonempty (Chapter02MeromorphicSection X U ≃+* X.functionField)

theorem chapter02_total_quotient_constant_on_integral_scheme
    (X : Scheme.{u}) [K : Chapter02MeromorphicSheaf X]
    [IsIntegral X] :
    Chapter02MeromorphicSheaf.IsConstantOnNonemptyOpens (X := X) := by
  sorry

theorem chapter02_component_function_field_isField (X : Scheme.{u})
    [IsReduced X] (i : irreducibleComponents X) :
    IsField (Chapter02ComponentFunctionField X i) := by
  apply isField_stalk_of_closure_mem_irreducibleComponents
  rw [i.2.1.closure_genericPoint
    (isClosed_of_mem_irreducibleComponents i.1 i.2)]
  exact i.2

def Chapter02MeromorphicSheaf.IsFiniteProductOfFunctionFields {X : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X] [IsReduced X] : Prop :=
  Nonempty (Chapter02MeromorphicSection X ⊤ ≃+*
    (∀ i : irreducibleComponents X, Chapter02ComponentFunctionField X i))

theorem chapter02_irreducible_components_finite
    (X : Scheme.{u}) [IsNoetherian X] :
    (irreducibleComponents X).Finite :=
  finite_irreducibleComponents_of_isNoetherian

/- LOCAL_DEPENDENCY_GUESS: the pinned API does not yet expose the function
   field attached to each irreducible component or the comparison with the
   total quotient sheaf.  Package those canonical component fields together
   with the comparison instead of allowing an arbitrary family of fields. -/
structure Chapter02FiniteComponentFunctionFieldData
    (X : Scheme.{u}) [K : Chapter02MeromorphicSheaf X]
    [IsReduced X] [IsLocallyNoetherian X]
    [Finite (irreducibleComponents X)] where
  product : Chapter02MeromorphicSheaf.IsFiniteProductOfFunctionFields (X := X)

theorem chapter02_total_quotient_product_of_reduced_finite_components
    (X : Scheme.{u}) [K : Chapter02MeromorphicSheaf X] [IsReduced X]
    [IsLocallyNoetherian X] [Finite (irreducibleComponents X)] :
    Nonempty (Chapter02FiniteComponentFunctionFieldData X) := by
  sorry

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter02
