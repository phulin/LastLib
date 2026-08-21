import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter12.Dependencies
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter12.Section01GroupLawsDescend
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.Section01DescentOfMaps

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter12

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped MonObj

universe u

universe v

/-!
### 12.3 Subgroups, homomorphisms, and exactness
-/

/-- A closed subgroup object in the (not necessarily commutative) group-scheme category. -/
structure Chapter12GroupClosedSubgroup {S : Scheme.{u}}
    (G : Chapter12GroupScheme S) where
  subgroup : Chapter12GroupScheme S
  inclusion : subgroup ⟶ G
  closed : IsClosedImmersion (Chapter12GroupScheme.homScheme inclusion)

@[ext]
theorem chapter12GroupClosedSubgroup.ext {S : Scheme.{u}}
    {G : Chapter12GroupScheme S}
    {K L : Chapter12GroupClosedSubgroup G}
    (h : K.subgroup = L.subgroup) (hi : HEq K.inclusion L.inclusion) : K = L := by
  cases K
  cases L
  cases h
  cases hi
  rfl

private theorem chapter12_grp_mkIso_hom
    {C : Type u} [Category.{v} C] [CartesianMonoidalCategory.{v} C]
    {A B : Grp C} (e : A.X ≅ B.X) [IsMonHom e.hom] :
    (Grp.mkIso' e).hom.hom.hom = e.hom := by
  change ((Grp.fullyFaithfulForget₂Mon C).preimage (Mon.mkIso' e).hom).hom.hom = e.hom
  have hmap :
      (Grp.forget₂Mon C).map (Grp.homMk e.hom) = (Mon.mkIso' e).hom := by
    apply Mon.Hom.ext
    rfl
  have hpre :
      (Grp.fullyFaithfulForget₂Mon C).preimage (Mon.mkIso' e).hom =
        Grp.homMk e.hom := by
    simpa only [hmap] using
      (Grp.fullyFaithfulForget₂Mon C).preimage_map (Grp.homMk e.hom)
  exact congrArg (fun f => f.hom.hom) hpre

private theorem chapter12_grp_mkIso_inv_hom
    {C : Type u} [Category.{v} C] [CartesianMonoidalCategory.{v} C]
    {A B : Grp C} (e : A.X ≅ B.X) [IsMonHom e.hom] :
    (Grp.mkIso' e).inv.hom.hom = e.inv := by
  change ((Grp.fullyFaithfulForget₂Mon C).preimage (Mon.mkIso' e).inv).hom.hom = e.inv
  have hmap :
      (Grp.forget₂Mon C).map (Grp.homMk e.inv) = (Mon.mkIso' e).inv := by
    apply Mon.Hom.ext
    rfl
  have hpre :
      (Grp.fullyFaithfulForget₂Mon C).preimage (Mon.mkIso' e).inv =
        Grp.homMk e.inv := by
    simpa only [hmap] using
      (Grp.fullyFaithfulForget₂Mon C).preimage_map (Grp.homMk e.inv)
  exact congrArg (fun f => f.hom.hom) hpre

private theorem chapter12_grp_mkIso_hom_abbrev
    {C : Type u} [Category.{v} C] [CartesianMonoidalCategory.{v} C]
    {A B : Grp C} (e : A.X ≅ B.X)
    (one_f : η[A.X] ≫ e.hom = η[B.X] := by cat_disch)
    (mul_f : μ[A.X] ≫ e.hom = (e.hom ⊗ₘ e.hom) ≫ μ[B.X] := by cat_disch) :
    (Grp.mkIso e one_f mul_f).hom.hom.hom = e.hom := by
  let : IsMonHom e.hom := ⟨one_f, mul_f⟩
  exact chapter12_grp_mkIso_hom e

private theorem chapter12_grp_mkIso_inv_hom_abbrev
    {C : Type u} [Category.{v} C] [CartesianMonoidalCategory.{v} C]
    {A B : Grp C} (e : A.X ≅ B.X)
    (one_f : η[A.X] ≫ e.hom = η[B.X] := by cat_disch)
    (mul_f : μ[A.X] ≫ e.hom = (e.hom ⊗ₘ e.hom) ≫ μ[B.X] := by cat_disch) :
    (Grp.mkIso e one_f mul_f).inv.hom.hom = e.inv := by
  let : IsMonHom e.hom := ⟨one_f, mul_f⟩
  exact chapter12_grp_mkIso_inv_hom e

private theorem chapter12_group_eqToIso_homScheme
    {S : Scheme.{u}} {A B : Chapter12GroupScheme S} (h : A = B) :
    Chapter12GroupScheme.homScheme (eqToIso h).hom =
      Over.Hom.left (eqToHom (congrArg (fun G : Chapter12GroupScheme S => G.X) h)) := by
  cases h
  rfl

theorem chapter12_group_closed_subgroup_descends
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FpqcCover p)
    (D_G D_K : Chapter12GroupSchemeDescentDatum p)
    {G : Chapter12GroupScheme S}
    (eG : Chapter12GroupScheme.baseChange p G ≅ D_G.upstairs)
    (heG : chapter12GroupSchemeDescentComparisonCompatible D_G G eG)
    (iT : D_K.upstairs ⟶ D_G.upstairs)
    (hiT : chapter12DescentHomCompatible D_K D_G iT)
    (hclosed : IsClosedImmersion (Chapter12GroupScheme.homScheme iT)) :
    ∃ (K : Chapter12GroupScheme S) (i : K ⟶ G)
      (eK : Chapter12GroupScheme.baseChange p K ≅ D_K.upstairs),
      chapter12GroupSchemeDescentComparisonCompatible D_K K eK ∧
        IsClosedImmersion (Chapter12GroupScheme.homScheme i) ∧
          Chapter12GroupScheme.baseChangeHom p i = eK.hom ≫ iT ≫ eG.inv := by
  obtain ⟨K, eK, heK⟩ := chapter12_group_laws_descend p hp D_K
  let uT : Chapter12GroupScheme.baseChange p K ⟶
      Chapter12GroupScheme.baseChange p G := eK.hom ≫ iT ≫ eG.inv
  let X : LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.Chapter10SchemeOver S :=
    ⟨K.X.left, K.X.hom⟩
  let Y : LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.Chapter10SchemeOver S :=
    ⟨G.X.left, G.X.hom⟩
  let u : LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10BaseChangeOver p X ⟶
      LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10BaseChangeOver p Y :=
    uT.hom.hom
  have hK := heK
    (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst p)
    (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p)
    (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlap_condition p)
  have hG := heG
    (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst p)
    (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p)
    (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlap_condition p)
  have hGinv₁ :
      Chapter12GroupScheme.baseChangeHom
          (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst p)
          eG.inv =
        (Chapter12GroupScheme.baseChangeIso
          (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst p)
          eG).inv := by
    rfl
  have hGinv₂ :
      Chapter12GroupScheme.baseChangeHom
          (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p)
          eG.inv =
        (Chapter12GroupScheme.baseChangeIso
          (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p)
          eG).inv := by
    rfl
  have hKhom₁ :
      Chapter12GroupScheme.baseChangeHom
          (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst p)
          eK.hom =
        (Chapter12GroupScheme.baseChangeIso
          (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst p)
          eK).hom := by
    rfl
  have hKhom₂ :
      Chapter12GroupScheme.baseChangeHom
          (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p)
          eK.hom =
        (Chapter12GroupScheme.baseChangeIso
          (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p)
          eK).hom := by
    rfl
  have hGinv :
      Chapter12GroupScheme.baseChangeHom
          (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst p)
          eG.inv ≫
        (chapter12GroupSchemeBaseChangeComparison p G
          (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst p)
          (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p)
          (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlap_condition p)).hom =
      (D_G.compare
          (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst p)
          (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p)
          (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlap_condition p)).hom ≫
        Chapter12GroupScheme.baseChangeHom
          (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p)
          eG.inv := by
    apply (cancel_mono
      (Chapter12GroupScheme.baseChangeIso
        (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p)
        eG).hom).1
    simp only [Category.assoc]
    rw [← hG]
    rw [hGinv₁, hGinv₂]
    simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  have hgroup :
      Chapter12GroupScheme.baseChangeHom
          (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst p)
          uT ≫
        (chapter12GroupSchemeBaseChangeComparison p G
          (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst p)
          (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p)
          (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlap_condition p)).hom =
      (chapter12GroupSchemeBaseChangeComparison p K
          (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst p)
          (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p)
          (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlap_condition p)).hom ≫
        Chapter12GroupScheme.baseChangeHom
          (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p)
          uT := by
    have hT := hiT
      (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst p)
      (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p)
      (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlap_condition p)
    have hmap₁ :
        Chapter12GroupScheme.baseChangeHom
            (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst p)
            uT =
          Chapter12GroupScheme.baseChangeHom
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst p)
              eK.hom ≫
            Chapter12GroupScheme.baseChangeHom
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst p)
              iT ≫
            Chapter12GroupScheme.baseChangeHom
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst p)
              eG.inv := by
      dsimp [uT, Chapter12GroupScheme.baseChangeHom]
      exact
        (Functor.map_comp
          (Over.pullback
            (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst p)).mapGrp
          (eK.hom ≫ iT) eG.inv).trans
          (congrArg
            (fun z => z ≫
              (Over.pullback
                (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst p)).mapGrp.map
                eG.inv)
            (Functor.map_comp
              (Over.pullback
                (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst p)).mapGrp
              eK.hom iT))
    have hmap₂ :
        Chapter12GroupScheme.baseChangeHom
            (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p)
            uT =
          Chapter12GroupScheme.baseChangeHom
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p)
              eK.hom ≫
            Chapter12GroupScheme.baseChangeHom
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p)
              iT ≫
            Chapter12GroupScheme.baseChangeHom
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p)
              eG.inv := by
      dsimp [uT, Chapter12GroupScheme.baseChangeHom]
      exact
        (Functor.map_comp
          (Over.pullback
            (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p)).mapGrp
          (eK.hom ≫ iT) eG.inv).trans
          (congrArg
            (fun z => z ≫
              (Over.pullback
                (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p)).mapGrp.map
                eG.inv)
            (Functor.map_comp
              (Over.pullback
                (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p)).mapGrp
              eK.hom iT))
    rw [hmap₁, hmap₂]
    simp only [Category.assoc]
    rw [hGinv]
    have hT' :
        Chapter12GroupScheme.baseChangeHom
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst p)
              eK.hom ≫
            Chapter12GroupScheme.baseChangeHom
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst p)
              iT ≫
            (D_G.compare
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst p)
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p)
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlap_condition p)).hom ≫
            Chapter12GroupScheme.baseChangeHom
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p)
              eG.inv =
          Chapter12GroupScheme.baseChangeHom
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst p)
              eK.hom ≫
            (D_K.compare
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst p)
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p)
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlap_condition p)).hom ≫
            Chapter12GroupScheme.baseChangeHom
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p)
              iT ≫
            Chapter12GroupScheme.baseChangeHom
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p)
              eG.inv := by
      simpa only [Category.assoc] using
        congrArg
          (fun z =>
            Chapter12GroupScheme.baseChangeHom
                (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst p)
                eK.hom ≫ z ≫
              Chapter12GroupScheme.baseChangeHom
                (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p)
                eG.inv) hT
    rw [hT']
    rw [← hKhom₁, ← hKhom₂] at hK
    have hK' :
        Chapter12GroupScheme.baseChangeHom
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst p)
              eK.hom ≫
            (D_K.compare
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst p)
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p)
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlap_condition p)).hom ≫
            Chapter12GroupScheme.baseChangeHom
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p)
              iT ≫
            Chapter12GroupScheme.baseChangeHom
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p)
              eG.inv =
          (chapter12GroupSchemeBaseChangeComparison p K
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst p)
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p)
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlap_condition p)).hom ≫
            Chapter12GroupScheme.baseChangeHom
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p)
              eK.hom ≫
            Chapter12GroupScheme.baseChangeHom
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p)
              iT ≫
            Chapter12GroupScheme.baseChangeHom
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p)
              eG.inv := by
      simpa only [Category.assoc] using
        congrArg
          (fun z => z ≫
            Chapter12GroupScheme.baseChangeHom
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p)
              iT ≫
            Chapter12GroupScheme.baseChangeHom
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p)
              eG.inv) hK
    rw [hK']
  have hu :
      LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DescentCompatible p u := by
    unfold LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DescentCompatible
    dsimp [LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10OverlapFirstHom,
      LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10OverlapSecondHomTransported]
    have hgroup' := congrArg (fun k => Over.Hom.left k.hom.hom) hgroup
    dsimp [Chapter12GroupScheme.baseChangeHom, Chapter12GroupScheme.baseChange] at hgroup'
    have hcompK :
        (chapter12GroupSchemeBaseChangeComparison p K
            (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst p)
            (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p)
            (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlap_condition p)).hom.hom.hom =
            (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapComparison p X).hom := by
      apply Over.OverMorphism.ext
      simp only [chapter12GroupSchemeBaseChangeComparison, Iso.trans_hom,
        Chapter12GroupScheme.homScheme_comp]
      have hfull₁ :
          Chapter12GroupScheme.homScheme
            (chapter12GroupSchemeBaseChangeCompIso p
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst p) K).hom =
            Over.Hom.left
              ((Over.pullbackComp
                (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst p) p).inv.app
                (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10OverObject X)) := by
        change Over.Hom.left
            ((chapter12GroupSchemeBaseChangeCompIso p
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst p) K).hom.hom.hom) = _
        rfl
      have hfull₂ :
          Chapter12GroupScheme.homScheme
            (chapter12GroupSchemeBaseChangeCompIso p
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p) K).symm.hom =
            Over.Hom.left
              ((Over.pullbackComp
                (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p) p).hom.app
                (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10OverObject X)) := by
        change Over.Hom.left
            ((chapter12GroupSchemeBaseChangeCompIso p
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p) K).symm.hom.hom.hom) = _
        rfl
      have hbc :
          Chapter12GroupScheme.baseChange
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst p ≫ p) K =
            Chapter12GroupScheme.baseChange
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p ≫ p) K :=
        congrArg (fun r => Chapter12GroupScheme.baseChange r K)
          (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlap_condition p)
      have hmiddle := chapter12_group_eqToIso_homScheme hbc
      rw [hfull₁, hfull₂, hmiddle]
      simp [LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapComparison,
        X, Chapter12GroupScheme.baseChange]
      congr 1
    have hcompG :
        (chapter12GroupSchemeBaseChangeComparison p G
            (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst p)
            (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p)
            (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlap_condition p)).hom.hom.hom =
            (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapComparison p Y).hom := by
      dsimp [Y]
      unfold Chapter12GroupScheme.baseChange
      apply Over.OverMorphism.ext
      simp only [chapter12GroupSchemeBaseChangeComparison,
        chapter12GroupSchemeBaseChangeCompIso,
        LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapComparison,
        Iso.trans_hom, Iso.symm_hom]
      have hc₁ :
          ((Functor.mapGrpCompIso (F := Over.pullback p)
            (G := Over.pullback
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst p))).app G).symm.hom.hom.hom =
            𝟙 _ := by
        change 𝟙 _ = 𝟙 _
        rfl
      have hc₂ :
          ((Functor.mapGrpCompIso (F := Over.pullback p)
            (G := Over.pullback
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p))).app G).symm.inv.hom.hom =
            𝟙 _ := by
        change 𝟙 _ = 𝟙 _
        rfl
      have hc₃ :
          ((Functor.mapGrpCompIso (F := Over.pullback p)
            (G := Over.pullback
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p))).app G).symm.hom.hom.hom =
            𝟙 _ := by
        change 𝟙 _ = 𝟙 _
        rfl
      have hc₄ :
          ((Functor.mapGrpCompIso (F := Over.pullback p)
            (G := Over.pullback
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst p))).app G).symm.inv.hom.hom =
            𝟙 _ := by
        change 𝟙 _ = 𝟙 _
        rfl
      have hn₁ :
          ((Functor.mapGrpNatIso
            (Over.pullbackComp
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst p) p)).app G).symm.hom.hom.hom =
            ((Over.pullbackComp
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst p) p).app G.X).inv := by
        apply Over.OverMorphism.ext
        rfl
      have hn₂ :
          ((Functor.mapGrpNatIso
            (Over.pullbackComp
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p) p)).app G).symm.inv.hom.hom =
            ((Over.pullbackComp
              (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond p) p).app G.X).hom := by
        apply Over.OverMorphism.ext
        rfl
      simp only [Over.comp_left]
      rw [hc₁, hn₁, hc₃, hn₂]
      simp
    rw [hcompG, hcompK] at hgroup'
  sorry

/-- A closed subgroup object with finite-locally-free structure recorded. -/
structure Chapter12FiniteLocallyFreeGroupClosedSubgroup {S : Scheme.{u}}
    (G : Chapter12GroupScheme S) where
  subgroup : Chapter12GroupScheme S
  inclusion : subgroup ⟶ G
  closed : IsClosedImmersion (Chapter12GroupScheme.homScheme inclusion)
  finiteLocallyFree : Chapter12FiniteLocallyFree subgroup.X.hom

theorem chapter12_finiteLocallyFree_group_closed_subgroup_descends
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FpqcCover p)
    (D_G D_K : Chapter12GroupSchemeDescentDatum p)
    {G : Chapter12GroupScheme S}
    (eG : Chapter12GroupScheme.baseChange p G ≅ D_G.upstairs)
    (heG : chapter12GroupSchemeDescentComparisonCompatible D_G G eG)
    (iT : D_K.upstairs ⟶ D_G.upstairs)
    (hiT : chapter12DescentHomCompatible D_K D_G iT)
    (hclosed : IsClosedImmersion (Chapter12GroupScheme.homScheme iT))
    (hfiniteLocallyFree : Chapter12FiniteLocallyFree D_K.upstairs.X.hom) :
    ∃ (K : Chapter12GroupScheme S) (i : K ⟶ G)
      (eK : Chapter12GroupScheme.baseChange p K ≅ D_K.upstairs),
      chapter12GroupSchemeDescentComparisonCompatible D_K K eK ∧
        IsClosedImmersion (Chapter12GroupScheme.homScheme i) ∧
          Chapter12FiniteLocallyFree K.X.hom ∧
            Chapter12GroupScheme.baseChangeHom p i = eK.hom ≫ iT ≫ eG.inv := by
  obtain ⟨K, i, eK, heK, hclosedK, hbase⟩ :=
    chapter12_group_closed_subgroup_descends p hp D_G D_K eG heG iT hiT hclosed
  refine ⟨K, i, eK, heK, hclosedK, ?_, hbase⟩
  exact chapter12_finiteLocallyFree_descends p hp K D_K.upstairs eK hfiniteLocallyFree

/-- A closed subgroup object in the slice. -/
structure Chapter12ClosedSubgroup {S : Scheme.{u}}
    (G : Chapter12CommutativeGroupScheme S) where
  subgroup : Chapter12CommutativeGroupScheme S
  inclusion : subgroup ⟶ G
  closed : IsClosedImmersion (Chapter12CommutativeGroupScheme.homScheme inclusion)

/-- The closed-subgroup package with its finite-locally-free property recorded. -/
structure Chapter12FiniteLocallyFreeClosedSubgroup {S : Scheme.{u}}
    (G : Chapter12CommutativeGroupScheme S) where
  subgroup : Chapter12CommutativeGroupScheme S
  inclusion : subgroup ⟶ G
  closed : IsClosedImmersion (Chapter12CommutativeGroupScheme.homScheme inclusion)
  finiteLocallyFree : Chapter12FiniteLocallyFree subgroup.X.hom

@[ext]
theorem chapter12ClosedSubgroup.ext {S : Scheme.{u}}
    {G : Chapter12CommutativeGroupScheme S}
    {K L : Chapter12ClosedSubgroup G}
    (h : K.subgroup = L.subgroup) (hi : HEq K.inclusion L.inclusion) : K = L := by
  cases K
  cases L
  cases h
  cases hi
  rfl

/-! Homomorphisms descend uniquely once their underlying morphism has descended. -/

theorem chapter12_homomorphism_descends
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FpqcCover p)
    (D₁ D₂ : Chapter12GroupSchemeDescentDatum p)
    {G H : Chapter12GroupScheme S}
    (eG : Chapter12GroupScheme.baseChange p G ≅ D₁.upstairs)
    (heG : chapter12GroupSchemeDescentComparisonCompatible D₁ G eG)
    (eH : Chapter12GroupScheme.baseChange p H ≅ D₂.upstairs)
    (heH : chapter12GroupSchemeDescentComparisonCompatible D₂ H eH)
    (fT : D₁.upstairs ⟶ D₂.upstairs)
    (hfT : chapter12DescentHomCompatible D₁ D₂ fT) :
    ∃ f : G ⟶ H,
      Chapter12GroupScheme.baseChangeHom p f = eG.hom ≫ fT ≫ eH.inv := by
  sorry

theorem chapter12_faithfullyFlatLocallyOfFinitePresentation_homomorphism_descends
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FpqcCover p)
    (D₁ D₂ : Chapter12GroupSchemeDescentDatum p)
    {G H : Chapter12GroupScheme S}
    (eG : Chapter12GroupScheme.baseChange p G ≅ D₁.upstairs)
    (heG : chapter12GroupSchemeDescentComparisonCompatible D₁ G eG)
    (eH : Chapter12GroupScheme.baseChange p H ≅ D₂.upstairs)
    (heH : chapter12GroupSchemeDescentComparisonCompatible D₂ H eH)
    (fT : D₁.upstairs ⟶ D₂.upstairs)
    (hfT : chapter12DescentHomCompatible D₁ D₂ fT)
    (hfflfp : Chapter12FaithfullyFlatLocallyOfFinitePresentation
      (Chapter12GroupScheme.homScheme fT)) :
    ∃ f : G ⟶ H,
      Chapter12FaithfullyFlatLocallyOfFinitePresentation
        (Chapter12GroupScheme.homScheme f) ∧
      Chapter12GroupScheme.baseChangeHom p f = eG.hom ≫ fT ≫ eH.inv := by
  sorry

theorem chapter12_commutative_faithfullyFlatLocallyOfFinitePresentation_homomorphism_descends
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FpqcCover p)
    (D₁ D₂ : Chapter12CommutativeGroupSchemeDescentDatum p)
    {G H : Chapter12CommutativeGroupScheme S}
    (eG : Chapter12CommutativeGroupScheme.baseChange p G ≅ D₁.upstairs)
    (heG : chapter12CommutativeGroupSchemeDescentComparisonCompatible D₁ G eG)
    (eH : Chapter12CommutativeGroupScheme.baseChange p H ≅ D₂.upstairs)
    (heH : chapter12CommutativeGroupSchemeDescentComparisonCompatible D₂ H eH)
    (fT : D₁.upstairs ⟶ D₂.upstairs)
    (hfT : chapter12CommutativeDescentHomCompatible D₁ D₂ fT)
    (hfflfp : Chapter12FaithfullyFlatLocallyOfFinitePresentation
      (Chapter12CommutativeGroupScheme.homScheme fT)) :
    ∃ f : G ⟶ H,
      Chapter12FaithfullyFlatLocallyOfFinitePresentation
        (Chapter12CommutativeGroupScheme.homScheme f) ∧
      Chapter12CommutativeGroupScheme.baseChangeHom p f = eG.hom ≫ fT ≫ eH.inv := by
  sorry

theorem chapter12_commutative_homomorphism_descends
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FpqcCover p)
    (D₁ D₂ : Chapter12CommutativeGroupSchemeDescentDatum p)
    {G H : Chapter12CommutativeGroupScheme S}
    (eG : Chapter12CommutativeGroupScheme.baseChange p G ≅ D₁.upstairs)
    (heG : chapter12CommutativeGroupSchemeDescentComparisonCompatible D₁ G eG)
    (eH : Chapter12CommutativeGroupScheme.baseChange p H ≅ D₂.upstairs)
    (heH : chapter12CommutativeGroupSchemeDescentComparisonCompatible D₂ H eH)
    (fT : D₁.upstairs ⟶ D₂.upstairs)
    (hfT : chapter12CommutativeDescentHomCompatible D₁ D₂ fT) :
    ∃ f : G ⟶ H,
      Chapter12CommutativeGroupScheme.baseChangeHom p f = eG.hom ≫ fT ≫ eH.inv := by
  sorry

theorem chapter12_commutative_homomorphism_descends_unique
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FpqcCover p)
    {G H : Chapter12CommutativeGroupScheme S} (f g : G ⟶ H)
    (h : Chapter12CommutativeGroupScheme.baseChangeHom p f =
      Chapter12CommutativeGroupScheme.baseChangeHom p g) :
    f = g := by
  exact chapter12_commutative_group_hom_ext_of_faithfullyFlat p
    ⟨hp.2.1, hp.2.2⟩ f g h

theorem chapter12_homomorphism_descends_unique
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FpqcCover p)
    {G H : Chapter12GroupScheme S} (f g : G ⟶ H)
    (h : Chapter12GroupScheme.baseChangeHom p f =
      Chapter12GroupScheme.baseChangeHom p g) :
    f = g := by
  exact chapter12_group_hom_ext_of_faithfullyFlat p ⟨hp.2.1, hp.2.2⟩ f g h

theorem chapter12_closed_subgroup_descends
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FpqcCover p)
    (D_G D_K : Chapter12CommutativeGroupSchemeDescentDatum p)
    {G : Chapter12CommutativeGroupScheme S}
    (eG : Chapter12CommutativeGroupScheme.baseChange p G ≅ D_G.upstairs)
    (heG : chapter12CommutativeGroupSchemeDescentComparisonCompatible D_G G eG)
    (iT : D_K.upstairs ⟶ D_G.upstairs)
    (hiT : chapter12CommutativeDescentHomCompatible D_K D_G iT)
    (hclosed : IsClosedImmersion
      (Chapter12CommutativeGroupScheme.homScheme iT)) :
    ∃ (K : Chapter12CommutativeGroupScheme S) (i : K ⟶ G)
      (eK : Chapter12CommutativeGroupScheme.baseChange p K ≅ D_K.upstairs),
      chapter12CommutativeGroupSchemeDescentComparisonCompatible D_K K eK ∧
        IsClosedImmersion (Chapter12CommutativeGroupScheme.homScheme i) ∧
        Chapter12CommutativeGroupScheme.baseChangeHom p i = eK.hom ≫ iT ≫ eG.inv := by
  sorry

theorem chapter12_finiteLocallyFree_closed_subgroup_descends
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FpqcCover p)
    (D_G D_K : Chapter12CommutativeGroupSchemeDescentDatum p)
    {G : Chapter12CommutativeGroupScheme S}
    (eG : Chapter12CommutativeGroupScheme.baseChange p G ≅ D_G.upstairs)
    (heG : chapter12CommutativeGroupSchemeDescentComparisonCompatible D_G G eG)
    (iT : D_K.upstairs ⟶ D_G.upstairs)
    (hiT : chapter12CommutativeDescentHomCompatible D_K D_G iT)
    (hclosed : IsClosedImmersion
      (Chapter12CommutativeGroupScheme.homScheme iT))
    (hfiniteLocallyFree : Chapter12FiniteLocallyFree D_K.upstairs.X.hom) :
    ∃ (K : Chapter12CommutativeGroupScheme S) (i : K ⟶ G)
      (eK : Chapter12CommutativeGroupScheme.baseChange p K ≅ D_K.upstairs),
      chapter12CommutativeGroupSchemeDescentComparisonCompatible D_K K eK ∧
        IsClosedImmersion (Chapter12CommutativeGroupScheme.homScheme i) ∧
          Chapter12FiniteLocallyFree K.X.hom ∧
        Chapter12CommutativeGroupScheme.baseChangeHom p i = eK.hom ≫ iT ≫ eG.inv := by
  obtain ⟨K, i, eK, heK, hclosedK, hbase⟩ :=
    chapter12_closed_subgroup_descends p hp D_G D_K eG heG iT hiT hclosed
  refine ⟨K, i, eK, heK, hclosedK, ?_, hbase⟩
  let K' : Chapter12GroupScheme S := K.toGrp
  let eK' : Chapter12GroupScheme.baseChange p K' ≅ D_K.upstairs.toGrp :=
    (CommGrp.forget₂Grp (Over T)).mapIso eK
  simpa [K'] using
    (chapter12_finiteLocallyFree_descends p hp K' D_K.upstairs.toGrp eK'
      hfiniteLocallyFree)

/-! ### Exact sequences -/

/--
An exact sequence of commutative group schemes.  The first map is identified with the kernel by a
pullback square, and the second map is required to be fppf; this is the fppf-sheaf exactness
convention used in the source.
-/
structure Chapter12ExactSequence
    {S : Scheme.{u}}
    (G' G G'' : Chapter12CommutativeGroupScheme S) where
  inclusion : G' ⟶ G
  projection : G ⟶ G''
  kernel : Chapter12CommutativeGroupScheme S
  kernelMap : kernel ⟶ G
  kernelIso : G' ≅ kernel
  kernelIso_inclusion : kernelIso.hom ≫ kernelMap = inclusion
  kernelIsPullback :
    IsPullback
      (Chapter12CommutativeGroupScheme.homScheme kernelMap)
      kernel.X.hom
      (Chapter12CommutativeGroupScheme.homScheme projection)
      (η[G''.X].left)
  projectionFppf : Chapter12Fppf (Chapter12CommutativeGroupScheme.homScheme projection)

@[simp]
theorem Chapter12ExactSequence.kernelMap_comp_projection
    {S : Scheme.{u}}
    {G' G G'' : Chapter12CommutativeGroupScheme S}
    (E : Chapter12ExactSequence G' G G'') :
    Chapter12CommutativeGroupScheme.homScheme E.kernelMap ≫
        Chapter12CommutativeGroupScheme.homScheme E.projection =
      E.kernel.X.hom ≫ η[G''.X].left := by
  exact E.kernelIsPullback.w

theorem chapter12_kernel_is_stable_under_base_change
    {S T : Scheme.{u}} (p : T ⟶ S)
    {G' G G'' : Chapter12CommutativeGroupScheme S}
    (E : Chapter12ExactSequence G' G G'') :
    IsPullback
      (Chapter12CommutativeGroupScheme.homScheme
        (Chapter12CommutativeGroupScheme.baseChangeHom p E.kernelMap))
      (Chapter12CommutativeGroupScheme.baseChange p E.kernel).X.hom
      (Chapter12CommutativeGroupScheme.homScheme
        (Chapter12CommutativeGroupScheme.baseChangeHom p E.projection))
      (η[(Chapter12CommutativeGroupScheme.baseChange p G'').X].left) := by
  have hE_over :
      IsPullback E.kernelMap.hom.hom.hom (CartesianMonoidalCategory.toUnit E.kernel.X)
        E.projection.hom.hom.hom (η[G''.X]) := by
    apply IsPullback.of_map (Over.forget S)
    · apply Over.OverMorphism.ext
      simp
    · simpa [Chapter12CommutativeGroupScheme.homScheme] using E.kernelIsPullback
  have hmapped := hE_over.map (Over.pullback p)
  let ε := Functor.LaxMonoidal.ε (Over.pullback p)
  have hone :
      η[((Over.pullback p).mapCommGrp.obj G'').X] =
        ε ≫ (Over.pullback p).map η[G''.X] := by
    rfl
  have hdesired_over :
      IsPullback ((Over.pullback p).map E.kernelMap.hom.hom.hom)
        (CartesianMonoidalCategory.toUnit ((Over.pullback p).obj E.kernel.X))
        ((Over.pullback p).map E.projection.hom.hom.hom)
        (η[((Over.pullback p).mapCommGrp.obj G'').X]) := by
    apply hmapped.of_iso (Iso.refl _) (Iso.refl _) (asIso ε).symm (Iso.refl _)
    · simp
    · exact CartesianMonoidalCategory.toUnit_unique _ _
    · simp
    · rw [← cancel_epi ε]
      rw [hone]
      simp [ε]
  have hscheme := hdesired_over.map (Over.forget T)
  exact hscheme

/-- An exact sequence whose three terms are finite locally free. -/
structure Chapter12FiniteLocallyFreeExactSequence
    {S : Scheme.{u}}
    (G' G G'' : Chapter12CommutativeGroupScheme S) where
  exact : Chapter12ExactSequence G' G G''
  finiteLocallyFree_left : Chapter12FiniteLocallyFree G'.X.hom
  finiteLocallyFree_middle : Chapter12FiniteLocallyFree G.X.hom
  finiteLocallyFree_right : Chapter12FiniteLocallyFree G''.X.hom

theorem chapter12_exact_sequence_descends
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FpqcCover p)
    (D' D D'' : Chapter12CommutativeGroupSchemeDescentDatum p)
    (E_T : Chapter12ExactSequence D'.upstairs D.upstairs D''.upstairs)
    (hfinite' : Chapter12FiniteLocallyFree D'.upstairs.X.hom)
    (hfinite : Chapter12FiniteLocallyFree D.upstairs.X.hom)
    (hfinite'' : Chapter12FiniteLocallyFree D''.upstairs.X.hom)
    (hi : chapter12CommutativeDescentHomCompatible D' D E_T.inclusion)
    (hq : chapter12CommutativeDescentHomCompatible D D'' E_T.projection) :
    ∃ (G' G G'' : Chapter12CommutativeGroupScheme S)
      (E : Chapter12FiniteLocallyFreeExactSequence G' G G''),
      ∃ (e' : Chapter12CommutativeGroupScheme.baseChange p G' ≅ D'.upstairs)
        (e : Chapter12CommutativeGroupScheme.baseChange p G ≅ D.upstairs)
        (e'' : Chapter12CommutativeGroupScheme.baseChange p G'' ≅ D''.upstairs),
        chapter12CommutativeGroupSchemeDescentComparisonCompatible D' G' e' ∧
          chapter12CommutativeGroupSchemeDescentComparisonCompatible D G e ∧
          chapter12CommutativeGroupSchemeDescentComparisonCompatible D'' G'' e'' ∧
          Chapter12CommutativeGroupScheme.baseChangeHom p E.exact.inclusion =
            e'.hom ≫ E_T.inclusion ≫ e.inv ∧
          Chapter12CommutativeGroupScheme.baseChangeHom p E.exact.projection =
            e.hom ≫ E_T.projection ≫ e''.inv := by
  sorry

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter12
