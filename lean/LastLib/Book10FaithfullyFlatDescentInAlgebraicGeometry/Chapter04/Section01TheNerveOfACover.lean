import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.Core

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04

noncomputable section

/-! ## 4.1 The nerve of a cover -/

noncomputable def chapter04CechNerve_zero_iso {S T : Scheme.{u}} (p : T ⟶ S) :
    Chapter04NerveLevel p 0 ≅ T := by
  change widePullback S (fun _ : Fin 1 => T) (fun _ => p) ≅ T
  let s : WidePullbackCone (fun _ : Fin 1 => p) :=
    WidePullbackCone.mk p (fun _ => 𝟙 T) (by intro i; simp)
  let hs : IsLimit s :=
    WidePullbackCone.IsLimit.mk s
      (fun t => t.π 0)
      (fun t => by
        change t.π 0 ≫ p = t.base
        exact WidePullbackCone.condition t 0)
      (fun t i => by
        change t.π 0 ≫ 𝟙 T = t.π i
        rw [Category.comp_id]
        congr 1
        exact Subsingleton.elim 0 i)
      (fun t m hbase hπ => by
        dsimp [s, WidePullbackCone.mk, WidePullbackShape.mkCone] at m ⊢
        simpa only [s, WidePullbackCone.mk, WidePullbackShape.mkCone, WidePullbackCone.π,
          Category.comp_id] using
          hπ 0)
  exact (limit.isLimit _).conePointUniqueUpToIso hs

noncomputable def chapter04CechNerve_one_iso {S T : Scheme.{u}} (p : T ⟶ S) :
    Chapter04NerveLevel p 1 ≅ chapter04PairProduct p := by
  change widePullback S (fun _ : Fin 2 => T) (fun _ => p) ≅ chapter04PairProduct p
  let s : WidePullbackCone (fun _ : Fin 2 => p) :=
    WidePullbackCone.mk (chapter04P1 p ≫ p)
      (fun i => Fin.cases (chapter04P1 p) (fun _ => chapter04P2 p) i)
      (by
        intro i
        fin_cases i
        · rfl
        · change chapter04P2 p ≫ p = chapter04P1 p ≫ p
          simpa [chapter04PairProduct, chapter04P1, chapter04P2] using
            (pullback.condition (f := p) (g := p)).symm)
  let hs : IsLimit s := by
    let π0 (t : WidePullbackCone (fun _ : Fin 2 => p)) : t.pt ⟶ T := by
      exact t.π 0
    let π1 (t : WidePullbackCone (fun _ : Fin 2 => p)) : t.pt ⟶ T := by
      exact t.π 1
    refine WidePullbackCone.IsLimit.mk s
      (fun t => pullback.lift (π0 t) (π1 t) (by
        change π0 t ≫ p = π1 t ≫ p
        change t.π 0 ≫ p = t.π 1 ≫ p
        rw [WidePullbackCone.condition t 0, WidePullbackCone.condition t 1]))
      (fun t => by
        dsimp [s, chapter04PairProduct, chapter04P1, chapter04P2, WidePullbackCone.mk,
          WidePullbackShape.mkCone, WidePullbackCone.base, WidePullbackCone.π]
        rw [← Category.assoc, pullback.lift_fst]
        exact WidePullbackCone.condition t 0)
      (fun t i => by
        fin_cases i
        · dsimp [s, chapter04PairProduct, chapter04P1, chapter04P2, WidePullbackCone.mk,
            WidePullbackShape.mkCone, WidePullbackCone.base, WidePullbackCone.π]
          exact pullback.lift_fst _ _ _
        · dsimp [s, chapter04PairProduct, chapter04P1, chapter04P2, WidePullbackCone.mk,
            WidePullbackShape.mkCone, WidePullbackCone.base, WidePullbackCone.π]
          exact pullback.lift_snd _ _ _)
      (fun t m hbase hπ => by
        dsimp [s, chapter04PairProduct, chapter04P1, chapter04P2, WidePullbackCone.mk,
          WidePullbackShape.mkCone, WidePullbackCone.base, WidePullbackCone.π] at m ⊢
        apply pullback.hom_ext
        · have h := hπ 0
          dsimp [s, chapter04PairProduct, chapter04P1, chapter04P2, WidePullbackCone.mk,
            WidePullbackShape.mkCone, WidePullbackCone.base, WidePullbackCone.π] at h
          rw [pullback.lift_fst]
          exact h
        · have h := hπ 1
          dsimp [s, chapter04PairProduct, chapter04P1, chapter04P2, WidePullbackCone.mk,
            WidePullbackShape.mkCone, WidePullbackCone.base, WidePullbackCone.π] at h
          rw [pullback.lift_snd]
          exact h)
  simpa [s, WidePullbackCone.mk, WidePullbackShape.mkCone] using
    (limit.isLimit _).conePointUniqueUpToIso hs

noncomputable def chapter04CechNerve_two_iso {S T : Scheme.{u}} (p : T ⟶ S) :
    Chapter04NerveLevel p 2 ≅ chapter04TripleProduct p := by
  change widePullback S (fun _ : Fin 3 => T) (fun _ => p) ≅ chapter04TripleProduct p
  let s : WidePullbackCone (fun _ : Fin 3 => p) :=
    WidePullbackCone.mk
      (pullback.fst (pullback.fst p p ≫ p) p ≫ pullback.fst p p ≫ p)
      (fun i =>
        Fin.cases (pullback.fst (pullback.fst p p ≫ p) p ≫ pullback.fst p p)
          (fun j =>
            Fin.cases (pullback.fst (pullback.fst p p ≫ p) p ≫ pullback.snd p p)
              (fun _ => pullback.snd (pullback.fst p p ≫ p) p) j) i)
      (by
        intro i
        fin_cases i
        · rfl
        · change
            (pullback.fst (pullback.fst p p ≫ p) p ≫ pullback.snd p p) ≫ p =
              (pullback.fst (pullback.fst p p ≫ p) p ≫ pullback.fst p p) ≫ p
          simpa [Category.assoc] using
            congrArg (fun q => pullback.fst (pullback.fst p p ≫ p) p ≫ q)
              (pullback.condition (f := p) (g := p)).symm
        · change pullback.snd (pullback.fst p p ≫ p) p ≫ p =
            pullback.fst (pullback.fst p p ≫ p) p ≫ pullback.fst p p ≫ p
          simpa [Category.assoc] using
            (pullback.condition (f := pullback.fst p p ≫ p) (g := p)).symm)
  let hs : IsLimit s := by
    let π0 (t : WidePullbackCone (fun _ : Fin 3 => p)) : t.pt ⟶ T := by
      exact t.π 0
    let π1 (t : WidePullbackCone (fun _ : Fin 3 => p)) : t.pt ⟶ T := by
      exact t.π 1
    let π2 (t : WidePullbackCone (fun _ : Fin 3 => p)) : t.pt ⟶ T := by
      exact t.π 2
    let pairLift (t : WidePullbackCone (fun _ : Fin 3 => p)) :
        t.pt ⟶ pullback p p := by
      exact pullback.lift (π0 t) (π1 t) (by
        change π0 t ≫ p = π1 t ≫ p
        change t.π 0 ≫ p = t.π 1 ≫ p
        rw [WidePullbackCone.condition t 0, WidePullbackCone.condition t 1])
    let tripleLift (t : WidePullbackCone (fun _ : Fin 3 => p)) :
        t.pt ⟶ pullback (pullback.fst p p ≫ p) p := by
      exact pullback.lift (pairLift t) (π2 t) (by
        change pairLift t ≫ (pullback.fst p p ≫ p) = π2 t ≫ p
        dsimp [pairLift]
        rw [← Category.assoc, pullback.lift_fst]
        change π0 t ≫ p = π2 t ≫ p
        change t.π 0 ≫ p = t.π 2 ≫ p
        rw [WidePullbackCone.condition t 0, WidePullbackCone.condition t 2])
    refine WidePullbackCone.IsLimit.mk s
      tripleLift
      (fun t => by
        dsimp [s, tripleLift, pairLift, chapter04TripleProduct, chapter04PairProduct,
          chapter04P12, chapter04P1, chapter04P2, chapter04P3, WidePullbackCone.mk,
          WidePullbackShape.mkCone, WidePullbackCone.base, WidePullbackCone.π]
        rw [← Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst]
        exact WidePullbackCone.condition t 0)
      (fun t i => by
        fin_cases i
        · dsimp [s, tripleLift, pairLift, chapter04TripleProduct, chapter04PairProduct,
            chapter04P12, chapter04P1, chapter04P2, chapter04P3, WidePullbackCone.mk,
            WidePullbackShape.mkCone, WidePullbackCone.base, WidePullbackCone.π]
          change _ = π0 t
          rw [← Category.assoc, pullback.lift_fst, pullback.lift_fst]
        · dsimp [s, tripleLift, pairLift, chapter04TripleProduct, chapter04PairProduct,
            chapter04P12, chapter04P1, chapter04P2, chapter04P3, WidePullbackCone.mk,
            WidePullbackShape.mkCone, WidePullbackCone.base, WidePullbackCone.π]
          change
            (pullback.lift (pairLift t) (π2 t) _) ≫
                (pullback.fst (pullback.fst p p ≫ p) p ≫ pullback.snd p p) = π1 t
          rw [← Category.assoc, pullback.lift_fst, pullback.lift_snd]
        · dsimp [s, tripleLift, pairLift, chapter04TripleProduct, chapter04PairProduct,
            chapter04P12, chapter04P1, chapter04P2, chapter04P3, WidePullbackCone.mk,
            WidePullbackShape.mkCone, WidePullbackCone.base, WidePullbackCone.π]
          change
            (pullback.lift (pairLift t) (π2 t) _) ≫
                pullback.snd (pullback.fst p p ≫ p) p = π2 t
          rw [pullback.lift_snd])
      (fun t m hbase hπ => by
        dsimp [s, tripleLift, pairLift, chapter04TripleProduct, chapter04PairProduct,
          chapter04P12, chapter04P1, chapter04P2, chapter04P3, WidePullbackCone.mk,
          WidePullbackShape.mkCone, WidePullbackCone.base, WidePullbackCone.π] at m ⊢
        apply pullback.hom_ext
        · rw [pullback.lift_fst]
          apply pullback.hom_ext
          · have h := hπ 0
            dsimp [s, WidePullbackCone.mk, WidePullbackShape.mkCone, WidePullbackCone.π] at h
            change
              m ≫ (pullback.fst (pullback.fst p p ≫ p) p ≫ pullback.fst p p) = π0 t at h
            rw [pullback.lift_fst]
            exact h
          · have h := hπ 1
            dsimp [s, WidePullbackCone.mk, WidePullbackShape.mkCone, WidePullbackCone.π] at h
            change
              m ≫ (pullback.fst (pullback.fst p p ≫ p) p ≫ pullback.snd p p) = π1 t at h
            rw [pullback.lift_snd]
            exact h
        · have h := hπ 2
          dsimp [s, WidePullbackCone.mk, WidePullbackShape.mkCone, WidePullbackCone.π] at h
          change m ≫ pullback.snd (pullback.fst p p ≫ p) p = π2 t at h
          rw [pullback.lift_snd]
          exact h)
  simpa [s, chapter04TripleProduct, chapter04PairProduct, chapter04P1,
    WidePullbackCone.mk, WidePullbackShape.mkCone] using
    (limit.isLimit _).conePointUniqueUpToIso hs

@[reassoc (attr := simp)]
theorem chapter04P1_base {S T : Scheme.{u}} (p : T ⟶ S) :
    chapter04P1 p ≫ p = chapter04P2 p ≫ p := by
  exact pullback.condition

@[reassoc (attr := simp)]
theorem chapter04P12_base {S T : Scheme.{u}} (p : T ⟶ S) :
    chapter04P12 p ≫ chapter04P1 p ≫ p = chapter04P3 p ≫ p := by
  simpa [chapter04TripleProduct, chapter04P12, chapter04P1, chapter04P3, Category.assoc] using
    (pullback.condition (f := chapter04P1 p ≫ p) (g := p))

@[reassoc (attr := simp)]
theorem chapter04P12_second_base {S T : Scheme.{u}} (p : T ⟶ S) :
    chapter04P12 p ≫ chapter04P2 p ≫ p = chapter04P3 p ≫ p := by
  rw [← chapter04P1_base p]
  exact chapter04P12_base p

@[reassoc (attr := simp)]
theorem chapter04P12_fst {S T : Scheme.{u}} (p : T ⟶ S) :
    chapter04P12 p ≫ chapter04P1 p =
      chapter04P12 p ≫ pullback.fst p p := by
  rfl

@[reassoc (attr := simp)]
theorem chapter04P23_fst {S T : Scheme.{u}} (p : T ⟶ S) :
    chapter04P23 p ≫ chapter04P1 p = chapter04P12 p ≫ chapter04P2 p := by
  change
    pullback.lift (chapter04P12 p ≫ chapter04P2 p) (chapter04P3 p) _ ≫
        pullback.fst p p = chapter04P12 p ≫ chapter04P2 p
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem chapter04P23_snd {S T : Scheme.{u}} (p : T ⟶ S) :
    chapter04P23 p ≫ chapter04P2 p = chapter04P3 p := by
  simp [chapter04PairProduct, chapter04TripleProduct, chapter04P23, chapter04P2,
    chapter04P3, pullback.lift_snd]

@[reassoc (attr := simp)]
theorem chapter04P13_fst {S T : Scheme.{u}} (p : T ⟶ S) :
    chapter04P13 p ≫ chapter04P1 p = chapter04P12 p ≫ chapter04P1 p := by
  change
    pullback.lift (chapter04P12 p ≫ chapter04P1 p) (chapter04P3 p) _ ≫
        pullback.fst p p = chapter04P12 p ≫ chapter04P1 p
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem chapter04P13_snd {S T : Scheme.{u}} (p : T ⟶ S) :
    chapter04P13 p ≫ chapter04P2 p = chapter04P3 p := by
  simp [chapter04PairProduct, chapter04TripleProduct, chapter04P13, chapter04P2,
    chapter04P3, pullback.lift_snd]

/-- The diagonal repeats the sole factor in the double overlap. -/
def chapter04Diagonal {S T : Scheme.{u}} (p : T ⟶ S) :
    T ⟶ chapter04PairProduct p :=
  pullback.diagonal p

@[reassoc (attr := simp)]
theorem chapter04Diagonal_p1 {S T : Scheme.{u}} (p : T ⟶ S) :
    chapter04Diagonal p ≫ chapter04P1 p = 𝟙 T := by
  simp [chapter04PairProduct, chapter04Diagonal, chapter04P1]

@[reassoc (attr := simp)]
theorem chapter04Diagonal_p2 {S T : Scheme.{u}} (p : T ⟶ S) :
    chapter04Diagonal p ≫ chapter04P2 p = 𝟙 T := by
  simp [chapter04PairProduct, chapter04Diagonal, chapter04P2]

/-- The transposition exchanges the two factors of the double overlap. -/
def chapter04Transposition {S T : Scheme.{u}} (p : T ⟶ S) :
    chapter04PairProduct p ⟶ chapter04PairProduct p :=
  pullback.lift (chapter04P2 p) (chapter04P1 p) (by
    simpa [chapter04PairProduct, chapter04P1, chapter04P2] using
      (pullback.condition (f := p) (g := p)).symm)

@[reassoc (attr := simp)]
theorem chapter04Transposition_p1 {S T : Scheme.{u}} (p : T ⟶ S) :
    chapter04Transposition p ≫ chapter04P1 p = chapter04P2 p := by
  simpa [chapter04PairProduct, chapter04Transposition, chapter04P1, chapter04P2] using
    (pullback.lift_fst (pullback.snd p p) (pullback.fst p p) _)

@[reassoc (attr := simp)]
theorem chapter04Transposition_p2 {S T : Scheme.{u}} (p : T ⟶ S) :
    chapter04Transposition p ≫ chapter04P2 p = chapter04P1 p := by
  simpa [chapter04PairProduct, chapter04Transposition, chapter04P1, chapter04P2] using
    (pullback.lift_snd (pullback.snd p p) (pullback.fst p p) _)

theorem chapter04Transposition_involutive {S T : Scheme.{u}} (p : T ⟶ S) :
    chapter04Transposition p ≫ chapter04Transposition p = 𝟙 _ := by
  apply pullback.hom_ext
  · change
      (chapter04Transposition p ≫ chapter04Transposition p) ≫ chapter04P1 p =
        (𝟙 _ : chapter04PairProduct p ⟶ chapter04PairProduct p) ≫ chapter04P1 p
    simp only [Category.assoc, chapter04Transposition_p1, chapter04Transposition_p2,
      Category.id_comp]
  · change
      (chapter04Transposition p ≫ chapter04Transposition p) ≫ chapter04P2 p =
        (𝟙 _ : chapter04PairProduct p ⟶ chapter04PairProduct p) ≫ chapter04P2 p
    simp only [Category.assoc, chapter04Transposition_p1, chapter04Transposition_p2,
      Category.id_comp]

theorem chapter04Transposition_diagonal {S T : Scheme.{u}} (p : T ⟶ S) :
    chapter04Diagonal p ≫ chapter04Transposition p = chapter04Diagonal p := by
  apply pullback.hom_ext
  · change
      (chapter04Diagonal p ≫ chapter04Transposition p) ≫ chapter04P1 p =
        chapter04Diagonal p ≫ chapter04P1 p
    simp only [Category.assoc, chapter04Transposition_p1, chapter04Diagonal_p2,
      chapter04Diagonal_p1]
  · change
      (chapter04Diagonal p ≫ chapter04Transposition p) ≫ chapter04P2 p =
        chapter04Diagonal p ≫ chapter04P2 p
    simp only [Category.assoc, chapter04Transposition_p2, chapter04Diagonal_p1,
      chapter04Diagonal_p2]

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04
