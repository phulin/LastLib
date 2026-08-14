import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.Core

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04

noncomputable section

/-! ## 4.1 The nerve of a cover -/

theorem chapter04CechNerve_zero_iso {S T : Scheme.{u}} (p : T ⟶ S) :
    Chapter04NerveLevel p 0 ≅ T := by
  sorry

theorem chapter04CechNerve_one_iso {S T : Scheme.{u}} (p : T ⟶ S) :
    Chapter04NerveLevel p 1 ≅ chapter04PairProduct p := by
  sorry

theorem chapter04CechNerve_two_iso {S T : Scheme.{u}} (p : T ⟶ S) :
    Chapter04NerveLevel p 2 ≅ chapter04TripleProduct p := by
  sorry

@[reassoc (attr := simp)]
theorem chapter04P1_base {S T : Scheme.{u}} (p : T ⟶ S) :
    chapter04P1 p ≫ p = chapter04P2 p ≫ p := by
  simp [chapter04P1, chapter04P2]

@[reassoc (attr := simp)]
theorem chapter04P12_base {S T : Scheme.{u}} (p : T ⟶ S) :
    chapter04P12 p ≫ chapter04P1 p ≫ p = chapter04P3 p ≫ p := by
  simp [chapter04P12, chapter04P3, Category.assoc]

@[reassoc (attr := simp)]
theorem chapter04P12_second_base {S T : Scheme.{u}} (p : T ⟶ S) :
    chapter04P12 p ≫ chapter04P2 p ≫ p = chapter04P3 p ≫ p := by
  simp [chapter04P12, chapter04P3, Category.assoc]

@[reassoc (attr := simp)]
theorem chapter04P12_fst {S T : Scheme.{u}} (p : T ⟶ S) :
    chapter04P12 p ≫ chapter04P1 p =
      chapter04P12 p ≫ pullback.fst p p := by
  rfl

@[reassoc (attr := simp)]
theorem chapter04P23_fst {S T : Scheme.{u}} (p : T ⟶ S) :
    chapter04P23 p ≫ chapter04P1 p = chapter04P12 p ≫ chapter04P2 p := by
  simp [chapter04P23]

@[reassoc (attr := simp)]
theorem chapter04P23_snd {S T : Scheme.{u}} (p : T ⟶ S) :
    chapter04P23 p ≫ chapter04P2 p = chapter04P3 p := by
  simp [chapter04P23]

@[reassoc (attr := simp)]
theorem chapter04P13_fst {S T : Scheme.{u}} (p : T ⟶ S) :
    chapter04P13 p ≫ chapter04P1 p = chapter04P12 p ≫ chapter04P1 p := by
  simp [chapter04P13]

@[reassoc (attr := simp)]
theorem chapter04P13_snd {S T : Scheme.{u}} (p : T ⟶ S) :
    chapter04P13 p ≫ chapter04P2 p = chapter04P3 p := by
  simp [chapter04P13]

/-- The diagonal repeats the sole factor in the double overlap. -/
def chapter04Diagonal {S T : Scheme.{u}} (p : T ⟶ S) :
    T ⟶ chapter04PairProduct p :=
  pullback.diagonal p

@[reassoc (attr := simp)]
theorem chapter04Diagonal_p1 {S T : Scheme.{u}} (p : T ⟶ S) :
    chapter04Diagonal p ≫ chapter04P1 p = 𝟙 T := by
  simp [chapter04Diagonal, chapter04P1]

@[reassoc (attr := simp)]
theorem chapter04Diagonal_p2 {S T : Scheme.{u}} (p : T ⟶ S) :
    chapter04Diagonal p ≫ chapter04P2 p = 𝟙 T := by
  simp [chapter04Diagonal, chapter04P2]

/-- The transposition exchanges the two factors of the double overlap. -/
def chapter04Transposition {S T : Scheme.{u}} (p : T ⟶ S) :
    chapter04PairProduct p ⟶ chapter04PairProduct p :=
  pullback.lift (chapter04P2 p) (chapter04P1 p) (by
    simp [chapter04P1, chapter04P2])

@[reassoc (attr := simp)]
theorem chapter04Transposition_p1 {S T : Scheme.{u}} (p : T ⟶ S) :
    chapter04Transposition p ≫ chapter04P1 p = chapter04P2 p := by
  simp [chapter04Transposition]

@[reassoc (attr := simp)]
theorem chapter04Transposition_p2 {S T : Scheme.{u}} (p : T ⟶ S) :
    chapter04Transposition p ≫ chapter04P2 p = chapter04P1 p := by
  simp [chapter04Transposition]

theorem chapter04Transposition_involutive {S T : Scheme.{u}} (p : T ⟶ S) :
    chapter04Transposition p ≫ chapter04Transposition p = 𝟙 _ := by
  apply pullback.hom_ext
  · simp [Category.assoc]
  · simp [Category.assoc]

theorem chapter04Transposition_diagonal {S T : Scheme.{u}} (p : T ⟶ S) :
    chapter04Diagonal p ≫ chapter04Transposition p = chapter04Diagonal p := by
  apply pullback.hom_ext <;> simp [Category.assoc]

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04
