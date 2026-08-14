import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.Section01TheNerveOfACover

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u v v' u'

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04

noncomputable section

/-! ## 4.2 Objects, isomorphisms, and cocycles -/

/-- The object over `T` underlying singleton descent data. -/
def chapter04DescentObject
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S T : Scheme.{u}} {p : T ⟶ S} (D : Chapter04SingleDescentData F p) :
    Chapter04FiberObject F T :=
  D.obj PUnit.unit

/-- The book-facing compatibility isomorphism on the double overlap. -/
def chapter04DescentIsomorphism
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S T : Scheme.{u}} {p : T ⟶ S} (D : Chapter04SingleDescentData F p) :
    (Chapter04PullbackFunctor F (chapter04P1 p)).obj (chapter04DescentObject F D) ≅
      (Chapter04PullbackFunctor F (chapter04P2 p)).obj (chapter04DescentObject F D) :=
  D.iso (chapter04P1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit)
    (chapter04P1 p) (chapter04P2 p)

theorem chapter04DescentData_normalized
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S T : Scheme.{u}} {p : T ⟶ S} (D : Chapter04SingleDescentData F p) :
    D.hom p (i₁ := PUnit.unit) (i₂ := PUnit.unit) (𝟙 T) (𝟙 T) = 𝟙 _ := by
  exact D.hom_self p (𝟙 T) (by simp)

/-- The cocycle written on the three maps from the triple overlap to `T`. -/
theorem chapter04DescentData_cocycle
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S T : Scheme.{u}} {p : T ⟶ S} (D : Chapter04SingleDescentData F p) :
    D.hom (chapter04P3 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit)
        (chapter04P12 p ≫ chapter04P1 p)
        (chapter04P12 p ≫ chapter04P2 p)
        ((Category.assoc (chapter04P12 p) (chapter04P1 p) p).trans
          (chapter04P12_base p)) ≫
        D.hom (chapter04P3 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit)
          (chapter04P12 p ≫ chapter04P2 p)
          (chapter04P3 p) =
      D.hom (chapter04P3 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit)
        (chapter04P12 p ≫ chapter04P1 p)
        (chapter04P3 p)
        ((Category.assoc (chapter04P12 p) (chapter04P1 p) p).trans
          (chapter04P12_base p)) := by
  simpa using
    (D.hom_comp (chapter04P3 p ≫ p)
      (chapter04P12 p ≫ chapter04P1 p)
      (chapter04P12 p ≫ chapter04P2 p)
      (chapter04P3 p)
      ((Category.assoc (chapter04P12 p) (chapter04P1 p) p).trans
        (chapter04P12_base p))
      (chapter04P12_second_base p)
      rfl)

/-- The same cocycle, displayed as pullback along the named maps `p₁₂`, `p₂₃`, and `p₁₃`. -/
theorem chapter04DescentData_cocycle_on_named_projections
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S T : Scheme.{u}} {p : T ⟶ S} (D : Chapter04SingleDescentData F p) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (D.hom (chapter04P1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit)
            (chapter04P1 p) (chapter04P2 p))
          (chapter04P12 p) (chapter04P12 p ≫ chapter04P1 p)
            (chapter04P12 p ≫ chapter04P2 p) ≫
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (D.hom (chapter04P1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit)
            (chapter04P1 p) (chapter04P2 p))
          (chapter04P23 p) (chapter04P12 p ≫ chapter04P2 p) (chapter04P3 p) =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (D.hom (chapter04P1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit)
          (chapter04P1 p) (chapter04P2 p))
        (chapter04P13 p) (chapter04P12 p ≫ chapter04P1 p) (chapter04P3 p) := by
  have h₁ := D.pullHom_hom (i₁ := PUnit.unit) (i₂ := PUnit.unit)
    (chapter04P12 p) (chapter04P1 p ≫ p) (chapter04P3 p ≫ p)
    ((Category.assoc (chapter04P12 p) (chapter04P1 p) p).trans
      (chapter04P12_base p))
    (chapter04P1 p) (chapter04P2 p) rfl (chapter04P1_base p).symm
    (chapter04P12 p ≫ chapter04P1 p) (chapter04P12 p ≫ chapter04P2 p) rfl rfl
  have h₂ := D.pullHom_hom (i₁ := PUnit.unit) (i₂ := PUnit.unit)
    (chapter04P23 p) (chapter04P1 p ≫ p) (chapter04P3 p ≫ p)
    (by
      rw [← Category.assoc, chapter04P23_fst]
      simpa only [Category.assoc] using (chapter04P12_second_base p))
    (chapter04P1 p) (chapter04P2 p) rfl (chapter04P1_base p).symm
    (chapter04P12 p ≫ chapter04P2 p) (chapter04P3 p)
    (chapter04P23_fst p) (chapter04P23_snd p)
  have h₃ := D.pullHom_hom (i₁ := PUnit.unit) (i₂ := PUnit.unit)
    (chapter04P13 p) (chapter04P1 p ≫ p) (chapter04P3 p ≫ p)
    (by
      rw [← Category.assoc, chapter04P13_fst]
      simpa only [Category.assoc] using (chapter04P12_base p))
    (chapter04P1 p) (chapter04P2 p) rfl (chapter04P1_base p).symm
    (chapter04P12 p ≫ chapter04P1 p) (chapter04P3 p)
    (chapter04P13_fst p) (chapter04P13_snd p)
  rw [h₁, h₂, h₃]
  exact D.hom_comp (chapter04P3 p ≫ p)
    (chapter04P12 p ≫ chapter04P1 p)
    (chapter04P12 p ≫ chapter04P2 p)
    (chapter04P3 p)
    ((Category.assoc (chapter04P12 p) (chapter04P1 p) p).trans
      (chapter04P12_base p))
    (chapter04P12_second_base p)
    rfl

/-- An idempotent automorphism is the identity; this is the abstract normalization warning. -/
theorem chapter04_idempotent_iso_eq_refl {C : Type u'} [Category.{v'} C] {X : C}
    (e : X ≅ X) (h : e.hom ≫ e.hom = e.hom) : e = Iso.refl X := by
  apply Iso.ext
  apply (cancel_mono e.hom).1
  simpa using h

/-- Swapping the two factors turns the compatibility isomorphism into its inverse. -/
theorem chapter04DescentData_transposed_eq_symm
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S T : Scheme.{u}} {p : T ⟶ S} (D : Chapter04SingleDescentData F p) :
    D.iso (chapter04P1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit)
        (chapter04P2 p) (chapter04P1 p) =
      (chapter04DescentIsomorphism F D).symm := by
  rfl

/-- The canonical datum obtained by pulling an object over `S` back to `T`. -/
def chapter04CanonicalDescentData
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S T : Scheme.{u}} (p : T ⟶ S) (E : Chapter04FiberObject F S) :
    Chapter04SingleDescentData F p :=
  (F.toDescentData (ι := PUnit.{1}) (X := fun _ : PUnit.{1} => T)
      (fun _ : PUnit.{1} => p)).obj E

/-- The pullback functor from objects over `S` to singleton descent data. -/
def chapter04DescentComparison
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S T : Scheme.{u}} (p : T ⟶ S) :
    Chapter04FiberObject F S ⥤ Chapter04SingleDescentData F p :=
  F.toDescentData (ι := PUnit.{1}) (X := fun _ : PUnit.{1} => T)
    (fun _ : PUnit.{1} => p)

def chapter04CanonicalDescentDatum
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S T : Scheme.{u}} (p : T ⟶ S) (E : Chapter04FiberObject F S) :
    Chapter04SingleDescentData F p :=
  (chapter04DescentComparison F p).obj E

/-- Full faithfulness of pullback is the uniqueness part of descent. -/
def Chapter04DescentIsFullyFaithful
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S T : Scheme.{u}} (p : T ⟶ S) : Prop :=
  Nonempty (chapter04DescentComparison F p).FullyFaithful

/-- Essential surjectivity of pullback is the existence part of descent. -/
def Chapter04DescentIsEssentiallySurjective
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S T : Scheme.{u}} (p : T ⟶ S) : Prop :=
  Functor.EssSurj (chapter04DescentComparison F p)

/-- Effective descent means that the pullback comparison is an equivalence. -/
def Chapter04DescentIsEffective
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S T : Scheme.{u}} (p : T ⟶ S) : Prop :=
  Functor.IsEquivalence (chapter04DescentComparison F p)

theorem chapter04DescentIsEffective_iff
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S T : Scheme.{u}} (p : T ⟶ S) :
    Chapter04DescentIsEffective F p ↔
    Chapter04DescentIsFullyFaithful F p ∧
        Chapter04DescentIsEssentiallySurjective F p := by
  change Functor.IsEquivalence (chapter04DescentComparison F p) ↔
    Nonempty (chapter04DescentComparison F p).FullyFaithful ∧
      Functor.EssSurj (chapter04DescentComparison F p)
  constructor
  · intro h
    let _ : Functor.IsEquivalence (chapter04DescentComparison F p) := h
    exact ⟨⟨Functor.FullyFaithful.ofFullyFaithful _⟩, inferInstance⟩
  · rintro ⟨⟨hFF⟩, hEssSurj⟩
    let _ : (chapter04DescentComparison F p).FullyFaithful := hFF
    exact ⟨hFF.faithful, hFF.full, hEssSurj⟩

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04
