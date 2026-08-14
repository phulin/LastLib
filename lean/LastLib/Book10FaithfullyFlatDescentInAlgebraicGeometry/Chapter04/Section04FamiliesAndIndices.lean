import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.Section03MorphismsAndFullFaithfulness

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u v v' u'

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04

noncomputable section

/-! ## 4.4 Families and indices -/

/-- The finite-reduction condition for a family over a scheme. -/
def Chapter04FiniteReduction {S : Scheme.{u}} {I : Type v}
    (source : I → Scheme.{u}) (map : ∀ i, source i ⟶ S) : Prop :=
  ∀ U : S.Opens, IsCompact (U : Set S) →
    ∃ (J : Finset I) (V : ∀ j : J, (source (j : I)).Opens),
      (∀ j, IsCompact (V j : Set (source (j : I)))) ∧
        (U : Set S) = ⋃ j : J, Set.image (map (j : I)) (V j : Set (source (j : I)))

/-- The same finite-reduction condition, tested only on affine opens of the base. -/
def Chapter04AffineFiniteReduction {S : Scheme.{u}} {I : Type v}
    (source : I → Scheme.{u}) (map : ∀ i, source i ⟶ S) : Prop :=
  ∀ U : S.Opens, IsAffineOpen U → IsCompact (U : Set S) →
    ∃ (J : Finset I) (V : ∀ j : J, (source (j : I)).Opens),
      (∀ j, IsCompact (V j : Set (source (j : I)))) ∧
        (U : Set S) = ⋃ j : J, Set.image (map (j : I)) (V j : Set (source (j : I)))

/-- A source-shaped set-indexed fpqc covering family. -/
structure Chapter04FpqcCoveringFamily (S : Scheme.{u}) where
  /-- The index type is bounded by the chosen universe. -/
  index : Type v
  /-- The schemes in the family. -/
  source : index → Scheme.{u}
  /-- The covering maps. -/
  map : ∀ i, source i ⟶ S
  /-- Every component map is flat. -/
  flat : ∀ i, Flat (map i)
  /-- The component maps are jointly surjective on points. -/
  jointlySurjective : ∀ x : S, ∃ i y, map i y = x
  /-- Every quasi-compact open of the base has a finite reduction through quasi-compact opens upstairs. -/
  finiteReduction : Chapter04FiniteReduction source map

theorem chapter04FiniteReduction_iff_affine
    {S : Scheme.{u}} {I : Type v} {source : I → Scheme.{u}}
    {map : ∀ i, source i ⟶ S} :
    Chapter04FiniteReduction source map ↔ Chapter04AffineFiniteReduction source map := by
  sorry

theorem chapter04FiniteAffineRefinement
    {S : Scheme.{u}} (𝒯 : Chapter04FpqcCoveringFamily (v := v) S)
    {U : S.Opens} (hU : IsAffineOpen U) (hUc : IsCompact (U : Set S)) :
    ∃ (J : Finset 𝒯.index) (V : ∀ j : J, (𝒯.source (j : 𝒯.index)).Opens),
      (∀ j, IsAffineOpen (V j)) ∧
        (U : Set S) = ⋃ j : J,
          Set.image (𝒯.map (j : 𝒯.index)) (V j : Set (𝒯.source (j : 𝒯.index))) := by
  sorry

/-- The pairwise overlap for two members of a family. -/
def chapter04FamilyPair {S : Scheme.{u}}
    (𝒯 : Chapter04FpqcCoveringFamily (v := v) S) (i j : 𝒯.index) : Scheme.{u} :=
  pullback (𝒯.map i) (𝒯.map j)

def chapter04FamilyP1 {S : Scheme.{u}}
    (𝒯 : Chapter04FpqcCoveringFamily (v := v) S) (i j : 𝒯.index) :
    chapter04FamilyPair 𝒯 i j ⟶ 𝒯.source i :=
  pullback.fst (𝒯.map i) (𝒯.map j)

def chapter04FamilyP2 {S : Scheme.{u}}
    (𝒯 : Chapter04FpqcCoveringFamily (v := v) S) (i j : 𝒯.index) :
    chapter04FamilyPair 𝒯 i j ⟶ 𝒯.source j :=
  pullback.snd (𝒯.map i) (𝒯.map j)

/-- The triple overlap for an ordered triple of members. -/
def chapter04FamilyTriple {S : Scheme.{u}}
    (𝒯 : Chapter04FpqcCoveringFamily (v := v) S) (i j k : 𝒯.index) : Scheme.{u} :=
  pullback (chapter04FamilyP1 𝒯 i j ≫ 𝒯.map i) (𝒯.map k)

def chapter04FamilyP12 {S : Scheme.{u}}
    (𝒯 : Chapter04FpqcCoveringFamily (v := v) S) (i j k : 𝒯.index) :
    chapter04FamilyTriple 𝒯 i j k ⟶ chapter04FamilyPair 𝒯 i j :=
  pullback.fst (chapter04FamilyP1 𝒯 i j ≫ 𝒯.map i) (𝒯.map k)

def chapter04FamilyP3 {S : Scheme.{u}}
    (𝒯 : Chapter04FpqcCoveringFamily (v := v) S) (i j k : 𝒯.index) :
    chapter04FamilyTriple 𝒯 i j k ⟶ 𝒯.source k :=
  pullback.snd (chapter04FamilyP1 𝒯 i j ≫ 𝒯.map i) (𝒯.map k)

def chapter04FamilyP23 {S : Scheme.{u}}
    (𝒯 : Chapter04FpqcCoveringFamily (v := v) S) (i j k : 𝒯.index) :
    chapter04FamilyTriple 𝒯 i j k ⟶ chapter04FamilyPair 𝒯 j k :=
  pullback.lift
    (chapter04FamilyP12 𝒯 i j k ≫ chapter04FamilyP2 𝒯 i j)
    (chapter04FamilyP3 𝒯 i j k) (by
      rw [Category.assoc, ← pullback.condition_assoc]
      simp [chapter04FamilyP12, chapter04FamilyP3, Category.assoc])

def chapter04FamilyP13 {S : Scheme.{u}}
    (𝒯 : Chapter04FpqcCoveringFamily (v := v) S) (i j k : 𝒯.index) :
    chapter04FamilyTriple 𝒯 i j k ⟶ chapter04FamilyPair 𝒯 i k :=
  pullback.lift
    (chapter04FamilyP12 𝒯 i j k ≫ chapter04FamilyP1 𝒯 i j)
    (chapter04FamilyP3 𝒯 i j k) (by
      simp [chapter04FamilyP12, chapter04FamilyP3, Category.assoc])

@[reassoc (attr := simp)]
theorem chapter04FamilyP23_p1 {S : Scheme.{u}}
    (𝒯 : Chapter04FpqcCoveringFamily (v := v) S) (i j k : 𝒯.index) :
    chapter04FamilyP23 𝒯 i j k ≫ chapter04FamilyP1 𝒯 j k =
      chapter04FamilyP12 𝒯 i j k ≫ chapter04FamilyP2 𝒯 i j := by
  sorry

@[reassoc (attr := simp)]
theorem chapter04FamilyP23_p2 {S : Scheme.{u}}
    (𝒯 : Chapter04FpqcCoveringFamily (v := v) S) (i j k : 𝒯.index) :
    chapter04FamilyP23 𝒯 i j k ≫ chapter04FamilyP2 𝒯 j k =
      chapter04FamilyP3 𝒯 i j k := by
  sorry

@[reassoc (attr := simp)]
theorem chapter04FamilyP13_p1 {S : Scheme.{u}}
    (𝒯 : Chapter04FpqcCoveringFamily (v := v) S) (i j k : 𝒯.index) :
    chapter04FamilyP13 𝒯 i j k ≫ chapter04FamilyP1 𝒯 i k =
      chapter04FamilyP12 𝒯 i j k ≫ chapter04FamilyP1 𝒯 i j := by
  sorry

@[reassoc (attr := simp)]
theorem chapter04FamilyP13_p2 {S : Scheme.{u}}
    (𝒯 : Chapter04FpqcCoveringFamily (v := v) S) (i j k : 𝒯.index) :
    chapter04FamilyP13 𝒯 i j k ≫ chapter04FamilyP2 𝒯 i k =
      chapter04FamilyP3 𝒯 i j k := by
  sorry

/-- Descent data for a family, without forming an infinite coproduct. -/
abbrev Chapter04FamilyDescentData
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S : Scheme.{u}} (𝒯 : Chapter04FpqcCoveringFamily (v := v) S) :=
  F.DescentData 𝒯.map

def chapter04FamilyDescentObject
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S : Scheme.{u}} {𝒯 : Chapter04FpqcCoveringFamily (v := v) S}
    (D : Chapter04FamilyDescentData F 𝒯) (i : 𝒯.index) :
    Chapter04FiberObject F (𝒯.source i) :=
  D.obj i

/-- The pairwise isomorphism `θᵢⱼ` for a family descent datum. -/
def chapter04FamilyTheta
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S : Scheme.{u}} {𝒯 : Chapter04FpqcCoveringFamily (v := v) S}
    (D : Chapter04FamilyDescentData F 𝒯) (i j : 𝒯.index) :
    (Chapter04PullbackFunctor F (chapter04FamilyP1 𝒯 i j)).obj
          (chapter04FamilyDescentObject F D i) ≅
      (Chapter04PullbackFunctor F (chapter04FamilyP2 𝒯 i j)).obj
          (chapter04FamilyDescentObject F D j) :=
  D.iso (chapter04FamilyP1 𝒯 i j ≫ 𝒯.map i) (i₁ := i) (i₂ := j)
    (chapter04FamilyP1 𝒯 i j) (chapter04FamilyP2 𝒯 i j)

theorem chapter04FamilyDescent_cocycle
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S : Scheme.{u}} {𝒯 : Chapter04FpqcCoveringFamily (v := v) S}
    (D : Chapter04FamilyDescentData F 𝒯) (i j k : 𝒯.index) :
    D.hom (chapter04FamilyP3 𝒯 i j k ≫ 𝒯.map k)
        (chapter04FamilyP12 𝒯 i j k ≫ chapter04FamilyP1 𝒯 i j)
        (chapter04FamilyP12 𝒯 i j k ≫ chapter04FamilyP2 𝒯 i j) ≫
        D.hom (chapter04FamilyP3 𝒯 i j k ≫ 𝒯.map k)
          (chapter04FamilyP12 𝒯 i j k ≫ chapter04FamilyP2 𝒯 i j)
          (chapter04FamilyP3 𝒯 i j k) =
      D.hom (chapter04FamilyP3 𝒯 i j k ≫ 𝒯.map k)
        (chapter04FamilyP12 𝒯 i j k ≫ chapter04FamilyP1 𝒯 i j)
        (chapter04FamilyP3 𝒯 i j k) := by
  sorry

/-- The family cocycle displayed using the three named triple-overlap projections. -/
theorem chapter04FamilyDescent_cocycle_on_named_projections
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S : Scheme.{u}} {𝒯 : Chapter04FpqcCoveringFamily (v := v) S}
    (D : Chapter04FamilyDescentData F 𝒯) (i j k : 𝒯.index) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (D.hom (chapter04FamilyP1 𝒯 i j ≫ 𝒯.map i)
            (chapter04FamilyP1 𝒯 i j) (chapter04FamilyP2 𝒯 i j))
          (chapter04FamilyP12 𝒯 i j k)
            (chapter04FamilyP12 𝒯 i j k ≫ chapter04FamilyP1 𝒯 i j)
            (chapter04FamilyP12 𝒯 i j k ≫ chapter04FamilyP2 𝒯 i j) ≫
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (D.hom (chapter04FamilyP1 𝒯 j k ≫ 𝒯.map j)
            (chapter04FamilyP1 𝒯 j k) (chapter04FamilyP2 𝒯 j k))
          (chapter04FamilyP23 𝒯 i j k)
            (chapter04FamilyP12 𝒯 i j k ≫ chapter04FamilyP2 𝒯 i j)
            (chapter04FamilyP3 𝒯 i j k) =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (D.hom (chapter04FamilyP1 𝒯 i k ≫ 𝒯.map i)
          (chapter04FamilyP1 𝒯 i k) (chapter04FamilyP2 𝒯 i k))
        (chapter04FamilyP13 𝒯 i j k)
          (chapter04FamilyP12 𝒯 i j k ≫ chapter04FamilyP1 𝒯 i j)
          (chapter04FamilyP3 𝒯 i j k) := by
  sorry

theorem chapter04FamilyDescent_normalized
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S : Scheme.{u}} {𝒯 : Chapter04FpqcCoveringFamily (v := v) S}
    (D : Chapter04FamilyDescentData F 𝒯) (i : 𝒯.index) :
    D.hom (𝒯.map i) (𝟙 (𝒯.source i)) (𝟙 (𝒯.source i)) = 𝟙 _ := by
  sorry

theorem chapter04FamilyTheta_transposed_eq_symm
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S : Scheme.{u}} {𝒯 : Chapter04FpqcCoveringFamily (v := v) S}
    (D : Chapter04FamilyDescentData F 𝒯) (i j : 𝒯.index) :
    D.iso (chapter04FamilyP1 𝒯 i j ≫ 𝒯.map i) (i₁ := j) (i₂ := i)
        (chapter04FamilyP2 𝒯 i j) (chapter04FamilyP1 𝒯 i j) =
      (chapter04FamilyTheta F D i j).symm := by
  sorry

abbrev Chapter04FamilyDescentMorphism
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S : Scheme.{u}} {𝒯 : Chapter04FpqcCoveringFamily (v := v) S}
    {D D' : Chapter04FamilyDescentData F 𝒯} :=
  D ⟶ D'

theorem chapter04FamilyMorphism_compatibility
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S : Scheme.{u}} {𝒯 : Chapter04FpqcCoveringFamily (v := v) S}
    {D D' : Chapter04FamilyDescentData F 𝒯}
    (φ : Chapter04FamilyDescentMorphism F) (i j : 𝒯.index) :
    (Chapter04PullbackFunctor F (chapter04FamilyP1 𝒯 i j)).map (φ.hom i) ≫
        (chapter04FamilyTheta F D' i j).hom =
      (chapter04FamilyTheta F D i j).hom ≫
        (Chapter04PullbackFunctor F (chapter04FamilyP2 𝒯 i j)).map (φ.hom j) := by
  sorry

/-- Pullback from `S` to a family of members and its descent-data category. -/
def chapter04FamilyDescentComparison
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S : Scheme.{u}} (𝒯 : Chapter04FpqcCoveringFamily (v := v) S) :
    Chapter04FiberObject F S ⥤ Chapter04FamilyDescentData F 𝒯 :=
  F.toDescentData 𝒯.map

def Chapter04FamilyDescentIsFullyFaithful
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S : Scheme.{u}} (𝒯 : Chapter04FpqcCoveringFamily (v := v) S) : Prop :=
  Nonempty (chapter04FamilyDescentComparison F 𝒯).FullyFaithful

def Chapter04FamilyDescentIsEssentiallySurjective
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S : Scheme.{u}} (𝒯 : Chapter04FpqcCoveringFamily (v := v) S) : Prop :=
  Functor.EssSurj (chapter04FamilyDescentComparison F 𝒯)

def Chapter04FamilyDescentIsEffective
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S : Scheme.{u}} (𝒯 : Chapter04FpqcCoveringFamily (v := v) S) : Prop :=
  Functor.IsEquivalence (chapter04FamilyDescentComparison F 𝒯)

theorem chapter04FamilyDescentIsEffective_iff
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S : Scheme.{u}} (𝒯 : Chapter04FpqcCoveringFamily (v := v) S) :
    Chapter04FamilyDescentIsEffective F 𝒯 ↔
      Chapter04FamilyDescentIsFullyFaithful F 𝒯 ∧
        Chapter04FamilyDescentIsEssentiallySurjective F 𝒯 := by
  sorry

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04
