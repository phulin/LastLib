import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.Core
import Mathlib.Topology.Sets.CompactOpenCovered

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
      (∀ j : J, IsCompact (V j : Set (source (j : I)))) ∧
        (U : Set S) = ⋃ j : J, Set.image (map (j : I)) (V j : Set (source (j : I)))

/-- The same finite-reduction condition, tested only on affine opens of the base. -/
def Chapter04AffineFiniteReduction {S : Scheme.{u}} {I : Type v}
    (source : I → Scheme.{u}) (map : ∀ i, source i ⟶ S) : Prop :=
  ∀ U : S.Opens, IsAffineOpen U → IsCompact (U : Set S) →
    ∃ (J : Finset I) (V : ∀ j : J, (source (j : I)).Opens),
      (∀ j : J, IsCompact (V j : Set (source (j : I)))) ∧
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
  classical
  constructor
  · intro h U _ hUc
    exact h U hUc
  · intro h U hUc
    have hcovered :
        IsCompactOpenCovered (fun i => (map i).base) (U : Set S) := by
      apply IsCompactOpenCovered.of_isCompact_of_forall_exists_isCompactOpenCovered hUc
      intro x hx
      obtain ⟨W, hWaff, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset hx
      obtain ⟨J, V, hV, hVW⟩ := h W hWaff hWaff.isCompact
      refine ⟨(W : Set S), hWU, hxW, W.isOpen, ?_⟩
      refine IsCompactOpenCovered.of_finite (a := fun j : J => (j : I)) V hV ?_
      simpa using hVW.symm
    obtain ⟨s, hs, V, hV, hU⟩ := hcovered
    let J : Finset I := hs.toFinset
    let V' : ∀ j : J, (source (j : I)).Opens := fun j =>
      V j.1 (hs.mem_toFinset.mp j.2)
    refine ⟨J, V', ?_, ?_⟩
    · intro j
      exact hV j.1 (hs.mem_toFinset.mp j.2)
    · rw [← hU]
      ext x
      simp [J, V', hs.mem_toFinset]

theorem chapter04FiniteAffineRefinement
    {S : Scheme.{u}} (𝒯 : Chapter04FpqcCoveringFamily S)
    {U : S.Opens} (hU : IsAffineOpen U) (hUc : IsCompact (U : Set S)) :
    ∃ (n : ℕ) (a : Fin n → 𝒯.index)
      (V : ∀ j : Fin n, (𝒯.source (a j)).Opens),
      (∀ j, IsAffineOpen (V j)) ∧
        (U : Set S) = ⋃ j : Fin n,
          Set.image (𝒯.map (a j)) (V j : Set (𝒯.source (a j))) := by
  have hcovered :
      IsCompactOpenCovered (fun i => (𝒯.map i).base) (U : Set S) := by
    obtain ⟨J, V, hV, hUV⟩ :=
      (chapter04FiniteReduction_iff_affine.mp 𝒯.finiteReduction) U hU hUc
    refine IsCompactOpenCovered.of_finite (κ := J) (fun j => (j : 𝒯.index)) V hV ?_
    simpa using hUV.symm
  obtain ⟨n, a, V, hV, hUV⟩ := hcovered.exists_mem_of_isBasis
    (fun i => (𝒯.source i).isBasis_affineOpens)
    (fun i _ h => h.isCompact)
  exact ⟨n, a, V, hV, hUV.symm⟩

/-- The pairwise overlap for two members of a family. -/
def chapter04FamilyPair {S : Scheme.{u}}
    (𝒯 : Chapter04FpqcCoveringFamily S) (i j : 𝒯.index) : Scheme.{u} :=
  pullback (𝒯.map i) (𝒯.map j)

def chapter04FamilyP1 {S : Scheme.{u}}
    (𝒯 : Chapter04FpqcCoveringFamily S) (i j : 𝒯.index) :
    chapter04FamilyPair 𝒯 i j ⟶ 𝒯.source i :=
  pullback.fst (𝒯.map i) (𝒯.map j)

def chapter04FamilyP2 {S : Scheme.{u}}
    (𝒯 : Chapter04FpqcCoveringFamily S) (i j : 𝒯.index) :
    chapter04FamilyPair 𝒯 i j ⟶ 𝒯.source j :=
  pullback.snd (𝒯.map i) (𝒯.map j)

/-- The triple overlap for an ordered triple of members. -/
def chapter04FamilyTriple {S : Scheme.{u}}
    (𝒯 : Chapter04FpqcCoveringFamily S) (i j k : 𝒯.index) : Scheme.{u} :=
  pullback (chapter04FamilyP1 𝒯 i j ≫ 𝒯.map i) (𝒯.map k)

def chapter04FamilyP12 {S : Scheme.{u}}
    (𝒯 : Chapter04FpqcCoveringFamily S) (i j k : 𝒯.index) :
    chapter04FamilyTriple 𝒯 i j k ⟶ chapter04FamilyPair 𝒯 i j :=
  pullback.fst (chapter04FamilyP1 𝒯 i j ≫ 𝒯.map i) (𝒯.map k)

def chapter04FamilyP3 {S : Scheme.{u}}
    (𝒯 : Chapter04FpqcCoveringFamily S) (i j k : 𝒯.index) :
    chapter04FamilyTriple 𝒯 i j k ⟶ 𝒯.source k :=
  pullback.snd (chapter04FamilyP1 𝒯 i j ≫ 𝒯.map i) (𝒯.map k)

def chapter04FamilyP23 {S : Scheme.{u}}
    (𝒯 : Chapter04FpqcCoveringFamily S) (i j k : 𝒯.index) :
    chapter04FamilyTriple 𝒯 i j k ⟶ chapter04FamilyPair 𝒯 j k :=
  pullback.lift (chapter04FamilyP12 𝒯 i j k ≫ chapter04FamilyP2 𝒯 i j)
    (chapter04FamilyP3 𝒯 i j k)
    (by
      change
        (pullback.fst
              (pullback.fst (𝒯.map i) (𝒯.map j) ≫ 𝒯.map i) (𝒯.map k) ≫
            pullback.snd (𝒯.map i) (𝒯.map j)) ≫ 𝒯.map j =
          pullback.snd
              (pullback.fst (𝒯.map i) (𝒯.map j) ≫ 𝒯.map i) (𝒯.map k) ≫ 𝒯.map k
      rw [Category.assoc,
        ← pullback.condition (f := 𝒯.map i) (g := 𝒯.map j)]
      exact pullback.condition
        (f := pullback.fst (𝒯.map i) (𝒯.map j) ≫ 𝒯.map i) (g := 𝒯.map k))

def chapter04FamilyP13 {S : Scheme.{u}}
    (𝒯 : Chapter04FpqcCoveringFamily S) (i j k : 𝒯.index) :
    chapter04FamilyTriple 𝒯 i j k ⟶ chapter04FamilyPair 𝒯 i k :=
  pullback.lift (chapter04FamilyP12 𝒯 i j k ≫ chapter04FamilyP1 𝒯 i j)
    (chapter04FamilyP3 𝒯 i j k)
    (by
      change
        (pullback.fst
              (pullback.fst (𝒯.map i) (𝒯.map j) ≫ 𝒯.map i) (𝒯.map k) ≫
            pullback.fst (𝒯.map i) (𝒯.map j)) ≫ 𝒯.map i =
          pullback.snd
              (pullback.fst (𝒯.map i) (𝒯.map j) ≫ 𝒯.map i) (𝒯.map k) ≫ 𝒯.map k
      simpa [Category.assoc] using
        (pullback.condition
          (f := pullback.fst (𝒯.map i) (𝒯.map j) ≫ 𝒯.map i) (g := 𝒯.map k)))

@[reassoc (attr := simp)]
theorem chapter04FamilyP23_p1 {S : Scheme.{u}}
    (𝒯 : Chapter04FpqcCoveringFamily S) (i j k : 𝒯.index) :
    chapter04FamilyP23 𝒯 i j k ≫ chapter04FamilyP1 𝒯 j k =
      chapter04FamilyP12 𝒯 i j k ≫ chapter04FamilyP2 𝒯 i j := by
  dsimp [chapter04FamilyP23, chapter04FamilyP1]
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem chapter04FamilyP23_p2 {S : Scheme.{u}}
    (𝒯 : Chapter04FpqcCoveringFamily S) (i j k : 𝒯.index) :
    chapter04FamilyP23 𝒯 i j k ≫ chapter04FamilyP2 𝒯 j k =
      chapter04FamilyP3 𝒯 i j k := by
  dsimp [chapter04FamilyP23, chapter04FamilyP2]
  exact pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem chapter04FamilyP13_p1 {S : Scheme.{u}}
    (𝒯 : Chapter04FpqcCoveringFamily S) (i j k : 𝒯.index) :
    chapter04FamilyP13 𝒯 i j k ≫ chapter04FamilyP1 𝒯 i k =
      chapter04FamilyP12 𝒯 i j k ≫ chapter04FamilyP1 𝒯 i j := by
  dsimp [chapter04FamilyP13, chapter04FamilyP1]
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem chapter04FamilyP13_p2 {S : Scheme.{u}}
    (𝒯 : Chapter04FpqcCoveringFamily S) (i j k : 𝒯.index) :
    chapter04FamilyP13 𝒯 i j k ≫ chapter04FamilyP2 𝒯 i k =
      chapter04FamilyP3 𝒯 i j k := by
  dsimp [chapter04FamilyP13, chapter04FamilyP2]
  exact pullback.lift_snd _ _ _

/-- Descent data for a family, without forming an infinite coproduct. -/
abbrev Chapter04FamilyDescentData
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S : Scheme.{u}} (𝒯 : Chapter04FpqcCoveringFamily S) :=
  F.DescentData 𝒯.map

def chapter04FamilyDescentObject
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S : Scheme.{u}} {𝒯 : Chapter04FpqcCoveringFamily S}
    (D : Chapter04FamilyDescentData F 𝒯) (i : 𝒯.index) :
    Chapter04FiberObject F (𝒯.source i) :=
  D.obj i

/-- The pairwise isomorphism `θᵢⱼ` for a family descent datum. -/
def chapter04FamilyTheta
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S : Scheme.{u}} {𝒯 : Chapter04FpqcCoveringFamily S}
    (D : Chapter04FamilyDescentData F 𝒯) (i j : 𝒯.index) :
    (Chapter04PullbackFunctor F (chapter04FamilyP1 𝒯 i j)).obj
          (chapter04FamilyDescentObject F D i) ≅
      (Chapter04PullbackFunctor F (chapter04FamilyP2 𝒯 i j)).obj
          (chapter04FamilyDescentObject F D j) :=
  D.iso (chapter04FamilyP1 𝒯 i j ≫ 𝒯.map i) (i₁ := i) (i₂ := j)
    (chapter04FamilyP1 𝒯 i j) (chapter04FamilyP2 𝒯 i j) (_hf₂ := by
      change
        pullback.snd (𝒯.map i) (𝒯.map j) ≫ 𝒯.map j =
          pullback.fst (𝒯.map i) (𝒯.map j) ≫ 𝒯.map i
      exact (pullback.condition (f := 𝒯.map i) (g := 𝒯.map j)).symm)

theorem chapter04FamilyDescent_cocycle
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S : Scheme.{u}} {𝒯 : Chapter04FpqcCoveringFamily S}
    (D : Chapter04FamilyDescentData F 𝒯) (i j k : 𝒯.index) :
    D.hom (chapter04FamilyP3 𝒯 i j k ≫ 𝒯.map k)
        (chapter04FamilyP12 𝒯 i j k ≫ chapter04FamilyP1 𝒯 i j)
        (chapter04FamilyP12 𝒯 i j k ≫ chapter04FamilyP2 𝒯 i j)
          (_hf₁ := by
            change
              (pullback.fst
                    (pullback.fst (𝒯.map i) (𝒯.map j) ≫ 𝒯.map i) (𝒯.map k) ≫
                pullback.fst (𝒯.map i) (𝒯.map j)) ≫ 𝒯.map i =
                pullback.snd
                  (pullback.fst (𝒯.map i) (𝒯.map j) ≫ 𝒯.map i) (𝒯.map k) ≫
                  𝒯.map k
            simpa [Category.assoc] using
              (pullback.condition
                (f := pullback.fst (𝒯.map i) (𝒯.map j) ≫ 𝒯.map i)
                (g := 𝒯.map k)))
          (_hf₂ := by
            change
              (pullback.fst
                    (pullback.fst (𝒯.map i) (𝒯.map j) ≫ 𝒯.map i) (𝒯.map k) ≫
                pullback.snd (𝒯.map i) (𝒯.map j)) ≫ 𝒯.map j =
                pullback.snd
                  (pullback.fst (𝒯.map i) (𝒯.map j) ≫ 𝒯.map i) (𝒯.map k) ≫
                  𝒯.map k
            rw [Category.assoc,
              ← pullback.condition (f := 𝒯.map i) (g := 𝒯.map j)]
            exact pullback.condition
              (f := pullback.fst (𝒯.map i) (𝒯.map j) ≫ 𝒯.map i)
              (g := 𝒯.map k)) ≫
        D.hom (chapter04FamilyP3 𝒯 i j k ≫ 𝒯.map k)
          (chapter04FamilyP12 𝒯 i j k ≫ chapter04FamilyP2 𝒯 i j)
          (chapter04FamilyP3 𝒯 i j k) (_hf₁ := by
            change
              (pullback.fst
                    (pullback.fst (𝒯.map i) (𝒯.map j) ≫ 𝒯.map i) (𝒯.map k) ≫
                pullback.snd (𝒯.map i) (𝒯.map j)) ≫ 𝒯.map j =
                pullback.snd
                  (pullback.fst (𝒯.map i) (𝒯.map j) ≫ 𝒯.map i) (𝒯.map k) ≫
                  𝒯.map k
            rw [Category.assoc,
              ← pullback.condition (f := 𝒯.map i) (g := 𝒯.map j)]
            exact pullback.condition
              (f := pullback.fst (𝒯.map i) (𝒯.map j) ≫ 𝒯.map i)
              (g := 𝒯.map k)) =
      D.hom (chapter04FamilyP3 𝒯 i j k ≫ 𝒯.map k)
          (chapter04FamilyP12 𝒯 i j k ≫ chapter04FamilyP1 𝒯 i j)
          (chapter04FamilyP3 𝒯 i j k) (_hf₁ := by
          change
            (pullback.fst
                  (pullback.fst (𝒯.map i) (𝒯.map j) ≫ 𝒯.map i) (𝒯.map k) ≫
              pullback.fst (𝒯.map i) (𝒯.map j)) ≫ 𝒯.map i =
              pullback.snd
                (pullback.fst (𝒯.map i) (𝒯.map j) ≫ 𝒯.map i) (𝒯.map k) ≫
                𝒯.map k
          simpa [Category.assoc] using
            (pullback.condition
                (f := pullback.fst (𝒯.map i) (𝒯.map j) ≫ 𝒯.map i)
              (g := 𝒯.map k))) := by
  have hp_ij :
      chapter04FamilyP1 𝒯 i j ≫ 𝒯.map i =
        chapter04FamilyP2 𝒯 i j ≫ 𝒯.map j := by
    exact pullback.condition (f := 𝒯.map i) (g := 𝒯.map j)
  have hp_jk :
      chapter04FamilyP1 𝒯 j k ≫ 𝒯.map j =
        chapter04FamilyP2 𝒯 j k ≫ 𝒯.map k := by
    exact pullback.condition (f := 𝒯.map j) (g := 𝒯.map k)
  have hp_ik :
      chapter04FamilyP1 𝒯 i k ≫ 𝒯.map i =
        chapter04FamilyP2 𝒯 i k ≫ 𝒯.map k := by
    exact pullback.condition (f := 𝒯.map i) (g := 𝒯.map k)
  have h₁ := D.pullHom_hom
    (chapter04FamilyP12 𝒯 i j k)
    (chapter04FamilyP1 𝒯 i j ≫ 𝒯.map i)
    (chapter04FamilyP3 𝒯 i j k ≫ 𝒯.map k)
    (by
      rw [← Category.assoc]
      exact pullback.condition
        (f := chapter04FamilyP1 𝒯 i j ≫ 𝒯.map i) (g := 𝒯.map k))
    (chapter04FamilyP1 𝒯 i j) (chapter04FamilyP2 𝒯 i j) rfl hp_ij.symm
    (chapter04FamilyP12 𝒯 i j k ≫ chapter04FamilyP1 𝒯 i j)
    (chapter04FamilyP12 𝒯 i j k ≫ chapter04FamilyP2 𝒯 i j) rfl rfl
  have h₂ := D.pullHom_hom
    (chapter04FamilyP23 𝒯 i j k)
    (chapter04FamilyP1 𝒯 j k ≫ 𝒯.map j)
    (chapter04FamilyP3 𝒯 i j k ≫ 𝒯.map k)
    (by
      calc
        chapter04FamilyP23 𝒯 i j k ≫
              (chapter04FamilyP1 𝒯 j k ≫ 𝒯.map j) =
            chapter04FamilyP23 𝒯 i j k ≫
              (chapter04FamilyP2 𝒯 j k ≫ 𝒯.map k) := by rw [hp_jk]
        _ = (chapter04FamilyP23 𝒯 i j k ≫
              chapter04FamilyP2 𝒯 j k) ≫ 𝒯.map k := by simp
        _ = chapter04FamilyP3 𝒯 i j k ≫ 𝒯.map k := by
          rw [chapter04FamilyP23_p2])
    (chapter04FamilyP1 𝒯 j k) (chapter04FamilyP2 𝒯 j k) rfl hp_jk.symm
    (chapter04FamilyP12 𝒯 i j k ≫ chapter04FamilyP2 𝒯 i j)
    (chapter04FamilyP3 𝒯 i j k)
    (chapter04FamilyP23_p1 𝒯 i j k) (chapter04FamilyP23_p2 𝒯 i j k)
  have h₃ := D.pullHom_hom
    (chapter04FamilyP13 𝒯 i j k)
    (chapter04FamilyP1 𝒯 i k ≫ 𝒯.map i)
    (chapter04FamilyP3 𝒯 i j k ≫ 𝒯.map k)
    (by
      calc
        chapter04FamilyP13 𝒯 i j k ≫
              (chapter04FamilyP1 𝒯 i k ≫ 𝒯.map i) =
            chapter04FamilyP13 𝒯 i j k ≫
              (chapter04FamilyP2 𝒯 i k ≫ 𝒯.map k) := by rw [hp_ik]
        _ = (chapter04FamilyP13 𝒯 i j k ≫
              chapter04FamilyP2 𝒯 i k) ≫ 𝒯.map k := by simp
        _ = chapter04FamilyP3 𝒯 i j k ≫ 𝒯.map k := by
          rw [chapter04FamilyP13_p2])
    (chapter04FamilyP1 𝒯 i k) (chapter04FamilyP2 𝒯 i k) rfl hp_ik.symm
    (chapter04FamilyP12 𝒯 i j k ≫ chapter04FamilyP1 𝒯 i j)
    (chapter04FamilyP3 𝒯 i j k)
    (chapter04FamilyP13_p1 𝒯 i j k) (chapter04FamilyP13_p2 𝒯 i j k)
  exact D.hom_comp (chapter04FamilyP3 𝒯 i j k ≫ 𝒯.map k)
    (chapter04FamilyP12 𝒯 i j k ≫ chapter04FamilyP1 𝒯 i j)
    (chapter04FamilyP12 𝒯 i j k ≫ chapter04FamilyP2 𝒯 i j)
    (chapter04FamilyP3 𝒯 i j k)
    _ _ rfl

/-- The family cocycle displayed using the three named triple-overlap projections. -/
theorem chapter04FamilyDescent_cocycle_on_named_projections
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S : Scheme.{u}} {𝒯 : Chapter04FpqcCoveringFamily S}
    (D : Chapter04FamilyDescentData F 𝒯) (i j k : 𝒯.index) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (D.hom (chapter04FamilyP1 𝒯 i j ≫ 𝒯.map i)
            (chapter04FamilyP1 𝒯 i j) (chapter04FamilyP2 𝒯 i j) (_hf₂ := by
              change
                pullback.snd (𝒯.map i) (𝒯.map j) ≫ 𝒯.map j =
                  pullback.fst (𝒯.map i) (𝒯.map j) ≫ 𝒯.map i
              exact (pullback.condition (f := 𝒯.map i) (g := 𝒯.map j)).symm))
          (chapter04FamilyP12 𝒯 i j k)
            (chapter04FamilyP12 𝒯 i j k ≫ chapter04FamilyP1 𝒯 i j)
            (chapter04FamilyP12 𝒯 i j k ≫ chapter04FamilyP2 𝒯 i j) ≫
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (D.hom (chapter04FamilyP1 𝒯 j k ≫ 𝒯.map j)
            (chapter04FamilyP1 𝒯 j k) (chapter04FamilyP2 𝒯 j k) (_hf₂ := by
              change
                pullback.snd (𝒯.map j) (𝒯.map k) ≫ 𝒯.map k =
                  pullback.fst (𝒯.map j) (𝒯.map k) ≫ 𝒯.map j
              exact (pullback.condition (f := 𝒯.map j) (g := 𝒯.map k)).symm))
          (chapter04FamilyP23 𝒯 i j k)
            (chapter04FamilyP12 𝒯 i j k ≫ chapter04FamilyP2 𝒯 i j)
            (chapter04FamilyP3 𝒯 i j k) =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (D.hom (chapter04FamilyP1 𝒯 i k ≫ 𝒯.map i)
          (chapter04FamilyP1 𝒯 i k) (chapter04FamilyP2 𝒯 i k) (_hf₂ := by
            change
              pullback.snd (𝒯.map i) (𝒯.map k) ≫ 𝒯.map k =
                pullback.fst (𝒯.map i) (𝒯.map k) ≫ 𝒯.map i
            exact (pullback.condition (f := 𝒯.map i) (g := 𝒯.map k)).symm))
        (chapter04FamilyP13 𝒯 i j k)
        (chapter04FamilyP12 𝒯 i j k ≫ chapter04FamilyP1 𝒯 i j)
          (chapter04FamilyP3 𝒯 i j k) := by
  have hp_jk :
      chapter04FamilyP1 𝒯 j k ≫ 𝒯.map j =
        chapter04FamilyP2 𝒯 j k ≫ 𝒯.map k := by
    exact pullback.condition (f := 𝒯.map j) (g := 𝒯.map k)
  have hp_ik :
      chapter04FamilyP1 𝒯 i k ≫ 𝒯.map i =
        chapter04FamilyP2 𝒯 i k ≫ 𝒯.map k := by
    exact pullback.condition (f := 𝒯.map i) (g := 𝒯.map k)
  have h₁ := D.pullHom_hom
    (chapter04FamilyP12 𝒯 i j k)
    (chapter04FamilyP1 𝒯 i j ≫ 𝒯.map i)
    (chapter04FamilyP3 𝒯 i j k ≫ 𝒯.map k)
    (by
      rw [← Category.assoc]
      exact pullback.condition
        (f := chapter04FamilyP1 𝒯 i j ≫ 𝒯.map i) (g := 𝒯.map k))
    (chapter04FamilyP1 𝒯 i j) (chapter04FamilyP2 𝒯 i j) rfl
    (pullback.condition (f := 𝒯.map i) (g := 𝒯.map j)).symm
    (chapter04FamilyP12 𝒯 i j k ≫ chapter04FamilyP1 𝒯 i j)
    (chapter04FamilyP12 𝒯 i j k ≫ chapter04FamilyP2 𝒯 i j) rfl rfl
  have h₂ := D.pullHom_hom
    (chapter04FamilyP23 𝒯 i j k)
    (chapter04FamilyP1 𝒯 j k ≫ 𝒯.map j)
    (chapter04FamilyP3 𝒯 i j k ≫ 𝒯.map k)
    (by
      calc
        chapter04FamilyP23 𝒯 i j k ≫
              (chapter04FamilyP1 𝒯 j k ≫ 𝒯.map j) =
            chapter04FamilyP23 𝒯 i j k ≫
              (chapter04FamilyP2 𝒯 j k ≫ 𝒯.map k) := by rw [hp_jk]
        _ = (chapter04FamilyP23 𝒯 i j k ≫
              chapter04FamilyP2 𝒯 j k) ≫ 𝒯.map k := by simp
        _ = chapter04FamilyP3 𝒯 i j k ≫ 𝒯.map k := by
          rw [chapter04FamilyP23_p2])
    (chapter04FamilyP1 𝒯 j k) (chapter04FamilyP2 𝒯 j k) rfl
    (pullback.condition (f := 𝒯.map j) (g := 𝒯.map k)).symm
    (chapter04FamilyP12 𝒯 i j k ≫ chapter04FamilyP2 𝒯 i j)
    (chapter04FamilyP3 𝒯 i j k)
    (chapter04FamilyP23_p1 𝒯 i j k) (chapter04FamilyP23_p2 𝒯 i j k)
  have h₃ := D.pullHom_hom
    (chapter04FamilyP13 𝒯 i j k)
    (chapter04FamilyP1 𝒯 i k ≫ 𝒯.map i)
    (chapter04FamilyP3 𝒯 i j k ≫ 𝒯.map k)
    (by
      calc
        chapter04FamilyP13 𝒯 i j k ≫
              (chapter04FamilyP1 𝒯 i k ≫ 𝒯.map i) =
            chapter04FamilyP13 𝒯 i j k ≫
              (chapter04FamilyP2 𝒯 i k ≫ 𝒯.map k) := by rw [hp_ik]
        _ = (chapter04FamilyP13 𝒯 i j k ≫
              chapter04FamilyP2 𝒯 i k) ≫ 𝒯.map k := by simp
        _ = chapter04FamilyP3 𝒯 i j k ≫ 𝒯.map k := by
          rw [chapter04FamilyP13_p2])
    (chapter04FamilyP1 𝒯 i k) (chapter04FamilyP2 𝒯 i k) rfl
    (pullback.condition (f := 𝒯.map i) (g := 𝒯.map k)).symm
    (chapter04FamilyP12 𝒯 i j k ≫ chapter04FamilyP1 𝒯 i j)
    (chapter04FamilyP3 𝒯 i j k)
    (chapter04FamilyP13_p1 𝒯 i j k) (chapter04FamilyP13_p2 𝒯 i j k)
  rw [h₁, h₂, h₃]
  exact D.hom_comp (chapter04FamilyP3 𝒯 i j k ≫ 𝒯.map k)
    (chapter04FamilyP12 𝒯 i j k ≫ chapter04FamilyP1 𝒯 i j)
    (chapter04FamilyP12 𝒯 i j k ≫ chapter04FamilyP2 𝒯 i j)
    (chapter04FamilyP3 𝒯 i j k)
    _ _ rfl

theorem chapter04FamilyDescent_normalized
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S : Scheme.{u}} {𝒯 : Chapter04FpqcCoveringFamily S}
    (D : Chapter04FamilyDescentData F 𝒯) (i : 𝒯.index) :
    D.hom (𝒯.map i) (𝟙 (𝒯.source i)) (𝟙 (𝒯.source i)) = 𝟙 _ := by
  exact D.hom_self (𝒯.map i) (𝟙 (𝒯.source i)) (by simp)

theorem chapter04FamilyTheta_transposed_eq_symm
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S : Scheme.{u}} {𝒯 : Chapter04FpqcCoveringFamily S}
    (D : Chapter04FamilyDescentData F 𝒯) (i j : 𝒯.index) :
    D.iso (chapter04FamilyP1 𝒯 i j ≫ 𝒯.map i) (i₁ := j) (i₂ := i)
        (chapter04FamilyP2 𝒯 i j) (chapter04FamilyP1 𝒯 i j) (_hf₁ := by
          change
            pullback.snd (𝒯.map i) (𝒯.map j) ≫ 𝒯.map j =
              pullback.fst (𝒯.map i) (𝒯.map j) ≫ 𝒯.map i
          exact (pullback.condition (f := 𝒯.map i) (g := 𝒯.map j)).symm) =
      (chapter04FamilyTheta F D i j).symm := by
  rfl

abbrev Chapter04FamilyDescentMorphism
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S : Scheme.{u}} {𝒯 : Chapter04FpqcCoveringFamily S}
    {D D' : Chapter04FamilyDescentData F 𝒯} :=
  D ⟶ D'

theorem chapter04FamilyMorphism_compatibility
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S : Scheme.{u}} {𝒯 : Chapter04FpqcCoveringFamily S}
    {D D' : Chapter04FamilyDescentData F 𝒯}
    (φ : Chapter04FamilyDescentMorphism F (D := D) (D' := D')) (i j : 𝒯.index) :
    (Chapter04PullbackFunctor F (chapter04FamilyP1 𝒯 i j)).map (φ.hom i) ≫
        (chapter04FamilyTheta F D' i j).hom =
      (chapter04FamilyTheta F D i j).hom ≫
        (Chapter04PullbackFunctor F (chapter04FamilyP2 𝒯 i j)).map (φ.hom j) := by
  exact φ.comm (chapter04FamilyP1 𝒯 i j ≫ 𝒯.map i)
    (chapter04FamilyP1 𝒯 i j) (chapter04FamilyP2 𝒯 i j) rfl
    (pullback.condition (f := 𝒯.map i) (g := 𝒯.map j)).symm

/-- Pullback from `S` to a family of members and its descent-data category. -/
def chapter04FamilyDescentComparison
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S : Scheme.{u}} (𝒯 : Chapter04FpqcCoveringFamily S) :
    Chapter04FiberObject F S ⥤ Chapter04FamilyDescentData F 𝒯 :=
  F.toDescentData 𝒯.map

def Chapter04FamilyDescentIsFullyFaithful
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S : Scheme.{u}} (𝒯 : Chapter04FpqcCoveringFamily S) : Prop :=
  Nonempty (chapter04FamilyDescentComparison F 𝒯).FullyFaithful

def Chapter04FamilyDescentIsEssentiallySurjective
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S : Scheme.{u}} (𝒯 : Chapter04FpqcCoveringFamily S) : Prop :=
  Functor.EssSurj (chapter04FamilyDescentComparison F 𝒯)

def Chapter04FamilyDescentIsEffective
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S : Scheme.{u}} (𝒯 : Chapter04FpqcCoveringFamily S) : Prop :=
  Functor.IsEquivalence (chapter04FamilyDescentComparison F 𝒯)

theorem chapter04FamilyDescentIsEffective_iff
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S : Scheme.{u}} (𝒯 : Chapter04FpqcCoveringFamily S) :
    Chapter04FamilyDescentIsEffective F 𝒯 ↔
      Chapter04FamilyDescentIsFullyFaithful F 𝒯 ∧
        Chapter04FamilyDescentIsEssentiallySurjective F 𝒯 := by
  change Functor.IsEquivalence (chapter04FamilyDescentComparison F 𝒯) ↔
    Nonempty (chapter04FamilyDescentComparison F 𝒯).FullyFaithful ∧
      Functor.EssSurj (chapter04FamilyDescentComparison F 𝒯)
  constructor
  · intro h
    let _ : Functor.IsEquivalence (chapter04FamilyDescentComparison F 𝒯) := h
    exact ⟨⟨Functor.FullyFaithful.ofFullyFaithful _⟩, inferInstance⟩
  · rintro ⟨⟨hFF⟩, hEssSurj⟩
    let _ : (chapter04FamilyDescentComparison F 𝒯).FullyFaithful := hFF
    exact ⟨hFF.faithful, hFF.full, hEssSurj⟩

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04
