import LastLib.Book04AdelesAndIdeles.Chapter03.Section03LocalCompactnessAndCompactOpens

namespace LastLib.Book04AdelesAndIdeles.Chapter03

open Set Filter Function
open scoped BigOperators Pointwise Topology

noncomputable section

/-! ### 3.4 Mapping properties -/

universe u v w z

section CoordinatewiseMaps

variable {I : Type u} {G : I → Type v} {G' : I → Type w}
  [∀ i, Group (G i)] [∀ i, Group (G' i)]

/-- The almost-everywhere condition needed for a family of local homomorphisms
to map one restricted product into another. -/
def chapter03CoordinatewiseMapCondition
    (H : ∀ i, Subgroup (G i)) (H' : ∀ i, Subgroup (G' i))
    (f : ∀ i, G i →* G' i) : Prop :=
  ∀ᶠ i in Filter.cofinite, ∀ x, x ∈ H i → f i x ∈ H' i

/-- The homomorphism induced by a coordinatewise family. -/
def chapter03RestrictedProductMap
    (H : ∀ i, Subgroup (G i)) (H' : ∀ i, Subgroup (G' i))
    (f : ∀ i, G i →* G' i)
    (hf : chapter03CoordinatewiseMapCondition H H' f) :
    Chapter03RestrictedProduct H →* Chapter03RestrictedProduct H' where
  toFun x :=
    ⟨fun i => f i ((x : ∀ i, G i) i), by
      have hx : ∀ᶠ i in Filter.cofinite,
          ((x : ∀ i, G i) i) ∈ H i :=
        (chapter03_restrictedProduct_mem_iff H (x : ∀ i, G i)).1 x.property
      exact (hx.and hf).mono fun i hi => hi.2 _ hi.1⟩
  map_one' := by
    ext i
    simp
  map_mul' := by
    intro x y
    ext i
    simp

theorem chapter03_restrictedProductMap_apply
    (H : ∀ i, Subgroup (G i)) (H' : ∀ i, Subgroup (G' i))
    (f : ∀ i, G i →* G' i)
    (hf : chapter03CoordinatewiseMapCondition H H' f)
    (x : Chapter03RestrictedProduct H) (i : I) :
    ((chapter03RestrictedProductMap H H' f hf x :
      Chapter03RestrictedProduct H') : ∀ i, G' i) i =
      f i ((x : ∀ i, G i) i) := by
  rfl

theorem chapter03_restrictedProductMap_preserves_identity
    (H : ∀ i, Subgroup (G i)) (H' : ∀ i, Subgroup (G' i))
    (f : ∀ i, G i →* G' i)
    (hf : chapter03CoordinatewiseMapCondition H H' f) :
    chapter03RestrictedProductMap H H' f hf 1 = 1 := by
  ext i
  simp

theorem chapter03_restrictedProductMap_comp_apply
    {G'' : I → Type z} [∀ i, Group (G'' i)]
    (H : ∀ i, Subgroup (G i)) (H' : ∀ i, Subgroup (G' i))
    (H'' : ∀ i, Subgroup (G'' i))
    (f : ∀ i, G i →* G' i) (g : ∀ i, G' i →* G'' i)
    (hf : chapter03CoordinatewiseMapCondition H H' f)
    (hg : chapter03CoordinatewiseMapCondition H' H'' g)
    (x : Chapter03RestrictedProduct H) (i : I) :
    ((chapter03RestrictedProductMap H' H'' g hg
        (chapter03RestrictedProductMap H H' f hf x) :
      Chapter03RestrictedProduct H'') : ∀ i, G'' i) i =
      g i (f i ((x : ∀ i, G i) i)) := by
  rfl

theorem chapter03_restrictedProductMap_continuous
    [∀ i, TopologicalSpace (G i)] [∀ i, TopologicalSpace (G' i)]
    [∀ i, IsTopologicalGroup (G i)] [∀ i, IsTopologicalGroup (G' i)]
    (H : ∀ i, Subgroup (G i)) (H' : ∀ i, Subgroup (G' i))
    (hH : ∀ i, IsOpen (H i : Set (G i)))
    (hH' : ∀ i, IsOpen (H' i : Set (G' i)))
    (f : ∀ i, G i →* G' i)
    (hf : chapter03CoordinatewiseMapCondition H H' f)
    (hcont : ∀ i, Continuous (f i)) :
    Continuous (chapter03RestrictedProductMap H H' f hf) := by
  sorry

/-- The identity map between stages and the ambient restricted product. -/
def chapter03StageInclusion
    (H : ∀ i, Subgroup (G i)) (S : Set I) :
    Chapter03Stage H S → Chapter03RestrictedProduct H :=
  fun x => x.1

theorem chapter03_stageInclusion_apply
    (H : ∀ i, Subgroup (G i)) (S : Set I)
    (x : Chapter03Stage H S) :
    chapter03StageInclusion H S x = x.1 :=
  rfl

def chapter03StageRestriction
    {X : Type z} [TopologicalSpace X]
    (H : ∀ i, Subgroup (G i)) (S : Set I) (F : Chapter03RestrictedProduct H → X) :
    Chapter03Stage H S → X :=
  F ∘ chapter03StageInclusion H S

theorem chapter03_continuous_iff_stage_restrictions_continuous
    {X : Type z} [TopologicalSpace X]
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i))
    (hH : ∀ i, IsOpen (H i : Set (G i)))
    (F : Chapter03RestrictedProduct H → X) :
    Continuous F ↔
      ∀ S : Chapter03FiniteStageIndex,
        Continuous (chapter03StageRestriction H S.1 F) := by
  sorry

theorem chapter03_continuous_hom_iff_stage_identity_continuity
    {X : Type z} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i))
    (hH : ∀ i, IsOpen (H i : Set (G i)))
    [∀ i, IsTopologicalGroup (G i)]
    [IsTopologicalGroup (Chapter03RestrictedProduct H)]
    (F : Chapter03RestrictedProduct H →* X) :
    Continuous F ↔
      ∀ S : Chapter03FiniteStageIndex,
        ContinuousAt (chapter03StageRestriction H S.1 F) 1 := by
  sorry

/-- Equality of local inverse images gives equality of the distinguished tail
under a coordinatewise map. -/
theorem chapter03_restrictedProductMap_preimage_distinguishedTail
    (H : ∀ i, Subgroup (G i)) (H' : ∀ i, Subgroup (G' i))
    (f : ∀ i, G i →* G' i)
    (hf : chapter03CoordinatewiseMapCondition H H' f)
    (hpreimage : ∀ i, ∀ x, f i x ∈ H' i ↔ x ∈ H i) :
    (chapter03RestrictedProductMap H H' f hf) ⁻¹'
        chapter03DistinguishedTail H' = chapter03DistinguishedTail H := by
  sorry

def chapter03CoordinatewisePreimageSubgroups
    (H' : ∀ i, Subgroup (G' i)) (f : ∀ i, G i →* G' i) :
    ∀ i, Subgroup (G i) :=
  fun i => (H' i).comap (f i)

def chapter03CoordinatewiseTailSet
    (H : ∀ i, Subgroup (G i)) (K : ∀ i, Subgroup (G i)) :
    Set (Chapter03RestrictedProduct H) :=
  {x | ∀ i, ((x : ∀ i, G i) i) ∈ K i}

theorem chapter03_restrictedProductMap_preimage_distinguishedTail_eq_tailSet
    (H : ∀ i, Subgroup (G i)) (H' : ∀ i, Subgroup (G' i))
    (f : ∀ i, G i →* G' i)
    (hf : chapter03CoordinatewiseMapCondition H H' f) :
    (chapter03RestrictedProductMap H H' f hf) ⁻¹'
        chapter03DistinguishedTail H' =
      chapter03CoordinatewiseTailSet H
        (chapter03CoordinatewisePreimageSubgroups H' f) := by
  sorry

theorem chapter03_restrictedProductMap_preimage_distinguishedTail_of_eventually_preimage
    (H : ∀ i, Subgroup (G i)) (H' : ∀ i, Subgroup (G' i))
    (f : ∀ i, G i →* G' i)
    (hf : chapter03CoordinatewiseMapCondition H H' f)
    (hpreimage : ∀ᶠ i in Filter.cofinite,
      ∀ x, f i x ∈ H' i ↔ x ∈ H i) :
    ((chapter03RestrictedProductMap H H' f hf) ⁻¹'
        chapter03DistinguishedTail H' =
      chapter03CoordinatewiseTailSet H
        (chapter03CoordinatewisePreimageSubgroups H' f)) ∧
      {i | chapter03CoordinatewisePreimageSubgroups H' f i ≠ H i}.Finite := by
  constructor
  · exact chapter03_restrictedProductMap_preimage_distinguishedTail_eq_tailSet
      H H' f hf
  · sorry

theorem chapter03_restrictedProductMap_preimage_tail_is_finite_change
    (H : ∀ i, Subgroup (G i)) (H' : ∀ i, Subgroup (G' i))
    (f : ∀ i, G i →* G' i)
    (hpreimage : ∀ᶠ i in Filter.cofinite,
      ∀ x, f i x ∈ H' i ↔ x ∈ H i) :
    {i | chapter03CoordinatewisePreimageSubgroups H' f i ≠ H i}.Finite := by
  sorry

end CoordinatewiseMaps

section ScalarProducts

variable {I : Type u} {G : I → Type v} [∀ i, Group (G i)]

/-- Local scalar factors are trivial on the distinguished subgroups almost
everywhere. -/
def chapter03ScalarProductTailCondition
    {M : Type w} [CommMonoid M]
    (H : ∀ i, Subgroup (G i)) (φ : ∀ i, G i →* M) : Prop :=
  ∀ᶠ i in Filter.cofinite, ∀ x, x ∈ H i → φ i x = 1

theorem chapter03_scalarExceptionalSet_finite_of_tail_condition
    {M : Type w} [CommMonoid M]
    (H : ∀ i, Subgroup (G i)) (φ : ∀ i, G i →* M)
    (hφ : chapter03ScalarProductTailCondition H φ)
    (x : Chapter03RestrictedProduct H) :
    (chapter03ScalarExceptionalSet (fun i y => φ i y)
      (x : ∀ i, G i)).Finite := by
  sorry

/- The scalar product is defined after the distinguished tail condition has
supplied finite exceptional support. -/
noncomputable def chapter03RestrictedScalarProduct
    {M : Type w} [CommMonoid M]
    (H : ∀ i, Subgroup (G i)) (φ : ∀ i, G i →* M)
    (hφ : chapter03ScalarProductTailCondition H φ)
    (x : Chapter03RestrictedProduct H) : M :=
  chapter03FiniteSupportProduct (fun i y => φ i y) (x : ∀ i, G i)
    (chapter03_scalarExceptionalSet_finite_of_tail_condition H φ hφ x)

theorem chapter03_restrictedScalarProduct_has_finite_support
    {M : Type w} [CommMonoid M]
    (H : ∀ i, Subgroup (G i)) (φ : ∀ i, G i →* M)
    (hφ : chapter03ScalarProductTailCondition H φ)
    (x : Chapter03RestrictedProduct H) :
    chapter03ScalarProductSupportedOnFiniteSet
      (fun i y => φ i y) (x : ∀ i, G i) := by
  exact chapter03_scalarExceptionalSet_finite_of_tail_condition H φ hφ x

theorem chapter03_restrictedScalarProduct_is_one_of_coordinatewise_one
    {M : Type w} [CommMonoid M]
    (H : ∀ i, Subgroup (G i)) (φ : ∀ i, G i →* M)
    (hφtail : chapter03ScalarProductTailCondition H φ)
    (x : Chapter03RestrictedProduct H)
    (hφ : ∀ i, φ i ((x : ∀ i, G i) i) = 1) :
    chapter03RestrictedScalarProduct H φ hφtail x = 1 := by
  exact chapter03_finiteSupportProduct_eq_one _ _ _ hφ

end ScalarProducts

end
end LastLib.Book04AdelesAndIdeles.Chapter03
