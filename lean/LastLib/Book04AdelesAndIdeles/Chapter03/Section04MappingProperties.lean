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

theorem chapter03_restrictedProductMap_comp
    {G'' : I → Type z} [∀ i, Group (G'' i)]
    (H : ∀ i, Subgroup (G i)) (H' : ∀ i, Subgroup (G' i))
    (H'' : ∀ i, Subgroup (G'' i))
    (f : ∀ i, G i →* G' i) (g : ∀ i, G' i →* G'' i)
    (hf : chapter03CoordinatewiseMapCondition H H' f)
    (hg : chapter03CoordinatewiseMapCondition H' H'' g) :
    (chapter03RestrictedProductMap H' H'' g hg).comp
        (chapter03RestrictedProductMap H H' f hf) =
      chapter03RestrictedProductMap H H''
        (fun i => (g i).comp (f i)) (by
          filter_upwards [hf, hg] with i hfi hgi
          intro x hx
          exact hgi _ (hfi _ hx)) := by
  apply MonoidHom.ext
  intro x
  apply chapter03_restrictedProduct_ext H''
  intro i
  rfl

theorem chapter03_restrictedProductMap_continuous
    [∀ i, TopologicalSpace (G i)] [∀ i, TopologicalSpace (G' i)]
    [∀ i, IsTopologicalGroup (G i)] [∀ i, IsTopologicalGroup (G' i)]
    (H : ∀ i, Subgroup (G i)) (H' : ∀ i, Subgroup (G' i))
    (hH : ∀ i, IsOpen (H i : Set (G i)))
    (f : ∀ i, G i →* G' i)
    (hf : chapter03CoordinatewiseMapCondition H H' f)
    (hcont : ∀ i, Continuous (f i)) :
    Continuous (chapter03RestrictedProductMap H H' f hf) := by
  classical
  rw [continuous_generateFrom_iff]
  rintro _ ⟨V, hV, rfl⟩
  have hE : {i | V i ≠ (H' i : Set (G' i))}.Finite := by
    exact Filter.eventually_cofinite.mp hV.2
  have hA : {i | ¬ ∀ z, z ∈ H i → f i z ∈ H' i}.Finite := by
    exact Filter.eventually_cofinite.mp hf
  apply isOpen_iff_mem_nhds.2
  intro x hx
  have hB : (chapter03ExceptionalSet H (x : ∀ i, G i)).Finite := by
    exact (chapter03_restrictedProduct_mem_iff_exceptional_finite H
      (x : ∀ i, G i)).1 x.property
  let S : Set I := {i | V i ≠ (H' i : Set (G' i))} ∪
    {i | ¬ ∀ z, z ∈ H i → f i z ∈ H' i} ∪
    chapter03ExceptionalSet H (x : ∀ i, G i)
  have hS : S.Finite := by
    exact (hE.union hA).union hB
  let W : ∀ i, Set (G i) := fun i =>
    if i ∈ S then (f i) ⁻¹' V i else (H i : Set (G i))
  have hW : chapter03BasicProductCondition H W := by
    constructor
    · intro i
      by_cases hi : i ∈ S
      · simpa [W, hi] using (hcont i).isOpen_preimage (V i) (hV.1 i)
      · simpa [W, hi] using hH i
    · filter_upwards [hS.compl_mem_cofinite] with i hi
      have hi' : i ∉ S := by simpa using hi
      simp [W, hi']
  have hxV : x ∈ chapter03BasicProductSet H W := by
    intro i
    by_cases hi : i ∈ S
    · have hxiV : f i ((x : ∀ i, G i) i) ∈ V i := by
        change ∀ i, f i ((x : ∀ i, G i) i) ∈ V i at hx
        exact hx i
      simpa [W, hi] using hxiV
    · have hiB : i ∉ chapter03ExceptionalSet H (x : ∀ i, G i) := by
        intro hiB
        apply hi
        change i ∈
          ({j | V j ≠ (H' j : Set (G' j))} ∪
            {j | ¬ ∀ z, z ∈ H j → f j z ∈ H' j}) ∪
            chapter03ExceptionalSet H (x : ∀ i, G i)
        exact Or.inr hiB
      have hxi : ((x : ∀ i, G i) i) ∈ H i := by
        simpa [chapter03ExceptionalSet] using hiB
      simpa [W, hi] using hxi
  have hsubset : chapter03BasicProductSet H W ⊆
      (chapter03RestrictedProductMap H H' f hf) ⁻¹'
        chapter03BasicProductSet H' V := by
    intro y hy
    change ∀ i, f i ((y : ∀ i, G i) i) ∈ V i
    intro i
    by_cases hi : i ∈ S
    · simpa [W, hi] using hy i
    · have hiE : V i = (H' i : Set (G' i)) := by
        by_contra hne
        apply hi
        change i ∈
          ({j | V j ≠ (H' j : Set (G' j))} ∪
            {j | ¬ ∀ z, z ∈ H j → f j z ∈ H' j}) ∪
            chapter03ExceptionalSet H (x : ∀ i, G i)
        exact Or.inl (Or.inl hne)
      have hiA : ∀ z, z ∈ H i → f i z ∈ H' i := by
        intro z hz
        by_contra hnot
        apply hi
        change i ∈
          ({j | V j ≠ (H' j : Set (G' j))} ∪
            {j | ¬ ∀ z, z ∈ H j → f j z ∈ H' j}) ∪
            chapter03ExceptionalSet H (x : ∀ i, G i)
        exact Or.inl (Or.inr (by
          intro hAll
          exact hnot (hAll z hz)))
      have hyH : ((y : ∀ i, G i) i) ∈ H i := by
        simpa [W, hi] using hy i
      rw [hiE]
      exact hiA _ hyH
  exact mem_of_superset
    ((chapter03_basicProductSet_isOpen H W hW).mem_nhds hxV) hsubset

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
  constructor
  · intro hF S
    exact hF.comp continuous_induced_dom
  · intro hF
    rw [continuous_def]
    intro U hU
    apply isOpen_iff_mem_nhds.2
    intro x hx
    have hfin : (chapter03ExceptionalSet H (x : ∀ i, G i)).Finite := by
      exact (chapter03_restrictedProduct_mem_iff_exceptional_finite H
        (x : ∀ i, G i)).1 x.property
    let S : Chapter03FiniteStageIndex :=
      ⟨chapter03ExceptionalSet H (x : ∀ i, G i), hfin⟩
    have hxS : x ∈ (chapter03StageSubgroup H S.1) := by
      intro i hi
      exact not_not.mp hi
    let xs : Chapter03Stage H S.1 := ⟨x, hxS⟩
    have hopenStage :
        IsOpen ((chapter03StageRestriction H S.1 F) ⁻¹' U) :=
      (hF S).isOpen_preimage U hU
    rcases isOpen_induced_iff.mp hopenStage with ⟨V, hV, hVeq⟩
    let W : Set (Chapter03RestrictedProduct H) :=
      V ∩ (chapter03StageSubgroup H S.1 : Set (Chapter03RestrictedProduct H))
    have hW : IsOpen W := by
      exact hV.inter (chapter03_stage_isOpen H S.2 hH)
    have hxV : x ∈ V := by
      have hxs : xs ∈ (chapter03StageRestriction H S.1 F) ⁻¹' U := by
        change F x ∈ U
        exact hx
      have : xs ∈ (fun y : Chapter03Stage H S.1 => (y : Chapter03RestrictedProduct H)) ⁻¹' V := by
        rw [hVeq]
        exact hxs
      exact this
    have hxW : x ∈ W := ⟨hxV, hxS⟩
    have hsubset : W ⊆ F ⁻¹' U := by
      intro y hy
      let ys : Chapter03Stage H S.1 := ⟨y, hy.2⟩
      have hys : ys ∈ (fun z : Chapter03Stage H S.1 =>
          (z : Chapter03RestrictedProduct H)) ⁻¹' V := by
        exact hy.1
      have hys' : ys ∈ (chapter03StageRestriction H S.1 F) ⁻¹' U := by
        rw [← hVeq]
        exact hys
      exact hys'
    exact mem_of_superset (hW.mem_nhds hxW) hsubset

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
  have hstage : ∀ S : Chapter03FiniteStageIndex,
      Continuous (chapter03StageRestriction H S.1 F) ↔
        ContinuousAt (chapter03StageRestriction H S.1 F) 1 := by
    intro S
    let _ : IsTopologicalGroup (Chapter03Stage H S.1) :=
      topologicalGroup_induced (chapter03StageSubgroup H S.1).subtype
    constructor
    · intro h
      exact h.continuousAt
    · intro h
      apply continuous_of_continuousAt_one
        (F.comp (chapter03StageSubgroup H S.1).subtype)
      simpa [chapter03StageRestriction, chapter03StageInclusion, Function.comp_def] using h
  constructor
  · intro hF S
    exact (hstage S).1
      ((chapter03_continuous_iff_stage_restrictions_continuous H hH F).1 hF S)
  · intro hF
    apply (chapter03_continuous_iff_stage_restrictions_continuous H hH F).2
    intro S
    exact (hstage S).2 (hF S)

/-- Equality of local inverse images gives equality of the distinguished tail
under a coordinatewise map. -/
theorem chapter03_restrictedProductMap_preimage_distinguishedTail
    (H : ∀ i, Subgroup (G i)) (H' : ∀ i, Subgroup (G' i))
    (f : ∀ i, G i →* G' i)
    (hf : chapter03CoordinatewiseMapCondition H H' f)
    (hpreimage : ∀ i, ∀ x, f i x ∈ H' i ↔ x ∈ H i) :
    (chapter03RestrictedProductMap H H' f hf) ⁻¹'
        chapter03DistinguishedTail H' = chapter03DistinguishedTail H := by
  ext x
  change (chapter03RestrictedProductMap H H' f hf x) ∈
      chapter03DistinguishedTail H' ↔ x ∈ chapter03DistinguishedTail H
  rw [chapter03_distinguishedTail_mem_iff,
    chapter03_distinguishedTail_mem_iff]
  constructor
  · intro hx i
    exact (hpreimage i ((x : ∀ i, G i) i)).1 (hx i)
  · intro hx i
    exact (hpreimage i ((x : ∀ i, G i) i)).2 (hx i)

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
  ext x
  change (chapter03RestrictedProductMap H H' f hf x) ∈
      chapter03DistinguishedTail H' ↔
    x ∈ chapter03CoordinatewiseTailSet H
      (chapter03CoordinatewisePreimageSubgroups H' f)
  rw [chapter03_distinguishedTail_mem_iff]
  rfl

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
  · have heq : ∀ᶠ i in Filter.cofinite,
        chapter03CoordinatewisePreimageSubgroups H' f i = H i :=
      hpreimage.mono fun i hi => Subgroup.ext fun x => hi x
    simpa using (Filter.eventually_cofinite.mp heq)

theorem chapter03_restrictedProductMap_preimage_tail_is_finite_change
    (H : ∀ i, Subgroup (G i)) (H' : ∀ i, Subgroup (G' i))
    (f : ∀ i, G i →* G' i)
    (hpreimage : ∀ᶠ i in Filter.cofinite,
      ∀ x, f i x ∈ H' i ↔ x ∈ H i) :
    {i | chapter03CoordinatewisePreimageSubgroups H' f i ≠ H i}.Finite := by
  have heq : ∀ᶠ i in Filter.cofinite,
      chapter03CoordinatewisePreimageSubgroups H' f i = H i :=
    hpreimage.mono fun i hi => Subgroup.ext fun x => hi x
  simpa using (Filter.eventually_cofinite.mp heq)

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
  have hx : ∀ᶠ i in Filter.cofinite,
      ((x : ∀ i, G i) i) ∈ H i :=
    (chapter03_restrictedProduct_mem_iff H (x : ∀ i, G i)).1 x.property
  have htrivial : ∀ᶠ i in Filter.cofinite,
      φ i ((x : ∀ i, G i) i) = 1 :=
    (hφ.and hx).mono fun i hi => hi.1 _ hi.2
  simpa [chapter03ScalarExceptionalSet] using
    (Filter.eventually_cofinite.mp htrivial)

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

theorem chapter03_restrictedScalarProduct_is_defined
    {M : Type w} [CommMonoid M] [TopologicalSpace M]
    (H : ∀ i, Subgroup (G i)) (φ : ∀ i, G i →* M)
    (hφ : chapter03ScalarProductTailCondition H φ)
    (x : Chapter03RestrictedProduct H) :
    chapter03ScalarProductIsDefined
      (fun i y => φ i y) (x : ∀ i, G i) := by
  exact Or.inl (chapter03_restrictedScalarProduct_has_finite_support H φ hφ x)

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
