import LastLib.Book04AdelesAndIdeles.Chapter03.Section06CompletenessCountabilityAndQuotients

namespace LastLib.Book04AdelesAndIdeles.Chapter03

open Set Filter
open scoped BigOperators Pointwise Topology

noncomputable section

/-! ### 3.7 Dependence on the distinguished subgroups -/

universe u v w

section FiniteChanges

variable {I : Type u} {G : I → Type v} [∀ i, Group (G i)]

/-- The set of coordinates at which two integral models differ. -/
def chapter03FiniteChangeSet
    (H H' : ∀ i, Subgroup (G i)) : Set I :=
  {i | H i ≠ H' i}

def chapter03FiniteChange
    (H H' : ∀ i, Subgroup (G i)) : Prop :=
  (chapter03FiniteChangeSet H H').Finite

theorem chapter03_finiteChange_symm
    (H H' : ∀ i, Subgroup (G i))
    (hchange : chapter03FiniteChange H H') :
    chapter03FiniteChange H' H := by
  unfold chapter03FiniteChange at hchange ⊢
  rw [show chapter03FiniteChangeSet H' H = chapter03FiniteChangeSet H H' by
    ext i
    simp [chapter03FiniteChangeSet, eq_comm]]
  exact hchange

theorem chapter03_eventually_mem_iff_of_finite_change
    (H H' : ∀ i, Subgroup (G i))
    (hchange : chapter03FiniteChange H H') (x : ∀ i, G i) :
    (∀ᶠ i in Filter.cofinite, x i ∈ H i) ↔
      ∀ᶠ i in Filter.cofinite, x i ∈ H' i := by
  have heq : ∀ᶠ i in Filter.cofinite, H i = H' i := by
    filter_upwards [hchange.compl_mem_cofinite] with i hi
    simpa [chapter03FiniteChange, chapter03FiniteChangeSet] using hi
  constructor <;> intro hx
  · filter_upwards [hx, heq] with i hi hEq
    simpa [hEq] using hi
  · filter_upwards [hx, heq] with i hi hEq
    simpa [hEq] using hi

def chapter03FiniteChangeEquiv
    (H H' : ∀ i, Subgroup (G i))
    (hchange : chapter03FiniteChange H H') :
    Chapter03RestrictedProduct H ≃ Chapter03RestrictedProduct H' where
  toFun x :=
    ⟨(x : ∀ i, G i),
      (chapter03_eventually_mem_iff_of_finite_change H H' hchange
        (x : ∀ i, G i)).mp x.property⟩
  invFun x :=
    ⟨(x : ∀ i, G i),
      (chapter03_eventually_mem_iff_of_finite_change H' H
        (chapter03_finiteChange_symm H H' hchange)
        (x : ∀ i, G i)).mp x.property⟩
  left_inv x := by
    exact Subtype.ext rfl
  right_inv x := by
    exact Subtype.ext rfl

theorem chapter03_finiteChangeEquiv_apply
    (H H' : ∀ i, Subgroup (G i))
    (hchange : chapter03FiniteChange H H')
    (x : Chapter03RestrictedProduct H) :
    (chapter03FiniteChangeEquiv H H' hchange x : ∀ i, G i) =
      (x : ∀ i, G i) := by
  rfl

theorem chapter03_finiteChangeEquiv_map_mul
    (H H' : ∀ i, Subgroup (G i))
    (hchange : chapter03FiniteChange H H')
    (x y : Chapter03RestrictedProduct H) :
    chapter03FiniteChangeEquiv H H' hchange (x * y) =
      chapter03FiniteChangeEquiv H H' hchange x *
        chapter03FiniteChangeEquiv H H' hchange y := by
  apply chapter03_restrictedProduct_ext H'
  intro i
  rfl

theorem chapter03_finite_change_preserves_restricted_product_topology
    [∀ i, TopologicalSpace (G i)]
    (H H' : ∀ i, Subgroup (G i))
    (hchange : chapter03FiniteChange H H')
    (hH : ∀ i, IsOpen (H i : Set (G i)))
    (hH' : ∀ i, IsOpen (H' i : Set (G i))) :
    Continuous (chapter03FiniteChangeEquiv H H' hchange) ∧
      Continuous (chapter03FiniteChangeEquiv H H' hchange).symm := by
  classical
  have hC : {i | H i ≠ H' i}.Finite := hchange
  have hforward : Continuous (chapter03FiniteChangeEquiv H H' hchange) := by
    rw [continuous_generateFrom_iff]
    rintro _ ⟨V, hV, rfl⟩
    have hE : {i | V i ≠ (H' i : Set (G i))}.Finite := by
      exact Filter.eventually_cofinite.mp hV.2
    apply isOpen_iff_mem_nhds.2
    intro x hx
    have hB : (chapter03ExceptionalSet H (x : ∀ i, G i)).Finite := by
      exact (chapter03_restrictedProduct_mem_iff_exceptional_finite H
        (x : ∀ i, G i)).1 x.property
    let S : Set I :=
      ({i | V i ≠ (H' i : Set (G i))} ∪ {i | H i ≠ H' i}) ∪
        chapter03ExceptionalSet H (x : ∀ i, G i)
    have hS : S.Finite := by
      exact (hE.union hC).union hB
    let W : ∀ i, Set (G i) := fun i =>
      if i ∈ S then V i else (H i : Set (G i))
    have hW : chapter03BasicProductCondition H W := by
      constructor
      · intro i
        by_cases hi : i ∈ S
        · simpa [W, hi] using hV.1 i
        · simpa [W, hi] using hH i
      · filter_upwards [hS.compl_mem_cofinite] with i hi
        have hi' : i ∉ S := by simpa using hi
        simp [W, hi']
    have hxW : x ∈ chapter03BasicProductSet H W := by
      change ∀ i, ((x : ∀ i, G i) i) ∈ W i
      intro i
      by_cases hi : i ∈ S
      · have hxiV : ((x : ∀ i, G i) i) ∈ V i := by
          change ∀ i, ((x : ∀ i, G i) i) ∈ V i at hx
          exact hx i
        simpa [W, hi] using hxiV
      · have hiB : i ∉ chapter03ExceptionalSet H (x : ∀ i, G i) := by
          intro hiB
          apply hi
          change i ∈
            ({j | V j ≠ (H' j : Set (G j))} ∪ {j | H j ≠ H' j}) ∪
              chapter03ExceptionalSet H (x : ∀ i, G i)
          exact Or.inr hiB
        have hxi : ((x : ∀ i, G i) i) ∈ H i := by
          simpa [chapter03ExceptionalSet] using hiB
        simpa [W, hi] using hxi
    have hsubset : chapter03BasicProductSet H W ⊆
        (chapter03FiniteChangeEquiv H H' hchange) ⁻¹'
          chapter03BasicProductSet H' V := by
      intro y hy
      change ∀ i, ((y : ∀ i, G i) i) ∈ V i
      intro i
      by_cases hi : i ∈ S
      · simpa [W, hi] using hy i
      · have hiE : V i = (H' i : Set (G i)) := by
          by_contra hne
          apply hi
          change i ∈
            ({j | V j ≠ (H' j : Set (G j))} ∪ {j | H j ≠ H' j}) ∪
              chapter03ExceptionalSet H (x : ∀ i, G i)
          exact Or.inl (Or.inl hne)
        have hiC : H i = H' i := by
          by_contra hne
          apply hi
          change i ∈
            ({j | V j ≠ (H' j : Set (G j))} ∪ {j | H j ≠ H' j}) ∪
              chapter03ExceptionalSet H (x : ∀ i, G i)
          exact Or.inl (Or.inr hne)
        have hyH : ((y : ∀ i, G i) i) ∈ H i := by
          simpa [W, hi] using hy i
        rw [hiE, ← hiC]
        exact hyH
    exact mem_of_superset
      ((chapter03_basicProductSet_isOpen H W hW).mem_nhds hxW) hsubset
  have hC' : {i | H' i ≠ H i}.Finite :=
    chapter03_finiteChange_symm H H' hchange
  have hreverse : Continuous (chapter03FiniteChangeEquiv H H' hchange).symm := by
    rw [continuous_generateFrom_iff]
    rintro _ ⟨V, hV, rfl⟩
    have hE : {i | V i ≠ (H i : Set (G i))}.Finite := by
      exact Filter.eventually_cofinite.mp hV.2
    apply isOpen_iff_mem_nhds.2
    intro x hx
    have hB : (chapter03ExceptionalSet H' (x : ∀ i, G i)).Finite := by
      exact (chapter03_restrictedProduct_mem_iff_exceptional_finite H'
        (x : ∀ i, G i)).1 x.property
    let S : Set I :=
      ({i | V i ≠ (H i : Set (G i))} ∪ {i | H' i ≠ H i}) ∪
        chapter03ExceptionalSet H' (x : ∀ i, G i)
    have hS : S.Finite := by
      exact (hE.union hC').union hB
    let W : ∀ i, Set (G i) := fun i =>
      if i ∈ S then V i else (H' i : Set (G i))
    have hW : chapter03BasicProductCondition H' W := by
      constructor
      · intro i
        by_cases hi : i ∈ S
        · simpa [W, hi] using hV.1 i
        · simpa [W, hi] using hH' i
      · filter_upwards [hS.compl_mem_cofinite] with i hi
        have hi' : i ∉ S := by simpa using hi
        simp [W, hi']
    have hxW : x ∈ chapter03BasicProductSet H' W := by
      change ∀ i, ((x : ∀ i, G i) i) ∈ W i
      intro i
      by_cases hi : i ∈ S
      · have hxiV : ((x : ∀ i, G i) i) ∈ V i := by
          change ∀ i, ((x : ∀ i, G i) i) ∈ V i at hx
          exact hx i
        simpa [W, hi] using hxiV
      · have hiB : i ∉ chapter03ExceptionalSet H' (x : ∀ i, G i) := by
          intro hiB
          apply hi
          change i ∈
            ({j | V j ≠ (H j : Set (G j))} ∪ {j | H' j ≠ H j}) ∪
              chapter03ExceptionalSet H' (x : ∀ i, G i)
          exact Or.inr hiB
        have hxi : ((x : ∀ i, G i) i) ∈ H' i := by
          simpa [chapter03ExceptionalSet] using hiB
        simpa [W, hi] using hxi
    have hsubset : chapter03BasicProductSet H' W ⊆
        (chapter03FiniteChangeEquiv H H' hchange).symm ⁻¹'
          chapter03BasicProductSet H V := by
      intro y hy
      change ∀ i, ((y : ∀ i, G i) i) ∈ V i
      intro i
      by_cases hi : i ∈ S
      · simpa [W, hi] using hy i
      · have hiE : V i = (H i : Set (G i)) := by
          by_contra hne
          apply hi
          change i ∈
            ({j | V j ≠ (H j : Set (G j))} ∪ {j | H' j ≠ H j}) ∪
              chapter03ExceptionalSet H' (x : ∀ i, G i)
          exact Or.inl (Or.inl hne)
        have hiC : H' i = H i := by
          by_contra hne
          apply hi
          change i ∈
            ({j | V j ≠ (H j : Set (G j))} ∪ {j | H' j ≠ H j}) ∪
              chapter03ExceptionalSet H' (x : ∀ i, G i)
          exact Or.inl (Or.inr hne)
        have hyH : ((y : ∀ i, G i) i) ∈ H' i := by
          simpa [W, hi] using hy i
        rw [hiE, ← hiC]
        exact hyH
    exact mem_of_superset
      ((chapter03_basicProductSet_isOpen H' W hW).mem_nhds hxW) hsubset
  exact ⟨hforward, hreverse⟩

theorem chapter03_finite_change_gives_canonical_topological_identification
    [∀ i, TopologicalSpace (G i)]
    (H H' : ∀ i, Subgroup (G i))
    (hchange : chapter03FiniteChange H H')
    (hH : ∀ i, IsOpen (H i : Set (G i)))
    (hH' : ∀ i, IsOpen (H' i : Set (G i))) :
    ∃ e : Chapter03RestrictedProduct H ≃ Chapter03RestrictedProduct H',
      (∀ x, (e x : ∀ i, G i) = (x : ∀ i, G i)) ∧
      Continuous e ∧ Continuous e.symm := by
  refine ⟨chapter03FiniteChangeEquiv H H' hchange, ?_⟩
  exact ⟨fun x => chapter03_finiteChangeEquiv_apply H H' hchange x,
    (chapter03_finite_change_preserves_restricted_product_topology H H'
      hchange hH hH').1,
    (chapter03_finite_change_preserves_restricted_product_topology H H'
      hchange hH hH').2⟩

end FiniteChanges

section AdditiveFiniteChanges

variable {I : Type u} {G : I → Type v} [∀ i, AddGroup (G i)]

/-- The additive version of the finite-change condition on integral models. -/
def chapter03AdditiveFiniteChangeSet
    (H H' : ∀ i, AddSubgroup (G i)) : Set I :=
  {i | H i ≠ H' i}

def chapter03AdditiveFiniteChange
    (H H' : ∀ i, AddSubgroup (G i)) : Prop :=
  (chapter03AdditiveFiniteChangeSet H H').Finite

theorem chapter03_additiveFiniteChange_symm
    (H H' : ∀ i, AddSubgroup (G i))
    (hchange : chapter03AdditiveFiniteChange H H') :
    chapter03AdditiveFiniteChange H' H := by
  unfold chapter03AdditiveFiniteChange at hchange ⊢
  rw [show chapter03AdditiveFiniteChangeSet H' H =
      chapter03AdditiveFiniteChangeSet H H' by
    ext i
    simp [chapter03AdditiveFiniteChangeSet, eq_comm]]
  exact hchange

theorem chapter03_additive_eventually_mem_iff_of_finite_change
    (H H' : ∀ i, AddSubgroup (G i))
    (hchange : chapter03AdditiveFiniteChange H H') (x : ∀ i, G i) :
    (∀ᶠ i in Filter.cofinite, x i ∈ H i) ↔
      ∀ᶠ i in Filter.cofinite, x i ∈ H' i := by
  have heq : ∀ᶠ i in Filter.cofinite, H i = H' i := by
    filter_upwards [hchange.compl_mem_cofinite] with i hi
    simpa [chapter03AdditiveFiniteChange, chapter03AdditiveFiniteChangeSet] using hi
  constructor <;> intro hx
  · filter_upwards [hx, heq] with i hi hEq
    simpa [hEq] using hi
  · filter_upwards [hx, heq] with i hi hEq
    simpa [hEq] using hi

def chapter03AdditiveFiniteChangeEquiv
    (H H' : ∀ i, AddSubgroup (G i))
    (hchange : chapter03AdditiveFiniteChange H H') :
    Chapter03AdditiveRestrictedProduct H ≃
      Chapter03AdditiveRestrictedProduct H' where
  toFun x :=
    ⟨(x : ∀ i, G i),
      (chapter03_additive_eventually_mem_iff_of_finite_change H H' hchange
        (x : ∀ i, G i)).mp x.property⟩
  invFun x :=
    ⟨(x : ∀ i, G i),
      (chapter03_additive_eventually_mem_iff_of_finite_change H' H
        (chapter03_additiveFiniteChange_symm H H' hchange)
        (x : ∀ i, G i)).mp x.property⟩
  left_inv x := by
    exact Subtype.ext rfl
  right_inv x := by
    exact Subtype.ext rfl

theorem chapter03_additiveFiniteChangeEquiv_apply
    (H H' : ∀ i, AddSubgroup (G i))
    (hchange : chapter03AdditiveFiniteChange H H')
    (x : Chapter03AdditiveRestrictedProduct H) :
    (chapter03AdditiveFiniteChangeEquiv H H' hchange x : ∀ i, G i) =
      (x : ∀ i, G i) := by
  rfl

theorem chapter03_additiveFiniteChangeEquiv_map_add
    (H H' : ∀ i, AddSubgroup (G i))
    (hchange : chapter03AdditiveFiniteChange H H')
    (x y : Chapter03AdditiveRestrictedProduct H) :
    chapter03AdditiveFiniteChangeEquiv H H' hchange (x + y) =
      chapter03AdditiveFiniteChangeEquiv H H' hchange x +
        chapter03AdditiveFiniteChangeEquiv H H' hchange y := by
  apply chapter03_additiveRestrictedProduct_ext H'
  intro i
  rfl

theorem chapter03_additive_finite_change_preserves_restricted_product_topology
    [∀ i, TopologicalSpace (G i)]
    (H H' : ∀ i, AddSubgroup (G i))
    (hchange : chapter03AdditiveFiniteChange H H')
    (hH : ∀ i, IsOpen (H i : Set (G i)))
    (hH' : ∀ i, IsOpen (H' i : Set (G i))) :
    Continuous (chapter03AdditiveFiniteChangeEquiv H H' hchange) ∧
      Continuous (chapter03AdditiveFiniteChangeEquiv H H' hchange).symm := by
  classical
  have hC : {i | H i ≠ H' i}.Finite := hchange
  have hforward : Continuous (chapter03AdditiveFiniteChangeEquiv H H' hchange) := by
    rw [continuous_generateFrom_iff]
    rintro _ ⟨V, hV, rfl⟩
    have hE : {i | V i ≠ (H' i : Set (G i))}.Finite := by
      exact Filter.eventually_cofinite.mp hV.2
    apply isOpen_iff_mem_nhds.2
    intro x hx
    have hB : {i | ((x : ∀ i, G i) i) ∉ H i}.Finite := by
      exact Filter.eventually_cofinite.mp
        ((chapter03_additiveRestrictedProduct_mem_iff H
          (x : ∀ i, G i)).1 x.property)
    let S : Set I :=
      ({i | V i ≠ (H' i : Set (G i))} ∪ {i | H i ≠ H' i}) ∪
        {i | ((x : ∀ i, G i) i) ∉ H i}
    have hS : S.Finite := by
      exact (hE.union hC).union hB
    let W : ∀ i, Set (G i) := fun i =>
      if i ∈ S then V i else (H i : Set (G i))
    have hW : chapter03AdditiveBasicProductCondition H W := by
      constructor
      · intro i
        by_cases hi : i ∈ S
        · simpa [W, hi] using hV.1 i
        · simpa [W, hi] using hH i
      · filter_upwards [hS.compl_mem_cofinite] with i hi
        have hi' : i ∉ S := by simpa using hi
        simp [W, hi']
    have hxW : x ∈ chapter03AdditiveBasicProductSet H W := by
      change ∀ i, ((x : ∀ i, G i) i) ∈ W i
      intro i
      by_cases hi : i ∈ S
      · have hxiV : ((x : ∀ i, G i) i) ∈ V i := by
          change ∀ i, ((x : ∀ i, G i) i) ∈ V i at hx
          exact hx i
        simpa [W, hi] using hxiV
      · have hxi : ((x : ∀ i, G i) i) ∈ H i := by
          by_contra hnot
          apply hi
          change i ∈
            ({j | V j ≠ (H' j : Set (G j))} ∪ {j | H j ≠ H' j}) ∪
              {j | ((x : ∀ i, G i) j) ∉ H j}
          exact Or.inr hnot
        simpa [W, hi] using hxi
    have hsubset : chapter03AdditiveBasicProductSet H W ⊆
        (chapter03AdditiveFiniteChangeEquiv H H' hchange) ⁻¹'
          chapter03AdditiveBasicProductSet H' V := by
      intro y hy
      change ∀ i, ((y : ∀ i, G i) i) ∈ V i
      intro i
      by_cases hi : i ∈ S
      · simpa [W, hi] using hy i
      · have hiE : V i = (H' i : Set (G i)) := by
          by_contra hne
          apply hi
          change i ∈
            ({j | V j ≠ (H' j : Set (G j))} ∪ {j | H j ≠ H' j}) ∪
              {j | ((x : ∀ i, G i) j) ∉ H j}
          exact Or.inl (Or.inl hne)
        have hiC : H i = H' i := by
          by_contra hne
          apply hi
          change i ∈
            ({j | V j ≠ (H' j : Set (G j))} ∪ {j | H j ≠ H' j}) ∪
              {j | ((x : ∀ i, G i) j) ∉ H j}
          exact Or.inl (Or.inr hne)
        have hyH : ((y : ∀ i, G i) i) ∈ H i := by
          simpa [W, hi] using hy i
        rw [hiE, ← hiC]
        exact hyH
    exact mem_of_superset
      ((chapter03_additive_basicProductSet_isOpen H W hW).mem_nhds hxW) hsubset
  have hC' : {i | H' i ≠ H i}.Finite :=
    chapter03_additiveFiniteChange_symm H H' hchange
  have hreverse :
      Continuous (chapter03AdditiveFiniteChangeEquiv H H' hchange).symm := by
    rw [continuous_generateFrom_iff]
    rintro _ ⟨V, hV, rfl⟩
    have hE : {i | V i ≠ (H i : Set (G i))}.Finite := by
      exact Filter.eventually_cofinite.mp hV.2
    apply isOpen_iff_mem_nhds.2
    intro x hx
    have hB : {i | ((x : ∀ i, G i) i) ∉ H' i}.Finite := by
      exact Filter.eventually_cofinite.mp
        ((chapter03_additiveRestrictedProduct_mem_iff H'
          (x : ∀ i, G i)).1 x.property)
    let S : Set I :=
      ({i | V i ≠ (H i : Set (G i))} ∪ {i | H' i ≠ H i}) ∪
        {i | ((x : ∀ i, G i) i) ∉ H' i}
    have hS : S.Finite := by
      exact (hE.union hC').union hB
    let W : ∀ i, Set (G i) := fun i =>
      if i ∈ S then V i else (H' i : Set (G i))
    have hW : chapter03AdditiveBasicProductCondition H' W := by
      constructor
      · intro i
        by_cases hi : i ∈ S
        · simpa [W, hi] using hV.1 i
        · simpa [W, hi] using hH' i
      · filter_upwards [hS.compl_mem_cofinite] with i hi
        have hi' : i ∉ S := by simpa using hi
        simp [W, hi']
    have hxW : x ∈ chapter03AdditiveBasicProductSet H' W := by
      change ∀ i, ((x : ∀ i, G i) i) ∈ W i
      intro i
      by_cases hi : i ∈ S
      · have hxiV : ((x : ∀ i, G i) i) ∈ V i := by
          change ∀ i, ((x : ∀ i, G i) i) ∈ V i at hx
          exact hx i
        simpa [W, hi] using hxiV
      · have hxi : ((x : ∀ i, G i) i) ∈ H' i := by
          by_contra hnot
          apply hi
          change i ∈
            ({j | V j ≠ (H j : Set (G j))} ∪ {j | H' j ≠ H j}) ∪
              {j | ((x : ∀ i, G i) j) ∉ H' j}
          exact Or.inr hnot
        simpa [W, hi] using hxi
    have hsubset : chapter03AdditiveBasicProductSet H' W ⊆
        (chapter03AdditiveFiniteChangeEquiv H H' hchange).symm ⁻¹'
          chapter03AdditiveBasicProductSet H V := by
      intro y hy
      change ∀ i, ((y : ∀ i, G i) i) ∈ V i
      intro i
      by_cases hi : i ∈ S
      · simpa [W, hi] using hy i
      · have hiE : V i = (H i : Set (G i)) := by
          by_contra hne
          apply hi
          change i ∈
            ({j | V j ≠ (H j : Set (G j))} ∪ {j | H' j ≠ H j}) ∪
              {j | ((x : ∀ i, G i) j) ∉ H' j}
          exact Or.inl (Or.inl hne)
        have hiC : H' i = H i := by
          by_contra hne
          apply hi
          change i ∈
            ({j | V j ≠ (H j : Set (G j))} ∪ {j | H' j ≠ H j}) ∪
              {j | ((x : ∀ i, G i) j) ∉ H' j}
          exact Or.inl (Or.inr hne)
        have hyH : ((y : ∀ i, G i) i) ∈ H' i := by
          simpa [W, hi] using hy i
        rw [hiE, ← hiC]
        exact hyH
    exact mem_of_superset
      ((chapter03_additive_basicProductSet_isOpen H' W hW).mem_nhds hxW) hsubset
  exact ⟨hforward, hreverse⟩

theorem chapter03_additive_local_lattice_agreement_outside_finite_set
    [∀ i, TopologicalSpace (G i)]
    (H H' : ∀ i, AddSubgroup (G i))
    (hagree : chapter03AdditiveFiniteChange H H')
    (hH : ∀ i, IsOpen (H i : Set (G i)))
    (hH' : ∀ i, IsOpen (H' i : Set (G i))) :
    ∃ e : Chapter03AdditiveRestrictedProduct H ≃
        Chapter03AdditiveRestrictedProduct H',
      (∀ x, (e x : ∀ i, G i) = (x : ∀ i, G i)) ∧
        Continuous e ∧ Continuous e.symm := by
  refine ⟨chapter03AdditiveFiniteChangeEquiv H H' hagree, ?_⟩
  exact ⟨fun x => chapter03_additiveFiniteChangeEquiv_apply H H' hagree x,
    (chapter03_additive_finite_change_preserves_restricted_product_topology H H'
      hagree hH hH').1,
    (chapter03_additive_finite_change_preserves_restricted_product_topology H H'
      hagree hH hH').2⟩

end AdditiveFiniteChanges

section PointwiseCommensurability

variable {I : Type u} {G : I → Type v} [∀ i, Group (G i)]

/-- A left coset of a subgroup, used to express finite index without choosing
a quotient construction. -/
def chapter03LeftCoset {i : I} (K : Subgroup (G i)) (g : G i) : Set (G i) :=
  {x | g⁻¹ * x ∈ K}

def chapter03FiniteCosetCover {i : I}
    (A K : Subgroup (G i)) : Prop :=
  ∃ t : Set (G i), t.Finite ∧
    (A : Set (G i)) ⊆ ⋃ g ∈ t, chapter03LeftCoset (i := i) K g

/-- Two subgroups are commensurable when they contain a common subgroup of
finite index in each. -/
def chapter03SubgroupsCommensurable {i : I}
    (A B : Subgroup (G i)) : Prop :=
  ∃ K : Subgroup (G i), K ≤ A ∧ K ≤ B ∧
    chapter03FiniteCosetCover (i := i) A K ∧
      chapter03FiniteCosetCover (i := i) B K

def chapter03PointwiseCommensurableFamily
    (H H' : ∀ i, Subgroup (G i)) : Prop :=
  ∀ i, chapter03SubgroupsCommensurable (i := i) (H i) (H' i)

def chapter03MultiplicativeRestrictedProductChangeWitness
    (H H' : ∀ i, Subgroup (G i)) : Prop :=
  ∃ x : ∀ i, G i,
    chapter03AlmostAllIn H x ∧ ¬ chapter03AlmostAllIn H' x

theorem chapter03_pointwise_commensurability_with_witness_changes_underlying_product
    (H H' : ∀ i, Subgroup (G i))
    (_hpoint : chapter03PointwiseCommensurableFamily H H')
    (hwitness : chapter03MultiplicativeRestrictedProductChangeWitness H H') :
    chapter03RestrictedProductSubgroup H ≠
      chapter03RestrictedProductSubgroup H' := by
  intro heq
  obtain ⟨x, hx, hnotx⟩ := hwitness
  apply hnotx
  have hxmem : x ∈ chapter03RestrictedProductSubgroup H :=
    (chapter03_restrictedProduct_mem_iff H x).2 hx
  have hxmem' : x ∈ chapter03RestrictedProductSubgroup H' := by
    rw [← heq]
    exact hxmem
  exact (chapter03_restrictedProduct_mem_iff H' x).1 hxmem'

end PointwiseCommensurability

section InfiniteChanges

variable {I : Type u} {G : I → Type v} [∀ i, AddGroup (G i)]

/-- There is a family which is integral for one model and not for the other. -/
def chapter03RestrictedProductChangeWitness
    (H H' : ∀ i, AddSubgroup (G i)) : Prop :=
  ∃ x : ∀ i, G i,
    (∀ᶠ i in Filter.cofinite, x i ∈ H i) ∧
      ¬ (∀ᶠ i in Filter.cofinite, x i ∈ H' i)

theorem chapter03_infinite_change_can_alter_restricted_product
    (H H' : ∀ i, AddSubgroup (G i))
    (h : chapter03RestrictedProductChangeWitness H H') :
    chapter03AdditiveRestrictedProductSubgroup H ≠
      chapter03AdditiveRestrictedProductSubgroup H' := by
  intro heq
  obtain ⟨x, hx, hnotx⟩ := h
  apply hnotx
  have hxmem : x ∈ chapter03AdditiveRestrictedProductSubgroup H :=
    (chapter03_additiveRestrictedProduct_mem_iff H x).2 hx
  have hxmem' : x ∈ chapter03AdditiveRestrictedProductSubgroup H' := by
    rw [← heq]
    exact hxmem
  exact (chapter03_additiveRestrictedProduct_mem_iff H' x).1 hxmem'

section AdditivePointwiseCommensurability

/-- Additive left cosets for the additive formulation of commensurability. -/
def chapter03AdditiveLeftCoset {i : I}
    (K : AddSubgroup (G i)) (g : G i) : Set (G i) :=
  {x | -g + x ∈ K}

def chapter03AdditiveFiniteCosetCover {i : I}
    (A K : AddSubgroup (G i)) : Prop :=
  ∃ t : Set (G i), t.Finite ∧
    (A : Set (G i)) ⊆ ⋃ g ∈ t, chapter03AdditiveLeftCoset (i := i) K g

def chapter03AdditiveSubgroupsCommensurable {i : I}
    (A B : AddSubgroup (G i)) : Prop :=
  ∃ K : AddSubgroup (G i), K ≤ A ∧ K ≤ B ∧
    chapter03AdditiveFiniteCosetCover (i := i) A K ∧
      chapter03AdditiveFiniteCosetCover (i := i) B K

def chapter03PointwiseAdditiveCommensurableFamily
    (H H' : ∀ i, AddSubgroup (G i)) : Prop :=
  ∀ i, chapter03AdditiveSubgroupsCommensurable (i := i) (H i) (H' i)

theorem chapter03_additive_pointwise_commensurability_with_witness_changes_underlying_product
    (H H' : ∀ i, AddSubgroup (G i))
    (_hpoint : chapter03PointwiseAdditiveCommensurableFamily H H')
    (hwitness : chapter03RestrictedProductChangeWitness H H') :
    chapter03AdditiveRestrictedProductSubgroup H ≠
      chapter03AdditiveRestrictedProductSubgroup H' := by
  intro heq
  obtain ⟨x, hx, hnotx⟩ := hwitness
  apply hnotx
  have hxmem : x ∈ chapter03AdditiveRestrictedProductSubgroup H :=
    (chapter03_additiveRestrictedProduct_mem_iff H x).2 hx
  have hxmem' : x ∈ chapter03AdditiveRestrictedProductSubgroup H' := by
    rw [← heq]
    exact hxmem
  exact (chapter03_additiveRestrictedProduct_mem_iff H' x).1 hxmem'

end AdditivePointwiseCommensurability

section ConstantOneWitness

variable [∀ i, One (G i)]

theorem chapter03_constant_one_witness_for_infinite_change
    (H H' : ∀ i, AddSubgroup (G i))
    (hone : ∀ i, (1 : G i) ∈ H i)
    (hnotone : {i | (1 : G i) ∉ H' i}.Infinite) :
    chapter03RestrictedProductChangeWitness H H' := by
  refine ⟨fun _ => 1, Filter.Eventually.of_forall hone, ?_⟩
  intro htail
  apply hnotone
  simpa using (Filter.eventually_cofinite.mp htail)

end ConstantOneWitness

end InfiniteChanges

section LatticeAndBasisIndependence

variable {I : Type u} {G : I → Type v} [∀ i, Group (G i)]

/-- Local lattice families which agree outside a finite set give canonically
the same restricted product. -/
theorem chapter03_local_lattice_agreement_outside_finite_set
    [∀ i, TopologicalSpace (G i)]
    (H H' : ∀ i, Subgroup (G i))
    (hagree : chapter03FiniteChange H H')
    (hH : ∀ i, IsOpen (H i : Set (G i)))
    (hH' : ∀ i, IsOpen (H' i : Set (G i))) :
    ∃ e : Chapter03RestrictedProduct H ≃ Chapter03RestrictedProduct H',
      (∀ x, (e x : ∀ i, G i) = (x : ∀ i, G i)) ∧
        Continuous e ∧ Continuous e.symm := by
  exact chapter03_finite_change_gives_canonical_topological_identification
    H H' hagree hH hH'

/-- Basis independence is reduced to the finite-change statement for the local
integral lattice models. -/
theorem chapter03_scalar_extension_basis_independence_interface
    [∀ i, TopologicalSpace (G i)]
    (H H' : ∀ i, Subgroup (G i))
    (hfinite : chapter03FiniteChange H H')
    (hH : ∀ i, IsOpen (H i : Set (G i)))
    (hH' : ∀ i, IsOpen (H' i : Set (G i))) :
    ∃ e : Chapter03RestrictedProduct H ≃ Chapter03RestrictedProduct H',
      (∀ x, (e x : ∀ i, G i) = (x : ∀ i, G i)) ∧
        Continuous e ∧ Continuous e.symm := by
  exact chapter03_local_lattice_agreement_outside_finite_set H H'
    hfinite hH hH'

end LatticeAndBasisIndependence

end
end LastLib.Book04AdelesAndIdeles.Chapter03
