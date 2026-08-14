import LastLib.Book04AdelesAndIdeles.Chapter03.Section01TheAlgebraicConstruction
import Mathlib.Order.Filter.Finite

namespace LastLib.Book04AdelesAndIdeles.Chapter03

open Set Filter
open scoped BigOperators Pointwise Topology

noncomputable section

/-! ### 3.2 The restricted-product topology -/

universe u v

section RestrictedTopology

variable {I : Type u} {G : I → Type v} [∀ i, Group (G i)]

theorem chapter03_basicProductCondition_inter
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i)) (U V : ∀ i, Set (G i))
    (hU : chapter03BasicProductCondition H U)
    (hV : chapter03BasicProductCondition H V) :
    chapter03BasicProductCondition H (fun i => U i ∩ V i) := by
  constructor
  · intro i
    exact (hU.1 i).inter (hV.1 i)
  · filter_upwards [hU.2, hV.2] with i hiU hiV
    simp [hiU, hiV]

theorem chapter03_basicProductSet_isOpen_of_condition
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i)) (U : ∀ i, Set (G i))
    (hU : chapter03BasicProductCondition H U) :
    IsOpen (chapter03BasicProductSet H U) :=
  chapter03_basicProductSet_isOpen H U hU

/-- Left translates of basic products are the neighborhoods used in the
restricted-product basis. -/
def chapter03LeftTranslate
    (H : ∀ i, Subgroup (G i)) (a : Chapter03RestrictedProduct H)
    (s : Set (Chapter03RestrictedProduct H)) :
    Set (Chapter03RestrictedProduct H) :=
  {x | a⁻¹ * x ∈ s}

theorem chapter03_leftTranslate_mem_iff
    (H : ∀ i, Subgroup (G i)) (a : Chapter03RestrictedProduct H)
    (s : Set (Chapter03RestrictedProduct H))
    (x : Chapter03RestrictedProduct H) :
    x ∈ chapter03LeftTranslate H a s ↔ a⁻¹ * x ∈ s :=
  Iff.rfl

theorem chapter03_basicProduct_translates_form_basis
    [∀ i, TopologicalSpace (G i)]
    [∀ i, IsTopologicalGroup (G i)]
    (H : ∀ i, Subgroup (G i))
    (hH : ∀ i, IsOpen (H i : Set (G i))) :
    ∀ x : Chapter03RestrictedProduct H, ∀ s ∈ 𝓝 x,
    ∃ a : Chapter03RestrictedProduct H,
        ∃ U : ∀ i, Set (G i),
          chapter03BasicProductCondition H U ∧
            x ∈ chapter03LeftTranslate H a
              (chapter03BasicProductSet H U) ∧
            chapter03LeftTranslate H a
              (chapter03BasicProductSet H U) ⊆ s := by
  intro x s hs
  change s ∈ @nhds _ (chapter03RestrictedProductTopology H) x at hs
  rw [TopologicalSpace.nhds_generateFrom] at hs
  rcases (Filter.mem_biInf_principal.mp hs) with ⟨T, hTfin, hTgen, hTsub⟩
  have hSx : (chapter03ExceptionalSet H (x : ∀ i, G i)).Finite := by
    exact (chapter03_restrictedProduct_mem_iff_exceptional_finite H
      (x : ∀ i, G i)).1 x.property
  rcases chapter03_stage_is_basicProduct H hSx hH with ⟨U₀, hU₀, hU₀eq⟩
  let b₀ : Set (Chapter03RestrictedProduct H) := chapter03BasicProductSet H U₀
  have hb₀ : b₀ ∈ chapter03BasicOpenSets H := by
    exact ⟨U₀, hU₀, rfl⟩
  have hxb₀ : x ∈ b₀ := by
    change x ∈ chapter03BasicProductSet H U₀
    rw [hU₀eq]
    exact (chapter03_stage_mem_iff_exceptional_subset H _ x).2 Set.Subset.rfl
  let T' : Set (Set (Chapter03RestrictedProduct H)) := insert b₀ T
  have hT'fin : T'.Finite := by
    exact hTfin.insert b₀
  have hT'gen : ∀ t ∈ T', t ∈ {s | x ∈ s ∧ s ∈ chapter03BasicOpenSets H} := by
    intro t ht
    simp only [T', mem_insert_iff] at ht
    rcases ht with rfl | ht
    · exact ⟨hxb₀, hb₀⟩
    · exact hTgen t ht
  have hT'sub : (⋂ t ∈ T', t) ⊆ s := by
    intro y hy
    apply hTsub
    simp only [mem_iInter] at hy ⊢
    intro t ht
    exact hy t (by simp [T', ht])
  have hbasic : ∀ t ∈ T', ∃ U : ∀ i, Set (G i),
      chapter03BasicProductCondition H U ∧
        chapter03BasicProductSet H U = t := by
    intro t ht
    rcases hT'gen t ht with ⟨_, htgen⟩
    rcases htgen with ⟨U, hU, rfl⟩
    exact ⟨U, hU, rfl⟩
  let _ : Fintype T' := hT'fin.fintype
  choose U hU hUt using (fun t : T' => hbasic t t.property)
  let W : ∀ i, Set (G i) := fun i => ⋂ t : T', U t i
  have hW : chapter03BasicProductCondition H W := by
    constructor
    · intro i
      exact isOpen_iInter_of_finite (fun t => (hU t).1 i)
    · have he : ∀ᶠ i in Filter.cofinite, ∀ t : T', U t i = (H i : Set (G i)) :=
        (Filter.eventually_all).2 fun t => (hU t).2
      filter_upwards [he] with i hi
      ext y
      simp only [W, mem_iInter]
      let t₀ : T' := ⟨b₀, by simp [T']⟩
      constructor
      · intro hy
        rw [← hi t₀]
        exact hy t₀
      · intro hy t
        rw [hi t]
        exact hy
  have hxW : x ∈ chapter03BasicProductSet H W := by
    intro i
    simp only [W, mem_iInter]
    intro t
    have hxt : x ∈ (t : Set (Chapter03RestrictedProduct H)) :=
      (hT'gen t t.property).1
    have hxt' : x ∈ chapter03BasicProductSet H (U t) := by
      rw [hUt t]
      exact hxt
    exact hxt' i
  have hWs : chapter03BasicProductSet H W ⊆ s := by
    intro y hy
    apply hT'sub
    simp only [mem_iInter]
    intro t ht
    have hy' : y ∈ chapter03BasicProductSet H (U ⟨t, ht⟩) := by
      intro i
      have hyW : ((y : ∀ i, G i) i) ∈ W i :=
        (chapter03_mem_basicProductSet_iff H W y).1 hy i
      exact (mem_iInter.1 hyW) ⟨t, ht⟩
    simpa only [hUt ⟨t, ht⟩] using hy'
  refine ⟨1, W, hW, ?_, ?_⟩
  · simpa [chapter03LeftTranslate] using hxW
  · intro y hy
    apply hWs
    simpa [chapter03LeftTranslate] using hy

/-- The ordinary product topology on a stage, viewed through its coordinate
    map into the unrestricted dependent product. -/
@[instance_reducible]
def chapter03StageProductTopology
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i)) (S : Set I) :
    TopologicalSpace (Chapter03Stage H S) :=
  TopologicalSpace.induced
    (fun x : Chapter03Stage H S =>
      ((x : Chapter03Stage H S).1 : ∀ i, G i)) inferInstance

/-- The topology inherited by a stage from the restricted product topology. -/
@[instance_reducible]
def chapter03StageSubtypeTopology
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i)) (S : Set I) :
    TopologicalSpace (Chapter03Stage H S) :=
  TopologicalSpace.induced
    (fun x : Chapter03Stage H S => (x : Chapter03RestrictedProduct H))
    inferInstance

instance chapter03Stage.topologicalSpace
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i)) (S : Set I) :
    TopologicalSpace (Chapter03Stage H S) :=
  chapter03StageSubtypeTopology H S

theorem chapter03_stage_subtype_topology_eq_product_topology
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i)) {S : Set I} (hS : S.Finite)
    (hH : ∀ i, IsOpen (H i : Set (G i))) :
    chapter03StageSubtypeTopology H S = chapter03StageProductTopology H S := by
  classical
  change TopologicalSpace.induced
      (fun x : Chapter03Stage H S => (x : Chapter03RestrictedProduct H))
      (chapter03RestrictedProductTopology H) =
    TopologicalSpace.induced
      (fun x : Chapter03Stage H S => ((x : Chapter03Stage H S).1 : ∀ i, G i))
      inferInstance
  apply le_antisymm
  · rw [← continuous_iff_le_induced]
    apply continuous_pi
    intro i
    rw [continuous_def]
    intro U hU
    let W : ∀ j, Set (G j) := fun j =>
      if hji : j = i then hji ▸ U
      else if j ∈ S then Set.univ else (H j : Set (G j))
    have hW : chapter03BasicProductCondition H W := by
      constructor
      · intro j
        by_cases hji : j = i
        · subst j
          simpa [W] using hU
        · by_cases hjS : j ∈ S
          · simp [W, hji, hjS]
          · simpa [W, hji, hjS] using hH j
      · filter_upwards [hS.compl_mem_cofinite, eventually_cofinite_ne i] with j hjS hji
        have hjS' : j ∉ S := by simpa using hjS
        simp [W, hjS', hji]
    have hset :
        (fun x : Chapter03Stage H S => ((x : Chapter03Stage H S).1 : ∀ i, G i) i) ⁻¹' U =
          (fun x : Chapter03Stage H S => (x : Chapter03RestrictedProduct H)) ⁻¹'
            chapter03BasicProductSet H W := by
      ext x
      constructor
      · intro hx
        change ∀ j, ((x : Chapter03Stage H S).1 : ∀ i, G i) j ∈ W j
        intro j
        by_cases hji : j = i
        · subst j
          simpa [W] using hx
        · by_cases hjS : j ∈ S
          · simp [W, hji, hjS]
          · simpa [W, hji, hjS] using x.2 j hjS
      · intro hx
        change ((x : Chapter03Stage H S).1 : ∀ i, G i) i ∈ U
        have hxi := hx i
        simpa [W] using hxi
    rw [hset]
    exact isOpen_induced (chapter03_basicProductSet_isOpen H W hW)
  · rw [← continuous_iff_le_induced]
    rw [continuous_generateFrom_iff]
    rintro _ ⟨U, hU, rfl⟩
    have hE : {i | U i ≠ (H i : Set (G i))}.Finite := by
      exact Filter.eventually_cofinite.mp hU.2
    let K : Set I := S ∪ {i | U i ≠ (H i : Set (G i))}
    have hK : K.Finite := hS.union hE
    let V : ∀ i, Set (G i) := fun i => if i ∈ K then U i else Set.univ
    have hV : IsOpen (Set.pi Set.univ V) := by
      rw [show Set.pi Set.univ V = Set.pi K V by
        ext x
        constructor
        · intro hx i hi
          exact hx i (by simp)
        · intro hx i hi
          by_cases hiK : i ∈ K
          · exact hx i hiK
          · simp [V, hiK]]
      apply isOpen_set_pi hK
      intro i hi
      by_cases hiK : i ∈ K
      · simpa [V, hiK] using hU.1 i
      · simp [V, hiK]
    have hset :
        (fun x : Chapter03Stage H S => (x : Chapter03RestrictedProduct H)) ⁻¹'
            chapter03BasicProductSet H U =
          (fun x : Chapter03Stage H S => ((x : Chapter03Stage H S).1 : ∀ i, G i)) ⁻¹'
            Set.pi Set.univ V := by
      ext x
      constructor
      · intro hx
        simp only [Set.mem_preimage, Set.mem_pi, mem_univ, true_implies]
        intro i
        by_cases hiK : i ∈ K
        · simpa [V, hiK] using hx i
        · simp [V, hiK]
      · intro hx
        change ∀ i, ((x : Chapter03Stage H S).1 : ∀ i, G i) i ∈ U i
        intro i
        by_cases hiK : i ∈ K
        · simpa [V, hiK] using hx i
        · have hiS : i ∉ S := by
            intro hiS
            exact hiK (Or.inl hiS)
          have hiE : U i = (H i : Set (G i)) := by
            by_contra hne
            exact hiK (Or.inr hne)
          simpa [hiE] using x.2 i hiS
    rw [hset]
    exact isOpen_induced hV

theorem chapter03_stage_is_open_subgroup
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i)) {S : Set I} (hS : S.Finite)
    (hH : ∀ i, IsOpen (H i : Set (G i))) :
    IsOpen (chapter03StageSubgroup H S : Set (Chapter03RestrictedProduct H)) :=
  chapter03_stage_isOpen H hS hH

private theorem chapter03_leftMul_continuous
    [∀ i, TopologicalSpace (G i)]
    [∀ i, IsTopologicalGroup (G i)]
    (H : ∀ i, Subgroup (G i))
    (hH : ∀ i, IsOpen (H i : Set (G i)))
    (a : Chapter03RestrictedProduct H) :
    Continuous (fun x : Chapter03RestrictedProduct H => a * x) := by
  classical
  rw [continuous_generateFrom_iff]
  rintro _ ⟨U, hU, rfl⟩
  let A : Set I := {i | ((a : ∀ i, G i) i) ∉ H i}
  let E : Set I := {i | U i ≠ (H i : Set (G i))}
  let S : Set I := A ∪ E
  have hA : A.Finite := by
    exact Filter.eventually_cofinite.mp a.property
  have hE : E.Finite := by
    exact Filter.eventually_cofinite.mp hU.2
  have hS : S.Finite := hA.union hE
  let W : ∀ i, Set (G i) := fun i =>
    if i ∈ S then (fun y => ((a : ∀ i, G i) i) * y) ⁻¹' U i
    else (H i : Set (G i))
  have hW : chapter03BasicProductCondition H W := by
    constructor
    · intro i
      by_cases hi : i ∈ S
      · simpa [W, hi] using
          (continuous_const_mul (((a : ∀ i, G i) i))).isOpen_preimage _ (hU.1 i)
      · simpa [W, hi] using hH i
    · filter_upwards [hS.compl_mem_cofinite] with i hi
      have hiS : i ∉ S := by simpa using hi
      simp [W, hiS]
  have hset :
      (fun x : Chapter03RestrictedProduct H => a * x) ⁻¹'
          chapter03BasicProductSet H U =
        chapter03BasicProductSet H W := by
    ext x
    constructor
    · intro hx
      change ∀ i, ((x : ∀ i, G i) i) ∈ W i
      intro i
      by_cases hi : i ∈ S
      · simpa [W, hi] using hx i
      · have hiA : i ∉ A := by
          intro hiA
          exact hi (Or.inl hiA)
        have hiE : i ∉ E := by
          intro hiE
          exact hi (Or.inr hiE)
        have hai : ((a : ∀ i, G i) i) ∈ H i := by
          by_contra hne
          exact hiA (by simpa [A] using hne)
        have hiU : U i = (H i : Set (G i)) := by
          by_contra hne
          exact hiE (by simpa [E] using hne)
        have hax : (((a * x : Chapter03RestrictedProduct H) : ∀ i, G i) i) ∈ H i := by
          simpa [hiU] using hx i
        have hxi : ((x : ∀ i, G i) i) ∈ H i := by
          have htmp := (H i).mul_mem ((H i).inv_mem hai) hax
          simpa [mul_assoc] using htmp
        simpa [W, hi] using hxi
    · intro hx
      change ∀ i, (((a * x : Chapter03RestrictedProduct H) : ∀ i, G i) i) ∈ U i
      intro i
      by_cases hi : i ∈ S
      · simpa [W, hi] using hx i
      · have hiA : i ∉ A := by
          intro hiA
          exact hi (Or.inl hiA)
        have hiE : i ∉ E := by
          intro hiE
          exact hi (Or.inr hiE)
        have hai : ((a : ∀ i, G i) i) ∈ H i := by
          by_contra hne
          exact hiA (by simpa [A] using hne)
        have hiU : U i = (H i : Set (G i)) := by
          by_contra hne
          exact hiE (by simpa [E] using hne)
        have hxi : ((x : ∀ i, G i) i) ∈ H i := by
          have hWxi := hx i
          simpa [W, hi] using hWxi
        simpa [hiU] using (H i).mul_mem hai hxi

  rw [hset]
  exact chapter03_basicProductSet_isOpen H W hW

private theorem chapter03_rightMul_continuous
    [∀ i, TopologicalSpace (G i)]
    [∀ i, IsTopologicalGroup (G i)]
    (H : ∀ i, Subgroup (G i))
    (hH : ∀ i, IsOpen (H i : Set (G i)))
    (a : Chapter03RestrictedProduct H) :
    Continuous (fun x : Chapter03RestrictedProduct H => x * a) := by
  classical
  rw [continuous_generateFrom_iff]
  rintro _ ⟨U, hU, rfl⟩
  let A : Set I := {i | ((a : ∀ i, G i) i) ∉ H i}
  let E : Set I := {i | U i ≠ (H i : Set (G i))}
  let S : Set I := A ∪ E
  have hA : A.Finite := by
    exact Filter.eventually_cofinite.mp a.property
  have hE : E.Finite := by
    exact Filter.eventually_cofinite.mp hU.2
  have hS : S.Finite := hA.union hE
  let W : ∀ i, Set (G i) := fun i =>
    if i ∈ S then (fun y => y * ((a : ∀ i, G i) i)) ⁻¹' U i
    else (H i : Set (G i))
  have hW : chapter03BasicProductCondition H W := by
    constructor
    · intro i
      by_cases hi : i ∈ S
      · simpa [W, hi] using
          (continuous_mul_const (((a : ∀ i, G i) i))).isOpen_preimage _ (hU.1 i)
      · simpa [W, hi] using hH i
    · filter_upwards [hS.compl_mem_cofinite] with i hi
      have hiS : i ∉ S := by simpa using hi
      simp [W, hiS]
  have hset :
      (fun x : Chapter03RestrictedProduct H => x * a) ⁻¹'
          chapter03BasicProductSet H U =
        chapter03BasicProductSet H W := by
    ext x
    constructor
    · intro hx
      change ∀ i, ((x : ∀ i, G i) i) ∈ W i
      intro i
      by_cases hi : i ∈ S
      · simpa [W, hi] using hx i
      · have hiA : i ∉ A := by
          intro hiA
          exact hi (Or.inl hiA)
        have hiE : i ∉ E := by
          intro hiE
          exact hi (Or.inr hiE)
        have hai : ((a : ∀ i, G i) i) ∈ H i := by
          by_contra hne
          exact hiA (by simpa [A] using hne)
        have hiU : U i = (H i : Set (G i)) := by
          by_contra hne
          exact hiE (by simpa [E] using hne)
        have hxa : (((x * a : Chapter03RestrictedProduct H) : ∀ i, G i) i) ∈ H i := by
          simpa [hiU] using hx i
        have hxi : ((x : ∀ i, G i) i) ∈ H i := by
          have htmp := (H i).mul_mem hxa ((H i).inv_mem hai)
          simpa [mul_assoc] using htmp
        simpa [W, hi] using hxi
    · intro hx
      change ∀ i, (((x * a : Chapter03RestrictedProduct H) : ∀ i, G i) i) ∈ U i
      intro i
      by_cases hi : i ∈ S
      · simpa [W, hi] using hx i
      · have hiA : i ∉ A := by
          intro hiA
          exact hi (Or.inl hiA)
        have hiE : i ∉ E := by
          intro hiE
          exact hi (Or.inr hiE)
        have hai : ((a : ∀ i, G i) i) ∈ H i := by
          by_contra hne
          exact hiA (by simpa [A] using hne)
        have hiU : U i = (H i : Set (G i)) := by
          by_contra hne
          exact hiE (by simpa [E] using hne)
        have hxi : ((x : ∀ i, G i) i) ∈ H i := by
          have hWxi := hx i
          simpa [W, hi] using hWxi
        simpa [hiU] using (H i).mul_mem hxi hai
  rw [hset]
  exact chapter03_basicProductSet_isOpen H W hW

private theorem chapter03_inv_continuous
    [∀ i, TopologicalSpace (G i)]
    [∀ i, IsTopologicalGroup (G i)]
    (H : ∀ i, Subgroup (G i))
    (hH : ∀ i, IsOpen (H i : Set (G i))) :
    Continuous (fun x : Chapter03RestrictedProduct H => x⁻¹) := by
  classical
  rw [continuous_generateFrom_iff]
  rintro _ ⟨U, hU, rfl⟩
  let E : Set I := {i | U i ≠ (H i : Set (G i))}
  have hE : E.Finite := by
    exact Filter.eventually_cofinite.mp hU.2
  let W : ∀ i, Set (G i) := fun i =>
    if i ∈ E then (fun y => y⁻¹) ⁻¹' U i else (H i : Set (G i))
  have hW : chapter03BasicProductCondition H W := by
    constructor
    · intro i
      by_cases hi : i ∈ E
      · simpa [W, hi] using continuous_inv.isOpen_preimage _ (hU.1 i)
      · simpa [W, hi] using hH i
    · filter_upwards [hE.compl_mem_cofinite] with i hi
      have hiE : i ∉ E := by simpa using hi
      simp [W, hiE]
  have hset :
      (fun x : Chapter03RestrictedProduct H => x⁻¹) ⁻¹'
          chapter03BasicProductSet H U =
        chapter03BasicProductSet H W := by
    ext x
    constructor
    · intro hx
      change ∀ i, ((x : ∀ i, G i) i) ∈ W i
      intro i
      by_cases hi : i ∈ E
      · simpa [W, hi] using hx i
      · have hiU : U i = (H i : Set (G i)) := by
          by_contra hne
          exact hi (by simpa [E] using hne)
        have hxin : (((x⁻¹ : Chapter03RestrictedProduct H) : ∀ i, G i) i) ∈ H i := by
          simpa [hiU] using hx i
        have hxi : ((x : ∀ i, G i) i) ∈ H i := by
          simpa using (H i).inv_mem hxin
        simpa [W, hi] using hxi
    · intro hx
      change ∀ i, (((x⁻¹ : Chapter03RestrictedProduct H) : ∀ i, G i) i) ∈ U i
      intro i
      by_cases hi : i ∈ E
      · simpa [W, hi] using hx i
      · have hiU : U i = (H i : Set (G i)) := by
          by_contra hne
          exact hi (by simpa [E] using hne)
        have hxi : ((x : ∀ i, G i) i) ∈ H i := by
          have hWxi := hx i
          simpa [W, hi] using hWxi
        simpa [hiU] using (H i).inv_mem hxi
  rw [hset]
  exact chapter03_basicProductSet_isOpen H W hW

private theorem chapter03_mul_continuous
    [∀ i, TopologicalSpace (G i)]
    [∀ i, IsTopologicalGroup (G i)]
    (H : ∀ i, Subgroup (G i))
    (hH : ∀ i, IsOpen (H i : Set (G i))) :
    Continuous (fun p : Chapter03RestrictedProduct H ×
      Chapter03RestrictedProduct H => p.1 * p.2) := by
  classical
  rw [continuous_generateFrom_iff]
  rintro _ ⟨U, hU, rfl⟩
  refine isOpen_iff_mem_nhds.2 ?_
  rintro ⟨x, y⟩ hxy
  change ∀ i, (((x * y : Chapter03RestrictedProduct H) : ∀ i, G i) i) ∈ U i at hxy
  let AX : Set I := {i | ((x : ∀ i, G i) i) ∉ H i}
  let AY : Set I := {i | ((y : ∀ i, G i) i) ∉ H i}
  let EU : Set I := {i | U i ≠ (H i : Set (G i))}
  let S : Set I := AX ∪ AY ∪ EU
  have hAX : AX.Finite := by
    exact Filter.eventually_cofinite.mp x.property
  have hAY : AY.Finite := by
    exact Filter.eventually_cofinite.mp y.property
  have hEU : EU.Finite := by
    exact Filter.eventually_cofinite.mp hU.2
  have hS : S.Finite := (hAX.union hAY).union hEU
  have hdata : ∀ i, ∃ V W : Set (G i),
      IsOpen V ∧ ((x : ∀ i, G i) i ∈ V) ∧
      IsOpen W ∧ ((y : ∀ i, G i) i ∈ W) ∧
      (V ×ˢ W ⊆ {p : G i × G i | p.1 * p.2 ∈ U i}) ∧
      (i ∉ S → V = (H i : Set (G i)) ∧ W = (H i : Set (G i))) := by
    intro i
    by_cases hi : i ∈ S
    · have hxyi : ((x : ∀ i, G i) i) * ((y : ∀ i, G i) i) ∈ U i := by
        simpa using hxy i
      have hmulnhds :
          (fun p : G i × G i => p.1 * p.2) ⁻¹' U i ∈
            𝓝 (((x : ∀ i, G i) i), ((y : ∀ i, G i) i)) :=
        continuous_mul.continuousAt ((hU.1 i).mem_nhds hxyi)
      rcases mem_nhds_prod_iff.mp hmulnhds with ⟨V₀, hV₀, W₀, hW₀, hVW₀⟩
      rcases mem_nhds_iff.mp hV₀ with ⟨V, hVV₀, hVopen, hxV⟩
      rcases mem_nhds_iff.mp hW₀ with ⟨W, hWW₀, hWopen, hyW⟩
      refine ⟨V, W, hVopen, hxV, hWopen, hyW, ?_, fun h => (h hi).elim⟩
      intro p hp
      exact hVW₀ ⟨hVV₀ hp.1, hWW₀ hp.2⟩
    · have hiAX : i ∉ AX := by
        intro hiAX
        exact hi (Or.inl (Or.inl hiAX))
      have hiAY : i ∉ AY := by
        intro hiAY
        exact hi (Or.inl (Or.inr hiAY))
      have hiEU : i ∉ EU := by
        intro hiEU
        exact hi (Or.inr hiEU)
      have hxi : ((x : ∀ i, G i) i) ∈ H i := by
        by_contra hne
        exact hiAX (by simpa [AX] using hne)
      have hyi : ((y : ∀ i, G i) i) ∈ H i := by
        by_contra hne
        exact hiAY (by simpa [AY] using hne)
      have hUi : U i = (H i : Set (G i)) := by
        by_contra hne
        exact hiEU (by simpa [EU] using hne)
      refine ⟨(H i : Set (G i)), (H i : Set (G i)), hH i, hxi, hH i, hyi, ?_,
        fun _ => ⟨rfl, rfl⟩⟩
      intro p hp
      simpa [hUi] using (H i).mul_mem hp.1 hp.2
  choose V W hVopen hxV hWopen hyW hVW hVtail using hdata
  have hV : chapter03BasicProductCondition H V := by
    constructor
    · exact hVopen
    · filter_upwards [hS.compl_mem_cofinite] with i hi
      exact (hVtail i (by simpa using hi)).1
  have hW : chapter03BasicProductCondition H W := by
    constructor
    · exact hWopen
    · filter_upwards [hS.compl_mem_cofinite] with i hi
      exact (hVtail i (by simpa using hi)).2
  have hprod :
      chapter03BasicProductSet H V ×ˢ chapter03BasicProductSet H W ⊆
        (fun p : Chapter03RestrictedProduct H × Chapter03RestrictedProduct H =>
          p.1 * p.2) ⁻¹' chapter03BasicProductSet H U := by
    rintro ⟨x', y'⟩ ⟨hx', hy'⟩
    change ∀ i, (((x' * y' : Chapter03RestrictedProduct H) : ∀ i, G i) i) ∈ U i
    intro i
    by_cases hi : i ∈ S
    · have hfactor :
          (((x' : ∀ i, G i) i), ((y' : ∀ i, G i) i)) ∈ V i ×ˢ W i :=
        ⟨hx' i, hy' i⟩
      simpa using hVW i hfactor
    · have htail := hVtail i hi
      have hxiH : ((x' : ∀ i, G i) i) ∈ H i := by
        simpa [htail.1] using hx' i
      have hyiH : ((y' : ∀ i, G i) i) ∈ H i := by
        simpa [htail.2] using hy' i
      have hiU : U i = (H i : Set (G i)) := by
        by_contra hne
        exact hi (Or.inr (by simpa [EU] using hne))
      simpa [hiU] using (H i).mul_mem hxiH hyiH
  have hopenprod : IsOpen
      (chapter03BasicProductSet H V ×ˢ chapter03BasicProductSet H W) :=
    (chapter03_basicProductSet_isOpen H V hV).prod
      (chapter03_basicProductSet_isOpen H W hW)
  have hpoint :
      (x, y) ∈ chapter03BasicProductSet H V ×ˢ chapter03BasicProductSet H W :=
    ⟨hxV, hyW⟩
  exact mem_of_superset (hopenprod.mem_nhds hpoint) hprod

theorem chapter03_restrictedProduct_is_topologicalGroup
    [∀ i, TopologicalSpace (G i)]
    [∀ i, IsTopologicalGroup (G i)]
    (H : ∀ i, Subgroup (G i))
    (hH : ∀ i, IsOpen (H i : Set (G i))) :
    IsTopologicalGroup (Chapter03RestrictedProduct H) := by
  apply IsTopologicalGroup.of_nhds_one'
  · have h := (chapter03_mul_continuous H hH).continuousAt
        (x := ((1 : Chapter03RestrictedProduct H), (1 : Chapter03RestrictedProduct H)))
    change Tendsto (fun p : Chapter03RestrictedProduct H × Chapter03RestrictedProduct H =>
      p.1 * p.2) (𝓝 ((1 : Chapter03RestrictedProduct H), (1 : Chapter03RestrictedProduct H)))
      (𝓝 ((1 : Chapter03RestrictedProduct H) * (1 : Chapter03RestrictedProduct H))) at h
    change Tendsto (fun p : Chapter03RestrictedProduct H × Chapter03RestrictedProduct H =>
      p.1 * p.2) (𝓝 (1 : Chapter03RestrictedProduct H) ×ˢ
        𝓝 (1 : Chapter03RestrictedProduct H)) (𝓝 (1 : Chapter03RestrictedProduct H))
    simpa only [nhds_prod_eq, one_mul] using h
  · have h := (chapter03_inv_continuous H hH).continuousAt
        (x := (1 : Chapter03RestrictedProduct H))
    change Tendsto (fun x : Chapter03RestrictedProduct H => x⁻¹)
      (𝓝 (1 : Chapter03RestrictedProduct H))
      (𝓝 ((1 : Chapter03RestrictedProduct H)⁻¹)) at h
    simpa using h
  · intro a
    let e : Chapter03RestrictedProduct H ≃ₜ Chapter03RestrictedProduct H :=
      { Equiv.mulLeft a with
        continuous_toFun := chapter03_leftMul_continuous H hH a
        continuous_invFun := by
          simpa using chapter03_leftMul_continuous H hH a⁻¹ }
    have hea : e (1 : Chapter03RestrictedProduct H) = a := by
      change a * (1 : Chapter03RestrictedProduct H) = a
      simp
    have hef : (e : Chapter03RestrictedProduct H → Chapter03RestrictedProduct H) =
        (fun x => a * x) := by
      funext x
      change a * x = a * x
      rfl
    calc
      𝓝 a = 𝓝 (e (1 : Chapter03RestrictedProduct H)) := by rw [hea]
      _ = map e (𝓝 (1 : Chapter03RestrictedProduct H)) :=
        (e.map_nhds_eq (1 : Chapter03RestrictedProduct H)).symm
      _ = map (fun x : Chapter03RestrictedProduct H => a * x)
          (𝓝 (1 : Chapter03RestrictedProduct H)) := by rw [hef]
  · intro a
    let e : Chapter03RestrictedProduct H ≃ₜ Chapter03RestrictedProduct H :=
      { Equiv.mulRight a with
        continuous_toFun := chapter03_rightMul_continuous H hH a
        continuous_invFun := by
          simpa using chapter03_rightMul_continuous H hH a⁻¹ }
    have hea : e (1 : Chapter03RestrictedProduct H) = a := by
      change (1 : Chapter03RestrictedProduct H) * a = a
      simp
    have hef : (e : Chapter03RestrictedProduct H → Chapter03RestrictedProduct H) =
        (fun x => x * a) := by
      funext x
      change x * a = x * a
      rfl
    calc
      𝓝 a = 𝓝 (e (1 : Chapter03RestrictedProduct H)) := by rw [hea]
      _ = map e (𝓝 (1 : Chapter03RestrictedProduct H)) :=
        (e.map_nhds_eq (1 : Chapter03RestrictedProduct H)).symm
      _ = map (fun x : Chapter03RestrictedProduct H => x * a)
          (𝓝 (1 : Chapter03RestrictedProduct H)) := by rw [hef]

private theorem chapter03_add_continuous
    {G : I → Type v} [∀ i, AddGroup (G i)]
    [∀ i, TopologicalSpace (G i)]
    [∀ i, IsTopologicalAddGroup (G i)]
    (H : ∀ i, AddSubgroup (G i))
    (hH : ∀ i, IsOpen (H i : Set (G i))) :
    Continuous (fun p : Chapter03AdditiveRestrictedProduct H ×
      Chapter03AdditiveRestrictedProduct H => p.1 + p.2) := by
  classical
  rw [continuous_generateFrom_iff]
  rintro _ ⟨U, hU, rfl⟩
  refine isOpen_iff_mem_nhds.2 ?_
  rintro ⟨x, y⟩ hxy
  change ∀ i, (((x + y : Chapter03AdditiveRestrictedProduct H) : ∀ i, G i) i) ∈ U i at hxy
  let AX : Set I := {i | ((x : ∀ i, G i) i) ∉ H i}
  let AY : Set I := {i | ((y : ∀ i, G i) i) ∉ H i}
  let EU : Set I := {i | U i ≠ (H i : Set (G i))}
  let S : Set I := AX ∪ AY ∪ EU
  have hAX : AX.Finite := by exact Filter.eventually_cofinite.mp x.property
  have hAY : AY.Finite := by exact Filter.eventually_cofinite.mp y.property
  have hEU : EU.Finite := by exact Filter.eventually_cofinite.mp hU.2
  have hS : S.Finite := (hAX.union hAY).union hEU
  have hdata : ∀ i, ∃ V W : Set (G i),
      IsOpen V ∧ ((x : ∀ i, G i) i ∈ V) ∧
      IsOpen W ∧ ((y : ∀ i, G i) i ∈ W) ∧
      (V ×ˢ W ⊆ {p : G i × G i | p.1 + p.2 ∈ U i}) ∧
      (i ∉ S → V = (H i : Set (G i)) ∧ W = (H i : Set (G i))) := by
    intro i
    by_cases hi : i ∈ S
    · have hxyi : ((x : ∀ i, G i) i) + ((y : ∀ i, G i) i) ∈ U i := by
        simpa using hxy i
      have haddnhds :
          (fun p : G i × G i => p.1 + p.2) ⁻¹' U i ∈
            𝓝 (((x : ∀ i, G i) i), ((y : ∀ i, G i) i)) :=
        continuous_add.continuousAt ((hU.1 i).mem_nhds hxyi)
      rcases mem_nhds_prod_iff.mp haddnhds with ⟨V₀, hV₀, W₀, hW₀, hVW₀⟩
      rcases mem_nhds_iff.mp hV₀ with ⟨V, hVV₀, hVopen, hxV⟩
      rcases mem_nhds_iff.mp hW₀ with ⟨W, hWW₀, hWopen, hyW⟩
      refine ⟨V, W, hVopen, hxV, hWopen, hyW, ?_, fun h => (h hi).elim⟩
      intro p hp
      exact hVW₀ ⟨hVV₀ hp.1, hWW₀ hp.2⟩
    · have hiAX : i ∉ AX := by
        intro hiAX
        exact hi (Or.inl (Or.inl hiAX))
      have hiAY : i ∉ AY := by
        intro hiAY
        exact hi (Or.inl (Or.inr hiAY))
      have hiEU : i ∉ EU := by
        intro hiEU
        exact hi (Or.inr hiEU)
      have hxi : ((x : ∀ i, G i) i) ∈ H i := by
        by_contra hne
        exact hiAX (by simpa [AX] using hne)
      have hyi : ((y : ∀ i, G i) i) ∈ H i := by
        by_contra hne
        exact hiAY (by simpa [AY] using hne)
      have hUi : U i = (H i : Set (G i)) := by
        by_contra hne
        exact hiEU (by simpa [EU] using hne)
      refine ⟨(H i : Set (G i)), (H i : Set (G i)), hH i, hxi, hH i, hyi, ?_,
        fun _ => ⟨rfl, rfl⟩⟩
      intro p hp
      simpa [hUi] using (H i).add_mem hp.1 hp.2
  choose V W hVopen hxV hWopen hyW hVW hVtail using hdata
  have hV : chapter03AdditiveBasicProductCondition H V := by
    constructor
    · exact hVopen
    · filter_upwards [hS.compl_mem_cofinite] with i hi
      exact (hVtail i (by simpa using hi)).1
  have hW : chapter03AdditiveBasicProductCondition H W := by
    constructor
    · exact hWopen
    · filter_upwards [hS.compl_mem_cofinite] with i hi
      exact (hVtail i (by simpa using hi)).2
  have hprod :
      chapter03AdditiveBasicProductSet H V ×ˢ chapter03AdditiveBasicProductSet H W ⊆
        (fun p : Chapter03AdditiveRestrictedProduct H ×
          Chapter03AdditiveRestrictedProduct H => p.1 + p.2) ⁻¹'
          chapter03AdditiveBasicProductSet H U := by
    rintro ⟨x', y'⟩ ⟨hx', hy'⟩
    change ∀ i, (((x' + y' : Chapter03AdditiveRestrictedProduct H) : ∀ i, G i) i) ∈ U i
    intro i
    by_cases hi : i ∈ S
    · have hfactor :
          (((x' : ∀ i, G i) i), ((y' : ∀ i, G i) i)) ∈ V i ×ˢ W i :=
        ⟨hx' i, hy' i⟩
      simpa using hVW i hfactor
    · have htail := hVtail i hi
      have hxiH : ((x' : ∀ i, G i) i) ∈ H i := by
        simpa [htail.1] using hx' i
      have hyiH : ((y' : ∀ i, G i) i) ∈ H i := by
        simpa [htail.2] using hy' i
      have hiU : U i = (H i : Set (G i)) := by
        by_contra hne
        exact hi (Or.inr (by simpa [EU] using hne))
      simpa [hiU] using (H i).add_mem hxiH hyiH
  have hVopen' : IsOpen (chapter03AdditiveBasicProductSet H V) := by
    change IsOpen[chapter03AdditiveRestrictedProductTopology H]
      (chapter03AdditiveBasicProductSet H V)
    exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨V, hV, rfl⟩
  have hWopen' : IsOpen (chapter03AdditiveBasicProductSet H W) := by
    change IsOpen[chapter03AdditiveRestrictedProductTopology H]
      (chapter03AdditiveBasicProductSet H W)
    exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨W, hW, rfl⟩
  have hopenprod : IsOpen
      (chapter03AdditiveBasicProductSet H V ×ˢ chapter03AdditiveBasicProductSet H W) :=
    hVopen'.prod hWopen'
  exact mem_of_superset (hopenprod.mem_nhds ⟨hxV, hyW⟩) hprod

private theorem chapter03_neg_continuous
    {G : I → Type v} [∀ i, AddGroup (G i)]
    [∀ i, TopologicalSpace (G i)]
    [∀ i, IsTopologicalAddGroup (G i)]
    (H : ∀ i, AddSubgroup (G i))
    (hH : ∀ i, IsOpen (H i : Set (G i))) :
    Continuous (fun x : Chapter03AdditiveRestrictedProduct H => -x) := by
  classical
  rw [continuous_generateFrom_iff]
  rintro _ ⟨U, hU, rfl⟩
  let E : Set I := {i | U i ≠ (H i : Set (G i))}
  have hE : E.Finite := by exact Filter.eventually_cofinite.mp hU.2
  let W : ∀ i, Set (G i) := fun i =>
    if i ∈ E then (fun y => -y) ⁻¹' U i else (H i : Set (G i))
  have hW : chapter03AdditiveBasicProductCondition H W := by
    constructor
    · intro i
      by_cases hi : i ∈ E
      · simpa [W, hi] using continuous_neg.isOpen_preimage _ (hU.1 i)
      · simpa [W, hi] using hH i
    · filter_upwards [hE.compl_mem_cofinite] with i hi
      have hiE : i ∉ E := by simpa using hi
      simp [W, hiE]
  have hset :
      (fun x : Chapter03AdditiveRestrictedProduct H => -x) ⁻¹'
          chapter03AdditiveBasicProductSet H U =
        chapter03AdditiveBasicProductSet H W := by
    ext x
    constructor
    · intro hx
      change ∀ i, ((x : ∀ i, G i) i) ∈ W i
      intro i
      by_cases hi : i ∈ E
      · simpa [W, hi] using hx i
      · have hiU : U i = (H i : Set (G i)) := by
          by_contra hne
          exact hi (by simpa [E] using hne)
        have hxin : (((-x : Chapter03AdditiveRestrictedProduct H) : ∀ i, G i) i) ∈ H i := by
          simpa [hiU] using hx i
        have hxi : ((x : ∀ i, G i) i) ∈ H i := by
          simpa using (H i).neg_mem hxin
        simpa [W, hi] using hxi
    · intro hx
      change ∀ i, (((-x : Chapter03AdditiveRestrictedProduct H) : ∀ i, G i) i) ∈ U i
      intro i
      by_cases hi : i ∈ E
      · simpa [W, hi] using hx i
      · have hiU : U i = (H i : Set (G i)) := by
          by_contra hne
          exact hi (by simpa [E] using hne)
        have hxin : (((-x : Chapter03AdditiveRestrictedProduct H) : ∀ i, G i) i) ∈ H i := by
          simpa [W, hi] using hx i
        have hxi : ((x : ∀ i, G i) i) ∈ H i := by
          simpa using (H i).neg_mem hxin
        simpa [hiU] using (H i).neg_mem hxi
  rw [hset]
  change IsOpen[chapter03AdditiveRestrictedProductTopology H]
    (chapter03AdditiveBasicProductSet H W)
  exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨W, hW, rfl⟩

theorem chapter03_additive_restrictedProduct_is_topologicalAddGroup
    {G : I → Type v} [∀ i, AddGroup (G i)]
    [∀ i, TopologicalSpace (G i)]
    [∀ i, IsTopologicalAddGroup (G i)]
    (H : ∀ i, AddSubgroup (G i))
    (hH : ∀ i, IsOpen (H i : Set (G i))) :
    IsTopologicalAddGroup (Chapter03AdditiveRestrictedProduct H) := by
  let hAdd : ContinuousAdd (Chapter03AdditiveRestrictedProduct H) :=
    ⟨chapter03_add_continuous H hH⟩
  let hNeg : ContinuousNeg (Chapter03AdditiveRestrictedProduct H) :=
    ⟨chapter03_neg_continuous H hH⟩
  exact { toContinuousAdd := hAdd, toContinuousNeg := hNeg }

theorem chapter03_additive_basicProductSet_isOpen
    {G : I → Type v} [∀ i, AddGroup (G i)]
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, AddSubgroup (G i)) (U : ∀ i, Set (G i))
    (hU : chapter03AdditiveBasicProductCondition H U) :
    IsOpen (chapter03AdditiveBasicProductSet H U) := by
  change IsOpen[chapter03AdditiveRestrictedProductTopology H]
    (chapter03AdditiveBasicProductSet H U)
  exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨U, hU, rfl⟩

theorem chapter03_mem_additiveBasicProductSet_iff
    {G : I → Type v} [∀ i, AddGroup (G i)]
    (H : ∀ i, AddSubgroup (G i)) (U : ∀ i, Set (G i))
    (x : Chapter03AdditiveRestrictedProduct H) :
    x ∈ chapter03AdditiveBasicProductSet H U ↔
      ∀ i, (x : ∀ i, G i) i ∈ U i :=
  Iff.rfl

theorem chapter03_additiveBasicProductSet_inter
    {G : I → Type v} [∀ i, AddGroup (G i)]
    (H : ∀ i, AddSubgroup (G i)) (U V : ∀ i, Set (G i)) :
    chapter03AdditiveBasicProductSet H U ∩
        chapter03AdditiveBasicProductSet H V =
      chapter03AdditiveBasicProductSet H (fun i => U i ∩ V i) := by
  ext x
  change
    ((∀ i, ((x : ∀ i, G i) i) ∈ U i) ∧
      (∀ i, ((x : ∀ i, G i) i) ∈ V i)) ↔
      ∀ i, ((x : ∀ i, G i) i) ∈ U i ∩ V i
  constructor
  · rintro ⟨hU, hV⟩ i
    exact ⟨hU i, hV i⟩
  · intro h
    exact ⟨fun i => (h i).1, fun i => (h i).2⟩

theorem chapter03_restrictedProduct_topology_is_generated_by_basicProducts
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i)) :
    chapter03RestrictedProductTopology H =
      TopologicalSpace.generateFrom (chapter03BasicOpenSets H) :=
  rfl

/-- The restricted topology requires the distinguished subgroup at every
unmentioned coordinate; the unrestricted product topology does not. -/
theorem chapter03_restrictedTopology_differs_from_unrestricted_subspace
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i))
    (hH : ∀ i, IsOpen (H i : Set (G i)))
    (hproper : chapter03InfinitelyManyProperDistinguishedSubgroups H) :
    chapter03RestrictedProductTopology H ≠
      chapter03UnrestrictedProductSubspaceTopology H :=
  chapter03_restrictedTopology_ne_subspaceTopology H hH hproper

end RestrictedTopology

end
end LastLib.Book04AdelesAndIdeles.Chapter03
