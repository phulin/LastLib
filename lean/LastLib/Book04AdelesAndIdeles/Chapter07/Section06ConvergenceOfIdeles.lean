import LastLib.Book04AdelesAndIdeles.Chapter07.Dependencies
import LastLib.Book04AdelesAndIdeles.Chapter07.Section01WhyNonzeroAdelesNotEnough
import Mathlib.Topology.Algebra.Group.Pointwise

namespace LastLib.Book04AdelesAndIdeles.Chapter07

noncomputable section

open Set Filter Topology
open scoped BigOperators DirectSum RestrictedProduct Pointwise

/-! # 7.6 Convergence of ideles -/

/-- The finite-place tail condition appearing in the convergence criterion for restricted
products of multiplicative local groups. -/
def chapter07RestrictedIdeleTailCondition
    {ι δ : Type*} (G : ι → Type*)
    [∀ i, Group (G i)] (B : (i : ι) → Subgroup (G i))
    (f : δ → Πʳ i, [(G i), (B i : Set (G i))])
    (x : Πʳ i, [(G i), (B i : Set (G i))]) (l : Filter δ) : Prop :=
  ∃ S : Set ι, S.Finite ∧
    ∀ᶠ n in l, ∀ i ∉ S, f n i * (x i)⁻¹ ∈ B i

/-- The additive analogue of the restricted-product tail condition. -/
def chapter07RestrictedAdditiveTailCondition
    {ι δ : Type*} (G : ι → Type*)
    [∀ i, AddGroup (G i)] (B : (i : ι) → AddSubgroup (G i))
    (f : δ → Πʳ i, [(G i), (B i : Set (G i))])
    (x : Πʳ i, [(G i), (B i : Set (G i))]) (l : Filter δ) : Prop :=
  ∃ S : Set ι, S.Finite ∧
    ∀ᶠ n in l, ∀ i ∉ S, f n i - x i ∈ B i

def chapter07RestrictedProductBasicOpenConvergence
    {ι : Type*} (R : ι → Type*) (A : (i : ι) → Set (R i))
    (S : Set ι) (U : (i : ι) → Set (R i)) :
    Set (Πʳ i, [R i, A i]) :=
  {x | (∀ i ∈ S, x i ∈ U i) ∧ ∀ i ∉ S, x i ∈ A i}

theorem chapter07_restrictedProduct_basicOpen_isOpen_convergence
    {ι : Type*} (R : ι → Type*) (A : (i : ι) → Set (R i))
    [∀ i, TopologicalSpace (R i)]
    (S : Set ι) (hS : S.Finite) (U : (i : ι) → Set (R i))
    (hU : ∀ i, IsOpen (U i)) (hA : ∀ i, IsOpen (A i)) :
    IsOpen (chapter07RestrictedProductBasicOpenConvergence R A S U) := by
  have hU' : IsOpen (⋂ i ∈ S, (fun x : Πʳ i, [R i, A i] => x i) ⁻¹' U i) :=
    hS.isOpen_biInter fun i hi =>
      (hU i).preimage (RestrictedProduct.continuous_eval (R := R) (A := A) i)
  have hA' : IsOpen {x : Πʳ i, [R i, A i] | ∀ i, i ∉ S → x i ∈ A i} :=
    RestrictedProduct.isOpen_forall_imp_mem hA
  have hopen := hU'.inter hA'
  rw [show chapter07RestrictedProductBasicOpenConvergence R A S U =
      (⋂ i ∈ S, (fun x : Πʳ i, [R i, A i] => x i) ⁻¹' U i) ∩
        {x : Πʳ i, [R i, A i] | ∀ i, i ∉ S → x i ∈ A i} by
    ext x
    simp [chapter07RestrictedProductBasicOpenConvergence]]
  exact hopen

theorem chapter07_restrictedProduct_basicOpen_basis_convergence
    {ι : Type*} (R : ι → Type*) (A : (i : ι) → Set (R i))
    [∀ i, TopologicalSpace (R i)] (hA : ∀ i, IsOpen (A i)) :
    ∀ x : Πʳ i, [R i, A i], ∀ U ∈ 𝓝 x,
      ∃ S : Set ι, S.Finite ∧ ∃ V : (i : ι) → Set (R i),
        (∀ i, IsOpen (V i)) ∧
          x ∈ chapter07RestrictedProductBasicOpenConvergence R A S V ∧
            chapter07RestrictedProductBasicOpenConvergence R A S V ⊆ U := by
  classical
  intro x U hUx
  rcases mem_nhds_iff.mp hUx with ⟨W, hWU, hWopen, hxW⟩
  let T : Set ι := {i | x i ∈ A i}
  have hT : cofinite ≤ 𝓟 T := by
    apply le_principal_iff.mpr
    change ∀ᶠ i in cofinite, x i ∈ A i
    exact x.2
  have hxT : ∀ᶠ i in 𝓟 T, x i ∈ A i := by
    exact Filter.mem_principal.mpr subset_rfl
  rcases RestrictedProduct.exists_inclusion_eq_of_eventually R A hT hxT with ⟨x', hxx⟩
  have hle :
      TopologicalSpace.coinduced (RestrictedProduct.inclusion R A hT)
          (RestrictedProduct.topologicalSpace R A (𝓟 T)) ≤
        (inferInstance : TopologicalSpace (Πʳ i, [R i, A i])) := by
    change TopologicalSpace.coinduced (RestrictedProduct.inclusion R A hT)
          (RestrictedProduct.topologicalSpace R A (𝓟 T)) ≤
        RestrictedProduct.topologicalSpace R A cofinite
    rw [RestrictedProduct.topologicalSpace_eq_iSup cofinite]
    exact le_iSup_of_le T (le_iSup_of_le hT le_rfl)
  have hWcomp : IsOpen[
      TopologicalSpace.coinduced (RestrictedProduct.inclusion R A hT)
        (RestrictedProduct.topologicalSpace R A (𝓟 T))] W :=
    hle W hWopen
  have hpre : IsOpen[RestrictedProduct.topologicalSpace R A (𝓟 T)]
      (RestrictedProduct.inclusion R A hT ⁻¹' W) :=
    isOpen_coinduced.mp hWcomp
  rw [RestrictedProduct.topologicalSpace_eq_of_principal] at hpre
  rcases isOpen_induced_iff.mp hpre with ⟨O, hO, hOeq⟩
  have hxpre : x' ∈ RestrictedProduct.inclusion R A hT ⁻¹' W := by
    change RestrictedProduct.inclusion R A hT x' ∈ W
    rw [hxx]
    exact hxW
  have hxO : (x' : ∀ i, R i) ∈ O := by
    have hxpre' := hxpre
    rw [← hOeq] at hxpre'
    exact hxpre'
  rcases isOpen_pi_iff.mp hO (x' : ∀ i, R i) hxO with ⟨J, q, hq, hqO⟩
  let S : Set ι := (J : Set ι) ∪ Tᶜ
  let V : (i : ι) → Set (R i) := fun i =>
    if i ∈ J then if i ∈ T then q i ∩ A i else q i else univ
  have hTcomp : Tᶜ.Finite := by
    change {i | x i ∉ A i}.Finite
    exact Filter.eventually_cofinite.mp x.2
  have hS : S.Finite := J.finite_toSet.union hTcomp
  have hV : ∀ i, IsOpen (V i) := by
    intro i
    by_cases hiJ : i ∈ J
    · by_cases hiT : i ∈ T
      · simpa [V, hiJ, hiT] using (hq i hiJ).1.inter (hA i)
      · simpa [V, hiJ, hiT] using (hq i hiJ).1
    · simp [V, hiJ]
  have hxB : x ∈ chapter07RestrictedProductBasicOpenConvergence R A S V := by
    constructor
    · intro i hiS
      by_cases hiJ : i ∈ J
      · have hxu : (x' : ∀ i, R i) i ∈ q i := (hq i hiJ).2
        have hxcoord : (x' : ∀ i, R i) i = x i := by
          simpa using congrArg (fun z : Πʳ i, [R i, A i] => z i) hxx
        rw [hxcoord] at hxu
        by_cases hiT : i ∈ T
        · have hxa : x i ∈ A i := hiT
          simpa [V, hiJ, hiT] using And.intro hxu hxa
        · simpa [V, hiJ, hiT] using hxu
      · simp [S] at hiS
        simp [V, hiJ]
    · intro i hiS
      have hiT : i ∈ T := by
        by_contra hiT
        exact hiS (by simp [S, hiT])
      exact hiT
  refine ⟨S, hS, V, hV, hxB, ?_⟩
  intro z hz
  have hzT : ∀ᶠ i in 𝓟 T, z i ∈ A i := by
    apply Filter.mem_principal.mpr
    intro i hiT
    by_cases hiJ : i ∈ J
    · have hzV : z i ∈ V i := hz.1 i (by simp [S, hiJ])
      have hzVA : z i ∈ q i ∩ A i := by
        simpa [V, hiJ, hiT] using hzV
      exact hzVA.2
    · exact hz.2 i (by simp [S, hiJ, hiT])
  rcases RestrictedProduct.exists_inclusion_eq_of_eventually R A hT hzT with ⟨z', hzz⟩
  have hzO : (z' : ∀ i, R i) ∈ O := by
    apply hqO
    intro i hiJ
    have hiJ' : i ∈ J := by simpa using hiJ
    have hiS : i ∈ S := by
      change i ∈ (J : Set ι) ∪ Tᶜ
      exact Or.inl hiJ
    have hzV : z i ∈ V i := hz.1 i hiS
    have hzq : z i ∈ q i := by
      by_cases hiT : i ∈ T
      · exact (show z i ∈ q i ∩ A i by simpa [V, hiJ', hiT] using hzV).1
      · simpa [V, hiJ', hiT] using hzV
    have hzcoord : (z' : ∀ i, R i) i = z i := by
      simpa using congrArg (fun w : Πʳ i, [R i, A i] => w i) hzz
    rw [hzcoord]
    exact hzq
  have hzpre : z' ∈ RestrictedProduct.inclusion R A hT ⁻¹' W := by
    rw [← hOeq]
    exact hzO
  apply hWU
  change RestrictedProduct.inclusion R A hT z' ∈ W at hzpre
  simpa [hzz] using hzpre

theorem chapter07_restrictedProduct_tendsto_iff
    {ι δ : Type*} (G : ι → Type*)
    [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, IsTopologicalGroup (G i)]
    (B : (i : ι) → Subgroup (G i))
    (hB : ∀ i, IsOpen (B i : Set (G i)))
    (f : δ → Πʳ i, [(G i), (B i : Set (G i))])
    (x : Πʳ i, [(G i), (B i : Set (G i))]) (l : Filter δ) :
    Tendsto f l (𝓝 x) ↔
      (∀ i, Tendsto (fun n => f n i) l (𝓝 (x i))) ∧
        chapter07RestrictedIdeleTailCondition G B f x l := by
  classical
  constructor
  · intro h
    constructor
    · intro i
      exact (RestrictedProduct.continuous_eval
        (R := G) (A := fun i => (B i : Set (G i))) i).tendsto (x := x) |>.comp h
    · let S : Set ι := {i | x i ∉ B i}
      let V : (i : ι) → Set (G i) := fun i =>
        (B i : Set (G i)) * ({x i} : Set (G i))
      have hS : S.Finite := by
        exact Filter.eventually_cofinite.mp x.2
      have hV : ∀ i, IsOpen (V i) := by
        intro i
        simpa [V] using (hB i).mul_right (t := ({x i} : Set (G i)))
      have hxV : x ∈ chapter07RestrictedProductBasicOpenConvergence G
          (fun i => (B i : Set (G i))) S V := by
        constructor
        · intro i hi
          simpa using Set.mul_mem_mul (B i).one_mem (by rfl)
        · intro i hi
          by_contra hxi
          exact hi hxi
      have hev : ∀ᶠ n in l,
          f n ∈ chapter07RestrictedProductBasicOpenConvergence G
            (fun i => (B i : Set (G i))) S V := by
        have hopen := chapter07_restrictedProduct_basicOpen_isOpen_convergence
          G (fun i => (B i : Set (G i))) S hS V hV hB
        exact (tendsto_nhds.mp h _ hopen hxV)
      refine ⟨S, hS, ?_⟩
      filter_upwards [hev] with n hn i hi
      have hfi : f n i ∈ B i := hn.2 i hi
      have hxi : x i ∈ B i := by
        by_contra hxi
        exact hi hxi
      have hmul := (B i).mul_mem hfi ((B i).inv_mem hxi)
      simpa using hmul
  · rintro ⟨hcoord, htail⟩
    rw [tendsto_nhds]
    intro U hUopen hxU
    have hUnhds : U ∈ 𝓝 x := hUopen.mem_nhds hxU
    rcases chapter07_restrictedProduct_basicOpen_basis_convergence G
        (fun i => (B i : Set (G i))) hB x U hUnhds with
      ⟨S, hS, V, hV, hxV, hVU⟩
    let S' : Set ι := S ∪ Classical.choose htail
    let V' : (i : ι) → Set (G i) := fun i =>
      if i ∈ S then V i else (B i : Set (G i))
    have hT : (Classical.choose htail).Finite := (Classical.choose_spec htail).1
    have htail' : ∀ᶠ n in l, ∀ i ∉ Classical.choose htail,
        f n i * (x i)⁻¹ ∈ B i := (Classical.choose_spec htail).2
    have hS' : S'.Finite := hS.union hT
    have hcoord' : ∀ i ∈ S', ∀ᶠ n in l, f n i ∈ V' i := by
      intro i hi
      by_cases hiS : i ∈ S
      · have hiV : ∀ᶠ n in l, f n i ∈ V i :=
          (tendsto_nhds.mp (hcoord i) (V i) (hV i) (hxV.1 i hiS))
        simpa [V', hiS] using hiV
      · have hiB : ∀ᶠ n in l, f n i ∈ B i := by
          have hxi : x i ∈ B i := hxV.2 i (by
            intro hiS'
            exact hiS hiS')
          exact tendsto_nhds.mp (hcoord i) (B i) (hB i) hxi
        simpa [V', hiS] using hiB
    have hevV : ∀ᶠ n in l, ∀ i ∈ S', f n i ∈ V' i :=
      hS'.eventually_all.mpr hcoord'
    have hevBasic : ∀ᶠ n in l,
        f n ∈ chapter07RestrictedProductBasicOpenConvergence G
          (fun i => (B i : Set (G i))) S' V' := by
      filter_upwards [hevV, htail'] with n hnV hnTail
      constructor
      · exact hnV
      · intro i hiS'
        have hiT : i ∉ Classical.choose htail := by
          intro hiT
          exact hiS' (Or.inr hiT)
        have hrel := hnTail i hiT
        have hxi : x i ∈ B i := hxV.2 i (by
          intro hiS
          exact hiS' (Or.inl hiS))
        have hmul := (B i).mul_mem hrel hxi
        simpa using hmul
    have hsubset : chapter07RestrictedProductBasicOpenConvergence G
        (fun i => (B i : Set (G i))) S' V' ⊆
        chapter07RestrictedProductBasicOpenConvergence G
          (fun i => (B i : Set (G i))) S V := by
      intro y hy
      constructor
      · intro i hiS
        have hy' := hy.1 i (Or.inl hiS)
        simpa [V', hiS] using hy'
      · intro i hiS
        by_cases hiS' : i ∈ S'
        · have hy' := hy.1 i hiS'
          simpa [V', hiS] using hy'
        · exact hy.2 i hiS'
    filter_upwards [hevBasic] with n hn
    exact hVU (hsubset hn)

theorem chapter07_restrictedProduct_tendsto_iff_eventually_integral_quotient
    {ι δ : Type*} (G : ι → Type*)
    [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, IsTopologicalGroup (G i)]
    (B : (i : ι) → Subgroup (G i))
    (hB : ∀ i, IsOpen (B i : Set (G i)))
    (f : δ → Πʳ i, [(G i), (B i : Set (G i))])
    (x : Πʳ i, [(G i), (B i : Set (G i))]) (l : Filter δ) :
    Tendsto f l (𝓝 x) ↔
      (∀ i, Tendsto (fun n => f n i) l (𝓝 (x i))) ∧
        ∃ S : Set ι, S.Finite ∧
          ∀ᶠ n in l, ∀ i ∉ S, f n i * (x i)⁻¹ ∈ B i :=
  chapter07_restrictedProduct_tendsto_iff G B hB f x l

theorem chapter07_restrictedProduct_additive_tendsto_iff
    {ι δ : Type*} (G : ι → Type*)
    [∀ i, AddGroup (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, IsTopologicalAddGroup (G i)]
    (B : (i : ι) → AddSubgroup (G i))
    (hB : ∀ i, IsOpen (B i : Set (G i)))
    (f : δ → Πʳ i, [(G i), (B i : Set (G i))])
    (x : Πʳ i, [(G i), (B i : Set (G i))]) (l : Filter δ) :
    Tendsto f l (𝓝 x) ↔
      (∀ i, Tendsto (fun n => f n i) l (𝓝 (x i))) ∧
        chapter07RestrictedAdditiveTailCondition G B f x l := by
  classical
  constructor
  · intro h
    constructor
    · intro i
      exact (RestrictedProduct.continuous_eval
        (R := G) (A := fun i => (B i : Set (G i))) i).tendsto (x := x) |>.comp h
    · let S : Set ι := {i | x i ∉ B i}
      let V : (i : ι) → Set (G i) := fun i =>
        (B i : Set (G i)) + ({x i} : Set (G i))
      have hS : S.Finite := by
        exact Filter.eventually_cofinite.mp x.2
      have hV : ∀ i, IsOpen (V i) := by
        intro i
        simpa [V] using (hB i).add_right (t := ({x i} : Set (G i)))
      have hxV : x ∈ chapter07RestrictedProductBasicOpenConvergence G
          (fun i => (B i : Set (G i))) S V := by
        constructor
        · intro i hi
          simpa using Set.add_mem_add (B i).zero_mem (by rfl)
        · intro i hi
          by_contra hxi
          exact hi hxi
      have hev : ∀ᶠ n in l,
          f n ∈ chapter07RestrictedProductBasicOpenConvergence G
            (fun i => (B i : Set (G i))) S V := by
        have hopen := chapter07_restrictedProduct_basicOpen_isOpen_convergence
          G (fun i => (B i : Set (G i))) S hS V hV hB
        exact (tendsto_nhds.mp h _ hopen hxV)
      refine ⟨S, hS, ?_⟩
      filter_upwards [hev] with n hn i hi
      have hfi : f n i ∈ B i := hn.2 i hi
      have hxi : x i ∈ B i := by
        by_contra hxi
        exact hi hxi
      exact (B i).sub_mem hfi hxi
  · rintro ⟨hcoord, htail⟩
    rw [tendsto_nhds]
    intro U hUopen hxU
    have hUnhds : U ∈ 𝓝 x := hUopen.mem_nhds hxU
    rcases chapter07_restrictedProduct_basicOpen_basis_convergence G
        (fun i => (B i : Set (G i))) hB x U hUnhds with
      ⟨S, hS, V, hV, hxV, hVU⟩
    let S' : Set ι := S ∪ Classical.choose htail
    let V' : (i : ι) → Set (G i) := fun i =>
      if i ∈ S then V i else (B i : Set (G i))
    have hT : (Classical.choose htail).Finite := (Classical.choose_spec htail).1
    have htail' : ∀ᶠ n in l, ∀ i ∉ Classical.choose htail,
        f n i - x i ∈ B i := (Classical.choose_spec htail).2
    have hS' : S'.Finite := hS.union hT
    have hcoord' : ∀ i ∈ S', ∀ᶠ n in l, f n i ∈ V' i := by
      intro i hi
      by_cases hiS : i ∈ S
      · have hiV : ∀ᶠ n in l, f n i ∈ V i :=
          (tendsto_nhds.mp (hcoord i) (V i) (hV i) (hxV.1 i hiS))
        simpa [V', hiS] using hiV
      · have hiB : ∀ᶠ n in l, f n i ∈ B i := by
          have hxi : x i ∈ B i := hxV.2 i (by
            intro hiS'
            exact hiS hiS')
          exact tendsto_nhds.mp (hcoord i) (B i) (hB i) hxi
        simpa [V', hiS] using hiB
    have hevV : ∀ᶠ n in l, ∀ i ∈ S', f n i ∈ V' i :=
      hS'.eventually_all.mpr hcoord'
    have hevBasic : ∀ᶠ n in l,
        f n ∈ chapter07RestrictedProductBasicOpenConvergence G
          (fun i => (B i : Set (G i))) S' V' := by
      filter_upwards [hevV, htail'] with n hnV hnTail
      constructor
      · exact hnV
      · intro i hiS'
        have hiT : i ∉ Classical.choose htail := by
          intro hiT
          exact hiS' (Or.inr hiT)
        have hrel := hnTail i hiT
        have hxi : x i ∈ B i := hxV.2 i (by
          intro hiS
          exact hiS' (Or.inl hiS))
        simpa [sub_add_cancel] using (B i).add_mem hrel hxi
    have hsubset : chapter07RestrictedProductBasicOpenConvergence G
        (fun i => (B i : Set (G i))) S' V' ⊆
        chapter07RestrictedProductBasicOpenConvergence G
          (fun i => (B i : Set (G i))) S V := by
      intro y hy
      constructor
      · intro i hiS
        have hy' := hy.1 i (Or.inl hiS)
        simpa [V', hiS] using hy'
      · intro i hiS
        by_cases hiS' : i ∈ S'
        · have hy' := hy.1 i hiS'
          simpa [V', hiS] using hy'
        · exact hy.2 i hiS'
    filter_upwards [hevBasic] with n hn
    exact hVU (hsubset hn)

theorem chapter07_additive_adele_tendsto_iff_aux
    {δ : Type*} (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (f : δ → chapter07AdeleRing R K)
    (x : chapter07AdeleRing R K) (l : Filter δ) :
    Tendsto f l (𝓝 x) ↔
      (∀ v : NumberField.InfinitePlace K,
        Tendsto (fun n => (f n).1 v) l (𝓝 (x.1 v))) ∧
      (∀ v : chapter07FinitePlace R,
        Tendsto (fun n => (f n).2 v) l (𝓝 (x.2 v))) ∧
      ∃ S : Set (chapter07FinitePlace R), S.Finite ∧
        ∀ᶠ n in l, ∀ v ∉ S,
          (f n).2 v - (x.2 v) ∈ chapter07LocalIntegerRing R K v := by
  constructor
  · intro h
    have hp := (Prod.tendsto_iff f x).mp h
    have hi : ∀ v : NumberField.InfinitePlace K,
        Tendsto (fun n => (f n).1 v) l (𝓝 (x.1 v)) := by
      exact fun v => (tendsto_pi_nhds.mp hp.1) v
    have hf := hp.2
    have hB : ∀ v : chapter07FinitePlace R,
        IsOpen (((chapter07LocalIntegerRing R K v).toSubring.toAddSubgroup :
          Set (chapter07LocalField R K v))) := by
      intro v
      change IsOpen (chapter07LocalIntegerRing R K v :
        Set (chapter07LocalField R K v))
      exact Valued.isOpen_valuationSubring _
    have hfinite :=
      (chapter07_restrictedProduct_additive_tendsto_iff
        (fun v : chapter07FinitePlace R => chapter07LocalField R K v)
        (fun v : chapter07FinitePlace R =>
          (chapter07LocalIntegerRing R K v).toSubring.toAddSubgroup)
        hB (fun n => (f n).2) (x.2) l).mp hf
    exact ⟨hi, hfinite.1, hfinite.2⟩
  · rintro ⟨hi, hf, htail⟩
    have hB : ∀ v : chapter07FinitePlace R,
        IsOpen (((chapter07LocalIntegerRing R K v).toSubring.toAddSubgroup :
          Set (chapter07LocalField R K v))) := by
      intro v
      change IsOpen (chapter07LocalIntegerRing R K v :
        Set (chapter07LocalField R K v))
      exact Valued.isOpen_valuationSubring _
    apply (Prod.tendsto_iff f x).mpr
    refine ⟨?_, ?_⟩
    · exact tendsto_pi_nhds.mpr hi
    · apply
        (chapter07_restrictedProduct_additive_tendsto_iff
          (fun v : chapter07FinitePlace R => chapter07LocalField R K v)
          (fun v : chapter07FinitePlace R =>
            (chapter07LocalIntegerRing R K v).toSubring.toAddSubgroup)
          hB (fun n => (f n).2) (x.2) l).mpr
      exact ⟨hf, htail⟩

theorem chapter07_idele_tendsto_iff
    {δ : Type*} (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (f : δ → chapter07IdeleGroup R K)
    (x : chapter07IdeleGroup R K) (l : Filter δ) :
    Tendsto f l (𝓝 x) ↔
      (∀ v : NumberField.InfinitePlace K,
        Tendsto (fun n => (f n).1.1 v) l (𝓝 (x.1.1 v))) ∧
        (∀ v : chapter07FinitePlace R,
          Tendsto (fun n => (f n).1.2 v) l (𝓝 (x.1.2 v))) ∧
        ∃ S : Set (chapter07FinitePlace R), S.Finite ∧
          ∀ᶠ n in l, ∀ v ∉ S,
            Valued.v ((f n).1.2 v * (x.1.2 v)⁻¹) = 1 := by
  have hinv_inf (u : chapter07IdeleGroup R K) (v : NumberField.InfinitePlace K) :
      (u⁻¹ : chapter07IdeleGroup R K).1.1 v = (u.1.1 v)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    exact congrArg (fun a : chapter07AdeleRing R K => a.1 v) u.val_inv
  have hinv_fin (u : chapter07IdeleGroup R K) (v : chapter07FinitePlace R) :
      (u⁻¹ : chapter07IdeleGroup R K).1.2 v = (u.1.2 v)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    exact congrArg (fun a : chapter07AdeleRing R K => a.2 v) u.val_inv
  constructor
  · intro h
    have hgraph := ((chapter07_ideleGraph_isEmbedding R K).tendsto_nhds_iff).mp h
    have hprod := (Prod.tendsto_iff
      (fun n => chapter07IdeleGraph R K (f n))
      (chapter07IdeleGraph R K x)).mp hgraph
    have hf := (chapter07_additive_adele_tendsto_iff_aux R K
      (fun n => (chapter07IdeleGraph R K (f n)).1)
      (chapter07IdeleGraph R K x).1 l).mp hprod.1
    have hinv := (chapter07_additive_adele_tendsto_iff_aux R K
      (fun n => (chapter07IdeleGraph R K (f n)).2)
      (chapter07IdeleGraph R K x).2 l).mp hprod.2
    have hcoord_inf : ∀ v : NumberField.InfinitePlace K,
        Tendsto (fun n => (f n).1.1 v) l (𝓝 (x.1.1 v)) := by
      intro v
      simpa [chapter07IdeleGraph] using hf.1 v
    have hcoord_fin : ∀ v : chapter07FinitePlace R,
        Tendsto (fun n => (f n).1.2 v) l (𝓝 (x.1.2 v)) := by
      intro v
      simpa [chapter07IdeleGraph] using hf.2.1 v
    refine ⟨hcoord_inf, hcoord_fin, ?_⟩
    rcases hf.2.2 with ⟨Sf, hSf, hTf⟩
    rcases hinv.2.2 with ⟨Si, hSi, hTi⟩
    let Sx : Set (chapter07FinitePlace R) :=
      {v | x.1.2 v ∉ chapter07LocalIntegerRing R K v}
    let Sxi : Set (chapter07FinitePlace R) :=
      {v | (x⁻¹ : chapter07IdeleGroup R K).1.2 v ∉
        chapter07LocalIntegerRing R K v}
    have hSx : Sx.Finite := by
      change {v : chapter07FinitePlace R |
        x.1.2 v ∉ chapter07LocalIntegerRing R K v}.Finite
      exact Filter.eventually_cofinite.mp x.1.2.2
    have hSxi : Sxi.Finite := by
      change {v : chapter07FinitePlace R |
        (x⁻¹ : chapter07IdeleGroup R K).1.2 v ∉
          chapter07LocalIntegerRing R K v}.Finite
      exact Filter.eventually_cofinite.mp (x⁻¹ : chapter07IdeleGroup R K).1.2.2
    let S : Set (chapter07FinitePlace R) := ((Sf ∪ Si) ∪ Sx) ∪ Sxi
    have hS : S.Finite := hSf.union hSi |>.union hSx |>.union hSxi
    refine ⟨S, hS, ?_⟩
    filter_upwards [hTf, hTi] with n hfn hin
    intro v hv
    have hvf : v ∉ Sf := by
      intro hv'
      exact hv (Or.inl (Or.inl (Or.inl hv')))
    have hvi : v ∉ Si := by
      intro hv'
      exact hv (Or.inl (Or.inl (Or.inr hv')))
    have hvx : v ∉ Sx := by
      intro hv'
      exact hv (Or.inl (Or.inr hv'))
    have hvxi : v ∉ Sxi := by
      intro hv'
      exact hv (Or.inr hv')
    have hfd : (f n).1.2 v - x.1.2 v ∈
        chapter07LocalIntegerRing R K v := hfn v hvf
    have hid : (x⁻¹ : chapter07IdeleGroup R K).1.2 v ∈
        chapter07LocalIntegerRing R K v := by
      by_contra hid
      exact hvxi hid
    have hird : (f n)⁻¹.1.2 v -
        (x⁻¹ : chapter07IdeleGroup R K).1.2 v ∈
        chapter07LocalIntegerRing R K v := hin v hvi
    have hxmem : x.1.2 v ∈ chapter07LocalIntegerRing R K v := by
      by_contra hxmem
      exact hvx hxmem
    have hfdmul : ((f n).1.2 v - x.1.2 v) *
        (x⁻¹ : chapter07IdeleGroup R K).1.2 v ∈
        chapter07LocalIntegerRing R K v :=
      (chapter07LocalIntegerRing R K v).mul_mem _ _ hfd hid
    have hirdmul : ((f n)⁻¹.1.2 v -
        (x⁻¹ : chapter07IdeleGroup R K).1.2 v) * x.1.2 v ∈
        chapter07LocalIntegerRing R K v :=
      (chapter07LocalIntegerRing R K v).mul_mem _ _ hird hxmem
    have hy : (f n).1.2 v * (x.1.2 v)⁻¹ ∈
        chapter07LocalIntegerRing R K v := by
      have hx0 : x.1.2 v ≠ 0 :=
        (chapter07IdeleFiniteCoordinate R K x v).ne_zero
      have hsum := (chapter07LocalIntegerRing R K v).add_mem _ _
        hfdmul (chapter07LocalIntegerRing R K v).one_mem
      simpa [hinv_fin, sub_mul, mul_assoc, hx0, mul_comm] using hsum
    have hyinv : ((f n).1.2 v * (x.1.2 v)⁻¹)⁻¹ ∈
        chapter07LocalIntegerRing R K v := by
      have hx0 : x.1.2 v ≠ 0 :=
        (chapter07IdeleFiniteCoordinate R K x v).ne_zero
      have hsum := (chapter07LocalIntegerRing R K v).add_mem _ _
        hirdmul (chapter07LocalIntegerRing R K v).one_mem
      rw [sub_mul] at hsum
      simpa [hinv_fin, sub_mul, mul_assoc, hx0, mul_comm] using hsum
    have hy0 : (f n).1.2 v * (x.1.2 v)⁻¹ ≠ 0 := by
      exact mul_ne_zero
        (chapter07IdeleFiniteCoordinate R K (f n) v).ne_zero
        (inv_ne_zero (chapter07IdeleFiniteCoordinate R K x v).ne_zero)
    let yu : (chapter07LocalField R K v)ˣ :=
      Units.mk0 ((f n).1.2 v * (x.1.2 v)⁻¹) hy0
    have hyunit : yu ∈
        (Submonoid.ofClass (chapter07LocalIntegerRing R K v)).units := by
      apply Submonoid.mem_units_of_val_mem_inv_val_mem
        (Submonoid.ofClass (chapter07LocalIntegerRing R K v))
      · change (f n).1.2 v * (x.1.2 v)⁻¹ ∈
          chapter07LocalIntegerRing R K v
        exact hy
      · change ((f n).1.2 v * (x.1.2 v)⁻¹)⁻¹ ∈
          chapter07LocalIntegerRing R K v
        exact hyinv
    exact (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
      (a := yu)).1 hyunit
  · rintro ⟨hcoord_inf, hcoord_fin, htail⟩
    have hcoord_inv_inf : ∀ v : NumberField.InfinitePlace K,
        Tendsto (fun n => (f n)⁻¹ |>.1.1 v) l
          (𝓝 ((x⁻¹ : chapter07IdeleGroup R K).1.1 v)) := by
      intro v
      have hx0 : x.1.1 v ≠ 0 :=
        (chapter07IdeleInfiniteCoordinate R K x v).ne_zero
      have h := (continuousAt_inv₀ hx0).tendsto.comp (hcoord_inf v)
      simpa only [Function.comp_def, hinv_inf] using h
    have hcoord_inv_fin : ∀ v : chapter07FinitePlace R,
        Tendsto (fun n => (f n)⁻¹ |>.1.2 v) l
          (𝓝 ((x⁻¹ : chapter07IdeleGroup R K).1.2 v)) := by
      intro v
      have hx0 : x.1.2 v ≠ 0 :=
        (chapter07IdeleFiniteCoordinate R K x v).ne_zero
      have h := (continuousAt_inv₀ hx0).tendsto.comp (hcoord_fin v)
      simpa only [Function.comp_def, hinv_fin] using h
    let S0 : Set (chapter07FinitePlace R) := Classical.choose htail
    have hS0 : S0.Finite := (Classical.choose_spec htail).1
    have hT0 : ∀ᶠ n in l, ∀ v ∉ S0,
        Valued.v ((f n).1.2 v * (x.1.2 v)⁻¹) = 1 :=
      (Classical.choose_spec htail).2
    let Sx : Set (chapter07FinitePlace R) :=
      {v | x.1.2 v ∉ chapter07LocalIntegerRing R K v}
    let Sxi : Set (chapter07FinitePlace R) :=
      {v | (x⁻¹ : chapter07IdeleGroup R K).1.2 v ∉
        chapter07LocalIntegerRing R K v}
    have hSx : Sx.Finite := by
      change {v : chapter07FinitePlace R |
        x.1.2 v ∉ chapter07LocalIntegerRing R K v}.Finite
      exact Filter.eventually_cofinite.mp x.1.2.2
    have hSxi : Sxi.Finite := by
      change {v : chapter07FinitePlace R |
        (x⁻¹ : chapter07IdeleGroup R K).1.2 v ∉
          chapter07LocalIntegerRing R K v}.Finite
      exact Filter.eventually_cofinite.mp (x⁻¹ : chapter07IdeleGroup R K).1.2.2
    have hf_tail : ∃ S : Set (chapter07FinitePlace R), S.Finite ∧
        ∀ᶠ n in l, ∀ v ∉ S,
          (f n).1.2 v - x.1.2 v ∈ chapter07LocalIntegerRing R K v := by
      let S : Set (chapter07FinitePlace R) := S0 ∪ Sx
      refine ⟨S, hS0.union hSx, ?_⟩
      filter_upwards [hT0] with n hn
      intro v hv
      have hv0 : v ∉ S0 := by
        intro hv'
        exact hv (Or.inl hv')
      have hvx : v ∉ Sx := by
        intro hv'
        exact hv (Or.inr hv')
      have hxmem : x.1.2 v ∈ chapter07LocalIntegerRing R K v := by
        by_contra hxmem
        exact hvx hxmem
      have hy0 : (f n).1.2 v * (x.1.2 v)⁻¹ ≠ 0 := by
        exact mul_ne_zero
          (chapter07IdeleFiniteCoordinate R K (f n) v).ne_zero
          (inv_ne_zero (chapter07IdeleFiniteCoordinate R K x v).ne_zero)
      let yu : (chapter07LocalField R K v)ˣ :=
        Units.mk0 ((f n).1.2 v * (x.1.2 v)⁻¹) hy0
      have hyu : yu ∈
          (Submonoid.ofClass (chapter07LocalIntegerRing R K v)).units := by
        apply IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.2
        simpa [yu] using hn v hv0
      have hy : (f n).1.2 v * (x.1.2 v)⁻¹ ∈
          chapter07LocalIntegerRing R K v :=
        by
          change (yu : chapter07LocalField R K v) ∈
            chapter07LocalIntegerRing R K v
          exact Submonoid.val_mem_of_mem_units
            (Submonoid.ofClass (chapter07LocalIntegerRing R K v)) hyu
      have hsub := (chapter07LocalIntegerRing R K v).sub_mem
        ((chapter07LocalIntegerRing R K v).mul_mem _ _
          ((chapter07LocalIntegerRing R K v).sub_mem hy
            (chapter07LocalIntegerRing R K v).one_mem) hxmem)
        (chapter07LocalIntegerRing R K v).zero_mem
      have hx0 : x.1.2 v ≠ 0 :=
        (chapter07IdeleFiniteCoordinate R K x v).ne_zero
      simpa [sub_mul, mul_assoc, hx0] using hsub
    have hinv_tail : ∃ S : Set (chapter07FinitePlace R), S.Finite ∧
        ∀ᶠ n in l, ∀ v ∉ S,
          (f n)⁻¹ |>.1.2 v -
            (x⁻¹ : chapter07IdeleGroup R K).1.2 v ∈
              chapter07LocalIntegerRing R K v := by
      let S : Set (chapter07FinitePlace R) := S0 ∪ Sxi
      refine ⟨S, hS0.union hSxi, ?_⟩
      filter_upwards [hT0] with n hn
      intro v hv
      have hv0 : v ∉ S0 := by
        intro hv'
        exact hv (Or.inl hv')
      have hvxi : v ∉ Sxi := by
        intro hv'
        exact hv (Or.inr hv')
      have hximem : (x⁻¹ : chapter07IdeleGroup R K).1.2 v ∈
          chapter07LocalIntegerRing R K v := by
        by_contra hximem
        exact hvxi hximem
      have hy0 : (f n).1.2 v * (x.1.2 v)⁻¹ ≠ 0 := by
        exact mul_ne_zero
          (chapter07IdeleFiniteCoordinate R K (f n) v).ne_zero
          (inv_ne_zero (chapter07IdeleFiniteCoordinate R K x v).ne_zero)
      let yu : (chapter07LocalField R K v)ˣ :=
        Units.mk0 ((f n).1.2 v * (x.1.2 v)⁻¹) hy0
      have hyu : yu ∈
          (Submonoid.ofClass (chapter07LocalIntegerRing R K v)).units := by
        apply IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.2
        simpa [yu] using hn v hv0
      have hyinv : ((f n).1.2 v * (x.1.2 v)⁻¹)⁻¹ ∈
          chapter07LocalIntegerRing R K v :=
        by
          change ((yu⁻¹ : (chapter07LocalField R K v)ˣ) :
            chapter07LocalField R K v) ∈ chapter07LocalIntegerRing R K v
          exact Submonoid.val_mem_of_mem_units
            (Submonoid.ofClass (chapter07LocalIntegerRing R K v))
            ((Submonoid.ofClass (chapter07LocalIntegerRing R K v)).units.inv_mem hyu)
      have hsub := (chapter07LocalIntegerRing R K v).sub_mem
        ((chapter07LocalIntegerRing R K v).mul_mem _ _
          ((chapter07LocalIntegerRing R K v).sub_mem hyinv
            (chapter07LocalIntegerRing R K v).one_mem) hximem)
        (chapter07LocalIntegerRing R K v).zero_mem
      rw [sub_mul] at hsub
      have hx0 : x.1.2 v ≠ 0 :=
        (chapter07IdeleFiniteCoordinate R K x v).ne_zero
      simpa [hinv_fin, sub_mul, mul_assoc, hx0, mul_comm] using hsub
    have hf := (chapter07_additive_adele_tendsto_iff_aux R K
      (fun n => (f n).1) x.1 l).2 ⟨hcoord_inf, hcoord_fin, hf_tail⟩
    have hinv := (chapter07_additive_adele_tendsto_iff_aux R K
      (fun n => (f n)⁻¹ |>.1) (x⁻¹ : chapter07IdeleGroup R K).1 l).2
      ⟨hcoord_inv_inf, hcoord_inv_fin, hinv_tail⟩
    apply ((chapter07_ideleGraph_isEmbedding R K).tendsto_nhds_iff).mpr
    exact (Prod.tendsto_iff
      (fun n => chapter07IdeleGraph R K (f n))
      (chapter07IdeleGraph R K x)).2 ⟨hf, hinv⟩

theorem chapter07_idele_sequence_tendsto_iff
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (f : ℕ → chapter07IdeleGroup R K) (x : chapter07IdeleGroup R K) :
    Tendsto f atTop (𝓝 x) ↔
      (∀ v : NumberField.InfinitePlace K,
        Tendsto (fun n => (f n).1.1 v) atTop (𝓝 (x.1.1 v))) ∧
        (∀ v : chapter07FinitePlace R,
          Tendsto (fun n => (f n).1.2 v) atTop (𝓝 (x.1.2 v))) ∧
        ∃ S : Set (chapter07FinitePlace R), S.Finite ∧
          ∀ᶠ n in atTop, ∀ v ∉ S,
            Valued.v ((f n).1.2 v * (x.1.2 v)⁻¹) = 1 := by
  exact chapter07_idele_tendsto_iff R K f x atTop

theorem chapter07_additive_adele_tendsto_iff
    {δ : Type*} (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (f : δ → chapter07AdeleRing R K)
    (x : chapter07AdeleRing R K) (l : Filter δ) :
    Tendsto f l (𝓝 x) ↔
      (∀ v : NumberField.InfinitePlace K,
        Tendsto (fun n => (f n).1 v) l (𝓝 (x.1 v))) ∧
        (∀ v : chapter07FinitePlace R,
          Tendsto (fun n => (f n).2 v) l (𝓝 (x.2 v))) ∧
    ∃ S : Set (chapter07FinitePlace R), S.Finite ∧
          ∀ᶠ n in l, ∀ v ∉ S,
            (f n).2 v - (x.2 v) ∈ chapter07LocalIntegerRing R K v := by
  exact chapter07_additive_adele_tendsto_iff_aux R K f x l

theorem chapter07_moving_prime_idele_does_not_tendsto_one :
    ¬ Tendsto chapter07MovingPrimeIdele cofinite
      (𝓝 (1 : chapter07IdeleGroup ℤ ℚ)) := by
  intro h
  have hcrit := (chapter07_idele_tendsto_iff ℤ ℚ
    chapter07MovingPrimeIdele (1 : chapter07IdeleGroup ℤ ℚ) cofinite).mp h
  rcases hcrit.2.2 with ⟨S, hS, htail⟩
  let e : Nat.Primes → chapter07FinitePlace ℤ :=
    (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm
  have he : Function.Injective e := by
    intro p q hpq
    exact (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm.injective hpq
  have hbad : {p : Nat.Primes | e p ∈ S}.Finite :=
    hS.preimage he.injOn
  have hfalse : ∀ᶠ p : Nat.Primes in cofinite, False := by
    filter_upwards [htail, hbad.compl_mem_cofinite] with p hp hpb
    let _ : Fact p.1.Prime := ⟨p.2⟩
    let v : chapter07FinitePlace ℤ := e p
    have hvS : v ∉ S := by
      intro hv
      exact hpb hv
    have hval := hp v hvS
    have hcoord : Padic.adicCompletionEquiv ℤ p
        (algebraMap ℚ (ℚ_[p]) (p.1 : ℚ)) =
        algebraMap ℚ (chapter07LocalField ℤ ℚ v) (p.1 : ℚ) := by
      exact (Padic.adicCompletionEquiv ℤ p).commutes (p.1 : ℚ)
    have hvaluation : Valued.v
        (Padic.adicCompletionEquiv ℤ p
          (algebraMap ℚ (ℚ_[p]) (p.1 : ℚ))) =
        v.valuation ℚ (p.1 : ℚ) := by
      rw [hcoord]
      rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
      simp only [Function.comp_apply]
      exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
        v (p.1 : ℚ)
    have hmap : (Rat.IsIntegralClosure.intEquiv ℤ)
        (p.1 : ℤ) ∈ v.asIdeal.map (Rat.IsIntegralClosure.intEquiv ℤ) := by
      have hgen : Rat.HeightOneSpectrum.natGenerator v = p.1 := by
        exact congrArg Subtype.val
          ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).apply_symm_apply p)
      simpa [hgen] using
        (Rat.HeightOneSpectrum.natGenerator_dvd_iff v).mp (dvd_refl _)
    have hmemR : (p.1 : ℤ) ∈ v.asIdeal :=
      (Ideal.apply_mem_of_equiv_iff
        (I := v.asIdeal) (f := Rat.IsIntegralClosure.intEquiv ℤ)
        (x := (p.1 : ℤ))).mp hmap
    have hlt : v.valuation ℚ (p.1 : ℚ) < 1 := by
      exact (v.valuation_lt_one_iff_mem (K := ℚ) (p.1 : ℤ)).2 hmemR
    have hnot : Valued.v
        (Padic.adicCompletionEquiv ℤ p
          (algebraMap ℚ (ℚ_[p]) (p.1 : ℚ))) ≠ 1 := by
      rw [hvaluation]
      exact ne_of_lt hlt
    have htarget : Valued.v
        ((chapter07MovingPrimeIdele p).1.2 v *
          ((1 : chapter07IdeleGroup ℤ ℚ).1.2 v)⁻¹) = 1 := hval
    have hmove : (chapter07MovingPrimeIdele p).1.2 v =
        Padic.adicCompletionEquiv ℤ p
          (algebraMap ℚ (ℚ_[p]) (p.1 : ℚ)) := by
      rw [show (chapter07MovingPrimeIdele p).1.2 v =
          (chapter07MovingPrimeAdele p).2 v by
        rw [chapter07MovingPrimeIdele_val]]
      simpa [v, e] using chapter07_moving_prime_adele_component_at_prime p
    rw [hmove] at htarget
    have hone : (1 : chapter07IdeleGroup ℤ ℚ).1.2 v = 1 := by rfl
    rw [hone, inv_one, mul_one] at htarget
    exact hnot htarget
  rcases hfalse.exists with ⟨p, hp⟩
  exact hp

theorem chapter07_moving_prime_is_additively_convergent_but_not_idelically :
    Tendsto chapter07MovingPrimeAdele cofinite
        (𝓝 (1 : chapter07AdeleRing ℤ ℚ)) ∧
      ¬ Tendsto chapter07MovingPrimeIdele cofinite
        (𝓝 (1 : chapter07IdeleGroup ℤ ℚ)) := by
  exact ⟨chapter07_moving_prime_adele_tendsto_one,
    chapter07_moving_prime_idele_does_not_tendsto_one⟩

theorem chapter07_idele_graph_tendsto_iff
    {δ : Type*} (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (f : δ → chapter07IdeleGroup R K) (x : chapter07IdeleGroup R K)
    (l : Filter δ) :
    Tendsto f l (𝓝 x) ↔
      Tendsto (fun n => chapter07IdeleGraph R K (f n)) l
        (𝓝 (chapter07IdeleGraph R K x)) := by
  simpa [Function.comp_def] using
    (chapter07_ideleGraph_isEmbedding R K).tendsto_nhds_iff

theorem chapter07_idele_inversion_is_continuous
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    Continuous (fun x : chapter07IdeleGroup R K => x⁻¹) := by
  exact continuous_inv

/-- The underlying set of ideles is exactly the set of units of the adele ring. -/
theorem chapter07_idele_underlying_set_iff_adele_is_unit
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (x : chapter07AdeleRing R K) :
    IsUnit x ↔ ∃ u : chapter07IdeleGroup R K, (u : chapter07AdeleRing R K) = x := by
  constructor
  · intro hx
    exact ⟨hx.unit, hx.unit_spec⟩
  · rintro ⟨u, rfl⟩
    exact u.isUnit

theorem chapter07_idele_underlying_set_eq_adele_units
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    Set.range (fun u : chapter07IdeleGroup R K =>
      (u : chapter07AdeleRing R K)) = {x | IsUnit x} := by
  ext x
  simp [chapter07_idele_underlying_set_iff_adele_is_unit]

theorem chapter07_idele_inversion_is_continuous_from_graph_topology
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    Continuous (fun x : chapter07IdeleGroup R K => x⁻¹) :=
  chapter07_idele_inversion_is_continuous R K

end

end LastLib.Book04AdelesAndIdeles.Chapter07
