import LastLib.Book04AdelesAndIdeles.Chapter07.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter07

noncomputable section

open Set Filter Topology
open scoped BigOperators DirectSum RestrictedProduct

/-! # 7.2 The idele group -/

/-- A basic restricted-product neighborhood with a finite exceptional set. -/
def chapter07RestrictedProductBasicOpen
    {ι : Type*} (R : ι → Type*) (A : (i : ι) → Set (R i))
    (S : Set ι) (U : (i : ι) → Set (R i)) :
    Set (Πʳ i, [R i, A i]) :=
  {x | (∀ i ∈ S, x i ∈ U i) ∧ ∀ i ∉ S, x i ∈ A i}

theorem chapter07_restrictedProduct_basicOpen_isOpen
    {ι : Type*} (R : ι → Type*) (A : (i : ι) → Set (R i))
    [∀ i, TopologicalSpace (R i)]
    (S : Set ι) (hS : S.Finite) (U : (i : ι) → Set (R i))
    (hU : ∀ i, IsOpen (U i)) (hA : ∀ i, IsOpen (A i)) :
    IsOpen (chapter07RestrictedProductBasicOpen R A S U) := by
  have hU' : IsOpen (⋂ i ∈ S, (fun x : Πʳ i, [R i, A i] => x i) ⁻¹' U i) :=
    hS.isOpen_biInter fun i hi =>
      (hU i).preimage (RestrictedProduct.continuous_eval (R := R) (A := A) i)
  have hA' : IsOpen {x : Πʳ i, [R i, A i] | ∀ i, i ∉ S → x i ∈ A i} :=
    RestrictedProduct.isOpen_forall_imp_mem hA
  have hopen := hU'.inter hA'
  rw [show chapter07RestrictedProductBasicOpen R A S U =
      (⋂ i ∈ S, (fun x : Πʳ i, [R i, A i] => x i) ⁻¹' U i) ∩
        {x : Πʳ i, [R i, A i] | ∀ i, i ∉ S → x i ∈ A i} by
    ext x
    simp [chapter07RestrictedProductBasicOpen]]
  exact hopen

theorem chapter07_restrictedProduct_basicOpen_basis
    {ι : Type*} (R : ι → Type*) (A : (i : ι) → Set (R i))
    [∀ i, TopologicalSpace (R i)] (hA : ∀ i, IsOpen (A i)) :
    ∀ x : Πʳ i, [R i, A i], ∀ U ∈ 𝓝 x,
      ∃ S : Set ι, S.Finite ∧ ∃ V : (i : ι) → Set (R i),
        (∀ i, IsOpen (V i)) ∧ x ∈ chapter07RestrictedProductBasicOpen R A S V ∧
      chapter07RestrictedProductBasicOpen R A S V ⊆ U := by
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
  have hS : S.Finite := by
    exact J.finite_toSet.union hTcomp
  have hV : ∀ i, IsOpen (V i) := by
    intro i
    by_cases hiJ : i ∈ J
    · by_cases hiT : i ∈ T
      · simpa [V, hiJ, hiT] using (hq i hiJ).1.inter (hA i)
      · simpa [V, hiJ, hiT] using (hq i hiJ).1
    · simp [V, hiJ]
  have hxB : x ∈ chapter07RestrictedProductBasicOpen R A S V := by
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

/-- The book's full-idele basic open set: all archimedean coordinates are restricted to chosen
local neighborhoods, while only the finite set `S` of finite places has arbitrary neighborhoods. -/
def chapter07IdeleBasicOpen
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (S : Finset (chapter07FinitePlace R))
    (Uinf : (v : NumberField.InfinitePlace K) → Set ((v.Completion)ˣ))
    (Uf : (v : chapter07FinitePlace R) → Set ((chapter07LocalField R K v)ˣ)) :
    Set (chapter07IdeleGroup R K) :=
  {x |
    (∀ v : NumberField.InfinitePlace K,
      chapter07IdeleInfiniteCoordinate R K x v ∈ Uinf v) ∧
      (∀ v : chapter07FinitePlace R, v ∈ S →
        chapter07IdeleFiniteCoordinate R K x v ∈ Uf v) ∧
      (∀ v : chapter07FinitePlace R, v ∉ S →
        chapter07IdeleFiniteCoordinate R K x v ∈
          (Submonoid.ofClass (chapter07LocalIntegerRing R K v)).units)}

theorem chapter07_idele_basic_open_isOpen
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    (S : Finset (chapter07FinitePlace R))
    (Uinf : (v : NumberField.InfinitePlace K) → Set ((v.Completion)ˣ))
    (Uf : (v : chapter07FinitePlace R) → Set ((chapter07LocalField R K v)ˣ))
    (hInf : ∀ v, IsOpen (Uinf v)) (hf : ∀ v, IsOpen (Uf v)) :
    IsOpen (chapter07IdeleBasicOpen R K S Uinf Uf) := by
  classical
  let P : Set (chapter07AllPlace R K) :=
    Set.range (Sum.inl : NumberField.InfinitePlace K → chapter07AllPlace R K) ∪
      (S : Set (chapter07FinitePlace R)).image Sum.inr
  let W : (w : chapter07AllPlace R K) → Set (chapter07AllLocalUnitGroup R K w) :=
    fun w => match w with
    | Sum.inl v => Uinf v
    | Sum.inr v => if v ∈ S then Uf v else
        (chapter07AllIntegralUnitSubgroup R K (Sum.inr v) : Set _)
  have hP : P.Finite := by
    exact (Set.finite_range (Sum.inl : NumberField.InfinitePlace K →
      chapter07AllPlace R K)).union
      (S.finite_toSet.image (Sum.inr : chapter07FinitePlace R → chapter07AllPlace R K))
  have hA : ∀ w, IsOpen (chapter07AllIntegralUnitSet R K w) := by
    intro w
    cases w with
    | inl v => simp [chapter07AllIntegralUnitSet, chapter07AllIntegralUnitSubgroup]
    | inr v =>
      change IsOpen ((Submonoid.ofClass (chapter07LocalIntegerRing R K v)).units :
        Set (chapter07LocalField R K v)ˣ)
      have hlocal : IsOpen (chapter07LocalIntegerRing R K v :
          Set (chapter07LocalField R K v)) := by
        exact Valued.isOpen_valuationSubring _
      exact Submonoid.isOpen_units hlocal
  have hW : ∀ w, IsOpen (W w) := by
    intro w
    cases w with
    | inl v => simpa [W] using hInf v
    | inr v =>
      by_cases hv : v ∈ S
      · simpa [W, hv] using hf v
      · simpa [W, hv] using hA (Sum.inr v)
  have hB : IsOpen (chapter07RestrictedProductBasicOpen
      (chapter07AllLocalUnitGroup R K) (chapter07AllIntegralUnitSet R K)
      P W) :=
    chapter07_restrictedProduct_basicOpen_isOpen
      (chapter07AllLocalUnitGroup R K) (chapter07AllIntegralUnitSet R K)
      P hP W hW hA
  let B := chapter07RestrictedProductBasicOpen
      (chapter07AllLocalUnitGroup R K) (chapter07AllIntegralUnitSet R K) P W
  have hEinf (x : chapter07IdeleGroup R K) (v : NumberField.InfinitePlace K) :
      chapter07IdeleRestrictedProductEquiv R K x (Sum.inl v) =
        chapter07IdeleInfiniteCoordinate R K x v := by
    rfl
  have hEfin (x : chapter07IdeleGroup R K) (v : chapter07FinitePlace R) :
      chapter07IdeleRestrictedProductEquiv R K x (Sum.inr v) =
        chapter07IdeleFiniteCoordinate R K x v := by
    rfl
  have hpre : (chapter07IdeleRestrictedProductEquiv R K) ⁻¹' B =
      chapter07IdeleBasicOpen R K S Uinf Uf := by
    ext x
    constructor
    · intro hx
      have hxP : ∀ w ∈ P,
          chapter07IdeleRestrictedProductEquiv R K x w ∈ W w := hx.1
      have hxA : ∀ w ∉ P,
          chapter07IdeleRestrictedProductEquiv R K x w ∈
            chapter07AllIntegralUnitSet R K w := hx.2
      constructor
      · intro v
        have hx' := hxP (Sum.inl v) (by exact Or.inl ⟨v, rfl⟩)
        rw [hEinf] at hx'
        simpa [W] using hx'
      · constructor
        · intro v hv
          have hx' := hxP (Sum.inr v) (by exact Or.inr ⟨v, hv, rfl⟩)
          rw [hEfin] at hx'
          simpa [W, hv] using hx'
        · intro v hv
          have hvP : Sum.inr v ∉ P := by simp [P, hv]
          have hx' := hxA (Sum.inr v) hvP
          rw [hEfin] at hx'
          simpa [chapter07AllIntegralUnitSet, chapter07AllIntegralUnitSubgroup] using hx'
    · intro hx
      refine ⟨?_, ?_⟩
      · intro w hw
        cases w with
        | inl v =>
          rw [hEinf]
          simpa [W] using hx.1 v
        | inr v =>
          by_cases hv : v ∈ S
          · have hx' := hx.2.1 v hv
            rw [hEfin]
            simpa [W, hv] using hx'
          · have hx' := hx.2.2 v hv
            rw [hEfin]
            simpa [W, hv, chapter07AllIntegralUnitSet,
              chapter07AllIntegralUnitSubgroup] using hx'
      · intro w hw
        cases w with
        | inl v => exact (by simp [chapter07AllIntegralUnitSet, chapter07AllIntegralUnitSubgroup])
        | inr v =>
          have hx' := hx.2.2 v (by
            intro hv
            apply hw
            exact Or.inr ⟨v, hv, rfl⟩)
          rw [hEfin]
          simpa [chapter07AllIntegralUnitSet, chapter07AllIntegralUnitSubgroup] using hx'
  have htop : IsOpen[TopologicalSpace.induced
      (chapter07IdeleRestrictedProductEquiv R K) inferInstance]
      ((chapter07IdeleRestrictedProductEquiv R K) ⁻¹' B) :=
    isOpen_induced_iff.mpr ⟨B, hB, rfl⟩
  rw [hpre] at htop
  rw [← chapter07_idele_restrictedProduct_topology R K] at htop
  exact htop

theorem chapter07_idele_basic_open_basis
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K] :
    ∀ U : Set (chapter07IdeleGroup R K), IsOpen U ↔
      ∀ x ∈ U, ∃ (S : Finset (chapter07FinitePlace R))
        (Uinf : (v : NumberField.InfinitePlace K) → Set ((v.Completion)ˣ))
        (Uf : (v : chapter07FinitePlace R) → Set ((chapter07LocalField R K v)ˣ)),
        (∀ v, IsOpen (Uinf v)) ∧ (∀ v, IsOpen (Uf v)) ∧
          x ∈ chapter07IdeleBasicOpen R K S Uinf Uf ∧
          chapter07IdeleBasicOpen R K S Uinf Uf ⊆ U := by
  sorry

@[simp]
theorem chapter07_idele_mul_apply_infinite
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (x y : chapter07IdeleGroup R K) (v : NumberField.InfinitePlace K) :
    (x * y).1.1 v = x.1.1 v * y.1.1 v := by
  rfl

@[simp]
theorem chapter07_idele_mul_apply_finite
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (x y : chapter07IdeleGroup R K) (v : chapter07FinitePlace R) :
    (x * y).1.2 v = x.1.2 v * y.1.2 v := by
  rfl

@[simp]
theorem chapter07_idele_inv_apply_infinite
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (x : chapter07IdeleGroup R K) (v : NumberField.InfinitePlace K) :
    (x⁻¹ : chapter07IdeleGroup R K).1.1 v = (x.1.1 v)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  exact congrArg (fun a : chapter07AdeleRing R K => a.1 v) x.val_inv

@[simp]
theorem chapter07_idele_inv_apply_finite
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (x : chapter07IdeleGroup R K) (v : chapter07FinitePlace R) :
    (x⁻¹ : chapter07IdeleGroup R K).1.2 v = (x.1.2 v)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  exact congrArg (fun a : chapter07AdeleRing R K => a.2 v) x.val_inv

instance chapter07_idele_group_is_comm_group
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    CommGroup (chapter07IdeleGroup R K) := by
  infer_instance

theorem chapter07_idele_group_is_topological_group
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    IsTopologicalGroup (chapter07IdeleGroup R K) := by
  infer_instance

theorem chapter07_idele_group_is_locally_compact
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R] :
    LocallyCompactSpace (chapter07IdeleGroup R K) := by
  sorry

/-- The compact-open subgroup usually denoted `\widehat{\mathcal O}_K^×`. -/
def chapter07FiniteIntegralUnitSubgroup
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    Subgroup (chapter07FiniteIdeleGroup R K) where
  carrier := {x | ∀ v : chapter07FinitePlace R,
    chapter07FiniteIdeleEquiv R K x v ∈
      (Submonoid.ofClass (chapter07LocalIntegerRing R K v)).units}
  one_mem' := by
    intro v
    simp
  mul_mem' := by
    intro x y hx hy v
    have hx' : chapter07FiniteIdeleEquiv R K x v ∈
        chapter07LocalIntegralUnitSubgroup R K v := hx v
    have hy' : chapter07FiniteIdeleEquiv R K y v ∈
        chapter07LocalIntegralUnitSubgroup R K v := hy v
    have h := (chapter07LocalIntegralUnitSubgroup R K v).mul_mem hx' hy'
    simpa using h
  inv_mem' := by
    intro x hx v
    have hx' : chapter07FiniteIdeleEquiv R K x v ∈
        chapter07LocalIntegralUnitSubgroup R K v := hx v
    have h := (chapter07LocalIntegralUnitSubgroup R K v).inv_mem hx'
    simpa using h

theorem chapter07_mem_finiteIntegralUnitSubgroup_iff
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (x : chapter07FiniteIdeleGroup R K) :
    x ∈ chapter07FiniteIntegralUnitSubgroup R K ↔
      ∀ v : chapter07FinitePlace R,
        chapter07FiniteIdeleEquiv R K x v ∈
          (Submonoid.ofClass (chapter07LocalIntegerRing R K v)).units :=
  Iff.rfl

theorem chapter07_finiteIntegralUnits_valued_iff
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (x : chapter07FiniteIdeleGroup R K) :
    x ∈ chapter07FiniteIntegralUnitSubgroup R K ↔
      ∀ v : chapter07FinitePlace R,
        Valued.v (chapter07FiniteIdeleEquiv R K x v).1 = 1 := by
  rw [chapter07_mem_finiteIntegralUnitSubgroup_iff]
  constructor
  · intro h v
    exact (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one).1
      (h v)
  · intro h v
    exact (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one).2
      (h v)

theorem chapter07_finiteIntegralUnits_compact_open
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Module.Finite ℤ R] [Module.Free ℤ R] :
    IsCompact (chapter07FiniteIntegralUnitSubgroup R K : Set (chapter07FiniteIdeleGroup R K)) ∧
      IsOpen (chapter07FiniteIntegralUnitSubgroup R K : Set (chapter07FiniteIdeleGroup R K)) := by
  sorry

theorem chapter07_idele_graph_subspace_topology
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    (inferInstance : TopologicalSpace (chapter07IdeleGroup R K)) =
      TopologicalSpace.induced (chapter07IdeleGraph R K) inferInstance :=
  chapter07_ideleTopology_is_graphTopology R K

end

end LastLib.Book04AdelesAndIdeles.Chapter07
