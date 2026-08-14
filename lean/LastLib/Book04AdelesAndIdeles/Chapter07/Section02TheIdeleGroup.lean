import LastLib.Book04AdelesAndIdeles.Chapter07.Dependencies
import Mathlib.Topology.Algebra.IsOpenUnits

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
  classical
  intro U
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
  constructor
  · intro hU x hx
    have hU' : IsOpen[TopologicalSpace.induced
        (chapter07IdeleRestrictedProductEquiv R K) inferInstance] U := by
      rw [← chapter07_idele_restrictedProduct_topology R K]
      exact hU
    rcases isOpen_induced_iff.mp hU' with ⟨W, hW, hWU⟩
    have hex : chapter07IdeleRestrictedProductEquiv R K x ∈ W := by
      have hx' : x ∈ (chapter07IdeleRestrictedProductEquiv R K) ⁻¹' W := by
        rw [hWU]
        exact hx
      exact hx'
    rcases chapter07_restrictedProduct_basicOpen_basis
        (chapter07AllLocalUnitGroup R K) (chapter07AllIntegralUnitSet R K) hA
        (chapter07IdeleRestrictedProductEquiv R K x) W
        (mem_nhds_iff.mpr ⟨W, subset_rfl, hW, hex⟩) with
      ⟨P, hP, V, hV, hxP, hPW⟩
    let Sset : Set (chapter07FinitePlace R) :=
      P.preimage (Sum.inr : chapter07FinitePlace R → chapter07AllPlace R K)
    have hSset : Sset.Finite := by
      exact hP.preimage
        (Sum.inr_injective : Function.Injective
          (Sum.inr : chapter07FinitePlace R → chapter07AllPlace R K)).injOn
    let S : Finset (chapter07FinitePlace R) := hSset.toFinset
    have hSmem (v : chapter07FinitePlace R) : v ∈ S ↔ Sum.inr v ∈ P := by
      simp [S, Sset]
    let Uinf : (v : NumberField.InfinitePlace K) → Set ((v.Completion)ˣ) :=
      fun v => if Sum.inl v ∈ P then V (Sum.inl v) else Set.univ
    let Uf : (v : chapter07FinitePlace R) → Set ((chapter07LocalField R K v)ˣ) :=
      fun v => V (Sum.inr v)
    have hUinf : ∀ v, IsOpen (Uinf v) := by
      intro v
      by_cases hv : Sum.inl v ∈ P
      · simpa [Uinf, hv] using hV (Sum.inl v)
      · simp [Uinf, hv]
    have hUf : ∀ v, IsOpen (Uf v) := by
      intro v
      exact hV (Sum.inr v)
    have hEinf (y : chapter07IdeleGroup R K)
        (v : NumberField.InfinitePlace K) :
        chapter07IdeleRestrictedProductEquiv R K y (Sum.inl v) =
          chapter07IdeleInfiniteCoordinate R K y v := by
      rfl
    have hEfin (y : chapter07IdeleGroup R K)
        (v : chapter07FinitePlace R) :
        chapter07IdeleRestrictedProductEquiv R K y (Sum.inr v) =
          chapter07IdeleFiniteCoordinate R K y v := by
      rfl
    have hpre :
        (chapter07IdeleRestrictedProductEquiv R K) ⁻¹'
            (chapter07RestrictedProductBasicOpen
              (chapter07AllLocalUnitGroup R K) (chapter07AllIntegralUnitSet R K) P V) =
          chapter07IdeleBasicOpen R K S Uinf Uf := by
      ext y
      constructor
      · intro hy
        have hyP : ∀ w ∈ P,
            chapter07IdeleRestrictedProductEquiv R K y w ∈ V w := hy.1
        have hyA : ∀ w ∉ P,
            chapter07IdeleRestrictedProductEquiv R K y w ∈
              chapter07AllIntegralUnitSet R K w := hy.2
        constructor
        · intro v
          by_cases hv : Sum.inl v ∈ P
          · have hy' := hyP (Sum.inl v) hv
            rw [hEinf] at hy'
            simpa [Uinf, hv] using hy'
          · simp [Uinf, hv]
        · constructor
          · intro v hv
            have hp : Sum.inr v ∈ P := (hSmem v).1 hv
            have hy' := hyP (Sum.inr v) hp
            rw [hEfin] at hy'
            simpa [Uf] using hy'
          · intro v hv
            have hp : Sum.inr v ∉ P := by
              intro hp
              exact hv ((hSmem v).2 hp)
            have hy' := hyA (Sum.inr v) hp
            rw [hEfin] at hy'
            simpa [chapter07AllIntegralUnitSet, chapter07AllIntegralUnitSubgroup] using hy'
      · intro hy
        have hyI := hy.1
        have hyF := hy.2
        refine ⟨?_, ?_⟩
        · intro w hw
          cases w with
          | inl v =>
            have hy' := hyI v
            have hv : Sum.inl v ∈ P := hw
            have hy'' : chapter07IdeleInfiniteCoordinate R K y v ∈
                V (Sum.inl v) := by
              simpa [Uinf, hv] using hy'
            rw [hEinf]
            exact hy''
          | inr v =>
            have hvS : v ∈ S := (hSmem v).2 hw
            have hy' := hyF.1 v hvS
            have hy'' : chapter07IdeleFiniteCoordinate R K y v ∈ Uf v := hy'
            rw [hEfin]
            simpa [Uf] using hy''
        · intro w hw
          cases w with
          | inl v =>
            simp [chapter07AllIntegralUnitSet, chapter07AllIntegralUnitSubgroup]
          | inr v =>
            have hvS : v ∉ S := by
              intro hv
              exact hw ((hSmem v).1 hv)
            have hy' := hyF.2 v hvS
            have hy'' : chapter07IdeleFiniteCoordinate R K y v ∈
                (Submonoid.ofClass (chapter07LocalIntegerRing R K v)).units := hy'
            rw [hEfin]
            simpa [chapter07AllIntegralUnitSet, chapter07AllIntegralUnitSubgroup] using hy''
    refine ⟨S, Uinf, Uf, hUinf, hUf, ?_, ?_⟩
    · rw [← hpre]
      exact hxP
    · intro y hy
      have hyP' : chapter07IdeleRestrictedProductEquiv R K y ∈
          chapter07RestrictedProductBasicOpen
            (chapter07AllLocalUnitGroup R K) (chapter07AllIntegralUnitSet R K) P V := by
        have hy' : y ∈ (chapter07IdeleRestrictedProductEquiv R K) ⁻¹'
            (chapter07RestrictedProductBasicOpen
              (chapter07AllLocalUnitGroup R K) (chapter07AllIntegralUnitSet R K) P V) := by
          rw [hpre]
          exact hy
        exact hy'
      have hyW := hPW hyP'
      rw [← hWU]
      exact hyW
  · intro hBasis
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    rcases hBasis x hx with ⟨S, Uinf, Uf, hUinf, hUf, hxB, hBU⟩
    have hB := chapter07_idele_basic_open_isOpen R K S Uinf Uf hUinf hUf
    exact Filter.mem_of_superset (hB.mem_nhds hxB) hBU

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
  have hlocalCompact : ∀ w : chapter07AllPlace R K,
      LocallyCompactSpace (chapter07AllLocalUnitGroup R K w) := by
    intro w
    cases w with
    | inl v =>
      exact (IsOpenUnits.isOpenEmbedding_unitsVal
        (M := v.Completion)).locallyCompactSpace
    | inr v =>
      have hcompact : IsCompact (chapter07LocalIntegerRing R K v :
          Set (chapter07LocalField R K v)) :=
        chapter07_finite_local_integer_isCompact R K v
      have hopen : IsOpen (chapter07LocalIntegerRing R K v :
          Set (chapter07LocalField R K v)) := by
        exact Valued.isOpen_valuationSubring _
      have hfield : LocallyCompactSpace (chapter07LocalField R K v) :=
        hcompact.locallyCompactSpace_of_mem_nhds_of_addGroup
          (hopen.mem_nhds (show (0 : chapter07LocalField R K v) ∈
            (chapter07LocalIntegerRing R K v :
              Set (chapter07LocalField R K v)) by
            simp))
      exact (IsOpenUnits.isOpenEmbedding_unitsVal
        (M := chapter07LocalField R K v)).locallyCompactSpace
  have hcompact : ∀ᶠ w : chapter07AllPlace R K in cofinite,
      IsCompact (chapter07AllIntegralUnitSet R K w :
        Set (chapter07AllLocalUnitGroup R K w)) := by
    let S : Set (chapter07AllPlace R K) :=
      Set.range (Sum.inl : NumberField.InfinitePlace K → chapter07AllPlace R K)
    have hS : S.Finite := Set.finite_range _
    filter_upwards [hS.compl_mem_cofinite] with w hw
    cases w with
    | inl v =>
      exact (hw ⟨v, rfl⟩).elim
    | inr v =>
      exact Submonoid.units_isCompact
        (chapter07_finite_local_integer_isCompact R K v)
  have hBopen : Fact (∀ w : chapter07AllPlace R K,
      IsOpen (chapter07AllIntegralUnitSet R K w :
        Set (chapter07AllLocalUnitGroup R K w))) :=
    ⟨fun w => by
      cases w with
      | inl v => simp [chapter07AllIntegralUnitSet, chapter07AllIntegralUnitSubgroup]
      | inr v =>
        have hlocal : IsOpen (chapter07LocalIntegerRing R K v :
            Set (chapter07LocalField R K v)) := by
          exact Valued.isOpen_valuationSubring _
        exact Submonoid.isOpen_units hlocal⟩
  have htopGroup : ∀ w : chapter07AllPlace R K,
      IsTopologicalGroup (chapter07AllLocalUnitGroup R K w) := by
    intro w
    cases w <;> infer_instance
  have hRP : LocallyCompactSpace (chapter07GlobalIdeleRestrictedProduct R K) := by
    exact RestrictedProduct.locallyCompactSpace_of_group
      (R := chapter07AllLocalUnitGroup R K)
      (B := chapter07AllIntegralUnitSubgroup R K) hcompact
  have he_inducing : IsInducing (chapter07IdeleRestrictedProductEquiv R K) :=
    ⟨chapter07_idele_restrictedProduct_topology R K⟩
  have he : Continuous (chapter07IdeleRestrictedProductEquiv R K) :=
    he_inducing.continuous
  have hinv : Continuous (chapter07IdeleRestrictedProductEquiv R K).symm := by
    apply he_inducing.continuous_iff.mpr
    change Continuous (fun y : chapter07GlobalIdeleRestrictedProduct R K =>
      chapter07IdeleRestrictedProductEquiv R K
        ((chapter07IdeleRestrictedProductEquiv R K).symm y))
    have hEq : (fun y : chapter07GlobalIdeleRestrictedProduct R K =>
        chapter07IdeleRestrictedProductEquiv R K
          ((chapter07IdeleRestrictedProductEquiv R K).symm y)) = id := by
      funext y
      exact (chapter07IdeleRestrictedProductEquiv R K).apply_symm_apply y
    rw [hEq]
    exact continuous_id
  let hhomeo : Homeomorph (chapter07IdeleGroup R K)
      (chapter07GlobalIdeleRestrictedProduct R K) :=
    Homeomorph.mk (chapter07IdeleRestrictedProductEquiv R K).toEquiv he hinv
  exact @Topology.IsInducing.locallyCompactSpace
    (chapter07IdeleGroup R K) (chapter07GlobalIdeleRestrictedProduct R K)
    inferInstance inferInstance hRP _ hhomeo.isInducing (by
      rw [Set.range_eq_univ.mpr hhomeo.surjective]
      exact isClosed_univ.isLocallyClosed)

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
  have hBcompact (v : chapter07FinitePlace R) :
      IsCompact (chapter07LocalIntegerRing R K v :
        Set (chapter07LocalField R K v)) := by
    exact LastLib.Book04AdelesAndIdeles.Chapter07.chapter07_finite_local_integer_isCompact
      R K v
  have hUcompact (v : chapter07FinitePlace R) :
      IsCompact (chapter07LocalIntegralUnitSubgroup R K v :
        Set ((chapter07LocalField R K v)ˣ)) := by
    exact Submonoid.units_isCompact (hBcompact v)
  have hUsubtype (v : chapter07FinitePlace R) :
      IsCompact (Set.univ : Set (chapter07LocalIntegralUnitSubgroup R K v)) := by
    rw [Subtype.isCompact_iff]
    simpa using hUcompact v
  let P : Set (chapter07FiniteIdeleRestrictedProduct R K) :=
    {y | ∀ v : chapter07FinitePlace R,
      y v ∈ chapter07LocalIntegralUnitSubgroup R K v}
  let sMap := RestrictedProduct.structureMap
    (fun v : chapter07FinitePlace R => (chapter07LocalField R K v)ˣ)
    (fun v : chapter07FinitePlace R =>
      (chapter07LocalIntegralUnitSubgroup R K v :
        Set ((chapter07LocalField R K v)ˣ))) cofinite
  have hPcompact : IsCompact P := by
    have hP_eq : P = Set.range sMap := by
      dsimp [sMap]
      rw [RestrictedProduct.range_structureMap]
      rfl
    rw [hP_eq]
    have hrange : Set.range sMap =
        sMap '' (Set.univ : Set (∀ v : chapter07FinitePlace R,
          chapter07LocalIntegralUnitSubgroup R K v)) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x, Set.mem_univ _, rfl⟩
      · rintro ⟨x, -, rfl⟩
        exact ⟨x, rfl⟩
    rw [hrange]
    simpa [sMap] using (isCompact_univ_pi (fun v => hUsubtype v)).image
      (RestrictedProduct.isEmbedding_structureMap
        (R := fun v : chapter07FinitePlace R => (chapter07LocalField R K v)ˣ)
        (A := fun v : chapter07FinitePlace R =>
          (chapter07LocalIntegralUnitSubgroup R K v :
            Set ((chapter07LocalField R K v)ˣ))) (𝓕 := cofinite)).continuous
  have hPopen : IsOpen P := by
    change IsOpen {y : chapter07FiniteIdeleRestrictedProduct R K |
      ∀ v : chapter07FinitePlace R,
        y v ∈ chapter07LocalIntegralUnitSubgroup R K v}
    exact RestrictedProduct.isOpen_forall_mem (fun v => by
      have hlocal : IsOpen (chapter07LocalIntegerRing R K v :
          Set (chapter07LocalField R K v)) := by
        exact Valued.isOpen_valuationSubring _
      exact Submonoid.isOpen_units hlocal)
  have he_inducing : IsInducing (chapter07FiniteIdeleEquiv R K) :=
    ⟨chapter07_finiteIdele_restrictedProduct_topology R K⟩
  have he_surjective : Function.Surjective (chapter07FiniteIdeleEquiv R K) :=
    (chapter07FiniteIdeleEquiv R K).surjective
  have hcarrier :
      (chapter07FiniteIntegralUnitSubgroup R K :
        Set (chapter07FiniteIdeleGroup R K)) =
        (chapter07FiniteIdeleEquiv R K) ⁻¹' P := by
    ext x
    rfl
  constructor
  · rw [hcarrier]
    apply he_inducing.isCompact_preimage' hPcompact
    exact fun y _ => he_surjective y
  · rw [hcarrier]
    exact hPopen.preimage he_inducing.continuous

theorem chapter07_idele_graph_subspace_topology
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    (inferInstance : TopologicalSpace (chapter07IdeleGroup R K)) =
      TopologicalSpace.induced (chapter07IdeleGraph R K) inferInstance :=
  chapter07_ideleTopology_is_graphTopology R K

end

end LastLib.Book04AdelesAndIdeles.Chapter07
