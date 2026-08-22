import LastLib.Book04AdelesAndIdeles.Chapter05.Section03DiscretenessInTheFullAdeles
import LastLib.Book04AdelesAndIdeles.Chapter05.Section02StrongApproximationInTheFiniteAdeles

namespace LastLib.Book04AdelesAndIdeles.Chapter05

open LastLib.Book04AdelesAndIdeles.Chapter01
open LastLib.Book04AdelesAndIdeles.Chapter04
open Set Filter

noncomputable section

open scoped Topology RestrictedProduct

/-! ## 5.6. Strong and weak approximation compared -/

theorem chapter05_away_complement_is_finite_place
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04Place K))
    (hSinf : chapter05InfinitePlaces K ⊆ S) :
    ∀ v : Chapter04Place K, v ∉ S →
      ∃ w : Chapter04FinitePlace K, v = Sum.inl w := by
  intro v hv
  cases v with
  | inl w => exact ⟨w, rfl⟩
  | inr w => exact (hv (hSinf ⟨w, rfl⟩)).elim

private def chapter05RestrictedProductBasicOpen
    {ι : Type*} (R : ι → Type*) (A : (i : ι) → Set (R i))
    (S : Set ι) (U : (i : ι) → Set (R i)) :
    Set (Πʳ i, [R i, A i]_[Filter.cofinite]) :=
  {x | (∀ i ∈ S, x i ∈ U i) ∧ ∀ i ∉ S, x i ∈ A i}

private theorem chapter05_restrictedProduct_basicOpen_basis
    {ι : Type*} (R : ι → Type*) (A : (i : ι) → Set (R i))
    [∀ i, TopologicalSpace (R i)] (hA : ∀ i, IsOpen (A i)) :
    ∀ x : Πʳ i, [R i, A i]_[Filter.cofinite], ∀ V ∈ 𝓝 x,
      ∃ S : Set ι, S.Finite ∧ ∃ U : (i : ι) → Set (R i),
        (∀ i, IsOpen (U i)) ∧
        x ∈ chapter05RestrictedProductBasicOpen R A S U ∧
            chapter05RestrictedProductBasicOpen R A S U ⊆ V ∧
              ∀ i ∉ S, x i ∈ A i := by
  classical
  intro x V hV
  rcases mem_nhds_iff.mp hV with ⟨W, hWV, hWopen, hxW⟩
  let T : Set ι := {i | x i ∈ A i}
  have hT : Filter.cofinite ≤ 𝓟 T := by
    apply le_principal_iff.mpr
    change ∀ᶠ i in Filter.cofinite, x i ∈ A i
    exact x.2
  have hxT : ∀ᶠ i in 𝓟 T, x i ∈ A i :=
    Filter.mem_principal.mpr subset_rfl
  rcases RestrictedProduct.exists_inclusion_eq_of_eventually R A hT hxT with ⟨x', hxx⟩
  have hle :
      TopologicalSpace.coinduced (RestrictedProduct.inclusion R A hT)
          (RestrictedProduct.topologicalSpace R A (𝓟 T)) ≤
        (inferInstance : TopologicalSpace (Πʳ i, [R i, A i]_[Filter.cofinite])) := by
    change TopologicalSpace.coinduced (RestrictedProduct.inclusion R A hT)
          (RestrictedProduct.topologicalSpace R A (𝓟 T)) ≤
        RestrictedProduct.topologicalSpace R A Filter.cofinite
    rw [RestrictedProduct.topologicalSpace_eq_iSup Filter.cofinite]
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
  let U : (i : ι) → Set (R i) := fun i =>
    if i ∈ J then if i ∈ T then q i ∩ A i else q i else univ
  have hTcomp : Tᶜ.Finite := by
    change {i | x i ∉ A i}.Finite
    exact Filter.eventually_cofinite.mp x.2
  have hS : S.Finite := by
    exact J.finite_toSet.union hTcomp
  have hU : ∀ i, IsOpen (U i) := by
    intro i
    by_cases hiJ : i ∈ J
    · by_cases hiT : i ∈ T
      · simpa [U, hiJ, hiT] using (hq i hiJ).1.inter (hA i)
      · simpa [U, hiJ, hiT] using (hq i hiJ).1
    · simp [U, hiJ]
  have hxB : x ∈ chapter05RestrictedProductBasicOpen R A S U := by
    constructor
    · intro i hiS
      by_cases hiJ : i ∈ J
      · have hxu : (x' : ∀ i, R i) i ∈ q i := (hq i hiJ).2
        have hxcoord : (x' : ∀ i, R i) i = x i := by
          simpa using congrArg (fun z : Πʳ i, [R i, A i] => z i) hxx
        rw [hxcoord] at hxu
        by_cases hiT : i ∈ T
        · simpa [U, hiJ, hiT] using And.intro hxu (show x i ∈ A i from hiT)
        · simpa [U, hiJ, hiT] using hxu
      · simp [S] at hiS
        simp [U, hiJ]
    · intro i hiS
      have hiT : i ∈ T := by
        by_contra hiT
        exact hiS (by simp [S, hiT])
      exact hiT
  refine ⟨S, hS, U, hU, hxB, ?_, ?_⟩
  · intro z hz
    have hzT : ∀ᶠ i in 𝓟 T, z i ∈ A i := by
      apply Filter.mem_principal.mpr
      intro i hiT
      by_cases hiJ : i ∈ J
      · have hzV : z i ∈ U i := hz.1 i (by simp [S, hiJ])
        have hzVA : z i ∈ q i ∩ A i := by
          simpa [U, hiJ, hiT] using hzV
        exact hzVA.2
      · exact hz.2 i (by simp [S, hiJ, hiT])
    rcases RestrictedProduct.exists_inclusion_eq_of_eventually R A hT hzT with ⟨z', hzz⟩
    have hzO : (z' : ∀ i, R i) ∈ O := by
      apply hqO
      intro i hiJ
      have hiJ' : i ∈ J := by simpa using hiJ
      have hiS : i ∈ S := Or.inl hiJ'
      have hzV : z i ∈ U i := hz.1 i hiS
      have hzq : z i ∈ q i := by
        by_cases hiT : i ∈ T
        · exact (show z i ∈ q i ∩ A i by simpa [U, hiJ', hiT] using hzV).1
        · simpa [U, hiJ', hiT] using hzV
      have hzcoord : (z' : ∀ i, R i) i = z i := by
        simpa using congrArg (fun w : Πʳ i, [R i, A i] => w i) hzz
      rw [hzcoord]
      exact hzq
    have hzpre : z' ∈ RestrictedProduct.inclusion R A hT ⁻¹' W := by
      rw [← hOeq]
      exact hzO
    apply hWV
    change RestrictedProduct.inclusion R A hT z' ∈ W at hzpre
    simpa [hzz] using hzpre
  · intro i hiS
    by_contra hiA
    apply hiS
    exact Or.inr hiA

/-! For a finite set `S` containing every canonical infinite place, the
following is the restricted product away from `S`. -/

theorem chapter05_theorem_5_6_strong_approximation_away_from_S
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04Place K)) (_hSfinite : S.Finite)
    (hSinf : chapter05InfinitePlaces K ⊆ S) :
    chapter05StrongApproximationAwayFrom K S := by
  classical
  intro T x W hW
  let f : {v // v ∉ S} → Chapter04FinitePlace K := fun v =>
    (chapter05_away_complement_is_finite_place K S hSinf v.1 v.2).choose
  have hf_spec : ∀ v : {v // v ∉ S}, v.1 = Sum.inl (f v) := by
    intro v
    exact (chapter05_away_complement_is_finite_place K S hSinf v.1 v.2).choose_spec
  have hf_inj : Function.Injective f := by
    intro v₁ v₂ h
    apply Subtype.ext
    rw [hf_spec v₁, hf_spec v₂, h]
  let Sfin : Finset (Chapter04FinitePlace K) :=
    T.image (fun v : {v // v ∉ S} => f v)
  have hSfin_mem (q : Chapter04FinitePlace K) (hq : q ∈ Sfin) :
      ∃ v : T, f v.1 = q := by
    rcases Finset.mem_image.mp hq with ⟨v, hv, rfl⟩
    exact ⟨⟨v, hv⟩, rfl⟩
  have hplace (q : Chapter04FinitePlace K) (hq : q ∈ Sfin) :
      Sum.inl q ∉ S := by
    rcases hSfin_mem q hq with ⟨v, hv⟩
    intro hqS
    apply v.1.2
    rw [hf_spec v.1, hv]
    exact hqS
  let pre : ∀ (q : Chapter04FinitePlace K), q ∈ Sfin → T := fun q hq =>
    Classical.choose (hSfin_mem q hq)
  have pre_spec (q : Chapter04FinitePlace K) (hq : q ∈ Sfin) :
      f (pre q hq).1 = q := by
    exact Classical.choose_spec (hSfin_mem q hq)
  have hplace_pre (q : Chapter04FinitePlace K) (hq : q ∈ Sfin) :
      (pre q hq).1.1 = Sum.inl q := by
    rw [hf_spec (pre q hq).1, pre_spec q hq]
  let xfin : ∀ (q : Chapter04FinitePlace K), q ∈ Sfin →
    Chapter04FiniteLocalField K q := fun q hq =>
    by
      change chapter04LocalField K (Sum.inl q)
      exact hplace_pre q hq ▸ x (pre q hq)
  let Wfin : ∀ (q : Chapter04FinitePlace K), q ∈ Sfin →
    Set (Chapter04FiniteLocalField K q) := fun q hq =>
    by
      change Set (chapter04LocalField K (Sum.inl q))
      exact hplace_pre q hq ▸ W (pre q hq)
  have htransport_nhds :
      ∀ (p : Chapter04Place K) (q : Chapter04FinitePlace K)
        (e : p = Sum.inl q) (Y : Set (chapter04LocalField K p)),
        Y ∈ 𝓝 (0 : chapter04LocalField K p) →
          (e ▸ Y) ∈ 𝓝 (0 : chapter04LocalField K (Sum.inl q)) := by
    intro p q e Y hY
    cases e
    exact hY
  have hWlocal (q : Chapter04FinitePlace K) (hq : q ∈ Sfin) :
      ∃ n : ℤ, ∀ z : Chapter04FiniteLocalField K q,
        chapter01LocallyClose q (xfin q hq) z n →
          z - xfin q hq ∈ Wfin q hq := by
    have hW0 : Wfin q hq ∈ 𝓝 (0 : Chapter04FiniteLocalField K q) := by
      change (hplace_pre q hq ▸ W (pre q hq)) ∈
        𝓝 (0 : chapter04LocalField K (Sum.inl q))
      exact htransport_nhds (pre q hq).1.1 q (hplace_pre q hq)
        (W (pre q hq)) (hW (pre q hq))
    have hU : {z : Chapter04FiniteLocalField K q |
        z - xfin q hq ∈ Wfin q hq} ∈ 𝓝 (xfin q hq) := by
      change (fun z : Chapter04FiniteLocalField K q =>
        z - xfin q hq) ⁻¹' Wfin q hq ∈ 𝓝 (xfin q hq)
      have hW0' : Wfin q hq ∈
          𝓝 ((fun z : Chapter04FiniteLocalField K q => z - xfin q hq)
            (xfin q hq)) := by
        simpa only [sub_self] using hW0
      exact (continuousAt_id.sub continuousAt_const).preimage_mem_nhds hW0'
    rcases Valued.mem_nhds.mp hU with ⟨γ, hγ⟩
    let γ' := MonoidWithZeroHom.ValueGroup₀.embedding γ.1
    refine ⟨-(WithZero.log γ' - 1), ?_⟩
    intro z hz
    apply hγ
    change Valued.v.restrict (z - xfin q hq) < γ.1
    rw [Valued.v.restrict_lt_iff_lt_embedding]
    have hz' : Valued.v (xfin q hq - z) ≤
        WithZero.exp (-(-(WithZero.log γ' - 1))) := by
      change Valued.v (xfin q hq - z) ≤
        WithZero.exp (-(-(WithZero.log γ' - 1))) at hz
      exact hz
    rw [Valuation.map_sub_swap] at hz'
    have hγ'ne : γ' ≠ 0 := by
      exact MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ
    change Valued.v (z - xfin q hq) < γ'
    rw [← WithZero.exp_log hγ'ne]
    apply lt_of_le_of_lt hz'
    rw [WithZero.exp_lt_exp]
    omega
  let m : ∀ q : Chapter04FinitePlace K, q ∈ Sfin → ℤ := fun q hq =>
    Classical.choose (hWlocal q hq)
  have hm (q : Chapter04FinitePlace K) (hq : q ∈ Sfin) :
      ∀ z : Chapter04FiniteLocalField K q,
        chapter01LocallyClose q (xfin q hq) z (m q hq) →
          z - xfin q hq ∈ Wfin q hq := by
    exact Classical.choose_spec (hWlocal q hq)
  obtain ⟨a, haS, haout⟩ :=
    chapter05_finite_approximation_hits_congruences K Sfin xfin m
  have htransport_away :
      ∀ (p : Chapter04Place K) (q : Chapter04FinitePlace K)
        (e : p = Sum.inl q) (X : chapter04LocalField K p)
        (Y : Set (chapter04LocalField K p)),
        chapter05LocalEmbedding K (Sum.inl q) a - (e ▸ X) ∈ (e ▸ Y) →
          chapter05LocalEmbedding K p a - X ∈ Y := by
    intro p q e X Y hz
    cases e
    exact hz
  refine ⟨a, ?_⟩
  constructor
  · intro v
    let q : Chapter04FinitePlace K := f v.1
    have hq : q ∈ Sfin := by
      exact Finset.mem_image.mpr ⟨v.1, v.2, rfl⟩
    have hpre : pre q hq = v := by
      apply Subtype.ext
      apply hf_inj
      simpa [q] using pre_spec q hq
    have hz := hm q hq (chapter05FiniteDiagonal K a q) (haS q hq)
    change chapter05LocalEmbedding K (Sum.inl q) a -
        (hplace_pre q hq ▸ x (pre q hq)) ∈
      (hplace_pre q hq ▸ W (pre q hq)) at hz
    have hres := htransport_away (pre q hq).1.1 q (hplace_pre q hq)
      (x (pre q hq)) (W (pre q hq)) hz
    rw [hpre] at hres
    exact hres
  · intro v hvT
    let q : Chapter04FinitePlace K := f v
    have hq : q ∉ Sfin := by
      intro hq
      rcases hSfin_mem q hq with ⟨u, hu⟩
      apply hvT
      apply Finset.mem_coe.mpr
      have huv : u.1 = v := by
        apply hf_inj
        simpa [q] using hu
      simpa [huv] using u.2
    have horder := haout q hq
    have hvplace : v.1 = Sum.inl q := hf_spec v
    rw [hvplace]
    change (a : q.adicCompletion K) ∈ q.adicCompletionIntegers K
    apply (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
      (NumberField.RingOfIntegers K) K q).2
    rw [chapter01_completion_valuation_agrees_with_global]
    by_cases ha0 : a = 0
    · simp [ha0]
    · have hval : q.valuation K a = WithZero.exp (-(chapter01Order q a)) := by
        simpa [chapter01Order,
          LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent] using
          (LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent_valuation
            q ha0)
      rw [hval, ← WithZero.exp_zero, WithZero.exp_le_exp]
      exact neg_nonpos.mpr horder

theorem chapter05_strong_approximation_away_neighborhood_form
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04Place K))
    (hstrong : chapter05StrongApproximationAwayFrom K S) :
    ∀ (T : Finset {v // v ∉ S})
      (x : ∀ v : T, chapter04LocalField K v.1)
      (W : ∀ v : T, Set (chapter04LocalField K v.1)),
      (∀ v : T, W v ∈ 𝓝 (0 : chapter04LocalField K v.1)) →
        ∃ a : K,
          (∀ v : T,
            chapter05LocalEmbedding K v.1 a - x v ∈ W v) ∧
          (∀ v : {v // v ∉ S}, v ∉ (T : Set {v // v ∉ S}) →
            chapter05LocalEmbedding K v.1 a ∈
              (chapter04LocalIntegralSubring K v.1 :
                Set (chapter04LocalField K v.1))) := by
  intro T x W hW
  exact hstrong T x W hW

private theorem chapter05_away_restricted_product_basis_with_integral_tail
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04Place K)) :
    ∀ (x : Chapter05AdeleAwayFrom K S)
      (U : Set (Chapter05AdeleAwayFrom K S)), U ∈ 𝓝 x →
      ∃ T : Finset {v // v ∉ S},
        ∃ W : ∀ v : T, Set (chapter04LocalField K v.1),
          (∀ v : T, W v ∈ 𝓝 (0 : chapter04LocalField K v.1)) ∧
            chapter05AwayBasicNeighborhood K S x T W ⊆ U ∧
              ∀ v : {v // v ∉ S}, v ∉ (T : Set {v // v ∉ S}) →
                x v ∈ (chapter04LocalIntegralSubring K v.1 :
                  Set (chapter04LocalField K v.1)) := by
  classical
  intro x U hU
  have hAopen : ∀ v : {v // v ∉ S},
      IsOpen (chapter04LocalIntegralSubring K v.1 :
        Set (chapter04LocalField K v.1)) := by
    intro v
    rcases v with ⟨v, hv⟩
    cases v with
    | inl w =>
        change IsOpen (w.adicCompletionIntegers K : Set (w.adicCompletion K))
        exact Valued.isOpen_valuationSubring _
    | inr w =>
        simp [chapter04LocalIntegralSubring]
  rcases chapter05_restrictedProduct_basicOpen_basis
      (fun v : {v // v ∉ S} => chapter04LocalField K v.1)
      (fun v : {v // v ∉ S} =>
        (chapter04LocalIntegralSubring K v.1 :
          Set (chapter04LocalField K v.1)))
      hAopen x U hU with
    ⟨E, hE, V, hVopen, hVx, hVsub, hxtail⟩
  let T : Finset {v // v ∉ S} := hE.toFinset
  let W : ∀ v : T, Set (chapter04LocalField K v.1) := fun v =>
    {z | z + x v.1 ∈ V v.1}
  let hlocal : ∀ v : {v // v ∉ S}, IsTopologicalRing (chapter04LocalField K v.1) := by
    intro v
    cases h : v.1 with
    | inl w =>
        change IsTopologicalRing (Chapter04FiniteLocalField K w)
        infer_instance
    | inr w =>
        change IsTopologicalRing w.Completion
        infer_instance
  refine ⟨T, W, ?_, ?_, ?_⟩
  · intro v
    have hvE : v.1 ∈ E := by
      apply hE.mem_toFinset.mp
      exact v.2
    have hWopen : IsOpen (W v) := by
      change IsOpen {z | z + x v.1 ∈ V v.1}
      exact (hVopen v.1).preimage (continuous_id.add continuous_const)
    apply hWopen.mem_nhds
    change 0 + x v.1 ∈ V v.1
    simp only [zero_add]
    exact hVx.1 v.1 hvE
  · intro y hy
    rw [chapter05_mem_awayBasicNeighborhood_iff] at hy
    have hzB :
        y ∈ chapter05RestrictedProductBasicOpen
          (fun v : {v // v ∉ S} => chapter04LocalField K v.1)
          (fun v : {v // v ∉ S} =>
            (chapter04LocalIntegralSubring K v.1 :
              Set (chapter04LocalField K v.1))) E V := by
      constructor
      · intro v hvE
        have hvTmem : v ∈ T := by
          simpa [T] using hE.mem_toFinset.mpr hvE
        have hvW := hy.1 ⟨v, hvTmem⟩
        change y v - x v ∈ {z | z + x v ∈ V v} at hvW
        change y v ∈ V v
        change (y v - x v) + x v ∈ V v at hvW
        simpa [sub_add_cancel] using hvW
      · intro v hvE
        have hvT : v ∉ (T : Set {v // v ∉ S}) := by
          intro hvT
          apply hvE
          apply hE.mem_toFinset.mp
          simpa [T] using hvT
        have hvTail := hy.2 v hvT
        have hxTail := hxtail v hvE
        simpa [sub_add_cancel] using
          (chapter04LocalIntegralSubring K v.1).add_mem hvTail hxTail
    exact hVsub hzB
  · intro v hvT
    apply hxtail v
    intro hvE
    apply hvT
    simpa [T] using hE.mem_toFinset.mpr hvE

theorem chapter05_away_restricted_product_has_canonical_basis
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04Place K)) :
    chapter05RestrictedProductBasis K S := by
  intro x U hU
  rcases chapter05_away_restricted_product_basis_with_integral_tail K S x U hU with
    ⟨T, W, hW, hsub, _⟩
  exact ⟨T, W, hW, hsub⟩

theorem chapter05_away_diagonal_dense
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04Place K)) (_hSfinite : S.Finite)
    (hSinf : chapter05InfinitePlaces K ⊆ S)
    (hstrong : chapter05StrongApproximationAwayFrom K S) :
    DenseRange (chapter05AwayDiagonal K S hSinf) := by
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_forall
  intro x
  rw [mem_closure_iff_nhds]
  intro U hU
  rcases chapter05_away_restricted_product_basis_with_integral_tail K S x U hU with
    ⟨T, W, hW, hsub, hxtail⟩
  obtain ⟨a, haT, haTail⟩ :=
    hstrong T (fun v : T => x v.1) W hW
  refine ⟨chapter05AwayDiagonal K S hSinf a, ?_⟩
  constructor
  · apply hsub
    rw [chapter05_mem_awayBasicNeighborhood_iff]
    change
      (∀ v : T, chapter05LocalEmbedding K v.1 a - x v.1 ∈ W v) ∧
        (∀ v : {v // v ∉ S}, v ∉ (T : Set {v // v ∉ S}) →
          chapter05LocalEmbedding K v.1 a - x v ∈
            (chapter04LocalIntegralSubring K v.1 :
              Set (chapter04LocalField K v.1)))
    constructor
    · exact haT
    · intro v hvT
      exact (chapter04LocalIntegralSubring K v.1).sub_mem
        (haTail v hvT) (hxtail v hvT)
  · exact ⟨a, rfl⟩

theorem chapter05_away_diagonal_closure_eq_univ
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04Place K)) (hSfinite : S.Finite)
    (hSinf : chapter05InfinitePlaces K ⊆ S)
    (hstrong : chapter05StrongApproximationAwayFrom K S) :
    closure (Set.range (chapter05AwayDiagonal K S hSinf)) =
      (Set.univ : Set (Chapter05AdeleAwayFrom K S)) := by
  rw [← denseRange_iff_closure_range]
  exact chapter05_away_diagonal_dense K S hSfinite hSinf hstrong

/-! The finite-to-away map is coordinate restriction on the canonical carrier;
the impossible infinite branch is retained only to make the dependent product
function total. -/

theorem chapter05_finite_to_away_projection_coordinate
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04Place K))
    (hfinite : ∀ v, v ∉ S → ∃ w : Chapter04FinitePlace K,
      v = Sum.inl w)
    (x : Chapter04FiniteAdeleRing K)
    (v : {v // v ∉ S}) :
    chapter05FiniteToAwayProjection K S hfinite x v =
      match _h : v.1 with
      | Sum.inl w => x w
      | Sum.inr _ => 0 := by
  change chapter05FiniteCoordinate K x v.1 = _
  cases v.1 with
  | inl w =>
      simp [chapter05FiniteCoordinate]
      exact rfl
  | inr w => simp [chapter05FiniteCoordinate]

theorem chapter05_finite_to_away_projection_surjective
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04Place K))
    (hfinite : ∀ v, v ∉ S → ∃ w : Chapter04FinitePlace K,
      v = Sum.inl w) :
    Function.Surjective (chapter05FiniteToAwayProjection K S hfinite) := by
  sorry

theorem chapter05_finite_to_away_projection_diagonal
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04Place K))
    (hSinf : chapter05InfinitePlaces K ⊆ S)
    (hfinite : ∀ v, v ∉ S → ∃ w : Chapter04FinitePlace K,
      v = Sum.inl w) (a : K) :
    chapter05FiniteToAwayProjection K S hfinite (chapter05FiniteDiagonal K a) =
      chapter05AwayDiagonal K S hSinf a := by
  sorry

/-! With no places omitted, the canonical full-adele diagonal is discrete and
therefore cannot be dense in a nondiscrete full adele group. -/

theorem chapter05_full_adele_diagonal_not_dense
    (K : Type*) [Field K] [NumberField K] :
    ¬ DenseRange (chapter05Diagonal K) := by
  sorry

theorem chapter05_strong_approximation_with_no_omitted_places_is_false
    (K : Type*) [Field K] [NumberField K] :
    ¬ DenseRange (chapter05Diagonal K) := by
  sorry

end

end LastLib.Book04AdelesAndIdeles.Chapter05
