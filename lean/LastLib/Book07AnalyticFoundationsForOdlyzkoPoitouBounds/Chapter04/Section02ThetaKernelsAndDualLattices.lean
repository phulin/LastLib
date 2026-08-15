import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04

noncomputable section

open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter02

open MeasureTheory NumberField NumberField.InfinitePlace
open scoped BigOperators ComplexConjugate NumberField nonZeroDivisors Classical

/-! ### 4.2. Theta kernels and dual lattices -/

theorem chapter04_self_dual_covolume_pos
    (K : Type*) [Field K] [NumberField K]
    (a : Chapter04NonzeroFractionalIdeal K) :
    0 < chapter04SelfDualCovolume K (a : Chapter04FractionalIdeal K) := by
  have hnorm := chapter04_fractional_ideal_norm_eq_chapter02 K a
  rw [chapter04SelfDualCovolume, hnorm]
  exact mul_pos (Real.sqrt_pos.2 (chapter04_absolute_discriminant_pos K))
    (chapter02_fractional_ideal_norm_pos K a)

theorem chapter04_ordinary_covolume_unchanged
    (K : Type*) [Field K] [NumberField K]
    (a : Chapter04NonzeroFractionalIdeal K) :
    ZLattice.covolume (E := chapter04MinkowskiSpace K)
      (chapter02FractionalIdealLattice K a) =
      chapter04FractionalIdealNorm K (a : Chapter04FractionalIdeal K) *
        (2 : ℝ)⁻¹ ^ chapter04ComplexPlaces K *
          Real.sqrt (chapter04AbsoluteDiscriminant K) := by
  exact chapter02_fractional_ideal_lattice_covolume K a

theorem chapter04_self_dual_covolume_eq_rescaled_ordinary
    (K : Type*) [Field K] [NumberField K]
    (a : Chapter04NonzeroFractionalIdeal K) :
    chapter04SelfDualCovolume K (a : Chapter04FractionalIdeal K) =
      (2 : ℝ) ^ chapter04ComplexPlaces K *
          ZLattice.covolume (E := chapter04MinkowskiSpace K)
            (chapter02FractionalIdealLattice K a) := by
  have hnorm := chapter04_fractional_ideal_norm_eq_chapter02 K a
  rw [chapter04SelfDualCovolume, hnorm,
    chapter02_fractional_ideal_lattice_covolume K a]
  have hpow :
      (2 : ℝ) ^ chapter04ComplexPlaces K *
          (2 : ℝ)⁻¹ ^ chapter04ComplexPlaces K = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    Real.sqrt (chapter04AbsoluteDiscriminant K) *
        chapter02FractionalIdealNorm K a =
        1 * (Real.sqrt (chapter04AbsoluteDiscriminant K) *
          chapter02FractionalIdealNorm K a) := by ring
    _ = ((2 : ℝ) ^ chapter04ComplexPlaces K *
          (2 : ℝ)⁻¹ ^ chapter04ComplexPlaces K) *
        (Real.sqrt (chapter04AbsoluteDiscriminant K) *
          chapter02FractionalIdealNorm K a) := by rw [hpow]
    _ = (2 : ℝ) ^ chapter04ComplexPlaces K *
        (chapter02FractionalIdealNorm K a * (2 : ℝ)⁻¹ ^
          chapter04ComplexPlaces K * Real.sqrt (chapter04AbsoluteDiscriminant K)) := by
            ring

/- The normalization is exposed as a lattice interface because the canonical
   mixed-space ideal lattice is a submodule, while its real scalar multiple is
   most naturally presented in the source as a set. -/
theorem chapter04_normalized_ideal_lattice_covolume_one
    (K : Type*) [Field K] [NumberField K]
    (a : Chapter04NonzeroFractionalIdeal K) :
    ∃ L : Submodule ℤ (chapter04MinkowskiSpace K),
        ∃ hL : DiscreteTopology L,
        @IsZLattice ℝ _ (chapter04MinkowskiSpace K) _ _ L hL ∧
          (L : Set (chapter04MinkowskiSpace K)) =
            chapter04NormalizedIdealLattice K (a : Chapter04FractionalIdeal K) ∧
          chapter04SelfDualLatticeCovolume K L = 1 := by
  let E := chapter04MinkowskiSpace K
  let I : Submodule ℤ E := chapter02FractionalIdealLattice K a
  let c : ℝ := chapter04NormalizationFactor K (a : Chapter04FractionalIdeal K)
  have hI_disc : DiscreteTopology I := by
    dsimp [I]
    infer_instance
  have : DiscreteTopology I := hI_disc
  have : IsZLattice ℝ I := by
    dsimp [I]
    exact chapter02_fractional_ideal_lattice_isZLattice K a
  have hc : c ≠ 0 := by
    dsimp [c, chapter04NormalizationFactor]
    exact (Real.rpow_pos_of_pos (chapter04_self_dual_covolume_pos K a) _).ne'
  let f : E ≃L[ℝ] E :=
    ContinuousLinearEquiv.equivOfInverse
      (c • (ContinuousLinearMap.id ℝ E))
      (c⁻¹ • (ContinuousLinearMap.id ℝ E))
      (by intro x; simp [smul_smul, hc])
      (by intro x; simp [smul_smul, hc])
  have hf_apply (x : E) : f x = c • x := by
    simp [f, ContinuousLinearEquiv.equivOfInverse]
  have hf_map : (f : E →ₗ[ℝ] E) = c • (1 : E →ₗ[ℝ] E) := by
    apply LinearMap.ext
    intro x
    change f x = _
    rw [hf_apply]
    simp
  let L : Submodule ℤ E := ZLattice.comap ℝ I f.symm.toLinearMap
  have : DiscreteTopology L := by
    dsimp [L]
    exact ZLattice.comap_discreteTopology ℝ I
      (e := f.symm.toLinearMap) f.symm.continuous f.symm.injective
  have : IsZLattice ℝ L := by
    refine ⟨?_⟩
    simpa only [L] using
      (ZLattice.comap_span_top ℝ I IsZLattice.span_top
        (e := f.symm.toLinearMap) (by
          intro x hx
          exact ⟨f x, by simp⟩))
  have hLset : (L : Set E) = f '' (I : Set E) := by
    ext y
    constructor
    · intro hy
      change f.symm y ∈ I at hy
      exact ⟨f.symm y, hy, by simp⟩
    · rintro ⟨x, hx, rfl⟩
      change f.symm (f x) ∈ I
      simpa using hx
  have hnormalized : (L : Set E) =
      chapter04NormalizedIdealLattice K (a : Chapter04FractionalIdeal K) := by
    rw [hLset, chapter04NormalizedIdealLattice,
      chapter04_fractional_ideal_image_eq_canonical K a]
    congr 1
  let bI := Module.Free.chooseBasis ℤ I
  let FI := ZSpan.fundamentalDomain (bI.ofZLatticeBasis ℝ I)
  have hFI : IsAddFundamentalDomain I FI volume := by
    exact ZLattice.isAddFundamentalDomain bI volume
  let q : I ≃ₗ[ℤ] L := ZLattice.comap_equiv ℝ I f.symm.toLinearEquiv
  let e : L ≃+ I := q.symm.toAddEquiv
  have hqmp : Measure.QuasiMeasurePreserving (f.symm : E → E) volume volume := by
    simpa using
      (Measure.ContinuousLinearMap.quasiMeasurePreserving
        (volume : Measure E) (f.symm : E →L[ℝ] E)
        (LinearEquiv.isUnit_det' f.symm.toLinearEquiv).ne_zero)
  have hsemiconj : ∀ g : L,
      Function.Semiconj f.toEquiv (e.toEquiv g + ·) (g + ·) := by
    intro g x
    change f ((e.toEquiv g : E) + x) = (g : E) + f x
    rw [map_add]
    congr 1
    change f (q.symm g : E) = (g : E)
    have hq := ZLattice.comap_equiv_apply ℝ I f.symm.toLinearEquiv (q.symm g)
    rw [q.apply_symm_apply] at hq
    simpa [q] using hq.symm
  have hFL : IsAddFundamentalDomain L (f '' FI) volume := by
    refine hFI.image_of_equiv f.toEquiv ?_ ?_ ?_
    · simpa using hqmp
    · exact e.toEquiv
    · exact hsemiconj
  have hcovL : ZLattice.covolume L = volume.real (f '' FI) :=
    ZLattice.covolume_eq_measure_fundamentalDomain L volume hFL
  have hcovI : ZLattice.covolume I =
      chapter04FractionalIdealNorm K (a : Chapter04FractionalIdeal K) *
        (2 : ℝ)⁻¹ ^ chapter04ComplexPlaces K *
          Real.sqrt (chapter04AbsoluteDiscriminant K) := by
    simpa [I] using chapter04_ordinary_covolume_unchanged K a
  have hvolume : volume.real (f '' FI) =
      |LinearMap.det (f : E →ₗ[ℝ] E)| * volume.real FI := by
    simp [Measure.real, ENNReal.toReal_mul]
  have hcovFI : volume.real FI = ZLattice.covolume I := by
    symm
    exact ZLattice.covolume_eq_measure_fundamentalDomain I volume hFI
  have hcovL' : ZLattice.covolume L =
      |LinearMap.det (f : E →ₗ[ℝ] E)| * ZLattice.covolume I := by
    rw [hcovL, hvolume, hcovFI]
  have hcpos : 0 < c := by
    dsimp [c, chapter04NormalizationFactor]
    exact Real.rpow_pos_of_pos (chapter04_self_dual_covolume_pos K a) _
  have hdet : LinearMap.det (f : E →ₗ[ℝ] E) =
      c ^ Module.finrank ℝ E := by
    rw [hf_map, LinearMap.det_smul]
    simp
  have hdet_abs : |LinearMap.det (f : E →ₗ[ℝ] E)| =
      c ^ chapter04Degree K := by
    rw [hdet, chapter02_minkowski_space_finrank K, abs_of_pos]
    exact pow_pos hcpos _
  have hcpow : c ^ chapter04Degree K =
      (chapter04SelfDualCovolume K (a : Chapter04FractionalIdeal K))⁻¹ := by
    dsimp [c, chapter04NormalizationFactor]
    have hD : 0 < chapter04SelfDualCovolume K
        (a : Chapter04FractionalIdeal K) := chapter04_self_dual_covolume_pos K a
    have hn : (chapter04Degree K : ℝ) ≠ 0 := by
      have hdegree : 0 < chapter04Degree K := by exact Module.finrank_pos
      exact_mod_cast (Nat.ne_of_gt hdegree)
    rw [← Real.rpow_mul_natCast hD.le]
    rw [show (-(1 / (chapter04Degree K : ℝ))) * chapter04Degree K =
      (-1 : ℝ) by field_simp]
    exact Real.rpow_neg_one _
  refine ⟨L, inferInstance, ⟨inferInstance, hnormalized, ?_⟩⟩
  rw [chapter04SelfDualLatticeCovolume, hcovL', hdet_abs, hcpow]
  calc
    (2 : ℝ) ^ chapter04ComplexPlaces K *
        ((chapter04SelfDualCovolume K (a : Chapter04FractionalIdeal K))⁻¹ *
          ZLattice.covolume I) =
      (chapter04SelfDualCovolume K (a : Chapter04FractionalIdeal K))⁻¹ *
        ((2 : ℝ) ^ chapter04ComplexPlaces K * ZLattice.covolume I) := by ring
    _ = 1 := by
      rw [← chapter04_self_dual_covolume_eq_rescaled_ordinary K a]
      exact inv_mul_cancel₀ (ne_of_gt (chapter04_self_dual_covolume_pos K a))

theorem chapter04_normalized_lattice_dual_eq_coordinate_conjugate_dual_ideal
    (K : Type*) [Field K] [NumberField K]
    (a : Chapter04NonzeroFractionalIdeal K) :
    chapter04LatticeDual K
        (chapter04NormalizedIdealLattice K (a : Chapter04FractionalIdeal K)) =
      chapter04CoordinateConjugation K ''
        chapter04NormalizedIdealLattice K
          (chapter04DualFractionalIdeal K (a : Chapter04FractionalIdeal K)) := by
  classical
  have htrace (x y : K) :
      (Algebra.trace ℚ K (x * y) : ℝ) =
        chapter04TracePairing K (NumberField.mixedEmbedding K x)
          (chapter04CoordinateConjugation K (NumberField.mixedEmbedding K y)) := by
    have hcomplex :
        algebraMap ℚ ℂ (Algebra.trace ℚ K (x * y)) =
          ∑ σ : K →ₐ[ℚ] ℂ, σ (x * y) :=
      trace_eq_sum_embeddings (E := ℂ)
    rw [← Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ)
      (fun σ : K →+* ℂ => σ (x * y))
      (fun σ : K →ₐ[ℚ] ℂ => σ (x * y)) (fun _ => rfl)] at hcomplex
    rw [← Fintype.sum_equiv (NumberField.mixedEmbedding.indexEquiv K)
      (fun c : NumberField.mixedEmbedding.index K =>
        (NumberField.mixedEmbedding.indexEquiv K c) (x * y))
      (fun σ : K →+* ℂ => σ (x * y)) (fun _ => rfl)] at hcomplex
    have hreal := congrArg Complex.re hcomplex
    have hreal_re (w : {w : InfinitePlace K // IsReal w}) (z : K) :
        (w.val.embedding z).re = embedding_of_isReal w.prop z := by
      exact congrArg Complex.re (embedding_of_isReal_apply w.prop z) |>.symm
    have hreal_im (w : {w : InfinitePlace K // IsReal w}) (z : K) :
        (w.val.embedding z).im = 0 := by
      have hz : ((embedding_of_isReal w.prop z : ℂ)) = w.val.embedding z :=
        embedding_of_isReal_apply w.prop z
      rw [← hz]
      rfl
    convert hreal using 1 <;>
      simp [chapter04TracePairing, chapter04CoordinateConjugation,
        Complex.mul_re, Fintype.sum_sum_type, Fintype.sum_prod_type,
        Fin.sum_univ_two,
        NumberField.mixedEmbedding.indexEquiv_apply_isReal,
        NumberField.mixedEmbedding.indexEquiv_apply_isComplex_fst,
        NumberField.mixedEmbedding.indexEquiv_apply_isComplex_snd,
        hreal_re, hreal_im, Finset.sum_sub_distrib] ;
      try rw [Finset.sum_sub_distrib]
    all_goals
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      ring
  have hdualideal :
      chapter04DualFractionalIdeal K (a : Chapter04FractionalIdeal K) =
        FractionalIdeal.dual ℤ ℚ (a : Chapter04FractionalIdeal K) := by
    unfold chapter04DualFractionalIdeal chapter04DifferentFractionalIdeal
    rw [FractionalIdeal.dual_eq_mul_inv]
    congr 1
    rw [coeIdeal_differentIdeal (K := ℚ) (L := K)]
    simp
  have hfactor :
      chapter04NormalizationFactor K
          (chapter04DualFractionalIdeal K (a : Chapter04FractionalIdeal K)) =
        (chapter04NormalizationFactor K (a : Chapter04FractionalIdeal K))⁻¹ := by
    unfold chapter04NormalizationFactor
    rw [chapter04_self_dual_covolume_dual K (a := (a : Chapter04FractionalIdeal K))
      (Units.ne_zero a)]
    exact Real.inv_rpow (chapter04_self_dual_covolume_pos K a).le _
  have hpair_add_left (x₁ x₂ y : chapter04MinkowskiSpace K) :
      chapter04TracePairing K (x₁ + x₂) y =
        chapter04TracePairing K x₁ y + chapter04TracePairing K x₂ y := by
    simp [chapter04TracePairing, Finset.sum_add_distrib, Complex.mul_re]
    simp_rw [add_mul, Finset.sum_add_distrib]
    ring
  have hpair_smul_left (c : ℝ) (x y : chapter04MinkowskiSpace K) :
      chapter04TracePairing K (c • x) y =
        c * chapter04TracePairing K x y := by
    simp [chapter04TracePairing, Complex.mul_re]
    simp only [mul_assoc]
    simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  have hpair_symm (x y : chapter04MinkowskiSpace K) :
      chapter04TracePairing K x y = chapter04TracePairing K y x := by
    simp [chapter04TracePairing, Complex.mul_re, mul_comm]
  have hpair_add_right (x y₁ y₂ : chapter04MinkowskiSpace K) :
      chapter04TracePairing K x (y₁ + y₂) =
        chapter04TracePairing K x y₁ + chapter04TracePairing K x y₂ := by
    calc
      chapter04TracePairing K x (y₁ + y₂) =
          chapter04TracePairing K (y₁ + y₂) x := hpair_symm _ _
      _ = chapter04TracePairing K y₁ x + chapter04TracePairing K y₂ x :=
        hpair_add_left _ _ _
      _ = chapter04TracePairing K x y₁ + chapter04TracePairing K x y₂ := by
        rw [hpair_symm y₁ x, hpair_symm y₂ x]
  have hpair_smul_right (c : ℝ) (x y : chapter04MinkowskiSpace K) :
      chapter04TracePairing K x (c • y) =
        c * chapter04TracePairing K x y := by
    calc
      chapter04TracePairing K x (c • y) =
          chapter04TracePairing K (c • y) x := hpair_symm _ _
      _ = c * chapter04TracePairing K y x := hpair_smul_left _ _ _
      _ = c * chapter04TracePairing K x y := by rw [hpair_symm]
  let B : LinearMap.BilinForm ℝ (chapter04MinkowskiSpace K) :=
    LinearMap.mk₂ ℝ
      (chapter04TracePairing K) hpair_add_left hpair_smul_left
        hpair_add_right hpair_smul_right
  have hB : B.Nondegenerate := by
    constructor
    · intro x hx
      apply (chapter04_trace_pairing_self_eq_zero_iff K x).mp
      simpa [B] using hx x
    · intro y hy
      apply (chapter04_trace_pairing_self_eq_zero_iff K y).mp
      simpa [B] using hy y
  let bK := NumberField.basisOfFractionalIdeal K a
  let bE := NumberField.mixedEmbedding.fractionalIdealLatticeBasis K a
  have hspan :
      Submodule.span ℤ (Set.range bE) =
        chapter02FractionalIdealLattice K a := by
    simpa [bE, chapter02FractionalIdealLattice] using
      (NumberField.mixedEmbedding.span_idealLatticeBasis K a)
  have hdualbasis (i : Module.Free.ChooseBasisIndex ℤ a) :
      B.dualBasis hB bE i =
        chapter04CoordinateConjugation K
          (NumberField.mixedEmbedding K (bK.traceDual i)) := by
    have hmap :
        B (B.dualBasis hB bE i) =
          B (chapter04CoordinateConjugation K
            (NumberField.mixedEmbedding K (bK.traceDual i))) := by
      apply bE.ext
      intro j
      calc
        B (B.dualBasis hB bE i) (bE j) = (if j = i then 1 else 0) :=
          LinearMap.BilinForm.apply_dualBasis_left hB bE i j
        _ = B (chapter04CoordinateConjugation K
            (NumberField.mixedEmbedding K (bK.traceDual i))) (bE j) := by
          symm
          calc
            B (chapter04CoordinateConjugation K
                (NumberField.mixedEmbedding K (bK.traceDual i))) (bE j) =
                chapter04TracePairing K
                  (chapter04CoordinateConjugation K
                    (NumberField.mixedEmbedding K (bK.traceDual i)))
                  (NumberField.mixedEmbedding K (bK j)) := by
                    simp [B, bE, bK]
            _ = chapter04TracePairing K
                  (NumberField.mixedEmbedding K (bK j))
                  (chapter04CoordinateConjugation K
                    (NumberField.mixedEmbedding K (bK.traceDual i))) :=
              hpair_symm _ _
            _ = (Algebra.trace ℚ K (bK j * bK.traceDual i) : ℝ) :=
              (htrace (bK j) (bK.traceDual i)).symm
            _ = (if j = i then 1 else 0) := by
              rw [bK.trace_mul_traceDual]
              split_ifs <;> norm_num
    apply sub_eq_zero.mp
    apply (hB.1 (B.dualBasis hB bE i -
      chapter04CoordinateConjugation K
        (NumberField.mixedEmbedding K (bK.traceDual i))))
    intro z
    rw [map_sub, hmap]
    simp
  have hIspan :
      ((a : Chapter04FractionalIdeal K) : Submodule (𝓞 K) K).restrictScalars ℤ =
        Submodule.span ℤ (Set.range bK) := by
    ext z
    simp [bK, NumberField.mem_span_basisOfFractionalIdeal]
  have hdual_span :
      ((FractionalIdeal.dual ℤ ℚ (a : Chapter04FractionalIdeal K)) :
        Submodule (𝓞 K) K).restrictScalars ℤ =
        Submodule.span ℤ (Set.range bK.traceDual) := by
    rw [FractionalIdeal.coe_dual (A := ℤ) (K := ℚ) (B := 𝓞 K) (L := K)
      (I := (a : Chapter04FractionalIdeal K)) (Units.ne_zero a)]
    exact Submodule.traceDual_span_of_basis ℤ
      ((a : Chapter04FractionalIdeal K) : Submodule (𝓞 K) K) bK hIspan
  let C : chapter04MinkowskiSpace K →ₗ[ℝ] chapter04MinkowskiSpace K :=
    { toFun := chapter04CoordinateConjugation K
      map_add' := by
        intro x₁ x₂
        ext <;> simp [chapter04CoordinateConjugation]
      map_smul' := by
        intro c x
        ext <;> simp [chapter04CoordinateConjugation, Complex.real_smul] }
  let g : K →ₗ[ℤ] chapter04MinkowskiSpace K :=
    (C.restrictScalars ℤ).comp
      ((NumberField.mixedEmbedding K).toIntAlgHom.toLinearMap)
  have hBdual :
      B.dualSubmodule (Submodule.span ℤ (Set.range bE)) =
        Submodule.span ℤ (Set.range (fun i =>
          C (NumberField.mixedEmbedding K (bK.traceDual i)))) := by
    rw [B.dualSubmodule_span_of_basis hB bE]
    congr 1
    ext z
    simp [hdualbasis, C]
  have hgdual :
      Submodule.map g
          (((FractionalIdeal.dual ℤ ℚ (a : Chapter04FractionalIdeal K)) :
            Submodule (𝓞 K) K).restrictScalars ℤ) =
        Submodule.span ℤ (Set.range (fun i => g (bK.traceDual i))) := by
    rw [hdual_span, Submodule.map_span]
    congr 1
    ext z
    simp
  have hraw :
      (B.dualSubmodule (Submodule.span ℤ (Set.range bE)) :
        Set (chapter04MinkowskiSpace K)) =
        chapter04CoordinateConjugation K ''
          chapter04FractionalIdealImage K
            (FractionalIdeal.dual ℤ ℚ (a : Chapter04FractionalIdeal K)) := by
    have hspan_map :
        Submodule.span ℤ (Set.range (fun i =>
          C (NumberField.mixedEmbedding K (bK.traceDual i)))) =
          Submodule.map g
            (((FractionalIdeal.dual ℤ ℚ (a : Chapter04FractionalIdeal K)) :
              Submodule (𝓞 K) K).restrictScalars ℤ) := by
      simpa [g, C] using hgdual.symm
    rw [hBdual, hspan_map]
    ext z
    simp [g, C, chapter04FractionalIdealImage]
  have hBmem (z : chapter04MinkowskiSpace K) :
      z ∈ (B.dualSubmodule (Submodule.span ℤ (Set.range bE)) :
        Set (chapter04MinkowskiSpace K)) ↔
        ∀ x ∈ Submodule.span ℤ (Set.range bE),
          ∃ m : ℤ, chapter04TracePairing K x z = (m : ℝ) := by
    constructor
    · intro hz x hx
      have hz' : B z x ∈ (1 : Submodule ℤ ℝ) := hz x hx
      rcases Submodule.mem_one.mp hz' with ⟨m, hm⟩
      refine ⟨m, ?_⟩
      calc
        chapter04TracePairing K x z = B z x := by
          exact hpair_symm _ _
        _ = (m : ℝ) := hm.symm
    · intro hz x hx
      apply Submodule.mem_one.mpr
      rcases hz x hx with ⟨m, hm⟩
      refine ⟨m, ?_⟩
      calc
        (m : ℝ) = chapter04TracePairing K x z := hm.symm
        _ = B z x := hpair_symm _ _
  let c : ℝ := chapter04NormalizationFactor K (a : Chapter04FractionalIdeal K)
  have hcpos : 0 < c := by
    dsimp [c]
    exact Real.rpow_pos_of_pos (chapter04_self_dual_covolume_pos K a) _
  have hc : c ≠ 0 := hcpos.ne'
  have hC_smul (r : ℝ) (x : chapter04MinkowskiSpace K) :
      chapter04CoordinateConjugation K (r • x) =
        r • chapter04CoordinateConjugation K x := by
    change C (r • x) = r • C x
    exact C.map_smul r x
  have hnormset :
      chapter04NormalizedIdealLattice K (a : Chapter04FractionalIdeal K) =
        Set.image (fun x : chapter04MinkowskiSpace K => c • x)
          (Submodule.span ℤ (Set.range bE) :
            Set (chapter04MinkowskiSpace K)) := by
    rw [chapter04NormalizedIdealLattice,
      chapter04_fractional_ideal_image_eq_canonical K a, hspan]
  have hscaled :
      chapter04LatticeDual K
          (Set.image (fun x : chapter04MinkowskiSpace K => c • x)
            (Submodule.span ℤ (Set.range bE) :
              Set (chapter04MinkowskiSpace K))) =
        Set.image (fun z : chapter04MinkowskiSpace K => c⁻¹ • z)
          (B.dualSubmodule (Submodule.span ℤ (Set.range bE)) :
            Set (chapter04MinkowskiSpace K)) := by
    ext y
    constructor
    · intro hy
      have hy' := (chapter04_mem_lattice_dual_iff K _ y).mp hy
      have hcy : c • y ∈
          (B.dualSubmodule (Submodule.span ℤ (Set.range bE)) :
            Set (chapter04MinkowskiSpace K)) := by
        apply (hBmem (c • y)).mpr
        intro x hx
        rcases hy' (c • x) ⟨x, hx, rfl⟩ with ⟨m, hm⟩
        refine ⟨m, ?_⟩
        calc
          chapter04TracePairing K x (c • y) =
              c * chapter04TracePairing K x y :=
            hpair_smul_right _ _ _
          _ = chapter04TracePairing K (c • x) y := by
            rw [hpair_smul_left]
          _ = (m : ℝ) := hm
      refine ⟨c • y, hcy, ?_⟩
      simp [smul_smul, hc]
    · rintro ⟨z, hz, rfl⟩
      apply (chapter04_mem_lattice_dual_iff K _ (c⁻¹ • z)).mpr
      intro x hx
      rcases hx with ⟨u, hu, rfl⟩
      rcases (hBmem z).mp hz u hu with ⟨m, hm⟩
      refine ⟨m, ?_⟩
      calc
        chapter04TracePairing K (c • u) (c⁻¹ • z) =
            c⁻¹ * chapter04TracePairing K (c • u) z :=
          hpair_smul_right _ _ _
        _ = c⁻¹ * (c * chapter04TracePairing K u z) := by
          rw [hpair_smul_left]
        _ = (m : ℝ) := by
          rw [hm]
          field_simp
  have hdualnormset :
      chapter04CoordinateConjugation K ''
          chapter04NormalizedIdealLattice K
            (chapter04DualFractionalIdeal K (a : Chapter04FractionalIdeal K)) =
        Set.image (fun z : chapter04MinkowskiSpace K => c⁻¹ • z)
          (chapter04CoordinateConjugation K ''
            chapter04FractionalIdealImage K
              (FractionalIdeal.dual ℤ ℚ (a : Chapter04FractionalIdeal K))) := by
    rw [chapter04NormalizedIdealLattice, hfactor, hdualideal]
    ext z
    constructor
    · rintro ⟨x, ⟨v, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
      refine ⟨chapter04CoordinateConjugation K
          (NumberField.mixedEmbedding K y),
        ⟨NumberField.mixedEmbedding K y, ⟨y, hy, rfl⟩, rfl⟩, ?_⟩
      simpa [c] using (hC_smul _ _).symm
    · rintro ⟨x, ⟨v, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
      refine ⟨c⁻¹ • NumberField.mixedEmbedding K y,
        ⟨NumberField.mixedEmbedding K y, ⟨y, hy, rfl⟩, rfl⟩, ?_⟩
      simpa [c] using hC_smul _ _
  rw [hnormset, hscaled, hdualnormset, hraw]

theorem chapter04_orbit_ideal_class
    (K : Type*) [Field K] [NumberField K]
    (a : Chapter04NonzeroFractionalIdeal K) {x₀ : K}
    (hx₀ : x₀ ∈ (a : Set K)) (hx₀_ne : x₀ ≠ 0) :
    ∃ J : (Ideal (𝓞 K))⁰,
      ClassGroup.mk0 J = (ClassGroup.mk K a)⁻¹ ∧
        (J : Chapter04FractionalIdeal K) =
          FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀ *
            (a : Chapter04FractionalIdeal K)⁻¹ := by
  simpa using
    (chapter02_principal_mul_inverse_class K ((ClassGroup.mk K a)⁻¹) a
      (by simp) hx₀ hx₀_ne)

noncomputable def chapter04NormalizedArchimedeanProduct
    (K : Type*) [Field K] [NumberField K]
    (a : Chapter04NonzeroFractionalIdeal K) (x₀ : K) : ℝ :=
  (chapter04SelfDualCovolume K (a : Chapter04FractionalIdeal K))⁻¹ *
    |Algebra.norm ℚ x₀|

theorem chapter04_normalized_archimedean_product_formula
    (K : Type*) [Field K] [NumberField K]
    (a : Chapter04NonzeroFractionalIdeal K) (x₀ : K) :
    chapter04NormalizedArchimedeanProduct K a x₀ =
        (Real.sqrt (chapter04AbsoluteDiscriminant K))⁻¹ *
        (chapter04FractionalIdealNorm K (a : Chapter04FractionalIdeal K))⁻¹ *
          |Algebra.norm ℚ x₀| := by
  rw [chapter04NormalizedArchimedeanProduct, chapter04SelfDualCovolume]
  field_simp

noncomputable def chapter04UnitLogLinearMap
    (K : Type*) [Field K] [NumberField K] :
    chapter04UnitLogHyperplane K →ₗ[ℝ]
      NumberField.Units.dirichletUnitTheorem.logSpace K :=
  { toFun := fun x w => (w.1.mult : ℝ) * x.1 w.1
    map_add' := by
      intro x y
      funext w
      simp [mul_add]
    map_smul' := by
      intro c x
      funext w
      simp [smul_eq_mul]
      ring }

theorem chapter04_unit_log_linear_map_injective
    (K : Type*) [Field K] [NumberField K] :
    Function.Injective (chapter04UnitLogLinearMap K) := by
  let w₀ : InfinitePlace K :=
    NumberField.Units.dirichletUnitTheorem.w₀
  intro x y hxy
  apply Subtype.ext
  funext v
  by_cases hv : v = w₀
  · subst v
    have hx := x.property
    have hy := y.property
    change (∑ v : InfinitePlace K, (v.mult : ℝ) * x.1 v) = 0 at hx
    change (∑ v : InfinitePlace K, (v.mult : ℝ) * y.1 v) = 0 at hy
    rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀] at hx hy
    have hrest : ∀ w : {w : InfinitePlace K // w ≠ w₀},
        x.1 w.1 = y.1 w.1 := by
      intro w
      have hw := congrFun hxy w
      dsimp [chapter04UnitLogLinearMap] at hw
      exact mul_left_cancel₀ mult_coe_ne_zero hw
    have hsum : ∑ v : InfinitePlace K,
        (v.mult : ℝ) * (x.1 v - y.1 v) = 0 := by
      have hx' : (∑ v : InfinitePlace K, (v.mult : ℝ) * x.1 v) = 0 := by
        rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀]
        exact hx
      have hy' : (∑ v : InfinitePlace K, (v.mult : ℝ) * y.1 v) = 0 := by
        rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀]
        exact hy
      calc
        (∑ v : InfinitePlace K,
            (v.mult : ℝ) * (x.1 v - y.1 v)) =
            (∑ v : InfinitePlace K, (v.mult : ℝ) * x.1 v) -
              ∑ v : InfinitePlace K, (v.mult : ℝ) * y.1 v := by
                rw [← Finset.sum_sub_distrib]
                apply Finset.sum_congr rfl
                intro v hv
                ring
        _ = 0 := by rw [hx', hy']; simp
    rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀] at hsum
    simp only [hrest, sub_self, mul_zero, Finset.sum_const_zero, add_zero] at hsum
    have hzero : x.1 w₀ - y.1 w₀ = 0 :=
      (mul_eq_zero.mp hsum).resolve_left mult_coe_ne_zero
    exact sub_eq_zero.mp hzero
  · have hw : (v.mult : ℝ) * x.1 v = (v.mult : ℝ) * y.1 v := by
      have h := congrFun hxy ⟨v, hv⟩
      simpa [chapter04UnitLogLinearMap] using h
    exact mul_left_cancel₀ mult_coe_ne_zero hw

theorem chapter04_unit_log_linear_map_embedding
    (K : Type*) [Field K] [NumberField K]
    (u : Additive ((𝓞 K)ˣ)) :
    chapter04UnitLogLinearMap K (chapter04UnitLogEmbedding K u) =
      NumberField.Units.logEmbedding K u := by
  ext w
  rfl

theorem chapter04_theta_series_and_derivatives_locally_uniform
    (K : Type*) [Field K] [NumberField K]
    {a : Chapter04FractionalIdeal K} (ha : a ≠ 0) :
    chapter04ThetaSeriesAndDerivativeLocallyUniform K a := by
  exact chapter04_normalized_ideal_lattice_theta_series_and_derivatives_locally_uniform K ha

theorem chapter04_theta_poisson_summation
    (K : Type*) [Field K] [NumberField K]
    {a : Chapter04FractionalIdeal K} (ha : a ≠ 0)
    {t : ℝ} (ht : 0 < t) (y : chapter04Y K) :
    chapter04Theta K a t y =
        t⁻¹ * chapter04Theta K (chapter04DualFractionalIdeal K a) t⁻¹
        (chapter04YInv K y) := by
  exact chapter04_normalized_ideal_lattice_theta_poisson_summation K ha ht y

theorem chapter04_unit_log_lattice_discrete
    (K : Type*) [Field K] [NumberField K] :
    DiscreteTopology (chapter04UnitLogLattice K) := by
  let e := chapter04UnitLogLinearMap K
  have hgen (u : Additive ((𝓞 K)ˣ)) :
      e (chapter04UnitLogEmbedding K u) =
        NumberField.Units.logEmbedding K u := by
    ext w
    rfl
  have hmap :
      Submodule.map (e.restrictScalars ℤ) (chapter04UnitLogLattice K) =
        NumberField.Units.unitLattice K := by
    change Submodule.map (e.restrictScalars ℤ)
        (Submodule.span ℤ (Set.range (chapter04UnitLogEmbedding K))) =
      Submodule.map
        (NumberField.Units.logEmbedding K).toIntLinearMap ⊤
    apply le_antisymm
    · intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      change e x ∈ Submodule.map
        (NumberField.Units.logEmbedding K).toIntLinearMap ⊤
      induction hx using Submodule.span_induction with
      | mem z hz =>
          rcases hz with ⟨u, rfl⟩
          exact ⟨u, trivial, (hgen u).symm⟩
      | zero =>
          simpa only [map_zero] using
            (Submodule.zero_mem
              (Submodule.map (NumberField.Units.logEmbedding K).toIntLinearMap ⊤))
      | add z w hz hw hzp hwp =>
          simpa only [map_add] using Submodule.add_mem _ hzp hwp
      | smul c z hz hzp =>
          change (e.restrictScalars ℤ) (c • z) ∈
            Submodule.map (NumberField.Units.logEmbedding K).toIntLinearMap ⊤
          rw [map_smul]
          exact Submodule.smul_mem _ c hzp
    · intro z hz
      rcases hz with ⟨u, hu, rfl⟩
      refine ⟨chapter04UnitLogEmbedding K u,
        Submodule.subset_span ⟨u, rfl⟩, ?_⟩
      exact hgen u
  have hpre : chapter04UnitLogLattice K =
      ZLattice.comap ℝ
        (NumberField.Units.unitLattice K) e := by
    apply Submodule.ext
    intro x
    constructor
    · intro hx
      have hx' : e x ∈ Submodule.map (e.restrictScalars ℤ)
          (chapter04UnitLogLattice K) := ⟨x, hx, rfl⟩
      rw [hmap] at hx'
      exact hx'
    · intro hx
      change e x ∈ NumberField.Units.unitLattice K at hx
      rw [← hmap] at hx
      rcases hx with ⟨y, hy, hyeq⟩
      rw [← chapter04_unit_log_linear_map_injective K hyeq]
      exact hy
  rw [hpre]
  exact ZLattice.comap_discreteTopology ℝ _
    e.continuous_of_finiteDimensional (chapter04_unit_log_linear_map_injective K)

attribute [instance] chapter04_unit_log_lattice_discrete

theorem chapter04_unit_log_lattice_is_full
    (K : Type*) [Field K] [NumberField K] :
    IsZLattice ℝ (chapter04UnitLogLattice K) := by
  let e := chapter04UnitLogLinearMap K
  let T : Submodule ℝ (chapter04UnitLogHyperplane K) :=
    Submodule.span ℝ (chapter04UnitLogLattice K :
      Set (chapter04UnitLogHyperplane K))
  have hgen (u : Additive ((𝓞 K)ˣ)) :
      e (chapter04UnitLogEmbedding K u) =
        NumberField.Units.logEmbedding K u :=
    chapter04_unit_log_linear_map_embedding K u
  have hunit_span :
      Submodule.span ℝ (NumberField.Units.unitLattice K :
        Set (NumberField.Units.dirichletUnitTheorem.logSpace K)) = ⊤ :=
    (inferInstance : IsZLattice ℝ (NumberField.Units.unitLattice K)).span_top
  have hunit_le : (NumberField.Units.unitLattice K :
      Set (NumberField.Units.dirichletUnitTheorem.logSpace K)) ⊆
      (Submodule.map e T : Set (NumberField.Units.dirichletUnitTheorem.logSpace K)) := by
    intro z hz
    change z ∈ Submodule.map (NumberField.Units.logEmbedding K).toIntLinearMap ⊤ at hz
    rcases hz with ⟨u, hu, rfl⟩
    have huL : chapter04UnitLogEmbedding K u ∈ chapter04UnitLogLattice K :=
      Submodule.subset_span ⟨u, rfl⟩
    have huT : chapter04UnitLogEmbedding K u ∈ T :=
      Submodule.subset_span huL
    exact ⟨chapter04UnitLogEmbedding K u, huT, hgen u⟩
  have hmap_top : Submodule.map e T = ⊤ := by
    apply top_unique
    rw [← hunit_span]
    exact Submodule.span_le.2 hunit_le
  refine ⟨?_⟩
  apply top_unique
  intro x hx
  have hxmap : e x ∈ Submodule.map e T := by
    rw [hmap_top]
    exact Submodule.mem_top
  rcases hxmap with ⟨y, hy, hyeq⟩
  have hyx : y = x := chapter04_unit_log_linear_map_injective K hyeq
  simpa [hyx] using hy

theorem chapter04_unit_log_lattice_span_eq_top
    (K : Type*) [Field K] [NumberField K] :
    Submodule.span ℝ (chapter04UnitLogLattice K :
      Set (chapter04UnitLogHyperplane K)) = ⊤ := by
  exact (chapter04_unit_log_lattice_is_full K).span_top

private noncomputable def chapter04YLog
    (K : Type*) [Field K] [NumberField K]
    (y : chapter04Y K) : chapter04UnitLogHyperplane K :=
  { val := fun v => Real.log (y.scale v)
    property := by
      change (∑ v : InfinitePlace K, (v.mult : ℝ) * Real.log (y.scale v)) = 0
      have hprodlog :
          Real.log (∏ v : InfinitePlace K, y.scale v ^ v.mult) =
            ∑ v : InfinitePlace K, Real.log (y.scale v ^ v.mult) := by
        simpa using
          (Real.log_prod (s := Finset.univ)
            (f := fun v : InfinitePlace K => y.scale v ^ v.mult)
            (fun v hv => pow_ne_zero _ (ne_of_gt (y.positive v))))
      calc
        (∑ v : InfinitePlace K, (v.mult : ℝ) * Real.log (y.scale v)) =
            ∑ v : InfinitePlace K, Real.log (y.scale v ^ v.mult) := by
              apply Finset.sum_congr rfl
              intro v hv
              rw [Real.log_pow]
        _ = Real.log (∏ v : InfinitePlace K, y.scale v ^ v.mult) := hprodlog.symm
        _ = Real.log 1 := congrArg Real.log y.determinant_one
        _ = 0 := by simp }

private noncomputable def chapter04YExp
    (K : Type*) [Field K] [NumberField K]
    (x : chapter04UnitLogHyperplane K) : chapter04Y K :=
  { scale := fun v => Real.exp (x.1 v)
    positive := by
      intro v
      exact Real.exp_pos _
    determinant_one := by
      calc
        (∏ v : InfinitePlace K, Real.exp (x.1 v) ^ v.mult) =
            ∏ v : InfinitePlace K, Real.exp ((v.mult : ℝ) * x.1 v) := by
              apply Finset.prod_congr rfl
              intro v hv
              rw [← Real.exp_nat_mul]
        _ = Real.exp (∑ v : InfinitePlace K, (v.mult : ℝ) * x.1 v) := by
              rw [Real.exp_sum]
        _ = 1 := by rw [x.2, Real.exp_zero] }

theorem chapter04_exists_unit_fundamental_domain
    (K : Type*) [Field K] [NumberField K] :
    Nonempty (Chapter04UnitFundamentalDomain K) := by
  let L := chapter04UnitLogLattice K
  have hdiscrete : DiscreteTopology L := chapter04_unit_log_lattice_discrete K
  have hfull : IsZLattice ℝ L := chapter04_unit_log_lattice_is_full K
  let b := Module.Free.chooseBasis ℤ L
  let e := b.ofZLatticeBasis ℝ L
  let F := ZSpan.fundamentalDomain e
  let μ : Measure (chapter04UnitLogHyperplane K) := e.addHaar
  have hlog_exp (x : chapter04UnitLogHyperplane K) :
      chapter04YLog K (chapter04YExp K x) = x := by
    apply Subtype.ext
    funext v
    simp [chapter04YLog, chapter04YExp]
  have hexp_log (y : chapter04Y K) :
      chapter04YExp K (chapter04YLog K y) = y := by
    rcases y with ⟨scale, hscale, hdet⟩
    simp only [chapter04YExp, chapter04YLog]
    congr
    funext v
    simp [Real.exp_log (hscale v)]
  have hF : IsAddFundamentalDomain L F μ := by
    exact ZLattice.isAddFundamentalDomain b μ
  have hFmeas : MeasurableSet F := by
    exact ZSpan.fundamentalDomain_measurableSet e
  have hlog_meas : Measurable (chapter04YLog K) := by
    apply Measurable.subtype_mk
    apply measurable_pi_lambda
    intro v
    apply Measurable.log
    exact (continuous_apply v).borel_measurable.comp
      (comap_measurable (fun y : chapter04Y K => y.scale))
  have hexp_meas : Measurable (chapter04YExp K) := by
    rw [measurable_comap_iff]
    rw [← @BorelSpace.measurable_eq (InfinitePlace K → ℝ) _ _ _]
    change Measurable (fun x : chapter04UnitLogHyperplane K =>
      fun v => Real.exp (x.1 v))
    exact measurable_pi_lambda _ fun v =>
      Real.measurable_exp.comp ((measurable_pi_apply v).comp measurable_subtype_coe)
  have hLmeas : MeasurableSet (chapter04YLog K ⁻¹' F) := by
    exact hlog_meas hFmeas
  have hLexp : chapter04YExp K '' F = chapter04YLog K ⁻¹' F := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Set.mem_preimage]
      rw [hlog_exp]
      exact hx
    · intro hy
      refine ⟨chapter04YLog K y, ?_, ?_⟩
      · exact hy
      · exact hexp_log y
  have hμF_nezero : μ F ≠ 0 := by
    dsimp [μ]
    exact ZSpan.measure_fundamentalDomain_ne_zero e
  have hμF_ne_top : μ F ≠ ⊤ := by
    exact (Bornology.IsBounded.measure_lt_top
      (μ := μ) (ZSpan.fundamentalDomain_isBounded e)).ne
  have hpre : chapter04YExp K ⁻¹' (chapter04YLog K ⁻¹' F) = F := by
    ext x
    simp [hlog_exp]
  have hmapF : Measure.map (chapter04YExp K) μ
      (chapter04YLog K ⁻¹' F) = μ F := by
    rw [Measure.map_apply hexp_meas hLmeas, hpre]
  have hmul_meas (g : chapter04Y K) :
      Measurable (chapter04YMul K g) := by
    rw [measurable_comap_iff]
    rw [← @BorelSpace.measurable_eq (InfinitePlace K → ℝ) _ _ _]
    change Measurable (fun y : chapter04Y K =>
      fun v => g.scale v * y.scale v)
    apply measurable_pi_lambda
    intro v
    exact measurable_const.mul
      ((continuous_apply v).borel_measurable.comp
        (comap_measurable (fun y : chapter04Y K => y.scale)))
  have hinv_meas : Measurable (chapter04YInv K) := by
    rw [measurable_comap_iff]
    rw [← @BorelSpace.measurable_eq (InfinitePlace K → ℝ) _ _ _]
    change Measurable (fun y : chapter04Y K =>
      fun v => (y.scale v)⁻¹)
    apply measurable_pi_lambda
    intro v
    exact Measurable.inv
      ((continuous_apply v).borel_measurable.comp
        (comap_measurable (fun y : chapter04Y K => y.scale)))
  have hmul_left_inv (g y : chapter04Y K) :
      chapter04YMul K (chapter04YInv K g) (chapter04YMul K g y) = y := by
    rcases g with ⟨g, hg, hgd⟩
    rcases y with ⟨y, hy, hyd⟩
    simp only [chapter04YMul, chapter04YInv]
    congr 1
    funext v
    field_simp [ne_of_gt (hg v)]
  have hinv_inv (g : chapter04Y K) :
      chapter04YInv K (chapter04YInv K g) = g := by
    rcases g with ⟨g, hg, hgd⟩
    simp only [chapter04YInv]
    congr 1
    funext v
    field_simp [ne_of_gt (hg v)]
  have hmul_right_inv (g y : chapter04Y K) :
      chapter04YMul K g (chapter04YMul K (chapter04YInv K g) y) = y := by
    simpa [hinv_inv] using hmul_left_inv (chapter04YInv K g) y
  have hmul_exp (g : chapter04Y K) (x : chapter04UnitLogHyperplane K) :
      chapter04YMul K g (chapter04YExp K x) =
        chapter04YExp K (chapter04YLog K g + x) := by
    rcases g with ⟨g, hg, hgd⟩
    simp only [chapter04YMul, chapter04YExp, chapter04YLog]
    congr
    funext v
    simp [Real.exp_add, Real.exp_log (hg v)]
  have hlog_inv (g : chapter04Y K) :
      chapter04YLog K (chapter04YInv K g) = -chapter04YLog K g := by
    apply Subtype.ext
    funext v
    simp [chapter04YLog, chapter04YInv, Real.log_inv]
  have hinv_exp (g : chapter04Y K) (x : chapter04UnitLogHyperplane K) :
      chapter04YMul K (chapter04YInv K g) (chapter04YExp K x) =
        chapter04YExp K (-chapter04YLog K g + x) := by
    simpa [hlog_inv] using hmul_exp (chapter04YInv K g) x
  have hcomp (g : chapter04Y K) :
      (chapter04YMul K g) ∘ chapter04YExp K =
        chapter04YExp K ∘ (chapter04YLog K g + ·) := by
    funext x
    exact hmul_exp g x
  have hmap_mul_raw (g : chapter04Y K) :
      Measure.map (chapter04YMul K g)
          (Measure.map (chapter04YExp K) μ) =
        Measure.map (chapter04YExp K) μ := by
    rw [Measure.map_map (hmul_meas g) hexp_meas, hcomp]
    rw [← Measure.map_map hexp_meas (measurable_const_add _)]
    exact congrArg (Measure.map (chapter04YExp K))
      (Measure.IsAddLeftInvariant.map_add_left_eq_self
        (μ := μ) (chapter04YLog K g))
  have hinv_exp_zero (x : chapter04UnitLogHyperplane K) :
      chapter04YInv K (chapter04YExp K x) = chapter04YExp K (-x) := by
    simp only [chapter04YInv, chapter04YExp]
    congr
    funext v
    simp [Real.exp_neg]
  have hcomp_inv :
      chapter04YInv K ∘ chapter04YExp K =
        chapter04YExp K ∘ (-·) := by
    funext x
    exact hinv_exp_zero x
  have hmap_neg :
      Measure.map (fun x : chapter04UnitLogHyperplane K => -x) μ = μ := by
    exact Measure.map_neg_eq_self μ
  have hspan : Submodule.span ℤ (Set.range e) = L := by
    exact b.ofZLatticeBasis_span ℝ
  have hfund (x : chapter04UnitLogHyperplane K) :
      ∃! z : L, (z : chapter04UnitLogHyperplane K) + x ∈ F := by
    rcases ZSpan.exist_unique_vadd_mem_fundamentalDomain e x with
      ⟨z, hz, hzu⟩
    have hzL : (z : chapter04UnitLogHyperplane K) ∈ L := by
      exact (le_of_eq hspan) z.property
    refine ⟨⟨z, hzL⟩, ?_, ?_⟩
    · change z +ᵥ x ∈ ZSpan.fundamentalDomain e
      exact hz
    · intro w hw
      have hw' :
          (⟨(w : chapter04UnitLogHyperplane K), hspan.symm ▸ w.property⟩ :
            Submodule.span ℤ (Set.range e)) +ᵥ x ∈ ZSpan.fundamentalDomain e := by
        change (w : chapter04UnitLogHyperplane K) + x ∈
          ZSpan.fundamentalDomain e at hw ⊢
        exact hw
      have heq := hzu _ hw'
      apply Subtype.ext
      change (w : chapter04UnitLogHyperplane K) = (z : chapter04UnitLogHyperplane K)
      exact congrArg Subtype.val heq
  have hunit_span (x : chapter04UnitLogHyperplane K) (hx : x ∈ L) :
      ∃ u : (𝓞 K)ˣ,
        chapter04UnitLogEmbedding K (Additive.ofMul u) = x := by
    induction hx using Submodule.span_induction with
    | mem z hz =>
        rcases hz with ⟨u, rfl⟩
        exact ⟨u.toMul, by rw [ofMul_toMul]⟩
    | zero =>
        exact ⟨1, by simp⟩
    | add z w hz hw hzp hwp =>
        rcases hzp with ⟨u, hu⟩
        rcases hwp with ⟨v, hv⟩
        refine ⟨u * v, ?_⟩
        rw [ofMul_mul, map_add, hu, hv]
    | smul c z hz hzp =>
        rcases hzp with ⟨u, hu⟩
        refine ⟨u ^ c, ?_⟩
        rw [ofMul_zpow, map_zsmul, hu]
  have hunit_surj (z : L) :
      ∃ u : (𝓞 K)ˣ,
        chapter04UnitLogEmbedding K (Additive.ofMul u) = (z : chapter04UnitLogHyperplane K) := by
    exact hunit_span z z.property
  have hunit_log (u : (𝓞 K)ˣ) :
      chapter04YLog K (chapter04UnitScaling K u) =
        chapter04UnitLogEmbedding K (Additive.ofMul u) := by
    apply Subtype.ext
    funext v
    rfl
  have hlog_mul (g y : chapter04Y K) :
      chapter04YLog K (chapter04YMul K g y) =
        chapter04YLog K g + chapter04YLog K y := by
    have h := congrArg (chapter04YLog K)
      (hmul_exp g (chapter04YLog K y))
    simpa [hexp_log, hlog_exp] using h
  have hunit_inv (u : (𝓞 K)ˣ) :
      chapter04YInv K (chapter04UnitScaling K u) =
        chapter04UnitScaling K u⁻¹ := by
    simp only [chapter04YInv, chapter04UnitScaling]
    congr 1
    funext v
    simp
  have hmap_inv_raw :
      Measure.map (chapter04YInv K) (Measure.map (chapter04YExp K) μ) =
        Measure.map (chapter04YExp K) μ := by
    rw [Measure.map_map hinv_meas hexp_meas, hcomp_inv]
    rw [← Measure.map_map hexp_meas measurable_neg]
    exact congrArg (Measure.map (chapter04YExp K)) hmap_neg
  let ν : Measure (chapter04Y K) := (μ F)⁻¹ • Measure.map (chapter04YExp K) μ
  have hmap_mul (g : chapter04Y K) :
      Measure.map (chapter04YMul K g) ν = ν := by
    dsimp [ν]
    rw [Measure.map_smul, hmap_mul_raw]
  have hmap_inv :
      Measure.map (chapter04YInv K) ν = ν := by
    dsimp [ν]
    rw [Measure.map_smul, hmap_inv_raw]
  have hleft (g : chapter04Y K) (s : Set (chapter04Y K))
      (hs : MeasurableSet s) :
      ν (chapter04YMul K g '' s) = ν s := by
    let e : chapter04Y K ≃ᵐ chapter04Y K :=
      ⟨{ toFun := chapter04YMul K g
         invFun := chapter04YMul K (chapter04YInv K g)
         left_inv := hmul_left_inv g
         right_inv := hmul_right_inv g },
       hmul_meas g, hmul_meas (chapter04YInv K g)⟩
    have himage : MeasurableSet (chapter04YMul K g '' s) :=
      e.measurableSet_image.mpr hs
    calc
      ν (chapter04YMul K g '' s) =
          Measure.map (chapter04YMul K g) ν
            (chapter04YMul K g '' s) := by rw [hmap_mul g]
      _ = ν (chapter04YMul K g ⁻¹' (chapter04YMul K g '' s)) := by
        rw [Measure.map_apply (hmul_meas g) himage]
      _ = ν s := by
        change ν (e ⁻¹' (e '' s)) = ν s
        rw [e.preimage_image]
  have hinverse (s : Set (chapter04Y K)) (hs : MeasurableSet s) :
      ν (chapter04YInv K '' s) = ν s := by
    let e : chapter04Y K ≃ᵐ chapter04Y K :=
      ⟨{ toFun := chapter04YInv K
         invFun := chapter04YInv K
         left_inv := hinv_inv
         right_inv := hinv_inv },
       hinv_meas, hinv_meas⟩
    have himage : MeasurableSet (chapter04YInv K '' s) :=
      e.measurableSet_image.mpr hs
    calc
      ν (chapter04YInv K '' s) =
          Measure.map (chapter04YInv K) ν (chapter04YInv K '' s) := by
            rw [hmap_inv]
      _ = ν (chapter04YInv K ⁻¹' (chapter04YInv K '' s)) := by
        rw [Measure.map_apply hinv_meas himage]
      _ = ν s := by
        change ν (e ⁻¹' (e '' s)) = ν s
        rw [e.preimage_image]
  have hunit_fundamental :
      ∀ y : chapter04Y K, ∃ u : (𝓞 K)ˣ, ∃ p ∈ chapter04YLog K ⁻¹' F,
        y = chapter04YMul K (chapter04UnitScaling K u) p := by
    intro y
    rcases hfund (chapter04YLog K y) with ⟨z, hz, hzu⟩
    rcases hunit_surj z with ⟨u, hu⟩
    refine ⟨u⁻¹, chapter04YMul K (chapter04UnitScaling K u) y, ?_, ?_⟩
    · change chapter04YLog K
        (chapter04YMul K (chapter04UnitScaling K u) y) ∈ F
      rw [hlog_mul, hunit_log, hu]
      exact hz
    · calc
        y = chapter04YMul K (chapter04YInv K (chapter04UnitScaling K u))
            (chapter04YMul K (chapter04UnitScaling K u) y) :=
          (hmul_left_inv (chapter04UnitScaling K u) y).symm
        _ = chapter04YMul K (chapter04UnitScaling K u⁻¹)
            (chapter04YMul K (chapter04UnitScaling K u) y) := by
          rw [hunit_inv]
  have hunit_unique :
      ∀ {u v : (𝓞 K)ˣ} {p q : chapter04Y K},
        p ∈ chapter04YLog K ⁻¹' F → q ∈ chapter04YLog K ⁻¹' F →
          chapter04YMul K (chapter04UnitScaling K u) p =
            chapter04YMul K (chapter04UnitScaling K v) q → p = q := by
    intro u v p q hp hq heq
    change chapter04YLog K p ∈ F at hp
    change chapter04YLog K q ∈ F at hq
    have hlogeq :
        chapter04UnitLogEmbedding K (Additive.ofMul u) +
            chapter04YLog K p =
          chapter04UnitLogEmbedding K (Additive.ofMul v) +
            chapter04YLog K q := by
      have h := congrArg (chapter04YLog K) heq
      simpa [hlog_mul, hunit_log] using h
    have hu_mem :
        chapter04UnitLogEmbedding K (Additive.ofMul u) ∈ L :=
      Submodule.subset_span ⟨Additive.ofMul u, rfl⟩
    have hv_mem :
        chapter04UnitLogEmbedding K (Additive.ofMul v) ∈ L :=
      Submodule.subset_span ⟨Additive.ofMul v, rfl⟩
    let zu : L := ⟨chapter04UnitLogEmbedding K (Additive.ofMul u), hu_mem⟩
    let zv : L := ⟨chapter04UnitLogEmbedding K (Additive.ofMul v), hv_mem⟩
    have hzero : ((0 : L) : chapter04UnitLogHyperplane K) +
        chapter04YLog K q ∈ F := by simpa using hq
    have hdiff_eq :
        chapter04YLog K p =
          ((zv - zu : L) : chapter04UnitLogHyperplane K) +
            chapter04YLog K q := by
      change chapter04YLog K p =
        (chapter04UnitLogEmbedding K (Additive.ofMul v) -
          chapter04UnitLogEmbedding K (Additive.ofMul u)) +
            chapter04YLog K q
      have h := congrArg
        (fun x : chapter04UnitLogHyperplane K =>
          x - chapter04UnitLogEmbedding K (Additive.ofMul u)) hlogeq
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
    have hdiff :
        ((zv - zu : L) : chapter04UnitLogHyperplane K) +
            chapter04YLog K q ∈ F := by
      rw [← hdiff_eq]
      exact hp
    rcases hfund (chapter04YLog K q) with ⟨z, hz, hzu⟩
    have hdiff_zero : zv - zu = 0 := by
      calc
        zv - zu = z := hzu (zv - zu) hdiff
        _ = 0 := (hzu 0 hzero).symm
    have hzvu : zv = zu := sub_eq_zero.mp hdiff_zero
    have huv :
        chapter04UnitLogEmbedding K (Additive.ofMul v) =
          chapter04UnitLogEmbedding K (Additive.ofMul u) := by
      exact congrArg Subtype.val hzvu
    rw [huv] at hlogeq
    have hlogpq : chapter04YLog K p = chapter04YLog K q :=
      add_left_cancel hlogeq
    have hexp := congrArg (chapter04YExp K) hlogpq
    simpa [hexp_log] using hexp
  exact ⟨⟨chapter04YLog K ⁻¹' F, ν,
      hLmeas, by
        dsimp [ν]
        rw [hmapF]
        exact ENNReal.inv_mul_cancel hμF_nezero hμF_ne_top,
      hleft, hinverse, hunit_fundamental, hunit_unique⟩⟩

theorem chapter04_unit_fundamental_domain_normalized
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter04UnitFundamentalDomain K) :
    D.measure D.carrier = 1 := by
  exact D.normalized_volume

/- The source leaves the positive orbit constant dependent on the chosen Haar
   normalization.  Record its existence for the selected normalized domain,
   then choose it for the continuation. -/
theorem chapter04_theta_mellin_constant_exists
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter04UnitFundamentalDomain K) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (a : Chapter04NonzeroFractionalIdeal K) {s : ℂ}, 1 < s.re →
        chapter04ThetaMellinIntegral K D
            (a : Chapter04FractionalIdeal K) s =
          (c : ℂ) *
            (chapter04AbsoluteDiscriminant K : ℂ) ^ (s / 2) *
                chapter04ArchimedeanFactor K s *
                chapter04PartialZeta K (chapter04InverseIdealClass K a) s := by
  exact chapter04_theta_mellin_orbit_bridge K D

noncomputable def chapter04MellinConstant
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter04UnitFundamentalDomain K) : ℝ :=
  Classical.choose (chapter04_theta_mellin_constant_exists K D)

theorem chapter04_mellin_constant_pos
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter04UnitFundamentalDomain K) :
    0 < chapter04MellinConstant K D := by
  exact (Classical.choose_spec (chapter04_theta_mellin_constant_exists K D)).1

theorem chapter04_mellin_constant_ne_zero
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter04UnitFundamentalDomain K) :
    chapter04MellinConstant K D ≠ 0 :=
  (chapter04_mellin_constant_pos K D).ne'

theorem chapter04_theta_mellin_eq_completed_partial_zeta
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter04UnitFundamentalDomain K)
    (a : Chapter04NonzeroFractionalIdeal K)
    {s : ℂ} (hs : 1 < s.re) :
    chapter04ThetaMellinIntegral K D (a : Chapter04FractionalIdeal K) s =
      (chapter04MellinConstant K D : ℂ) *
        (chapter04AbsoluteDiscriminant K : ℂ) ^ (s / 2) *
          chapter04ArchimedeanFactor K s *
            chapter04PartialZeta K (chapter04InverseIdealClass K a) s := by
  exact (Classical.choose_spec (chapter04_theta_mellin_constant_exists K D)).2 a hs

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04
