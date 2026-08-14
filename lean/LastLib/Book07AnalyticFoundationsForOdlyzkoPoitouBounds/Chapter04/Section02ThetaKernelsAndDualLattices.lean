import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04.Dependencies
import Mathlib.RingTheory.Trace.Basic

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

theorem chapter04_theta_series_and_derivatives_locally_uniform
    (K : Type*) [Field K] [NumberField K]
    {a : Chapter04FractionalIdeal K} (ha : a ≠ 0) :
    chapter04ThetaSeriesAndDerivativeLocallyUniform K a := by
  sorry

theorem chapter04_theta_poisson_summation
    (K : Type*) [Field K] [NumberField K]
    {a : Chapter04FractionalIdeal K} (ha : a ≠ 0)
    {t : ℝ} (ht : 0 < t) (y : chapter04Y K) :
    chapter04Theta K a t y =
      t⁻¹ * chapter04Theta K (chapter04DualFractionalIdeal K a) t⁻¹
        (chapter04YInv K y) := by
  sorry

theorem chapter04_unit_log_lattice_discrete
    (K : Type*) [Field K] [NumberField K] :
    DiscreteTopology (chapter04UnitLogLattice K) := by sorry

attribute [instance] chapter04_unit_log_lattice_discrete

theorem chapter04_unit_log_lattice_is_full
    (K : Type*) [Field K] [NumberField K] :
    IsZLattice ℝ (chapter04UnitLogLattice K) := by
  sorry

theorem chapter04_unit_log_lattice_span_eq_top
    (K : Type*) [Field K] [NumberField K] :
    Submodule.span ℝ (chapter04UnitLogLattice K :
      Set (chapter04UnitLogHyperplane K)) = ⊤ := by
  exact (chapter04_unit_log_lattice_is_full K).span_top

theorem chapter04_exists_unit_fundamental_domain
    (K : Type*) [Field K] [NumberField K] :
    Nonempty (Chapter04UnitFundamentalDomain K) := by
  sorry

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
  sorry

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
