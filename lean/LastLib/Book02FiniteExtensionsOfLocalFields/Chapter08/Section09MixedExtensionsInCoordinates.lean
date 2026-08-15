import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.Section08PrimeToP_RadicalExtensions

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08

noncomputable section

open Polynomial
open scoped BigOperators

/-! # 8.9. A mixed extension in coordinates -/

/-- A finite residue field of cardinality `q`. -/
def chapter08FiniteResidueFieldOfCardinality
    (k : Type*) [Field k] [Fintype k] (q : ℕ) : Prop :=
  Fintype.card k = q

/-- Book §8.9: the unramified stage has degree `f`, ramification index one,
and residue degree `f`. -/
theorem chapter08_unramified_stage_profile
    {K Kf : Type*} [Field K] [Field Kf] [Algebra K Kf]
    [FiniteDimensional K Kf]
    (f : ℕ) (_hdegree : Module.finrank K Kf = f)
    (vK : AddValuation K (WithTop ℤ))
    (vKf : AddValuation Kf (WithTop ℤ))
    (_hdiscreteK :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vK)
    (_hdiscreteKf :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vKf)
    (hval : vK.IsEquiv (AddValuation.comap (algebraMap K Kf) vKf))
    (hunramified :
      ∃ d : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10HeterogeneousExtensionData
          vK vKf hval,
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10UnramifiedBranch
          vK vKf hval d ∧
        d.ramificationIndex * d.residueDegree = Module.finrank K Kf) :
    ∃ d : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10HeterogeneousExtensionData
        vK vKf hval,
      ∃ q : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10FiniteExtensionProfile,
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ProfileRealizedByData d q ∧
          q.degree = f ∧ q.ramificationIndex = 1 ∧ q.residueDegree = f ∧
          LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10Unramified q ∧
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10UnramifiedBranch
            vK vKf hval d := by
  rcases hunramified with ⟨d, hbranch, hprod⟩
  have hbranch' := hbranch
  unfold LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10UnramifiedBranch
    at hbranch'
  have hram : d.ramificationIndex = 1 := hbranch'.1
  have hres : d.residueDegree = f := by
    calc
      d.residueDegree = 1 * d.residueDegree := by simp
      _ = d.ramificationIndex * d.residueDegree := by rw [hram]
      _ = Module.finrank K Kf := hprod
      _ = f := _hdegree
  refine ⟨d, { degree := f, ramificationIndex := 1, residueDegree := f }, ?_⟩
  refine ⟨⟨_hdegree.symm, hram.symm, hres.symm⟩, rfl, rfl, rfl, ⟨rfl, rfl⟩,
    hbranch⟩

/-- Book §8.9: adjoining a root of `varpi^e = π_K` over the unramified stage
produces the ramified degree-`e` stage. -/
theorem chapter08_ramified_stage_profile
    {K Kf L : Type*} [Field K] [Field Kf] [Field L]
    [Algebra K Kf] [Algebra Kf L] [Algebra K L]
    [IsScalarTower K Kf L]
    [FiniteDimensional K Kf] [FiniteDimensional Kf L]
    [FiniteDimensional K L]
    (e f : ℕ) (_he : 0 < e) (_hf : 0 < f)
    (πK : K) (varpi : L)
    (vK : AddValuation K (WithTop ℤ))
    (hdiscreteK :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vK)
    (_hroot : algebraMap Kf L (algebraMap K Kf πK) = varpi ^ e)
    (_hgen : Algebra.adjoin Kf ({varpi} : Set L) = ⊤)
    (hdegree : Module.finrank Kf L = e)
    (hbaseDegree : Module.finrank K Kf = f)
    (vKf : AddValuation Kf (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (hdiscreteKf :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vKf)
    (hdiscreteL :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vL)
    (hvalKf : vK.IsEquiv (AddValuation.comap (algebraMap K Kf) vKf))
    (hvalL : vKf.IsEquiv (AddValuation.comap (algebraMap Kf L) vL))
    (hval : vK.IsEquiv (AddValuation.comap (algebraMap K L) vL))
    (hπK : vK πK = 1)
    (hvarpi : vL varpi = 1)
    (hscale : ∀ x : Kf, x ≠ 0 →
      vL (algebraMap Kf L x) = e • vKf x)
    (hunramified :
      ∃ d : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10HeterogeneousExtensionData
          vK vKf hvalKf,
        ∃ q : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10FiniteExtensionProfile,
          LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ProfileRealizedByData d q ∧
            q.degree = f ∧ q.ramificationIndex = 1 ∧ q.residueDegree = f ∧
            LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10Unramified q ∧
            LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10UnramifiedBranch
              vK vKf hvalKf d) :
    Module.finrank K L = e * f ∧
      ∃ d : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10HeterogeneousExtensionData
          vK vL hval,
        ∃ q : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10FiniteExtensionProfile,
          LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ProfileRealizedByData d q ∧
            q.degree = e * f ∧ q.ramificationIndex = e ∧ q.residueDegree = f := by
  have hfinrank : Module.finrank K L = e * f := by
    calc
      Module.finrank K L = Module.finrank K Kf * Module.finrank Kf L :=
        (Module.finrank_mul_finrank K Kf L).symm
      _ = f * e := by rw [hbaseDegree, hdegree]
      _ = e * f := Nat.mul_comm _ _
  have hπK0 : πK ≠ 0 := by
    intro hzero
    subst πK
    simp at hπK
  obtain ⟨r, hr, hscaleK⟩ :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_normalized_restriction_formula
      vK vKf hdiscreteK hdiscreteKf hvalKf
  rcases hunramified with ⟨du, qu, hduprof, hqdeg, hqram, hqres, hqunram, hbranch⟩
  have hbranch' := hbranch
  unfold LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10UnramifiedBranch
    at hbranch'
  have hri_base :=
    @LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_normalized_ramification_index_eq_scale
      K Kf _ _ _ _ vK vKf hdiscreteK hdiscreteKf hvalKf du r hr hscaleK
      du.finite_quotient
  have hr1 : r = 1 := hri_base.2.symm.trans hbranch'.1
  have ht : vKf (algebraMap K Kf πK) = 1 := by
    calc
      vKf (algebraMap K Kf πK) = r • vK πK := hscaleK πK hπK0
      _ = r • (1 : WithTop ℤ) := by rw [hπK]
      _ = 1 := by rw [hr1]; simp
  have hroot :
      Polynomial.eval₂ (algebraMap Kf L) varpi
        (X ^ e - C (algebraMap K Kf πK) : Kf[X]) = 0 := by
    simp [_hroot]
  have hvarpi_root :
      Polynomial.aeval varpi
        (X ^ e - C (algebraMap K Kf πK) : Kf[X]) = 0 := by
    simpa [Polynomial.aeval_def] using hroot
  have hvarpi_int : IsIntegral Kf varpi := by
    exact ⟨X ^ e - C (algebraMap K Kf πK),
      monic_X_pow_sub_C _ (Nat.ne_of_gt _he), hvarpi_root⟩
  have htop :
      IntermediateField.adjoin Kf ({varpi} : Set L) = ⊤ := by
    exact
      (IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic
        hvarpi_int.isAlgebraic).2 _hgen
  have hminpoly_degree :
      (minpoly Kf varpi).natDegree = Module.finrank Kf L := by
    calc
      (minpoly Kf varpi).natDegree =
          Module.finrank Kf (IntermediateField.adjoin Kf ({varpi} : Set L)) :=
        (IntermediateField.adjoin.finrank hvarpi_int).symm
      _ = Module.finrank Kf (⊤ : IntermediateField Kf L) := by rw [htop]
      _ = Module.finrank Kf L := by simp
  have hPdegree :
      (X ^ e - C (algebraMap K Kf πK) : Kf[X]).natDegree = e := by
    rw [natDegree_X_pow_sub_C]
  have hP_eq_minpoly :
      (X ^ e - C (algebraMap K Kf πK) : Kf[X]) = minpoly Kf varpi := by
    exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (minpoly.monic hvarpi_int)
      (monic_X_pow_sub_C _ (Nat.ne_of_gt _he))
      (minpoly.dvd Kf varpi hvarpi_root)
      (by simpa [hPdegree, hminpoly_degree] using hdegree.ge)
  have hirreducible :
      Irreducible (X ^ e - C (algebraMap K Kf πK) : Kf[X]) := by
    rw [hP_eq_minpoly]
    exact minpoly.irreducible hvarpi_int
  obtain ⟨drel, qrel, hdrel, hqrel_degree, hqrel_ram, hqrel_res,
      hqrel_total⟩ :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_equal_characteristic_totally_ramified_profile
      (k := Kf) (K := Kf) (L := L)
      (algebraMap K Kf πK) varpi e _he _hroot hirreducible hdegree
      vKf vL hdiscreteKf hdiscreteL hvalL ht hvarpi
  have hrelres :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10HeterogeneousResidueDegree
        vKf.toValuation vL.toValuation hvalL = 1 := by
    calc
      _ = drel.residueDegree := drel.residueDegree_eq.symm
      _ = qrel.residueDegree := hdrel.2.2.symm
      _ = 1 := hqrel_res
  have hdfinal_nonempty :
      Nonempty (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10HeterogeneousExtensionData
        vK.toValuation vL.toValuation hval) :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_heterogeneous_extension_data_exists
      vK.toValuation vL.toValuation hval
  obtain ⟨dfinal⟩ := hdfinal_nonempty
  have hri_final :=
    @LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_normalized_ramification_index_eq_scale
      K L _ _ _ _ vK vL hdiscreteK hdiscreteL hval dfinal e _he (by
        intro x hx
        calc
          vL (algebraMap K L x) =
              vL (algebraMap Kf L (algebraMap K Kf x)) := by
            rw [IsScalarTower.algebraMap_apply K Kf L]
          _ = e • vKf (algebraMap K Kf x) :=
            hscale (algebraMap K Kf x) (by
              intro hzero
              apply hx
              apply (RingHom.injective (algebraMap K Kf))
              simpa using hzero)
          _ = e • vK x := by rw [hscaleK x hx, hr1]; simp)
      dfinal.finite_quotient
  have hram_final : dfinal.ramificationIndex = e := hri_final.2
  refine ⟨hfinrank, dfinal,
    { degree := e * f, ramificationIndex := e, residueDegree := f }, ?_⟩
  let : Valuation.HasExtension vK.toValuation vKf.toValuation := ⟨hvalKf⟩
  let : Valuation.HasExtension vKf.toValuation vL.toValuation := ⟨hvalL⟩
  let : Valuation.HasExtension vK.toValuation vL.toValuation := ⟨hval⟩
  let : Module.IsTorsionFree vKf.toValuation.valuationSubring
      vL.toValuation.valuationSubring := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro a x hax
    rcases eq_or_ne a 0 with rfl | ha
    · exact Or.inl rfl
    · right
      have hmap :
          algebraMap vKf.toValuation.valuationSubring
              vL.toValuation.valuationSubring a ≠ 0 := by
        intro hzero
        apply ha
        have hz :
            algebraMap vKf.toValuation.valuationSubring
                vL.toValuation.valuationSubring a =
              algebraMap vKf.toValuation.valuationSubring
                vL.toValuation.valuationSubring
                (0 : vKf.toValuation.valuationSubring) := by
          simpa using hzero
        exact (Valuation.HasExtension.algebraMap_injective
          (vK := vKf.toValuation) (vA := vL.toValuation)) hz
      apply (mul_eq_zero.mp ?_).resolve_left hmap
      simpa [Algebra.smul_def] using hax
  let : Module.Flat vKf.toValuation.valuationSubring
      vL.toValuation.valuationSubring := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout]
    rw [← Submodule.isTorsionFree_iff_torsion_eq_bot]
    infer_instance
  let mA : Ideal vK.toValuation.valuationSubring :=
    IsLocalRing.maximalIdeal _
  let mB : Ideal vKf.toValuation.valuationSubring :=
    IsLocalRing.maximalIdeal _
  let mC : Ideal vL.toValuation.valuationSubring :=
    IsLocalRing.maximalIdeal _
  let : mB.LiesOver mA := by
    dsimp [mA, mB]
    infer_instance
  let : mC.LiesOver mB := by
    dsimp [mB, mC]
    infer_instance
  let : IsScalarTower vK.toValuation.valuationSubring
      vKf.toValuation.valuationSubring vL.toValuation.valuationSubring := by
    constructor
    intro a b c
    apply Subtype.ext
    simp [Algebra.smul_def, mul_assoc, IsScalarTower.algebraMap_apply K Kf L]
  have hres_tower :
      mC.inertiaDeg vK.toValuation.valuationSubring =
        mB.inertiaDeg vK.toValuation.valuationSubring *
          mC.inertiaDeg vKf.toValuation.valuationSubring := by
    exact Ideal.inertiaDeg_tower (R := vK.toValuation.valuationSubring)
      (S := vKf.toValuation.valuationSubring)
      (T := vL.toValuation.valuationSubring) mB mC
  have hbase_residue :
      mB.inertiaDeg vK.toValuation.valuationSubring = f := by
    calc
      mB.inertiaDeg vK.toValuation.valuationSubring = du.residueDegree := by
        rw [Ideal.inertiaDeg_eq_of_isMaximal mA mB]
        change Module.finrank
          (IsLocalRing.ResidueField vK.toValuation.valuationSubring)
          (IsLocalRing.ResidueField vKf.toValuation.valuationSubring) =
          du.residueDegree
        exact du.residueDegree_eq.symm
      _ = qu.residueDegree := hduprof.2.2.symm
      _ = f := hqres
  have hrelative_residue :
      mC.inertiaDeg vKf.toValuation.valuationSubring = 1 := by
    rw [Ideal.inertiaDeg_eq_of_isMaximal mB mC]
    change Module.finrank
      (IsLocalRing.ResidueField vKf.toValuation.valuationSubring)
      (IsLocalRing.ResidueField vL.toValuation.valuationSubring) = 1
    simpa [
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10HeterogeneousResidueDegree]
      using hrelres
  have hfinal_residue :
      dfinal.residueDegree = mC.inertiaDeg vK.toValuation.valuationSubring := by
    rw [dfinal.residueDegree_eq]
    rw [Ideal.inertiaDeg_eq_of_isMaximal mA mC]
    change Module.finrank
      (IsLocalRing.ResidueField vK.toValuation.valuationSubring)
      (IsLocalRing.ResidueField vL.toValuation.valuationSubring) =
      Module.finrank
        (IsLocalRing.ResidueField vK.toValuation.valuationSubring)
        (IsLocalRing.ResidueField vL.toValuation.valuationSubring)
    rfl
  have hdfinal_residue : dfinal.residueDegree = f := by
    calc
      dfinal.residueDegree = mC.inertiaDeg vK.toValuation.valuationSubring :=
        hfinal_residue
      _ = mB.inertiaDeg vK.toValuation.valuationSubring *
          mC.inertiaDeg vKf.toValuation.valuationSubring := hres_tower
      _ = f * 1 := by rw [hbase_residue, hrelative_residue]
      _ = f := by simp
  refine ⟨⟨hfinrank.symm, hram_final.symm, hdfinal_residue.symm⟩, rfl, rfl,
    rfl⟩

/-- The coordinate term `θ^j varpi^i` in the mixed integral basis. -/
def chapter08MixedIntegralBasisTerm
    {A B L : Type*} [CommRing A] [CommRing B] [IsDomain B] [Field L]
    [Algebra A B] [Algebra B L] [Algebra A L]
    [IsScalarTower A B L]
    [IsIntegralClosure B A L]
    (θ varpi : B) (j i : ℕ) : L :=
  algebraMap B L (θ ^ j * varpi ^ i)

/-- The integral-basis predicate for the coordinate family in Book §8.9. -/
def chapter08MixedIntegralBasis
    {A B L : Type*} [CommRing A] [CommRing B] [IsDomain B] [Field L]
    [Algebra A B] [Algebra B L] [Algebra A L]
    [IsScalarTower A B L]
    [IsIntegralClosure B A L]
    (e f : ℕ) (θ varpi : B) : Prop :=
    ∃ b : Module.Basis (Fin f × Fin e) A B,
    ∀ ji : Fin f × Fin e,
      algebraMap B L (b ji) =
        chapter08MixedIntegralBasisTerm (A := A) (B := B) (L := L)
          θ varpi ji.1 ji.2

/-- Book §8.9: the two-stage power basis gives the displayed integral basis.
The spanning and independence hypotheses are the algebraic content of the
unramified residue basis and the Eisenstein power basis. -/
theorem chapter08_mixed_extension_has_integral_basis
    {A B L : Type*} [CommRing A] [CommRing B] [IsDomain B] [Field L]
    [Algebra A B] [Algebra B L] [Algebra A L]
    [IsScalarTower A B L]
    [IsIntegralClosure B A L] [Module.Free A B] [Module.Finite A B]
    (e f : ℕ) (θ varpi : B)
    (hspan : ∀ x : B, ∃ c : Fin f × Fin e → A,
      x = ∑ ji, c ji • (θ ^ (ji.1 : ℕ) * varpi ^ (ji.2 : ℕ)))
    (hindependent : LinearIndependent A
      (fun ji : Fin f × Fin e =>
        θ ^ (ji.1 : ℕ) * varpi ^ (ji.2 : ℕ))) :
    chapter08MixedIntegralBasis (A := A) (B := B) (L := L) e f θ varpi := by
  let term : Fin f × Fin e → B := fun ji =>
    θ ^ (ji.1 : ℕ) * varpi ^ (ji.2 : ℕ)
  have htop : (⊤ : Submodule A B) ≤ Submodule.span A (Set.range term) := by
    intro x hx
    rcases hspan x with ⟨c, hc⟩
    rw [hc]
    refine Submodule.sum_mem _ (fun ji _ => ?_)
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self ji))
  refine ⟨Module.Basis.mk hindependent htop, ?_⟩
  intro ji
  simp [term, chapter08MixedIntegralBasisTerm]

/-- The root-of-unity condition needed for the ramified stage to be Kummer
Galois over the unramified field. -/
def chapter08AllRelevantRootsOfUnity
    (K : Type*) [Field K] (e : ℕ) : Prop :=
  (primitiveRoots e K).Nonempty

/-- Book §8.9: if the relevant roots of unity lie in `K_f`, the ramified stage
is Galois over `K_f`. -/
theorem chapter08_mixed_ramified_stage_is_galois_when_roots_are_present
    {Kf : Type*} [Field Kf]
    {a : Kf} {e : ℕ} [NeZero e]
    [Fact (Irreducible (chapter08KummerPolynomial a e))]
    (hroots : chapter08AllRelevantRootsOfUnity Kf e) :
    IsGalois Kf (chapter08KummerRadicalField Kf a e) ∧
      Nonempty
        (rootsOfUnity e Kf ≃*
          (chapter08KummerRadicalField Kf a e ≃ₐ[Kf]
            chapter08KummerRadicalField Kf a e)) := by
  have H : Irreducible (X ^ e - C a) := by
    simpa [chapter08KummerPolynomial] using
      (Fact.out : Irreducible (chapter08KummerPolynomial a e))
  let _ : Fact (Irreducible (X ^ e - C a)) := ⟨H⟩
  let _ : IsSplittingField Kf (chapter08KummerRadicalField Kf a e)
      (X ^ e - C a) := isSplittingField_AdjoinRoot_X_pow_sub_C hroots H
  exact ⟨isGalois_of_isSplittingField_X_pow_sub_C hroots H _,
    ⟨autAdjoinRootXPowSubCEquiv hroots H⟩⟩

/-- The numerical data `(e,f)` for a mixed local extension. -/
def chapter08MixedExtensionProfile (e f : ℕ) : Prop :=
  0 < e ∧ 0 < f

/-- Book §8.9: normality is additional data beyond the numerical `(e,f)`
profile.  The degree equation ties the bookkeeping pair to the displayed
finite extension; without it, the predicate would accept arbitrary positive
numbers independently of `K/L`. -/
def chapter08MixedExtensionGaloisProfile
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (e f : ℕ) : Prop :=
  chapter08MixedExtensionProfile e f ∧
    Module.finrank K L = e * f ∧ IsGalois K L

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08
