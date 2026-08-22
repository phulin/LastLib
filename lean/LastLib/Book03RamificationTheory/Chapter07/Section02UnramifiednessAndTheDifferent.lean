import LastLib.Book03RamificationTheory.Chapter07.Section01MeasuringTheDefectOfIntegralTraceDuality

namespace LastLib.Book03RamificationTheory.Chapter07

noncomputable section

open scoped BigOperators Polynomial nonZeroDivisors

/-! ## 7.2. Unramifiedness and the different -/

/-- The numerical and residue-field profile of an unramified extension. -/
def chapter07UnramifiedProfile
    (e : ℕ) (k l : Type*) [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l] : Prop :=
  e = 1 ∧ Algebra.IsSeparable k l

@[simp] theorem chapter07UnramifiedProfile_iff
    (e : ℕ) (k l : Type*) [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l] :
    chapter07UnramifiedProfile e k l ↔ e = 1 ∧ Algebra.IsSeparable k l :=
  Iff.rfl

/- Perfectness of the integral trace pairing is stated as a lattice
   isomorphism, rather than as an informal determinant condition. -/
def chapter07IntegralTracePairingPerfect
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] : Prop :=
  ∃ e : B ≃ₗ[A] (B →ₗ[A] A),
    ∀ x y : B,
      algebraMap A K ((e x) y) =
        Algebra.trace K L (algebraMap B L x * algebraMap B L y)

theorem chapter07_integral_trace_pairing_perfect_iff
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] :
    chapter07IntegralTracePairingPerfect A B K L ↔
      ∃ e : B ≃ₗ[A] (B →ₗ[A] A),
        ∀ x y : B,
          algebraMap A K ((e x) y) =
            Algebra.trace K L (algebraMap B L x * algebraMap B L y) := Iff.rfl

/- The unramified lift of a separating residue generator gives a perfect
   integral trace pairing and the unit different. -/
theorem chapter07_unramified_trace_pairing_perfect
    (A B K L k l : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDedekindDomain B]
    [IsDiscreteValuationRing B] [Field K] [Field L] [Field k] [Field l]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [Algebra k l] [FiniteDimensional k l]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B]
    (mA : Ideal A) (mB : Ideal B)
    (hmA : mA = IsLocalRing.maximalIdeal A)
    (hmB : mB = IsLocalRing.maximalIdeal B)
    (e : ℕ) (hunram : chapter07UnramifiedProfile e k l)
    (hpower :
      (Ideal.map (algebraMap A B) mA : FractionalIdeal B⁰ L) =
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
          B L mB (e : ℤ))
    (_hdegree : Module.finrank K L = Module.finrank k l)
    (hresidue_model : chapter07CompatibleResidueModel A B k l) :
    chapter07IntegralTracePairingPerfect A B K L ∧
      chapter07DifferentIdeal A B = ⊤ ∧ e = 1 := by
  rcases hunram with ⟨he, hsep⟩
  have hmap : Ideal.map (algebraMap A B) mA = mB := by
    apply FractionalIdeal.coeIdeal_injective (R := B) (K := L)
    simpa [he,
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower]
      using hpower
  obtain ⟨eA, eB, hcompat⟩ := hresidue_model
  let : (IsLocalRing.maximalIdeal A).IsMaximal :=
    IsLocalRing.maximalIdeal.isMaximal A
  let : (IsLocalRing.maximalIdeal B).IsMaximal :=
    IsLocalRing.maximalIdeal.isMaximal B
  let : Field (A ⧸ IsLocalRing.maximalIdeal A) :=
    Ideal.Quotient.field _
  let : Field (B ⧸ IsLocalRing.maximalIdeal B) :=
    Ideal.Quotient.field _
  have hmapMax :
      Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
        IsLocalRing.maximalIdeal B := by
    simpa [hmA, hmB] using hmap
  let : Algebra (A ⧸ IsLocalRing.maximalIdeal A)
      (B ⧸ IsLocalRing.maximalIdeal B) :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (Ideal.map_le_iff_le_comap.mp (hmapMax.le))
  have hsep_res : Algebra.IsSeparable
      (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ IsLocalRing.maximalIdeal B) := by
    apply Algebra.IsSeparable.of_equiv_equiv eA.symm eB.symm
    ext x
    change algebraMap (A ⧸ IsLocalRing.maximalIdeal A)
        (B ⧸ IsLocalRing.maximalIdeal B) (eA.symm x) =
      eB.symm (algebraMap k l x)
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (eA.symm x)
    have hax : eA (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a) = x := by
      rw [ha, eA.apply_symm_apply]
    rw [← ha]
    rw [← hax]
    apply eB.injective
    simpa using hcompat a
  let : Algebra.IsSeparable
      (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ IsLocalRing.maximalIdeal B) := hsep_res
  let : Algebra.IsSeparable (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField B) := hsep_res
  let : IsLocalHom (algebraMap A B) :=
    ⟨fun a ha => by
      rw [← IsLocalRing.notMem_maximalIdeal] at ha ⊢
      intro ham
      apply ha
      rw [← hmB, ← hmap]
      exact Ideal.mem_map_of_mem (algebraMap A B)
        ((hmA ▸ ham))⟩
  let : IsNoetherianRing A := inferInstance
  have hDVRiff : IsDiscreteValuationRing A ↔ IsDedekindDomain A :=
    (IsDiscreteValuationRing.TFAE A (IsDiscreteValuationRing.not_isField A)).out 0 2
  let : IsDedekindDomain A := hDVRiff.mp inferInstance
  have hformal : Algebra.FormallyUnramified A B :=
    Algebra.FormallyUnramified.of_map_maximalIdeal (by
      simpa [hmA, hmB] using hmap)
  let : mB.IsPrime := by
    simpa [hmB] using
      (inferInstance : (IsLocalRing.maximalIdeal B).IsPrime)
  let : Algebra (FractionRing A) (FractionRing B) :=
    FractionRing.liftAlgebra A (FractionRing B)
  have hsepFrac : Algebra.IsSeparable (FractionRing A) (FractionRing B) := by
    apply Algebra.IsSeparable.of_equiv_equiv
      (FractionRing.algEquiv A K).symm.toRingEquiv
      (FractionRing.algEquiv B L).symm.toRingEquiv
    ext x
    exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv A K).symm
      (FractionRing.algEquiv B L).symm x
  let : Algebra.IsSeparable (FractionRing A) (FractionRing B) := hsepFrac
  have hDtop : chapter07DifferentIdeal A B = ⊤ := by
    by_contra hDne
    have hle : chapter07DifferentIdeal A B ≤ mB := by
      simpa [hmB] using (IsLocalRing.le_maximalIdeal hDne)
    have hdiv : mB ∣ chapter07DifferentIdeal A B :=
      Ideal.dvd_iff_le.mpr hle
    have hunramified : Algebra.IsUnramifiedAt A mB :=
      (Algebra.formallyUnramified_iff_forall (R := A) (A := B)).mp hformal
        ⟨mB, inferInstance⟩
    have hdiv' : mB ∣ differentIdeal A B := by
      simpa [chapter07DifferentIdeal] using hdiv
    have hnotdvd : ¬mB ∣ differentIdeal A B :=
      (not_dvd_differentIdeal_iff (A := A) (B := B) (P := mB)
        ).mpr hunramified
    exact hnotdvd hdiv'
  refine ⟨?_, hDtop, he⟩
  have hcodiff_inv :
      (chapter07CodifferentFractionalIdeal A B K L)⁻¹ = 1 := by
    calc
      (chapter07CodifferentFractionalIdeal A B K L)⁻¹ =
          chapter07DifferentFractionalIdeal A B K L :=
        (chapter07_different_fractional_is_inverse_codifferent A B K L).symm
      _ = (chapter07DifferentIdeal A B : FractionalIdeal B⁰ L) :=
        (chapter07_different_fractional_coe_eq A B K L).symm
      _ = 1 := by rw [hDtop]; simp
  have hcodiff : chapter07CodifferentFractionalIdeal A B K L = 1 := by
    rw [← inv_inv (chapter07CodifferentFractionalIdeal A B K L), hcodiff_inv,
      inv_one]
  let hbasisA : Module.Basis (Module.Free.ChooseBasisIndex A B) A B :=
    Module.Free.chooseBasis A B
  let : Fintype (Module.Free.ChooseBasisIndex A B) := Fintype.ofFinite _
  let : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L :=
    IsIntegralClosure.isLocalization A K L B
  let hbasisK : Module.Basis (Module.Free.ChooseBasisIndex A B) K L :=
    hbasisA.localizationLocalization K A⁰ L
  have hbasisA_span :
      (1 : Submodule B L).restrictScalars A =
        Submodule.span A (Set.range hbasisK) := by
    rw [Module.Basis.localizationLocalization_span K A⁰ L hbasisA]
    ext x
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨b, ?_⟩
      simpa [Algebra.linearMap_apply, IsScalarTower.toAlgHom_apply,
        LinearMap.toSpanSingleton_apply, Algebra.algebraMap_eq_smul_one] using hb
    · rintro ⟨b, hb⟩
      refine ⟨b, ?_⟩
      simpa [Algebra.linearMap_apply, IsScalarTower.toAlgHom_apply,
        LinearMap.toSpanSingleton_apply, Algebra.algebraMap_eq_smul_one] using hb
  have hdual_span :
      (Submodule.traceDual A K (1 : Submodule B L)).restrictScalars A =
        Submodule.span A (Set.range hbasisK.traceDual) :=
    Submodule.traceDual_span_of_basis A (1 : Submodule B L) hbasisK hbasisA_span
  have hcodiff_sub :
      (chapter07CodifferentFractionalIdeal A B K L : Submodule B L) =
        Submodule.traceDual A K (1 : Submodule B L) := by
    dsimp [chapter07CodifferentFractionalIdeal]
    simpa only using
      (FractionalIdeal.coe_dual_one (A := A) (K := K) (B := B) (L := L))
  have hdual_mem : ∀ i, hbasisK.traceDual i ∈ (1 : Submodule B L) := by
    intro i
    have hi : hbasisK.traceDual i ∈
        (Submodule.traceDual A K (1 : Submodule B L)).restrictScalars A := by
      rw [hdual_span]
      exact Submodule.subset_span ⟨i, rfl⟩
    have hi' : hbasisK.traceDual i ∈
        (chapter07CodifferentFractionalIdeal A B K L : Submodule B L) := by
      rw [hcodiff_sub]
      exact hi
    rw [hcodiff] at hi'
    simpa only [FractionalIdeal.coe_one] using hi'
  have hdual_mem' : ∀ i, ∃ c : B,
      algebraMap B L c = hbasisK.traceDual i := by
    intro i
    have hi := hdual_mem i
    rw [Submodule.one_eq_range] at hi
    exact hi
  choose c hc using hdual_mem'
  have htrace_expansion (x : L) :
      x = ∑ i, Algebra.trace K L (x * hbasisK i) • hbasisK.traceDual i := by
    symm
    simpa only [Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply] using
      hbasisK.traceDual.sum_repr x
  have htrace_mem (x y : B) : ∃ a : A,
      algebraMap A K a =
        Algebra.trace K L (algebraMap B L x * algebraMap B L y) := by
    have hx : algebraMap B L x ∈
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04TraceDual
          A B K L := by
      rw [← chapter07_codifferent_fractional_coe_eq A B K L]
      exact (chapter07_integral_ring_le_codifferent A B K L) (by simp)
    change ∀ y : B, ∃ a : A,
      algebraMap A K a =
        Algebra.trace K L (algebraMap B L x * algebraMap B L y) at hx
    exact hx y
  have hex (x : B) : ∃! φ : B →ₗ[A] A,
      chapter07TraceDualRepresentation A B K L (algebraMap B L x) φ := by
    apply (chapter07_codifferent_iff_unique_trace_dual A B K L
      (algebraMap B L x)).mp
    exact htrace_mem x
  let E0 : B → (B →ₗ[A] A) := fun x => Classical.choose (hex x)
  have hE0 (x : B) :
      chapter07TraceDualRepresentation A B K L (algebraMap B L x) (E0 x) :=
    (Classical.choose_spec (hex x)).1
  let E : B →ₗ[A] (B →ₗ[A] A) :=
    { toFun := E0
      map_add' := by
        intro x y
        have hsum :
            chapter07TraceDualRepresentation A B K L (algebraMap B L (x + y))
              (E0 x + E0 y) := by
          intro z
          rw [LinearMap.add_apply, map_add, hE0 x z, hE0 y z]
          simp [map_add, add_mul]
        exact ((hex (x + y)).unique hsum (hE0 (x + y))).symm
      map_smul' := by
        intro a x
        have hsmul :
            chapter07TraceDualRepresentation A B K L (algebraMap B L (a • x))
              (a • E0 x) := by
          intro z
          have hmap : algebraMap B L (a • x) =
              (algebraMap A K a) • algebraMap B L x := by
            rw [Algebra.smul_def (R := A) (A := B), map_mul,
              ← IsScalarTower.algebraMap_apply A B L,
              IsScalarTower.algebraMap_apply A K L,
              Algebra.smul_def (R := K) (A := L)]
          calc
            algebraMap A K ((a • E0 x) z) =
                algebraMap A K a * algebraMap A K (E0 x z) := by simp
            _ = algebraMap A K a *
                Algebra.trace K L (algebraMap B L x * algebraMap B L z) := by
              rw [hE0 x z]
            _ = Algebra.trace K L
                ((algebraMap A K a) •
                  (algebraMap B L x * algebraMap B L z)) := by
              rw [LinearMap.map_smul_of_tower]
              simp
            _ = Algebra.trace K L
                (algebraMap B L (a • x) * algebraMap B L z) := by
              rw [hmap]
              congr 1
              rw [Algebra.smul_def (R := K) (A := L),
                Algebra.smul_def (R := K) (A := L)]
              ac_rfl
        exact ((hex (a • x)).unique hsmul (hE0 (a • x))).symm
    }
  have hE_trace (x y : B) :
      algebraMap A K ((E x) y) =
        Algebra.trace K L (algebraMap B L x * algebraMap B L y) := by
    change algebraMap A K ((E0 x) y) = _
    exact hE0 x y
  have hc_trace (i j : Module.Free.ChooseBasisIndex A B) :
      Algebra.trace K L
          (algebraMap B L (c i) * algebraMap B L (hbasisA j)) =
        if j = i then 1 else 0 := by
    rw [hc i, ← Module.Basis.localizationLocalization_apply K A⁰ L hbasisA j]
    exact hbasisK.trace_traceDual_mul i j
  have hinj : Function.Injective E := by
    intro x y hxy
    apply IsIntegralClosure.algebraMap_injective B A L
    apply hbasisK.traceDual.repr.injective
    ext i
    rw [Module.Basis.traceDual_repr_apply, Module.Basis.traceDual_repr_apply,
      Algebra.traceForm_apply, Algebra.traceForm_apply]
    have hi := congrArg (fun φ => algebraMap A K (φ (hbasisA i))) hxy
    rw [hE_trace x (hbasisA i), hE_trace y (hbasisA i)] at hi
    rw [← Module.Basis.localizationLocalization_apply K A⁰ L hbasisA i] at hi
    exact hi
  have hsurj (φ : B →ₗ[A] A) : ∃ x : B, E x = φ := by
    let x : B := ∑ i, φ (hbasisA i) • c i
    refine ⟨x, ?_⟩
    apply hbasisA.ext
    intro j
    apply IsFractionRing.injective A K
    change algebraMap A K ((E x) (hbasisA j)) =
      algebraMap A K (φ (hbasisA j))
    dsimp [x]
    rw [map_sum]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
    simp only [Algebra.smul_def, map_mul]
    simp_rw [hE_trace, hc_trace]
    simp
  refine ⟨LinearEquiv.ofBijective E ⟨hinj, hsurj⟩, ?_⟩
  intro x y
  exact hE_trace x y

/- A trace matrix records the determinant criterion used in the forward
   direction. -/
def chapter07IntegralTraceMatrix
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    {ι : Type*} (tr : B →ₗ[A] A) (b : ι → B) : Matrix ι ι A :=
  fun i j => tr (b i * b j)

theorem chapter07_perfect_trace_pairing_has_unit_trace_determinant
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [IsDomain A] [IsFractionRing A K]
    [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (tr : B →ₗ[A] A)
    (hperfect : chapter07IntegralTracePairingPerfect A B K L)
    (hbasis : Module.Basis ι A B)
    (htrace : ∀ x y : B,
      algebraMap A K (tr (x * y)) =
        Algebra.trace K L (algebraMap B L x * algebraMap B L y)) :
    IsUnit (Matrix.det
      (chapter07IntegralTraceMatrix A B tr (fun i => hbasis i))) := by
  rcases hperfect with ⟨e, he⟩
  have hmatrix :
      chapter07IntegralTraceMatrix A B tr (fun i => hbasis i) =
        ((LinearMap.toMatrix hbasis hbasis.dualBasis) e).transpose := by
    ext i j
    simp only [chapter07IntegralTraceMatrix, Matrix.transpose_apply,
      LinearMap.toMatrix_apply, Module.Basis.dualBasis_repr]
    apply IsFractionRing.injective A K
    exact (htrace _ _).trans (he _ _).symm
  rw [hmatrix, Matrix.det_transpose]
  exact LinearEquiv.isUnit_det e hbasis hbasis.dualBasis

/- The trace pairing on a finite algebra over a field is represented by the
   trace of its multiplication operators. -/
def chapter07FiniteAlgebraTracePairing
    (k R : Type*) [Field k] [CommRing R] [Algebra k R]
    [FiniteDimensional k R] (x y : R) : k :=
  LinearMap.trace k R (Algebra.lmul k R (x * y))

def chapter07TracePairingNondegenerate
    (R k : Type*) [Field k] [CommRing R] [Algebra k R]
    (pair : R → R → k) : Prop :=
  ∀ x : R, (∀ y : R, pair x y = 0) → x = 0

theorem chapter07_nilpotent_is_in_trace_radical
    (k R : Type*) [Field k] [CommRing R] [Algebra k R]
    [FiniteDimensional k R] (z : R) (hz : IsNilpotent z) :
    ∀ y : R, chapter07FiniteAlgebraTracePairing k R z y = 0 := by
  intro y
  change LinearMap.trace k R (Algebra.lmul k R (z * y)) = 0
  exact
    (LinearMap.isNilpotent_trace_of_isNilpotent
      (((Commute.all z y).isNilpotent_mul_right hz).map
        (Algebra.lmul k R))).eq_zero

theorem chapter07_reduced_finite_local_algebra_is_a_field
    (k R : Type*) [Field k] [CommRing R] [Algebra k R]
    [FiniteDimensional k R] [IsLocalRing R] [IsReduced R] :
    IsField R := by
  sorry

theorem chapter07_field_trace_pairing_nondegenerate_iff_separable
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l] :
    chapter07TracePairingNondegenerate l k
        (chapter07FiniteAlgebraTracePairing k l) ↔
      Algebra.IsSeparable k l := by
  sorry

/- If the different is the unit ideal, the reduced quotient argument forces
   both value-group invariants and residue separability. -/
theorem chapter07_zero_different_implies_unramified
    (A B K L k l : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDedekindDomain B]
    [IsDiscreteValuationRing B] [Field K] [Field L] [Field k] [Field l]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [Algebra k l] [FiniteDimensional k l] [IsScalarTower A K L]
    [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B]
    (e : ℕ) (mA : Ideal A) (mB : Ideal B)
    (hmA : mA = IsLocalRing.maximalIdeal A)
    (hmB : mB = IsLocalRing.maximalIdeal B)
    (hpower :
      (Ideal.map (algebraMap A B) mA : FractionalIdeal B⁰ L) =
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
          B L mB (e : ℤ))
    (hzero : chapter07DifferentIdeal A B = ⊤)
    (hquotient_reduced : chapter07DifferentIdeal A B = ⊤ →
      IsReduced (B ⧸ Ideal.map (algebraMap A B) mA))
    (hresidue : Nonempty ((B ⧸ mB) ≃+* l))
    (htrace_nondegenerate : chapter07DifferentIdeal A B = ⊤ →
      chapter07TracePairingNondegenerate l k
        (chapter07FiniteAlgebraTracePairing k l)) :
    chapter07UnramifiedProfile e k l := by
  sorry

theorem chapter07_different_zero_iff_unramified
    (A B K L k l : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDedekindDomain B]
    [IsDiscreteValuationRing B] [Field K] [Field L] [Field k] [Field l]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [Algebra k l] [FiniteDimensional k l] [IsScalarTower A K L]
    [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B]
    (e : ℕ) (mA : Ideal A) (mB : Ideal B)
    (hmA : mA = IsLocalRing.maximalIdeal A)
    (hmB : mB = IsLocalRing.maximalIdeal B)
    (hpower :
      (Ideal.map (algebraMap A B) mA : FractionalIdeal B⁰ L) =
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
          B L mB (e : ℤ))
    (hdegree : Module.finrank K L = Module.finrank k l)
    (hresidue_model : chapter07CompatibleResidueModel A B k l)
    (hquotient_reduced : chapter07DifferentIdeal A B = ⊤ →
      IsReduced (B ⧸ Ideal.map (algebraMap A B) mA))
    (htrace_nondegenerate : chapter07DifferentIdeal A B = ⊤ →
      chapter07TracePairingNondegenerate l k
        (chapter07FiniteAlgebraTracePairing k l)) :
    chapter07DifferentIdeal A B = ⊤ ↔
      chapter07UnramifiedProfile e k l := by
  sorry

/- The value group may be unchanged while inseparable residue growth still
   forces a nontrivial different. -/
theorem chapter07_e_one_inseparable_residue_forces_nontrivial_different
    (A B K L k l : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDedekindDomain B]
    [IsDiscreteValuationRing B] [Field K] [Field L] [Field k] [Field l]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [Algebra k l] [FiniteDimensional k l] [IsScalarTower A K L]
    [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B]
    (mA : Ideal A) (mB : Ideal B)
    (hmA : mA = IsLocalRing.maximalIdeal A)
    (hmB : mB = IsLocalRing.maximalIdeal B)
    (hpower :
      (Ideal.map (algebraMap A B) mA : FractionalIdeal B⁰ L) =
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
          B L mB (1 : ℤ))
    (hdegree : Module.finrank K L = Module.finrank k l)
    (hresidue_model : chapter07CompatibleResidueModel A B k l)
    (hquotient_reduced : chapter07DifferentIdeal A B = ⊤ →
      IsReduced (B ⧸ Ideal.map (algebraMap A B) mA))
    (htrace_nondegenerate : chapter07DifferentIdeal A B = ⊤ →
      chapter07TracePairingNondegenerate l k
        (chapter07FiniteAlgebraTracePairing k l))
    (hinsep : ¬Algebra.IsSeparable k l) :
    chapter07DifferentIdeal A B ≠ ⊤ := by
  sorry

end

end LastLib.Book03RamificationTheory.Chapter07
