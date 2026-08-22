import LastLib.Book03RamificationTheory.Chapter07.Section03TheDerivativeFormula

namespace LastLib.Book03RamificationTheory.Chapter07

noncomputable section

open Polynomial
open scoped BigOperators Polynomial nonZeroDivisors

/-! ## 7.4. Kähler differentials -/

/- SOURCE_ISSUE (7.4): The source says that residue separability alone lets
   Book 2 supply an integral generator.  Over an imperfect residue field, the
   integral monogenic conclusion also needs the henselian, finite-normalization,
   and defectless/monogenic hypotheses used by the local presentation theorem.
   The declarations below retain the explicit `hmono` certificate. -/

/-- A presentation-level form of `Ω[B⁄A] ≅ B/(f'(α)) dα`. -/
def chapter07MonogenicDifferentialPresentation
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (α : B) (f : A[X]) : Prop :=
  ∃ e : KaehlerDifferential A B ≃ₗ[B]
      B ⧸ Ideal.span ({aeval α f.derivative} : Set B),
    e (KaehlerDifferential.D A B α) =
      Ideal.Quotient.mk (Ideal.span ({aeval α f.derivative} : Set B)) 1

@[simp] theorem chapter07MonogenicDifferentialPresentation_iff
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (α : B) (f : A[X]) :
    chapter07MonogenicDifferentialPresentation A B α f ↔
      ∃ e : KaehlerDifferential A B ≃ₗ[B]
          B ⧸ Ideal.span ({aeval α f.derivative} : Set B),
        e (KaehlerDifferential.D A B α) =
          Ideal.Quotient.mk (Ideal.span ({aeval α f.derivative} : Set B)) 1 :=
  Iff.rfl

theorem chapter07_kaehler_differential_monogenic_equiv
    (A B K L : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDedekindDomain B]
    [IsDiscreteValuationRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B]
    (α : B) (f : A[X])
    (hmono : chapter07MonogenicPresentation A B K L α f) :
    chapter07MonogenicDifferentialPresentation A B α f := by
  rw [chapter07MonogenicDifferentialPresentation_iff]
  let I : Ideal B := Ideal.span ({chapter07DerivativeAt A B f α} : Set B)
  have hf : f = minpoly A α := by
    apply Polynomial.map_injective (algebraMap A K)
      (FaithfulSMul.algebraMap_injective A K)
    calc
      f.map (algebraMap A K) = minpoly K (algebraMap B L α) := hmono.2.2.2.2
      _ = (minpoly A α).map (algebraMap A K) :=
        minpoly.isIntegrallyClosed_eq_field_fractions K L hmono.1
  subst f
  let f : A[X] := minpoly A α
  let hroot : IsAdjoinRoot B f := by
    exact IsAdjoinRoot.mkOfAdjoinEqTop
      (chapter07MonogenicPresentation_is_integral A B K L α f hmono)
      (chapter07MonogenicPresentation_generates A B K L α f hmono)
  have hroot_map_aeval : hroot.map = aeval α := by
    dsimp [hroot]
    rfl
  have hroot_root : hroot.root = α := by
    change hroot.map (Polynomial.X : A[X]) = α
    rw [hroot_map_aeval]
    simp
  have hderiv_generator : hroot.map f.derivative ∈ I := by
    rw [hroot_map_aeval]
    change chapter07DerivativeAt A B f α ∈ I
    exact Ideal.subset_span (Set.mem_singleton _)
  have hderiv_kernel : ∀ p : A[X], hroot.map p = 0 →
      I.mkQ (hroot.map p.derivative) = 0 := by
    intro p hp
    have hp' : p ∈ RingHom.ker hroot.map := hp
    obtain ⟨q, rfl⟩ := hroot.mem_ker_map.mp hp'
    rw [Polynomial.derivative_mul]
    rw [map_add, map_mul, map_mul, hroot.map_self, zero_mul, add_zero]
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
    exact Ideal.mul_mem_right (hroot.map q) I hderiv_generator
  have hderiv_congr {p q : A[X]} (hpq : hroot.map p = hroot.map q) :
      I.mkQ (hroot.map p.derivative) = I.mkQ (hroot.map q.derivative) := by
    have hker : hroot.map (p - q) = 0 := by
      rw [map_sub, hpq, sub_self]
    have h := hderiv_kernel (p - q) hker
    apply sub_eq_zero.mp
    simpa only [Polynomial.derivative_sub, map_sub] using h
  let hrep : B → A[X] := Function.surjInv hroot.map_surjective
  have hrep_map (b : B) : hroot.map (hrep b) = b := by
    exact Function.rightInverse_surjInv hroot.map_surjective b
  have hmkQ_smul (a : A) (z : B) : I.mkQ (a • z) = a • I.mkQ z := by
    simp only [Algebra.smul_def]
    rw [← Ideal.Quotient.mk_algebraMap A I a]
    change (Ideal.Quotient.mk I) (algebraMap A B a * z) =
      (Ideal.Quotient.mk I) (algebraMap A B a) * (Ideal.Quotient.mk I) z
    rw [map_mul]
  let qDlin : B →ₗ[A] B ⧸ I :=
    { toFun := fun b => I.mkQ (hroot.map (hrep b).derivative)
      map_add' := by
        intro x y
        change I.mkQ (hroot.map (hrep (x + y)).derivative) = _
        calc
          I.mkQ (hroot.map (hrep (x + y)).derivative) =
              I.mkQ (hroot.map (hrep x + hrep y).derivative) := by
                apply hderiv_congr
                simp only [hrep_map, map_add]
          _ = I.mkQ (hroot.map ((hrep x).derivative + (hrep y).derivative)) := by
                rw [Polynomial.derivative_add]
          _ = I.mkQ (hroot.map (hrep x).derivative) +
              I.mkQ (hroot.map (hrep y).derivative) := by
                simp only [map_add]
      map_smul' := by
        intro a x
        change I.mkQ (hroot.map (hrep (a • x)).derivative) = _
        calc
          I.mkQ (hroot.map (hrep (a • x)).derivative) =
              I.mkQ (hroot.map (a • hrep x).derivative) := by
                apply hderiv_congr
                simp only [hrep_map, map_smul]
          _ = a • I.mkQ (hroot.map (hrep x).derivative) := by
                rw [Polynomial.derivative_smul, map_smul]
                exact hmkQ_smul a _ }
  have hqDlin_leibniz (x y : B) : qDlin (x * y) =
      x • qDlin y + y • qDlin x := by
    change I.mkQ (hroot.map (hrep (x * y)).derivative) = _
    calc
      I.mkQ (hroot.map (hrep (x * y)).derivative) =
          I.mkQ (hroot.map (hrep x * hrep y).derivative) := by
            apply hderiv_congr
            simp only [hrep_map, map_mul]
      _ = I.mkQ (hroot.map ((hrep x).derivative * hrep y +
          hrep x * (hrep y).derivative)) := by
            rw [Polynomial.derivative_mul]
      _ = x • qDlin y + y • qDlin x := by
            rw [map_add, map_mul, map_mul, hrep_map x, hrep_map y]
            change I.mkQ (hroot.map (hrep x).derivative * y +
                x * hroot.map (hrep y).derivative) =
              x • I.mkQ (hroot.map (hrep y).derivative) +
                y • I.mkQ (hroot.map (hrep x).derivative)
            rw [← I.mkQ.map_smul, ← I.mkQ.map_smul, ← I.mkQ.map_add]
            congr 1
            simp only [smul_eq_mul]
            ring
  let qder : Derivation A B (B ⧸ I) := Derivation.mk' qDlin hqDlin_leibniz
  let q : KaehlerDifferential A B →ₗ[B] B ⧸ I :=
    (KaehlerDifferential.linearMapEquivDerivation A B (M := B ⧸ I)).symm qder
  have hqDlin_alpha : qDlin α = I.mkQ 1 := by
    change I.mkQ (hroot.map (hrep α).derivative) = I.mkQ 1
    calc
      I.mkQ (hroot.map (hrep α).derivative) =
          I.mkQ (hroot.map (Polynomial.X : A[X]).derivative) := by
            apply hderiv_congr
            rw [hrep_map, hroot.map_X, hroot_root]
      _ = I.mkQ 1 := by simp
  have hqD : q (KaehlerDifferential.D A B α) = I.mkQ 1 := by
    change qder.liftKaehlerDifferential (KaehlerDifferential.D A B α) = I.mkQ 1
    rw [Derivation.liftKaehlerDifferential_comp_D]
    change qDlin α = I.mkQ 1
    exact hqDlin_alpha
  let smulD : B →ₗ[B] KaehlerDifferential A B :=
    (LinearMap.lsmul B (KaehlerDifferential A B)).flip
      (KaehlerDifferential.D A B α)
  have hz : chapter07DerivativeAt A B f α • KaehlerDifferential.D A B α = 0 := by
    have h := (KaehlerDifferential.D A B).map_aeval f α
    change (aeval α f.derivative) • KaehlerDifferential.D A B α = 0
    calc
      (aeval α f.derivative) • KaehlerDifferential.D A B α =
          KaehlerDifferential.D A B (aeval α f) := h.symm
      _ = 0 := by rw [hmono.2.2.2.1]; simp
  have hIker : I ≤ LinearMap.ker smulD := by
    change Ideal.span ({chapter07DerivativeAt A B f α} : Set B) ≤ LinearMap.ker smulD
    rw [Ideal.span_le]
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact hz
  let r : (B ⧸ I) →ₗ[B] KaehlerDifferential A B :=
    I.liftQ smulD hIker
  have hrq_on (b : B) : r (qder b) = KaehlerDifferential.D A B b := by
    change r (qDlin b) = KaehlerDifferential.D A B b
    change r (I.mkQ (hroot.map (hrep b).derivative)) = KaehlerDifferential.D A B b
    have hrlift (z : B) : r (I.mkQ z) = smulD z := by
      change (r.comp I.mkQ) z = smulD z
      simp [r]
    rw [hrlift]
    calc
      hroot.map (hrep b).derivative • KaehlerDifferential.D A B α =
          (aeval α (hrep b).derivative : B) • KaehlerDifferential.D A B α := by
            rw [hroot_map_aeval]
      _ = KaehlerDifferential.D A B (aeval α (hrep b)) :=
        ((KaehlerDifferential.D A B).map_aeval (hrep b) α).symm
      _ = KaehlerDifferential.D A B (hroot.map (hrep b)) := by
        rw [hroot_map_aeval]
      _ = KaehlerDifferential.D A B b := by rw [hrep_map]
  have hrq : r.comp q = LinearMap.id := by
    apply Derivation.liftKaehlerDifferential_unique
    ext b
    change r (q (KaehlerDifferential.D A B b)) = KaehlerDifferential.D A B b
    have hqb : q (KaehlerDifferential.D A B b) = qder b := by
      change qder.liftKaehlerDifferential (KaehlerDifferential.D A B b) = qder b
      rw [Derivation.liftKaehlerDifferential_comp_D]
    rw [hqb]
    exact hrq_on b
  have hq_surj : Function.Surjective q := by
    intro x
    obtain ⟨b, rfl⟩ := I.mkQ_surjective x
    refine ⟨b • KaehlerDifferential.D A B α, ?_⟩
    rw [map_smul, hqD]
    change b • I.mkQ 1 = I.mkQ b
    rw [← I.mkQ.map_smul]
    simp
  have hq_inj : Function.Injective q := by
    intro x y hxy
    have := congrArg r hxy
    simpa [← LinearMap.comp_apply, hrq] using this
  let e : KaehlerDifferential A B ≃ₗ[B] B ⧸ I :=
    LinearEquiv.ofBijective q ⟨hq_inj, hq_surj⟩
  refine ⟨e, ?_⟩
  change q (KaehlerDifferential.D A B α) = I.mkQ 1
  exact hqD

/- Mathlib's `KaehlerDifferential` is the canonical module; this is the
   computed zeroth Fitting ideal of the displayed one-generator presentation.
   The definition deliberately records the presentation rather than claiming
   a global Fitting-ideal API for arbitrary finite modules. -/
def chapter07ZerothFittingIdealOfMonogenicPresentation
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (α : B) (f : A[X]) : Ideal B :=
  Ideal.span ({aeval α f.derivative} : Set B)

theorem chapter07_fitting_ideal_of_monogenic_presentation_eq_different
    (A B K L : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDedekindDomain B]
    [IsDiscreteValuationRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B]
    (α : B) (f : A[X])
    (hmono : chapter07MonogenicPresentation A B K L α f) :
    chapter07ZerothFittingIdealOfMonogenicPresentation A B α f =
      chapter07DifferentIdeal A B := by
  symm
  exact chapter07_different_eq_derivative_ideal A B K L α f hmono

/-- The source's geometric slogan, made explicit as a vanishing statement. -/
theorem chapter07_unramified_monogenic_differentials_subsingleton
    (A B K L : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDedekindDomain B]
    [IsDiscreteValuationRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B]
    (α : B) (f : A[X])
    (hmono : chapter07MonogenicPresentation A B K L α f)
    (hunit : chapter07DifferentIdeal A B = ⊤) :
    Subsingleton (KaehlerDifferential A B) := by
  obtain ⟨e, _⟩ := chapter07_kaehler_differential_monogenic_equiv
    A B K L α f hmono
  let I : Ideal B := Ideal.span ({chapter07DerivativeAt A B f α} : Set B)
  have hI : I = ⊤ := by
    change Ideal.span ({chapter07DerivativeAt A B f α} : Set B) = ⊤
    rw [← chapter07_different_eq_derivative_ideal A B K L α f hmono]
    exact hunit
  have hsub : Subsingleton (B ⧸ I) := by
    constructor
    intro x y
    obtain ⟨x, rfl⟩ := I.mkQ_surjective x
    obtain ⟨y, rfl⟩ := I.mkQ_surjective y
    have hx : I.mkQ x = 0 := by
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ, hI]
      exact Submodule.mem_top
    have hy : I.mkQ y = 0 := by
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ, hI]
      exact Submodule.mem_top
    rw [hx, hy]
  constructor
  intro x y
  apply e.injective
  exact @Subsingleton.elim (B ⧸ I) hsub (e x) (e y)

theorem chapter07_differential_module_has_finite_length
    (A B K L : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDedekindDomain B]
    [IsDiscreteValuationRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B]
    (α : B) (f : A[X])
    (hmono : chapter07MonogenicPresentation A B K L α f) :
    IsFiniteLength B (KaehlerDifferential A B) := by
  obtain ⟨e, _⟩ := chapter07_kaehler_differential_monogenic_equiv
    A B K L α f hmono
  have hderiv :
      algebraMap B L (chapter07DerivativeAt A B f α) =
        aeval (algebraMap B L α) (derivative (minpoly K (algebraMap B L α))) := by
    change algebraMap B L (eval₂ (algebraMap A B) α f.derivative) =
      eval₂ (algebraMap K L) (algebraMap B L α)
        (derivative (minpoly K (algebraMap B L α)))
    rw [hom_eval₂]
    rw [show (algebraMap B L).comp (algebraMap A B) = algebraMap A L by
      ext a
      rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply A B L]]
    have hderiv_map :
        f.derivative.map (algebraMap A K) =
          derivative (minpoly K (algebraMap B L α)) := by
      rw [← derivative_map, hmono.2.2.2.2]
    rw [← hderiv_map, eval₂_map]
    congr 1
    ext a
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply A K L]
  have hδ :
      aeval (algebraMap B L α) (derivative (minpoly K (algebraMap B L α))) ≠ 0 := by
    exact (Algebra.IsSeparable.isSeparable K (algebraMap B L α)).aeval_derivative_ne_zero
      (minpoly.aeval K (algebraMap B L α))
  have hne : chapter07DerivativeAt A B f α ≠ 0 := by
    intro hz
    apply hδ
    rw [← hderiv, hz]
    simp
  have hnd : chapter07DerivativeAt A B f α ∈ B⁰ :=
    mem_nonZeroDivisors_iff_ne_zero.mpr hne
  have hquot :
      IsFiniteLength B
        (B ⧸ Ideal.span ({chapter07DerivativeAt A B f α} : Set B)) :=
    isFiniteLength_quotient_span_singleton B hnd
  exact e.symm.isFiniteLength hquot

theorem chapter07_different_exponent_eq_differential_length
    (A B K L : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDedekindDomain B]
    [IsDiscreteValuationRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B]
    (mB : Ideal B) (d : ℕ) (α : B) (f : A[X])
    (hmono : chapter07MonogenicPresentation A B K L α f)
    (hmB : mB = IsLocalRing.maximalIdeal B)
    (hD : chapter07DifferentIdeal A B = mB ^ d) :
    Module.length B (KaehlerDifferential A B) = d := by
  obtain ⟨e, _⟩ := chapter07_kaehler_differential_monogenic_equiv
    A B K L α f hmono
  calc
    Module.length B (KaehlerDifferential A B) =
        Module.length B (B ⧸ Ideal.span
          ({chapter07DerivativeAt A B f α} : Set B)) := e.length_eq
    _ = Module.length B (B ⧸ mB ^ d) := by
      rw [← chapter07_different_eq_derivative_ideal A B K L α f hmono, hD]
    _ = d := by
      rw [hmB]
      exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal B d

/- This interface records the hypothesis needed before identifying a trace
   different with a differential Fitting ideal. -/
def chapter07TraceAndDifferentialAgreement
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    (α : B) (f : A[X]) : Prop :=
  chapter07MonogenicDifferentialPresentation A B α f ∧
    chapter07MonogenicPresentation A B K L α f

theorem chapter07_trace_differential_agreement_from_presentation
    (A B K L : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDedekindDomain B]
    [IsDiscreteValuationRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B]
    (α : B) (f : A[X])
    (hpresentation : chapter07TraceAndDifferentialAgreement A B K L α f) :
    chapter07ZerothFittingIdealOfMonogenicPresentation A B α f =
      chapter07DifferentIdeal A B := by
  exact chapter07_fitting_ideal_of_monogenic_presentation_eq_different
    A B K L α f hpresentation.2

end

end LastLib.Book03RamificationTheory.Chapter07
