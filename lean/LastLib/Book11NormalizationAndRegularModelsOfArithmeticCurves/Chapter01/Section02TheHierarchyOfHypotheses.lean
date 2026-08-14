import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01.Dependencies
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.Section04ProofsOfPrincipalCases
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Field.IsField
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.RegularLocalRing.Polynomial

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10
open scoped AlgebraicGeometry

universe u v

/-! ### 1.2 The hierarchy of hypotheses -/

theorem chapter01_smooth_iff_lfp_flat_geometricallyRegularFibers
    {X S : Scheme.{u}} (f : X ⟶ S) :
    Chapter01SmoothMorphism f ↔
      LocallyOfFinitePresentation f ∧ Flat f ∧
        Chapter01GeometricallyRegularFibers f := by
  exact chapter10_smooth_iff_lfp_flat_geometricallyRegularFibers f

theorem chapter01_smooth_iff_smoothMorphismData
    {X S : Scheme.{u}} (f : X ⟶ S) :
    Chapter01SmoothMorphism f ↔ Nonempty (Chapter01SmoothMorphismData f) := by
  rw [chapter01_smooth_iff_lfp_flat_geometricallyRegularFibers]
  constructor
  · rintro ⟨hfp, hflat, hfibers⟩
    exact ⟨⟨hfp, hflat, hfibers⟩⟩
  · rintro ⟨⟨hfp, hflat, hfibers⟩⟩
    exact ⟨hfp, hflat, hfibers⟩

theorem chapter01_smooth_over_regular_base_is_regular
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hS : Chapter01RegularScheme S) (hf : Chapter01SmoothMorphism f) :
    Chapter01RegularScheme X := by
  sorry

theorem chapter01_regular_scheme_is_normal
    (X : Scheme.{u}) (hX : Chapter01RegularScheme X) :
    Chapter01NormalScheme X := by
  sorry

theorem chapter01_regular_local_ring_iff_cotangentSpace
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    Chapter01RegularLocalRing R ↔
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) =
        ringKrullDim R := by
  exact IsRegularLocalRing.iff_finrank_cotangentSpace R

theorem chapter01_excellent_is_nagata
    (R : Type u) [CommRing R] (hR : Chapter01ExcellentRing R) :
    Chapter01Nagata R := by
  sorry

theorem chapter01_proper_iff_separated_finiteType_universallyClosed
    {X S : Scheme.{u}} (f : X ⟶ S) :
    Chapter01ProperMorphism f ↔
      IsSeparated f ∧ Chapter01FiniteType f ∧ UniversallyClosed f := by
  constructor
  · intro hf
    exact ⟨hf.toIsSeparated, ⟨hf.toLocallyOfFiniteType, {
      isCompact_preimage := fun _ _ hU' =>
        (@Scheme.Hom.isProperMap _ _ f hf.toUniversallyClosed).isCompact_preimage hU'
    }⟩, hf.toUniversallyClosed⟩
  · rintro ⟨hsep, ⟨hft, _hqc⟩, huc⟩
    exact IsProper.mk (f := f) (toIsSeparated := hsep)
      (toUniversallyClosed := huc) (toLocallyOfFiniteType := hft)

theorem chapter01_projective_iff_projective_witness
    {X S : Scheme.{u}} (f : X ⟶ S) :
    Chapter01ProjectiveMorphism f ↔ Nonempty (Chapter04ProjectiveWitness f) := by
  rfl

private theorem chapter01_regular_spec_of_isRegularRing
    (R : Type u) [CommRing R] [IsRegularRing R] :
    Chapter01RegularScheme (Spec (CommRingCat.of R)) := by
  intro x
  let : x.asIdeal.IsPrime := x.isPrime
  exact IsRegularLocalRing.of_ringEquiv
    (Spec.stalkIso (CommRingCat.of R) x).commRingCatIsoToRingEquiv.symm

private theorem chapter01_polynomial_evaluation_not_flat :
    ¬ RingHom.Flat (Polynomial.evalRingHom (0 : (ULift.{u} ℚ))) := by
  intro hflat
  let k : Type u := ULift.{u} ℚ
  let : IsDomain k := by
    change IsDomain (ULift.{u} ℚ)
    exact @DivisionRing.isDomain (ULift.{u} ℚ) inferInstance
  let φ : Polynomial k →+* k := Polynomial.evalRingHom 0
  have hgen : GeneralizingMap (PrimeSpectrum.comap φ) := by
    exact hflat.generalizingMap_comap
  let R := Polynomial k
  let p₀ : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  let p₁ : PrimeSpectrum R :=
    ⟨Ideal.span ({Polynomial.X} : Set R),
      (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X⟩
  let q : PrimeSpectrum k := ⟨⊥, Ideal.isPrime_bot⟩
  have hp₀₁ : p₀ ⤳ p₁ := by
    apply (PrimeSpectrum.le_iff_specializes p₀ p₁).mp
    exact bot_le
  have hq₁ : PrimeSpectrum.comap (Polynomial.evalRingHom (0 : k)) q = p₁ := by
    apply PrimeSpectrum.ext
    change Ideal.comap (Polynomial.evalRingHom (0 : k)) (⊥ : Ideal k) = _
    rw [← RingHom.ker_eq_comap_bot, Polynomial.ker_evalRingHom]
    simp [p₁]
    rfl
  have hrel : p₀ ⤳ PrimeSpectrum.comap φ q := by
    rw [hq₁]
    exact hp₀₁
  obtain ⟨q', hq', hq'eq⟩ := hgen (a := q) (b := p₀) hrel
  have hq_eq : q' = q := by
    apply PrimeSpectrum.ext
    let : q'.asIdeal.IsPrime := q'.isPrime
    have hbot : q'.asIdeal = (⊥ : Ideal k) :=
      @Ideal.eq_bot_of_prime k _ q'.asIdeal q'.isPrime
    rw [hbot]
  have hp_eq : p₀ = p₁ := by
    calc
      p₀ = PrimeSpectrum.comap φ q' := hq'eq.symm
      _ = PrimeSpectrum.comap φ q := by rw [hq_eq]
      _ = p₁ := hq₁
  have hne : p₁ ≠ p₀ := by
    intro h
    have hspan : Ideal.span ({Polynomial.X} : Set R) = (⊥ : Ideal R) :=
      congrArg PrimeSpectrum.asIdeal h
    have hX : (Polynomial.X : R) ∈ (⊥ : Ideal R) := by
      rw [← hspan]
      exact Ideal.subset_span (by simp)
    apply @Polynomial.X_ne_zero k _ inferInstance
    exact Ideal.mem_bot.mp hX
  exact hne hp_eq.symm

private theorem chapter01_infinite_mvPolynomial_not_noetherian :
    ¬ IsNoetherianRing (MvPolynomial ℕ ℚ) := by
  let R := MvPolynomial ℕ ℚ
  let I : Ideal R := Ideal.span (Set.range (fun n : ℕ => MvPolynomial.X n))
  let e₀ : R →+* ℚ :=
    MvPolynomial.eval₂Hom (RingHom.id ℚ) (fun _ => 0)
  have hIker : I ≤ RingHom.ker e₀ := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨n, rfl⟩
    change e₀ (MvPolynomial.X n) = 0
    dsimp [e₀]
    rw [MvPolynomial.eval₂Hom_X']
  have hnotfg : ¬ I.FG := by
    intro hfg
    rcases hfg with ⟨S, hS⟩
    let V : Finset ℕ := S.biUnion fun p => p.vars
    obtain ⟨n, hn⟩ := Infinite.exists_notMem_finset V
    have hnS : ∀ p ∈ S, n ∉ p.vars := by
      intro p hp hpn
      apply hn
      exact Finset.mem_biUnion.mpr ⟨p, hp, hpn⟩
    let e : R →+* ℚ :=
      MvPolynomial.eval₂Hom (RingHom.id ℚ) (fun i => if i = n then 1 else 0)
    have hgen : ∀ p ∈ S, e p = 0 := by
      intro p hp
      have hpvars : ∀ i ∈ p.vars, (if i = n then 1 else 0) = (0 : ℚ) := by
        intro i hi
        have hin : i ≠ n := by
          intro h
          exact hnS p hp (h ▸ hi)
        simp [hin]
      dsimp [e]
      rw [MvPolynomial.eval₂Hom_eq_constantCoeff_of_vars (RingHom.id ℚ) hpvars]
      have hpI : p ∈ I := by
        rw [← hS]
        exact Ideal.subset_span hp
      have hpzero : e₀ p = 0 := hIker hpI
      simpa [e₀] using hpzero
    have hspan : Ideal.span (S : Set R) ≤ RingHom.ker e := by
      refine Ideal.span_le.2 ?_
      intro p hp
      exact hgen p hp
    have hxn : MvPolynomial.X n ∈ Ideal.span (S : Set R) := by
      rw [hS]
      exact Ideal.subset_span (Set.mem_range_self n)
    have hxzero : e (MvPolynomial.X n) = 0 := hspan hxn
    have hxone : e (MvPolynomial.X n) = 1 := by
      dsimp [e]
      rw [MvPolynomial.eval₂Hom_X']
      simp
    exact one_ne_zero (hxone.symm.trans hxzero)
  intro hnoeth
  exact hnotfg ((isNoetherianRing_iff_ideal_fg R).mp hnoeth I)

theorem chapter01_nagata_gives_finite_normalization
    (A L : Type u) [CommRing A] [IsDomain A] [Field L] [Algebra A L]
    [Algebra (FractionRing A) L] [IsScalarTower A (FractionRing A) L]
    [FiniteDimensional (FractionRing A) L]
    (hA : Chapter01Nagata A) :
    Chapter01NormalizationFinite A L := by
  change Module.Finite A (integralClosure A L)
  let Q := A ⧸ (⊥ : Ideal A)
  let e : Q ≃+* A := RingEquiv.quotientBot A
  let : Algebra Q A := e.toRingHom.toAlgebra
  let : Algebra Q (FractionRing A) :=
    (RingHom.comp (algebraMap A (FractionRing A)) e.toRingHom).toAlgebra
  let : SMul Q (FractionRing A) :=
    (inferInstance : Algebra Q (FractionRing A)).toSMul
  let : Algebra Q L :=
    (RingHom.comp (algebraMap A L) e.toRingHom).toAlgebra
  let : SMul Q L := (inferInstance : Algebra Q L).toSMul
  let : IsFractionRing Q (FractionRing A) :=
    IsFractionRing.of_ringEquiv_left e (by intro x; rfl)
  let : IsScalarTower Q A A :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower Q A L :=
    IsScalarTower.of_algebraMap_eq' (by rfl)
  let : IsScalarTower Q A (FractionRing A) :=
    IsScalarTower.of_algebraMap_eq' (by rfl)
  let : IsScalarTower Q (FractionRing A) L :=
    IsScalarTower.to₁₃₄ Q A (FractionRing A) L
  have hQ : Chapter01Japanese Q :=
    hA.japanese_quotient (⊥ : Ideal A)
  have hIntegral (x : L) : IsIntegral Q x ↔ IsIntegral A x :=
    RingEquiv.isIntegral_iff e (by rfl) x
  let phi : integralClosure Q L →ₛₗ[e.toRingHom] integralClosure A L :=
    { toFun := fun x => ⟨x, (hIntegral x).mp x.2⟩
      map_add' := by intro x y; rfl
      map_smul' := by
        intro q x
        simp only [Algebra.smul_def]
        apply Subtype.ext
        change algebraMap Q L q * (x : L) =
          algebraMap A L (e q) * (x : L)
        rfl }
  have hphi : Function.Surjective phi := by
    intro y
    refine ⟨⟨y, (hIntegral y).mpr y.2⟩, ?_⟩
    rfl
  exact Module.Finite.of_surjective
    (hM := hQ.finite_integral_closure (FractionRing A) L) phi hphi

theorem chapter01_projective_is_proper
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : Chapter01ProjectiveMorphism f) :
    Chapter01ProperMorphism f := by
  rcases hf with ⟨w⟩
  have hmap : IsProper w.map := by
    let : IsClosedImmersion w.map := w.closedImmersion
    infer_instance
  have hprojection : IsProper w.projectiveBundle.projection :=
    w.projectiveBundle.projection_isProper
  rw [← w.over]
  exact IsProper.stableUnderComposition.comp_mem _ _ hmap hprojection

/- These structures make the source's warning about non-reversible implications explicit without
turning a counterexample into an opaque proposition. -/
structure Chapter01RegularBaseNonSmoothExample where
  source : Scheme.{u}
  target : Scheme.{u}
  map : source ⟶ target
  sourceRegular : Chapter01RegularScheme source
  targetRegular : Chapter01RegularScheme target
  notSmooth : ¬ Chapter01SmoothMorphism map

structure Chapter01NormalNonRegularRingExample where
  carrier : Type u
  commRing : CommRing carrier
  normal : @Chapter01NormalRing carrier commRing
  notRegular : ¬ @Chapter01RegularRing carrier commRing

structure Chapter01NagataNonExcellentRingExample where
  carrier : Type u
  commRing : CommRing carrier
  nagata : @Chapter01Nagata carrier commRing
  notExcellent : ¬ @Chapter01ExcellentRing carrier commRing

structure Chapter01ProperNonProjectiveExample where
  source : Scheme.{u}
  target : Scheme.{u}
  map : source ⟶ target
  proper : Chapter01ProperMorphism map
  notProjective : ¬ Chapter01ProjectiveMorphism map

theorem chapter01_smooth_over_regular_base_has_no_converse :
    Nonempty Chapter01RegularBaseNonSmoothExample := by
  let k : Type _ := ULift.{_} ℚ
  let R := Polynomial k
  let φ : R →+* k := Polynomial.evalRingHom 0
  let f : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom φ)
  have hk : Chapter01RegularScheme (Spec (CommRingCat.of k)) := by
    let : IsRegularRing k := by infer_instance
    exact chapter01_regular_spec_of_isRegularRing k
  have hR : Chapter01RegularScheme (Spec (CommRingCat.of R)) := by
    let : IsRegularRing k := by infer_instance
    let : IsRegularRing R := by infer_instance
    exact chapter01_regular_spec_of_isRegularRing R
  have hnot : ¬ Chapter01SmoothMorphism f := by
    intro hsmooth
    let : Smooth f := hsmooth
    have hflat : Flat f := inferInstance
    have hφflat : RingHom.Flat φ := by
      exact (Flat.SpecMap_iff (f := CommRingCat.ofHom φ)).mp
        (by simpa [f] using hflat)
    exact chapter01_polynomial_evaluation_not_flat (by simpa [φ] using hφflat)
  exact ⟨{
    source := Spec (CommRingCat.of k)
    target := Spec (CommRingCat.of R)
    map := f
    sourceRegular := hk
    targetRegular := hR
    notSmooth := hnot
  }⟩

theorem chapter01_regular_has_no_normality_converse :
    Nonempty Chapter01NormalNonRegularRingExample := by
  let R₀ := MvPolynomial ℕ ℚ
  have hnormal₀ : Chapter01NormalRing R₀ := by
    constructor <;> infer_instance
  let R := ULift.{_} R₀
  let e : R ≃+* R₀ := ULift.ringEquiv
  let : IsDomain R := e.toMulEquiv.isDomain
  let : IsIntegrallyClosed R :=
    IsIntegrallyClosed.of_equiv e.symm
  have hnormal : Chapter01NormalRing R := by
    constructor <;> infer_instance
  have hnotNoetherian : ¬ IsNoetherianRing R := by
    intro hR
    let : IsNoetherianRing R := hR
    exact chapter01_infinite_mvPolynomial_not_noetherian
      (isNoetherianRing_of_ringEquiv R e)
  exact ⟨{
    carrier := R
    commRing := inferInstance
    normal := hnormal
    notRegular := by
      intro hregular
      exact hnotNoetherian ⟨hregular.noetherian⟩
  }⟩

theorem chapter01_nagata_has_no_excellence_converse :
    Nonempty Chapter01NagataNonExcellentRingExample := by
  sorry

theorem chapter01_proper_has_no_projectivity_converse :
    Nonempty Chapter01ProperNonProjectiveExample := by
  sorry

end
end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01
