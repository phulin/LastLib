import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07.Section06FactorizationAndBaseChange

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07

open Set
open Polynomial
open LastLib.Book01ValuationsDVRsAndCompletions.Chapter10

noncomputable section

universe uC

/-! # Book 2, Chapter 7, §7.7: roots of unity prime to the residue characteristic -/

/-- `m` is invertible in the valuation ring. -/
def Chapter07OrderInvertibleIn
    (A : Type*) [CommRing A] (m : ℕ) : Prop :=
  IsUnit (m : A)

/-- A reduction homomorphism on units that respects `m`th roots of unity. -/
def chapter07RootsOfUnityReduction
    {K k : Type*} [CommMonoid K] [CommMonoid k]
    (m : ℕ) (ρ : K →* k) :
    rootsOfUnity m K →* rootsOfUnity m k :=
  restrictRootsOfUnity ρ m

private theorem chapter07_hensel_simple_root_lifts_uniquely
    {B l : Type*} [CommRing B] [Field l] [HenselianLocalRing B]
    (res : B →+* l) (m : ℕ) (hm : Chapter07OrderInvertibleIn B m)
    (hres : Function.Surjective res)
    (hker : RingHom.ker res = IsLocalRing.maximalIdeal B)
    (ζ : l) (hζ : ζ ^ m = 1) :
    ∃! ξ : B, ξ ^ m = 1 ∧ res ξ = ζ := by
  classical
  let _ : Nontrivial B := RingHom.domain_nontrivial res
  let _ : IsLocalHom res := IsLocalHom.of_surjective res hres
  have hmne : m ≠ 0 := by
    intro hmz
    exact hm.ne_zero (by simp [hmz])
  have hζ0 : ζ ≠ 0 := by
    intro h
    subst ζ
    simp [Nat.ne_of_gt (Nat.pos_of_ne_zero hmne)] at hζ
  obtain ⟨a₀, ha₀⟩ := hres ζ
  let f : B[X] := X ^ m - 1
  have hf : f.Monic := by
    dsimp [f]
    exact monic_X_pow_sub_C 1 hmne
  have hfa : f.eval a₀ ∈ IsLocalRing.maximalIdeal B := by
    rw [← hker]
    change res (f.eval a₀) = 0
    simp [f, ha₀, hζ]
  have hderiv_formula : f.derivative = C (m : B) * X ^ (m - 1) := by
    dsimp [f]
    rw [derivative_sub, derivative_X_pow, derivative_one, sub_zero]
  have hderivunit_at (x : B) (hx : res x = ζ) :
      IsUnit (f.derivative.eval x) := by
    have hxunit : IsUnit x := by
      apply isUnit_of_map_unit res x
      rw [hx]
      exact isUnit_iff_ne_zero.mpr hζ0
    rw [hderiv_formula]
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    exact hm.mul (hxunit.pow (m - 1))
  obtain ⟨ξ, hξroot, hξres⟩ :=
    HenselianLocalRing.is_henselian f hf a₀ hfa (hderivunit_at a₀ ha₀)
  have hξpow : ξ ^ m = 1 := by
    apply sub_eq_zero.mp
    simpa [f] using hξroot.eq_zero
  have hξres' : res ξ = ζ := by
    have hmem : ξ - a₀ ∈ RingHom.ker res := by
      rw [hker]
      exact hξres
    have hzero : res (ξ - a₀) = 0 := (RingHom.mem_ker).mp hmem
    rw [map_sub, sub_eq_zero] at hzero
    exact hzero.trans ha₀
  refine ⟨ξ, ⟨hξpow, hξres'⟩, ?_⟩
  intro η hη
  apply IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub (f := f)
  · simpa [f] using sub_eq_zero.mpr hη.1
  · simpa [f] using sub_eq_zero.mpr hξpow
  · intro hunit
    have hmem : η - ξ ∈ IsLocalRing.maximalIdeal B := by
      rw [← hker]
      apply (RingHom.mem_ker).mpr
      rw [map_sub, hη.2, hξres', sub_self]
    exact (IsLocalRing.notMem_maximalIdeal).2 hunit hmem
  · exact hderivunit_at η hη.2

/-- A bijective reduction map induces a bijection on the prime-to-
residue-characteristic roots of unity. -/
theorem chapter07_roots_of_unity_reduction_bijective
    {B l : Type*} [CommRing B] [Field l] [HenselianLocalRing B]
    (res : B →+* l) (m : ℕ) (hm : Chapter07OrderInvertibleIn B m)
    (hres : Function.Surjective res)
    (hker : RingHom.ker res = IsLocalRing.maximalIdeal B) :
    Function.Bijective
      (chapter07RootsOfUnityReduction m res.toMonoidHom) := by
  let _ : Nontrivial B := RingHom.domain_nontrivial res
  have hmne : m ≠ 0 := by
    intro hmz
    exact hm.ne_zero (by simp [hmz])
  let _ : NeZero m := ⟨hmne⟩
  constructor
  · intro x y hxy
    have hxy' :
        res ((x : Bˣ) : B) =
          res ((y : Bˣ) : B) := by
      have h := congrArg (fun z : rootsOfUnity m l => ((z : lˣ) : l)) hxy
      simpa [chapter07RootsOfUnityReduction] using h
    have hxpow :
        ((x : Bˣ) : B) ^ m = 1 :=
      (mem_rootsOfUnity' m (x : Bˣ)).mp x.prop
    have hypow :
        ((y : Bˣ) : B) ^ m = 1 :=
      (mem_rootsOfUnity' m (y : Bˣ)).mp y.prop
    have hu :=
      chapter07_hensel_simple_root_lifts_uniquely
        res m hm hres hker
        (res ((x : Bˣ) : B))
        (by
          simpa only [map_pow, map_one] using congrArg res hxpow)
    apply rootsOfUnity.coe_injective
    exact hu.unique ⟨hxpow, rfl⟩ ⟨hypow, hxy'.symm⟩
  · intro y
    have hypow : ((y : lˣ) : l) ^ m = 1 :=
      (mem_rootsOfUnity' m (y : lˣ)).mp y.prop
    obtain ⟨ξ, hξ, -⟩ :=
      chapter07_hensel_simple_root_lifts_uniquely
        res m hm hres hker ((y : lˣ) : l) hypow
    let x : rootsOfUnity m B := rootsOfUnity.mkOfPowEq ξ hξ.1
    refine ⟨x, ?_⟩
    apply rootsOfUnity.coe_injective
    simpa [x, chapter07RootsOfUnityReduction] using hξ.2

/-- The derivative of `T^m - 1` has the expected normalization factor. -/
theorem chapter07_derivative_power_minus_one
    {R : Type*} [CommRing R] (m : ℕ) :
    derivative (X ^ m - 1 : R[X]) = C (m : R) * X ^ (m - 1) := by
  rw [derivative_sub, derivative_X_pow, derivative_one, sub_zero]

/-- When `m` is a unit, every residue root is simple. -/
theorem chapter07_prime_to_residue_characteristic_roots_are_simple
    {A k : Type*} [CommRing A] [Field k]
    (res : A →+* k) (m : ℕ) (hm : Chapter07OrderInvertibleIn A m)
    (ζ : k) (hζ : ζ ^ m = 1) :
    eval₂ (RingHom.id k) ζ (derivative (X ^ m - 1 : k[X])) ≠ 0 := by
  let _ : Nontrivial A := RingHom.domain_nontrivial res
  have hm' : IsUnit (res (m : A)) := hm.map res
  have hm0 : (m : k) ≠ 0 := by
    simpa only [map_natCast] using hm'.ne_zero
  have hmne : m ≠ 0 := by
    intro hmz
    exact hm.ne_zero (by simp [hmz])
  have hζ0 : ζ ≠ 0 := by
    intro h
    subst ζ
    simp [Nat.ne_of_gt (Nat.pos_of_ne_zero hmne)] at hζ
  rw [chapter07_derivative_power_minus_one]
  simp only [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, RingHom.id_apply]
  exact mul_ne_zero hm0 (pow_ne_zero (m - 1) hζ0)

/-- Hensel's simple-root criterion lifts every residue `m`th root when `m` is
invertible in the local ring. -/
theorem chapter07_prime_to_residue_characteristic_root_lifts_uniquely
    {B l : Type*} [CommRing B] [Field l] [HenselianLocalRing B]
    (res : B →+* l) (m : ℕ) (hm : Chapter07OrderInvertibleIn B m)
    (hres : Function.Surjective res)
    (hker : RingHom.ker res = IsLocalRing.maximalIdeal B)
    (ζ : l) (hζ : ζ ^ m = 1) :
    ∃! ξ : B, ξ ^ m = 1 ∧ res ξ = ζ := by
  exact chapter07_hensel_simple_root_lifts_uniquely res m hm hres hker ζ hζ

/-- Reduction preserves exact order for roots of unity whose order is invertible
in the henselian local ring.  The hypotheses make the reduction map the actual
residue map; exactness is not assumed as an independent predicate. -/
theorem chapter07_reduction_preserves_primitive_root_order
    {B l : Type*} [CommRing B] [Field l] [HenselianLocalRing B]
    (res : B →+* l) (m : ℕ)
    (hm : Chapter07OrderInvertibleIn B m)
    (hres : Function.Surjective res)
    (hker : RingHom.ker res = IsLocalRing.maximalIdeal B)
    (ζ : rootsOfUnity m B) (hζ : IsPrimitiveRoot (ζ : Bˣ) m) :
    IsPrimitiveRoot
      (((chapter07RootsOfUnityReduction m res.toMonoidHom) ζ : rootsOfUnity m l) : lˣ) m := by
  let ρ :=
    chapter07RootsOfUnityReduction m res.toMonoidHom
  let _ : Nontrivial B := RingHom.domain_nontrivial res
  have hmne : m ≠ 0 := by
    intro hmz
    exact hm.ne_zero (by simp [hmz])
  let _ : NeZero m := ⟨hmne⟩
  apply IsPrimitiveRoot.mk
  · exact (ρ ζ).prop
  · intro n hn
    have hunitres :
        (Units.map res.toMonoidHom (ζ : Bˣ)) ^ n = 1 := by
      change (Units.map res.toMonoidHom (ζ : Bˣ)) ^ n = 1 at hn
      exact hn
    have hunitres' :
        Units.map res.toMonoidHom ((ζ : Bˣ) ^ n) = 1 := by
      simpa only [map_pow] using hunitres
    have hrespow :
        res (((ζ : Bˣ) ^ n : Bˣ) : B) = 1 := by
      have h := congrArg (fun u : lˣ => (u : l)) hunitres'
      change res.toMonoidHom (((ζ : Bˣ) ^ n : Bˣ) : B) = 1
      exact h
    have hunitpow : ((ζ : Bˣ) ^ n) ^ m = 1 := by
      calc
        ((ζ : Bˣ) ^ n) ^ m = (ζ : Bˣ) ^ (n * m) := by rw [pow_mul]
        _ = (ζ : Bˣ) ^ (m * n) := by rw [Nat.mul_comm]
        _ = ((ζ : Bˣ) ^ m) ^ n := by rw [pow_mul]
        _ = 1 := by rw [hζ.pow_eq_one, one_pow]
    have hpow :
        (((ζ : Bˣ) ^ n : Bˣ) : B) ^ m = 1 := by
      have h := congrArg (fun u : Bˣ => (u : B)) hunitpow
      simpa only [Units.val_pow_eq_pow_val, Units.val_one] using h
    have huniq :=
      chapter07_hensel_simple_root_lifts_uniquely
        res m hm hres hker 1 (by simp)
    have hzeta_pow_val : ((ζ : Bˣ) ^ n : B) = 1 := by
      exact huniq.unique ⟨hpow, hrespow⟩ ⟨by simp, by simp⟩
    have hzeta_pow : (ζ : Bˣ) ^ n = 1 := by
      apply Units.ext
      simpa only [Units.val_pow_eq_pow_val, Units.val_one] using hzeta_pow_val
    exact hζ.dvd_of_pow_eq_one n hzeta_pow

/-- The numerical relation defining the multiplicative order of `q` modulo
`m`; it avoids silently assuming that the modulus is prime. -/
def Chapter07MultiplicativeOrderModulo
    (q m d : ℕ) : Prop :=
  1 < q ∧ 0 < m ∧ 0 < d ∧ Nat.Coprime q m ∧
    m ∣ q ^ d - 1 ∧ ∀ n : ℕ, 0 < n → n < d → ¬m ∣ q ^ n - 1

/-- In a finite residue field, a primitive root generates the residue field
whose degree is the least exponent for which `m ∣ q^d - 1`. -/
theorem chapter07_finite_field_primitive_root_degree
    {k l : Type*} [Field k] [Field l] [Fintype k]
    [Algebra k l] [FiniteDimensional k l] [Finite l]
    (q m d : ℕ) (hq : Fintype.card k = q)
    (horder : Chapter07MultiplicativeOrderModulo q m d)
    (hroot : ∃ ζ : l, IsPrimitiveRoot ζ m ∧
      Algebra.adjoin k ({ζ} : Set l) = ⊤) :
    Module.finrank k l = d := by
  rcases horder with ⟨hq1, hmpos, hdpos, hcop, hmd, hminimal⟩
  obtain ⟨ζ, hζ, hζgen⟩ := hroot
  let _ : Fintype l := Fintype.ofFinite l
  have hcardl : Fintype.card l = q ^ Module.finrank k l := by
    calc
      Fintype.card l = Fintype.card k ^ Module.finrank k l :=
        Module.card_eq_pow_finrank
      _ = q ^ Module.finrank k l := by rw [hq]
  have hdiv_finrank : m ∣ q ^ Module.finrank k l - 1 := by
    have hζ0 : ζ ≠ 0 := hζ.ne_zero hmpos.ne'
    have hpow : ζ ^ (Fintype.card l - 1) = 1 :=
      FiniteField.pow_card_sub_one_eq_one ζ hζ0
    have hdiv : m ∣ Fintype.card l - 1 :=
      hζ.dvd_of_pow_eq_one (Fintype.card l - 1) hpow
    simpa [hcardl] using hdiv
  have hfinrank_ge : d ≤ Module.finrank k l := by
    by_contra hnot
    have hlt : Module.finrank k l < d := Nat.lt_of_not_ge hnot
    exact (hminimal (Module.finrank k l) Module.finrank_pos hlt) hdiv_finrank
  have hqcard : Nat.card k = q := by
    simpa only [Nat.card_eq_fintype_card] using hq
  have hpow_d : ζ ^ (q ^ d) = ζ := by
    have hqpow_pos : 0 < q ^ d := pow_pos (Nat.zero_lt_of_lt hq1) _
    have hqpow_one : 1 ≤ q ^ d := hqpow_pos
    have hsub : ζ ^ (q ^ d - 1) = 1 := by
      obtain ⟨c, hc⟩ := hmd
      rw [hc, pow_mul, hζ.pow_eq_one, one_pow]
    rw [← Nat.sub_add_cancel hqpow_one, pow_add, hsub, one_mul, pow_one]
  have hminpoly_dvd :
      minpoly k ζ ∣ X ^ (Nat.card k) ^ d - X := by
    apply minpoly.dvd k ζ
    rw [aeval_def]
    simp only [eval₂_sub, eval₂_X_pow, eval₂_X]
    rw [hqcard, hpow_d]
    simp
  have hminpoly_dvd_degree :
      (minpoly k ζ).natDegree ∣ d :=
    Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X
      (minpoly.irreducible (IsIntegral.of_finite k ζ)) hminpoly_dvd
  have hfinrank_le : Module.finrank k l ≤ d := by
    have hζgen' :
        IntermediateField.adjoin k ({ζ} : Set l) = ⊤ :=
      IntermediateField.adjoin_eq_top_of_algebra k ({ζ} : Set l) hζgen
    rw [← (Field.primitive_element_iff_minpoly_natDegree_eq k ζ).mp hζgen']
    exact Nat.le_of_dvd hdpos hminpoly_dvd_degree
  exact le_antisymm hfinrank_le hfinrank_ge

/-- The residue degree of a primitive `m`th root is the least `d` satisfying
`m ∣ q^d - 1`; the generic field-degree equality is supplied by the local
extension construction and is used to identify the ramification index. -/
theorem chapter07_primitive_root_unramified_degree
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Algebra K L] [Algebra k l] [FiniteDimensional K L]
    [FiniteDimensional k l] [Fintype k] [Finite l]
    (q m d : ℕ) (hq : Fintype.card k = q)
    (horder : Chapter07MultiplicativeOrderModulo q m d)
    (E : Chapter07FiniteLocalExtensionData K L k l)
    (hfield_degree : Module.finrank K L = d)
    (hresroot : ∃ ζ : l, IsPrimitiveRoot ζ m ∧
      Algebra.adjoin k ({ζ} : Set l) = ⊤) :
    Chapter07UnramifiedExtension E ∧
      Module.finrank k l = d := by
  have hres_degree :
      Module.finrank k l = d :=
    chapter07_finite_field_primitive_root_degree q m d hq horder hresroot
  have hram : E.ramificationIndex = 1 := by
    have hprod : E.ramificationIndex * d = d := by
      calc
        E.ramificationIndex * d =
            E.ramificationIndex * E.residueDegree := by
              rw [E.residueDegree_eq, hres_degree]
        _ = Module.finrank K L :=
          E.degree_eq_ramification_residue.symm
        _ = d := hfield_degree
    apply Nat.mul_right_cancel (horder.2.2.1)
    simpa using hprod
  refine ⟨?_, hres_degree⟩
  refine ⟨hram, ?_⟩
  let _ : PerfectField k := PerfectField.ofFinite
  intro x
  exact Algebra.IsSeparable.isSeparable k x

/-- An actual p-adic field/root extension carrying the numerical profile of
the cyclotomic construction. -/
structure Chapter07PadicCyclotomicExtension (p m d : ℕ) where
  [primeFact : Fact p.Prime]
  field : Type uC
  [fieldField : Field field]
  [fieldAlgebra : Algebra ℚ_[p] field]
  [fieldFinite : FiniteDimensional ℚ_[p] field]
  root : field
  root_primitive : IsPrimitiveRoot root m
  root_generates : Algebra.adjoin ℚ_[p] ({root} : Set field) = ⊤
  degree : Module.finrank ℚ_[p] field = d
  profile : Chapter10FiniteExtensionProfile
  profile_degree : profile.degree = d
  profile_ramificationIndex : profile.ramificationIndex = 1
  profile_residueDegree : profile.residueDegree = d
  profile_unramified : Chapter10Unramified profile
  valuation : AddValuation field (WithTop ℤ)
  valuation_extension :
    (Padic.addValuation (p := p)).IsEquiv
      (valuation.comap (algebraMap ℚ_[p] field))
  extensionData :
    Chapter10HeterogeneousExtensionData
      (Padic.addValuation (p := p)) valuation valuation_extension
  profile_realized :
    profile.ramificationIndex = extensionData.ramificationIndex ∧
      profile.residueDegree = extensionData.residueDegree
  residueField : Type uC
  [residueFieldField : Field residueField]
  [residueFieldAlgebra : Algebra (ZMod p) residueField]
  [residueFieldFinite : FiniteDimensional (ZMod p) residueField]
  residueDegree : Module.finrank (ZMod p) residueField = d
  residue_separable : ∀ x : residueField, IsSeparable (ZMod p) x
  baseResidueIdentification :
    Chapter10ResidueField (Padic.addValuation (p := p)) ≃+* ZMod p
  extensionResidueIdentification :
    Chapter10ResidueField valuation ≃+* residueField
  residueMap :
    Chapter10ResidueField (Padic.addValuation (p := p)) →+*
      Chapter10ResidueField valuation
  residueMap_is_canonical :
    letI : Valuation.HasExtension (Padic.addValuation (p := p)) valuation :=
      ⟨valuation_extension⟩
    residueMap = Chapter10ResidueFieldMap
      (Padic.addValuation (p := p)) valuation
  residueMap_compatible :
    extensionResidueIdentification.toRingHom.comp residueMap =
      (algebraMap (ZMod p) residueField).comp
        baseResidueIdentification.toRingHom

/-- The p-adic cyclotomic result quantifies the actual field and primitive root,
not just a detached numerical profile. -/
theorem chapter07_padic_prime_to_p_roots_of_unity
    {p m d : ℕ} [Fact p.Prime]
    (horder : Chapter07MultiplicativeOrderModulo p m d) :
    Nonempty (Chapter07PadicCyclotomicExtension p m d) := by
  sorry

/-- In residue characteristic `p`, the derivative of `T^p - 1` has a
non-unit `p` factor; this is the boundary with wild ramification. -/
theorem chapter07_p_power_root_derivative_is_not_a_unit
    {A : Type*} [CommRing A] (p r : ℕ)
    (hp : ¬Chapter07OrderInvertibleIn A p) (hr : 0 < r)
    (ζ : A) :
    ¬IsUnit (eval₂ (RingHom.id A) ζ
      (derivative (X ^ (p ^ r) - 1 : A[X]))) := by
  intro hunit
  rw [chapter07_derivative_power_minus_one] at hunit
  have hunit' :
      IsUnit ((p : A) ^ r * ζ ^ (p ^ r - 1)) := by
    simpa [Nat.cast_pow] using hunit
  have hp_pow : IsUnit ((p : A) ^ r) :=
    (IsUnit.mul_iff.mp hunit').1
  exact hp ((isUnit_pow_iff hr.ne').mp hp_pow)

/-! The valuation-theoretic core of the (p)-power-root warning is numerical:
once the extension has degree greater than one and residue degree one, its
profile cannot be unramified.  The derivative theorem above supplies the
root-specific obstruction; this lemma deliberately does not carry unrelated
integral-model witnesses that the conclusion does not use. -/
theorem chapter07_nontrivial_residue_degree_one_extension_is_ramified
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Algebra K L] [Algebra k l]
    [FiniteDimensional K L] [FiniteDimensional k l]
    (E : Chapter07FiniteLocalExtensionData K L k l)
    (hdegree : 1 < Module.finrank K L)
    (hresidue_degree : Module.finrank k l = 1) :
    E.ramificationIndex ≠ 1 ∧ ¬Chapter07UnramifiedExtension E := by
  have hresdeg : E.residueDegree = 1 :=
    E.residueDegree_eq.trans hresidue_degree
  have hramdegree : E.ramificationIndex = Module.finrank K L := by
    calc
      E.ramificationIndex =
          E.ramificationIndex * E.residueDegree := by rw [hresdeg, mul_one]
      _ = Module.finrank K L := E.degree_eq_ramification_residue.symm
  have hram_ne : E.ramificationIndex ≠ 1 := by
    rw [hramdegree]
    exact Nat.ne_of_gt hdegree
  exact ⟨hram_ne, fun hU => hram_ne hU.1⟩

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07
