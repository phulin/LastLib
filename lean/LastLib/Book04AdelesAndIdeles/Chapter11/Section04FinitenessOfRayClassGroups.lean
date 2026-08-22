import LastLib.Book04AdelesAndIdeles.Chapter11.Dependencies
import LastLib.Book04AdelesAndIdeles.Chapter11.Section02LocalCongruenceGroups

namespace LastLib.Book04AdelesAndIdeles.Chapter11

open NumberField
open scoped WithZero

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

private theorem chapter11_exists_finite_idele_with_components
    (g : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      (v.adicCompletion K)ˣ)
    (hg : ∀ v, g v ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units) :
    ∃ y : Chapter11FiniteIdeleGroup K,
      ∀ v, chapter11FiniteIdeleComponent K v y = g v := by
  let z : RestrictedProduct
      (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
        (v.adicCompletion K)ˣ)
      (fun v => (Submonoid.ofClass (v.adicCompletionIntegers K)).units)
      Filter.cofinite := ⟨g, Filter.Eventually.of_forall hg⟩
  refine ⟨(RestrictedProduct.unitsEquiv
      (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
      (B := fun v => v.adicCompletionIntegers K)
      (𝓕 := Filter.cofinite)).symm z, ?_⟩
  intro v
  apply Units.ext
  change ((z : ∀ v, (v.adicCompletion K)ˣ) v : v.adicCompletion K) =
    (g v : v.adicCompletion K)
  change (RestrictedProduct.unitsEquiv
      (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
      (B := fun v => v.adicCompletionIntegers K)
      (𝓕 := Filter.cofinite)
      ((RestrictedProduct.unitsEquiv
        (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
        (B := fun v => v.adicCompletionIntegers K)
        (𝓕 := Filter.cofinite)).symm z) v : v.adicCompletion K) = _
  rw [RestrictedProduct.unitsEquiv_apply]
  rfl

private theorem chapter11_integer_unit_component_is_integral
    (a : (𝓞 K)ˣ)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    chapter11FiniteGlobalComponent K
        v (Units.map (algebraMap (𝓞 K) K).toMonoidHom a) ∈
      (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
  apply (Submonoid.mem_units_iff _ _).2
  constructor
  · change ((chapter11FiniteGlobalComponent K v
      (Units.map (algebraMap (𝓞 K) K).toMonoidHom a) :
        (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈
      (v.adicCompletionIntegers K : Set (v.adicCompletion K))
    change ((algebraMap (𝓞 K) (v.adicCompletionIntegers K) (a : 𝓞 K) :
      v.adicCompletionIntegers K) : v.adicCompletion K) ∈
      (v.adicCompletionIntegers K : Set (v.adicCompletion K))
    exact (algebraMap (𝓞 K) (v.adicCompletionIntegers K) (a : 𝓞 K)).property
  · rw [← (chapter11FiniteGlobalComponent K v).map_inv]
    change ((algebraMap (𝓞 K) (v.adicCompletionIntegers K) (↑(a⁻¹) : 𝓞 K) :
      v.adicCompletionIntegers K) : v.adicCompletion K) ∈
      (v.adicCompletionIntegers K : Set (v.adicCompletion K))
    exact (algebraMap (𝓞 K) (v.adicCompletionIntegers K)
      (↑(a⁻¹) : 𝓞 K)).property

private theorem chapter11_finite_ideal_ne_top_of_support_nonempty
    (m : RayModulus K)
    (hS : m.finiteExponent.support.Nonempty) :
    m.finiteIdeal ≠ (⊤ : Ideal (𝓞 K)) := by
  classical
  obtain ⟨v, hv⟩ := hS
  have hprod_le : ∀ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
      v ∈ S →
        (∏ w ∈ S, w.asIdeal ^ m.finiteExponent w) ≤ v.asIdeal := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert w S hw ih =>
        intro hvS
        rw [Finset.prod_insert hw]
        by_cases h : v = w
        · subst w
          exact (Ideal.mul_le_left.trans
            (Ideal.pow_le_self (Finsupp.mem_support_iff.mp hv)))
        · rcases Finset.mem_insert.mp hvS with hvw | hvS
          · exact False.elim (h hvw)
          · exact (Ideal.mul_le_right.trans (ih hvS))
  intro htop
  have hle : (⊤ : Ideal (𝓞 K)) ≤ v.asIdeal := by
    rw [← htop, RayModulus.finiteIdeal]
    exact hprod_le _ hv
  exact v.2.ne_top (top_unique hle)

private noncomputable def chapter11ResidueRepresentative (m : RayModulus K)
    (r : chapter11RayResidueGroup m) : 𝓞 K := by
  classical
  by_cases hS : m.finiteExponent.support.Nonempty
  · exact Classical.choose (Ideal.Quotient.mk_surjective
      (r : 𝓞 K ⧸ m.finiteIdeal))
  · exact 1

private theorem chapter11_residue_representative_spec (m : RayModulus K)
    (r : chapter11RayResidueGroup m) :
    Ideal.Quotient.mk m.finiteIdeal
        (↑(chapter11ResidueRepresentative m r) : 𝓞 K) = r := by
  classical
  by_cases hS : m.finiteExponent.support.Nonempty
  · letI : Nontrivial (𝓞 K ⧸ m.finiteIdeal) :=
      Ideal.Quotient.nontrivial_iff.mpr
        (chapter11_finite_ideal_ne_top_of_support_nonempty m hS)
    change Ideal.Quotient.mk m.finiteIdeal
        (chapter11ResidueRepresentative m r) = r
    simpa [chapter11ResidueRepresentative, hS] using
      (Classical.choose_spec (Ideal.Quotient.mk_surjective
        (r : 𝓞 K ⧸ m.finiteIdeal)))
  · have hm : m.finiteIdeal = ⊤ := by
      have hS0 : m.finiteExponent.support = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hS
      simp [RayModulus.finiteIdeal, hS0]
    letI : Subsingleton (𝓞 K ⧸ m.finiteIdeal) := by
      rw [hm]
      infer_instance
    have hr : r = 1 := by
      apply Units.ext
      exact Subsingleton.elim _ _
    rw [hr]
    simp [chapter11ResidueRepresentative, hS, hm]

private theorem chapter11_finite_ideal_le_prime_power
    (m : RayModulus K)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hv : v ∈ m.finiteExponent.support) :
    m.finiteIdeal ≤ v.asIdeal ^ m.finiteExponent v := by
  classical
  have hprod_le : ∀ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
      v ∈ S →
        (∏ w ∈ S, w.asIdeal ^ m.finiteExponent w) ≤
          v.asIdeal ^ m.finiteExponent v := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert w S hw ih =>
        intro hvS
        rw [Finset.prod_insert hw]
        rcases Finset.mem_insert.mp hvS with hvw | hvS
        · subst w
          exact Ideal.mul_le_left
        · exact (Ideal.mul_le_right.trans (ih hvS))
  rw [RayModulus.finiteIdeal]
  exact hprod_le _ hv

private noncomputable def chapter11ResidueRepresentativeUnit
    (m : RayModulus K) (r : chapter11RayResidueGroup m) : Kˣ := by
  classical
  by_cases hS : m.finiteExponent.support.Nonempty
  · letI : Nontrivial (𝓞 K ⧸ m.finiteIdeal) :=
      Ideal.Quotient.nontrivial_iff.mpr
        (chapter11_finite_ideal_ne_top_of_support_nonempty m hS)
    let a : 𝓞 K := chapter11ResidueRepresentative m r
    exact Units.mk0 (algebraMap (𝓞 K) K a) (by
      intro hzero
      have ha : a = 0 := (IsFractionRing.injective (𝓞 K) K) (by simpa using hzero)
      have hspec : Ideal.Quotient.mk m.finiteIdeal a = r := by
        simpa [a] using chapter11_residue_representative_spec m r
      have hrzero : (r : 𝓞 K ⧸ m.finiteIdeal) = 0 := by
        rw [← hspec, ha]
        simp
      exact r.ne_zero hrzero)
  · exact Units.mk0 1 one_ne_zero

private theorem chapter11_residue_component_is_integral_unit
    (m : RayModulus K)
    (r : chapter11RayResidueGroup m)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hv : v ∈ m.finiteExponent.support) :
    chapter11FiniteGlobalComponent K v
        (chapter11ResidueRepresentativeUnit m r) ∈
      (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
  classical
  letI : Nontrivial (𝓞 K ⧸ m.finiteIdeal) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (chapter11_finite_ideal_ne_top_of_support_nonempty m ⟨v, hv⟩)
  let a : 𝓞 K := chapter11ResidueRepresentative m r
  let b : 𝓞 K := chapter11ResidueRepresentative m (r⁻¹)
  have habq : Ideal.Quotient.mk m.finiteIdeal (a * b - 1) = 0 := by
    rw [map_sub, map_mul, map_one,
      chapter11_residue_representative_spec m r,
      chapter11_residue_representative_spec m (r⁻¹)]
    simp
  have hab : a * b - 1 ∈ m.finiteIdeal :=
    (Ideal.Quotient.eq_zero_iff_mem).mp habq
  have habv : a * b - 1 ∈ v.asIdeal ^ m.finiteExponent v :=
    (chapter11_finite_ideal_le_prime_power m v hv) hab
  let A := v.adicCompletionIntegers K
  have hmap : algebraMap (𝓞 K) A (a * b - 1) ∈
      Ideal.map (algebraMap (𝓞 K) A) (v.asIdeal ^ m.finiteExponent v) :=
    Ideal.mem_map_of_mem (algebraMap (𝓞 K) A) habv
  have hmap' : algebraMap (𝓞 K) A (a * b - 1) ∈
      (IsLocalRing.maximalIdeal A) ^ m.finiteExponent v := by
    rw [Ideal.map_pow,
      ← LastLib.Book04AdelesAndIdeles.Chapter01.chapter01_completion_maximal_ideal_eq_prime_extension]
      at hmap
    exact hmap
  have hmax : algebraMap (𝓞 K) A (a * b - 1) ∈ IsLocalRing.maximalIdeal A := by
    exact (Ideal.pow_le_self (Finsupp.mem_support_iff.mp hv)) hmap'
  let z : A := algebraMap (𝓞 K) A (a * b - 1)
  have hnot : 1 + z ∉ IsLocalRing.maximalIdeal A := by
    intro hmem
    have hone : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
      have hsub := (IsLocalRing.maximalIdeal A).sub_mem hmem hmax
      simpa [z, sub_eq_add_neg, add_assoc] using hsub
    exact (IsLocalRing.notMem_maximalIdeal (R := A)).2 isUnit_one hone
  have huab : IsUnit (algebraMap (𝓞 K) A a * algebraMap (𝓞 K) A b) := by
    have hz : algebraMap (𝓞 K) A a * algebraMap (𝓞 K) A b = 1 + z := by
      simp [z, map_sub, map_mul]
    rw [hz]
    exact (IsLocalRing.notMem_maximalIdeal (R := A)).1 hnot
  have hua : IsUnit (algebraMap (𝓞 K) A a) :=
    (IsUnit.mul_iff.mp huab).1
  let ua : Aˣ := hua.unit
  have hua_val : (ua : A) = algebraMap (𝓞 K) A a := hua.unit_spec
  let ak : Kˣ := chapter11ResidueRepresentativeUnit m r
  have hS : m.finiteExponent.support.Nonempty := ⟨v, hv⟩
  have hak : (ak : K) = algebraMap (𝓞 K) K a := by
    simp [ak, chapter11ResidueRepresentativeUnit, a, hS]
  have hak0 : algebraMap (𝓞 K) K a ≠ 0 := by
    intro hzero
    exact (by
      have ha : a = 0 := (IsFractionRing.injective (𝓞 K) K) (by simpa using hzero)
      have hspec : Ideal.Quotient.mk m.finiteIdeal a = r := by
        simpa [a] using chapter11_residue_representative_spec m r
      have hrzero : (r : 𝓞 K ⧸ m.finiteIdeal) = 0 := by
        rw [← hspec, ha]
        simp
      exact r.ne_zero hrzero)
  let ak' : Kˣ := Units.mk0 (algebraMap (𝓞 K) K a) hak0
  have hak' : ak = ak' := by
    apply Units.ext
    exact hak
  have hu' : chapter11FiniteGlobalComponent K v ak' =
      Units.map A.subtype.toMonoidHom ua := by
    apply Units.ext
    change NumberField.FinitePlace.embedding v (algebraMap (𝓞 K) K a) =
      ((ua : A) : v.adicCompletion K)
    rw [NumberField.FinitePlace.embedding_apply, hua_val,
      IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
  have hu : chapter11FiniteGlobalComponent K v ak =
      Units.map A.subtype.toMonoidHom ua := by
    simpa [hak'] using hu'
  apply (Submonoid.mem_units_iff _ _).2
  constructor
  · rw [hu]
    change ((ua : A) : v.adicCompletion K) ∈
      (v.adicCompletionIntegers K : Set (v.adicCompletion K))
    exact (ua : A).property
  ·
    rw [hu, ← (Units.map A.subtype.toMonoidHom).map_inv]
    change (((ua⁻¹ : Aˣ) : A) : v.adicCompletion K) ∈
      (v.adicCompletionIntegers K : Set (v.adicCompletion K))
    exact (((ua⁻¹ : Aˣ) : A)).property

private noncomputable def chapter11ResidueFiniteComponent
    (m : RayModulus K) (r : chapter11RayResidueGroup m)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ := by
  classical
  exact if hv : v ∈ m.finiteExponent.support then
    chapter11FiniteGlobalComponent K v
      (chapter11ResidueRepresentativeUnit m r)
  else 1

private theorem chapter11_exists_residue_finite_idele
    (m : RayModulus K) (r : chapter11RayResidueGroup m) :
    ∃ y : Chapter11FiniteIdeleGroup K, ∀ v,
      chapter11FiniteIdeleComponent K v y =
        chapter11ResidueFiniteComponent m r v := by
  classical
  let g : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      (v.adicCompletion K)ˣ := fun v => chapter11ResidueFiniteComponent m r v
  have hg : ∀ v, g v ∈
      (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
    intro v
    by_cases hv : v ∈ m.finiteExponent.support
    · change chapter11ResidueFiniteComponent m r v ∈
        (Submonoid.ofClass (v.adicCompletionIntegers K)).units
      rw [chapter11ResidueFiniteComponent, dif_pos hv]
      exact chapter11_residue_component_is_integral_unit m r v hv
    · change chapter11ResidueFiniteComponent m r v ∈
        (Submonoid.ofClass (v.adicCompletionIntegers K)).units
      rw [chapter11ResidueFiniteComponent, dif_neg hv]
      exact (Submonoid.one_mem _)
  obtain ⟨y, hy⟩ := chapter11_exists_finite_idele_with_components g hg
  refine ⟨y, ?_⟩
  intro v
  rw [hy v]

private theorem chapter11_residue_representatives_multiply_is_local_unit
    (m : RayModulus K) (r₁ r₂ r₃ : chapter11RayResidueGroup m)
    (hr : r₁ * r₂ = r₃)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hv : v ∈ m.finiteExponent.support) :
    chapter11FiniteGlobalComponent K v
        (chapter11ResidueRepresentativeUnit m r₁ *
          chapter11ResidueRepresentativeUnit m r₂ *
            (chapter11ResidueRepresentativeUnit m r₃)⁻¹) ∈
      chapter11FiniteLocalUnitGroup K v (m.finiteExponent v) := by
  classical
  letI : Nontrivial (𝓞 K ⧸ m.finiteIdeal) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (chapter11_finite_ideal_ne_top_of_support_nonempty m ⟨v, hv⟩)
  let A := v.adicCompletionIntegers K
  let L := v.adicCompletion K
  let a : 𝓞 K := chapter11ResidueRepresentative m r₁
  let b : 𝓞 K := chapter11ResidueRepresentative m r₂
  let c : 𝓞 K := chapter11ResidueRepresentative m r₃
  have hq : Ideal.Quotient.mk m.finiteIdeal (a * b - c) = 0 := by
    rw [map_sub, map_mul,
      chapter11_residue_representative_spec m r₁,
      chapter11_residue_representative_spec m r₂,
      chapter11_residue_representative_spec m r₃]
    have hr' : (r₁ : 𝓞 K ⧸ m.finiteIdeal) * (r₂ : 𝓞 K ⧸ m.finiteIdeal) =
        (r₃ : 𝓞 K ⧸ m.finiteIdeal) := congrArg Units.val hr
    rw [hr']
    simp
  have hab : a * b - c ∈ m.finiteIdeal :=
    (Ideal.Quotient.eq_zero_iff_mem).mp hq
  have habv : a * b - c ∈ v.asIdeal ^ m.finiteExponent v :=
    (chapter11_finite_ideal_le_prime_power m v hv) hab
  have hmap : algebraMap (𝓞 K) A (a * b - c) ∈
      Ideal.map (algebraMap (𝓞 K) A) (v.asIdeal ^ m.finiteExponent v) :=
    Ideal.mem_map_of_mem (algebraMap (𝓞 K) A) habv
  have hmap' : algebraMap (𝓞 K) A (a * b - c) ∈
      (IsLocalRing.maximalIdeal A) ^ m.finiteExponent v := by
    rw [Ideal.map_pow,
      ← LastLib.Book04AdelesAndIdeles.Chapter01.chapter01_completion_maximal_ideal_eq_prime_extension]
      at hmap
    exact hmap
  have hunit (r : chapter11RayResidueGroup m) :
      chapter11FiniteGlobalComponent K v
          (chapter11ResidueRepresentativeUnit m r) ∈
        (Submonoid.ofClass A).units := by
    exact chapter11_residue_component_is_integral_unit m r v hv
  let ga : Lˣ := chapter11FiniteGlobalComponent K v
    (chapter11ResidueRepresentativeUnit m r₁)
  let gb : Lˣ := chapter11FiniteGlobalComponent K v
    (chapter11ResidueRepresentativeUnit m r₂)
  let gc : Lˣ := chapter11FiniteGlobalComponent K v
    (chapter11ResidueRepresentativeUnit m r₃)
  have hga := (Submonoid.mem_units_iff (Submonoid.ofClass A) ga).mp (by
    simpa [ga] using hunit r₁)
  have hgb := (Submonoid.mem_units_iff (Submonoid.ofClass A) gb).mp (by
    simpa [gb] using hunit r₂)
  have hgc := (Submonoid.mem_units_iff (Submonoid.ofClass A) gc).mp (by
    simpa [gc] using hunit r₃)
  let ua : Aˣ :=
    { val := ⟨(ga : L), hga.1⟩
      inv := ⟨((ga⁻¹ : Lˣ) : L), hga.2⟩
      val_inv := by
        apply Subtype.ext
        exact ga.val_inv
      inv_val := by
        apply Subtype.ext
        exact ga.inv_val }
  let ub : Aˣ :=
    { val := ⟨(gb : L), hgb.1⟩
      inv := ⟨((gb⁻¹ : Lˣ) : L), hgb.2⟩
      val_inv := by
        apply Subtype.ext
        exact gb.val_inv
      inv_val := by
        apply Subtype.ext
        exact gb.inv_val }
  let uc : Aˣ :=
    { val := ⟨(gc : L), hgc.1⟩
      inv := ⟨((gc⁻¹ : Lˣ) : L), hgc.2⟩
      val_inv := by
        apply Subtype.ext
        exact gc.val_inv
      inv_val := by
        apply Subtype.ext
        exact gc.inv_val }
  have hga_val : (ga : L) = algebraMap (𝓞 K) L a := by
    have hak : (chapter11ResidueRepresentativeUnit m r₁ : K) =
        algebraMap (𝓞 K) K a := by
      simp [chapter11ResidueRepresentativeUnit, a,
        show m.finiteExponent.support.Nonempty from ⟨v, hv⟩]
    change NumberField.FinitePlace.embedding v
      (chapter11ResidueRepresentativeUnit m r₁ : K) = _
    rw [hak, NumberField.FinitePlace.embedding_apply]
    have hcoe (x : K) : algebraMap K L x = (x : L) := by
      change algebraMap K L x = (x : L)
      rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
      rfl
    rw [← hcoe]
    rw [IsScalarTower.algebraMap_apply (𝓞 K) K L]
  have hgb_val : (gb : L) = algebraMap (𝓞 K) L b := by
    have hbk : (chapter11ResidueRepresentativeUnit m r₂ : K) =
        algebraMap (𝓞 K) K b := by
      simp [chapter11ResidueRepresentativeUnit, b,
        show m.finiteExponent.support.Nonempty from ⟨v, hv⟩]
    change NumberField.FinitePlace.embedding v
      (chapter11ResidueRepresentativeUnit m r₂ : K) = _
    rw [hbk, NumberField.FinitePlace.embedding_apply]
    have hcoe (x : K) : algebraMap K L x = (x : L) := by
      change algebraMap K L x = (x : L)
      rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
      rfl
    rw [← hcoe]
    rw [IsScalarTower.algebraMap_apply (𝓞 K) K L]
  have hgc_val : (gc : L) = algebraMap (𝓞 K) L c := by
    have hck : (chapter11ResidueRepresentativeUnit m r₃ : K) =
        algebraMap (𝓞 K) K c := by
      simp [chapter11ResidueRepresentativeUnit, c,
        show m.finiteExponent.support.Nonempty from ⟨v, hv⟩]
    change NumberField.FinitePlace.embedding v
      (chapter11ResidueRepresentativeUnit m r₃ : K) = _
    rw [hck, NumberField.FinitePlace.embedding_apply]
    have hcoe (x : K) : algebraMap K L x = (x : L) := by
      change algebraMap K L x = (x : L)
      rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
      rfl
    rw [← hcoe]
    rw [IsScalarTower.algebraMap_apply (𝓞 K) K L]
  have hua : (ua : A) = algebraMap (𝓞 K) A a := by
    apply Subtype.ext
    change (ga : L) = algebraMap (𝓞 K) L a
    exact hga_val
  have hub : (ub : A) = algebraMap (𝓞 K) A b := by
    apply Subtype.ext
    change (gb : L) = algebraMap (𝓞 K) L b
    exact hgb_val
  have huc : (uc : A) = algebraMap (𝓞 K) A c := by
    apply Subtype.ext
    change (gc : L) = algebraMap (𝓞 K) L c
    exact hgc_val
  have hprod :
      algebraMap (𝓞 K) A a * algebraMap (𝓞 K) A b -
        algebraMap (𝓞 K) A c ∈ (IsLocalRing.maximalIdeal A) ^
          m.finiteExponent v := by
    simpa only [map_sub, map_mul] using hmap'
  let u : Aˣ := ua * ub * uc⁻¹
  have hu : (u : A) - 1 ∈
      (IsLocalRing.maximalIdeal A) ^ m.finiteExponent v := by
    have huc0 : (uc : A) * ((uc⁻¹ : Aˣ) : A) = 1 := uc.val_inv
    rw [show (u : A) - 1 =
        ((ua : A) * (ub : A) - (uc : A)) * ((uc⁻¹ : Aˣ) : A) by
          simp only [u, Units.val_mul, Units.val_inv_eq_inv_val]
          rw [sub_mul, huc0]
          ]
    rw [hua, hub, huc]
    apply ((IsLocalRing.maximalIdeal A) ^ m.finiteExponent v).mul_mem_right
      ((uc⁻¹ : Aˣ) : A)
    exact hprod
  have hn : m.finiteExponent v ≠ 0 := Finsupp.mem_support_iff.mp hv
  have huf : u ∈ chapter11LocalUnitFiltration (A := A) (m.finiteExponent v) := by
    apply (chapter11_local_unit_positive_level_is_one_plus_an_element_of_the_power hn u).2
    exact ⟨(u : A) - 1, hu, by ring⟩
  have hua_map : Units.map A.subtype.toMonoidHom ua = ga := by
    apply Units.ext
    rfl
  have hub_map : Units.map A.subtype.toMonoidHom ub = gb := by
    apply Units.ext
    rfl
  have huc_map : Units.map A.subtype.toMonoidHom uc = gc := by
    apply Units.ext
    rfl
  refine ⟨u, huf, ?_⟩
  change Units.map A.subtype.toMonoidHom u = _
  have hright :
      chapter11FiniteGlobalComponent K v
          (chapter11ResidueRepresentativeUnit m r₁ *
            chapter11ResidueRepresentativeUnit m r₂ *
              (chapter11ResidueRepresentativeUnit m r₃)⁻¹) =
        ga * gb * gc⁻¹ := by
    simp only [map_mul, map_inv]
    rfl
  rw [hright]
  simp only [u, map_mul, map_inv, hua_map, hub_map, huc_map]

private theorem chapter11_ray_class_to_ordinary_surjective (m : RayModulus K) :
    Function.Surjective (chapter11RayClassToOrdinaryClassHom m) := by
  intro c
  refine ClassGroup.induction (R := 𝓞 K) K (fun I => ?_) c
  obtain ⟨x, hx⟩ := (chapter11CanonicalIdeleIdealMap K).surjective I
  refine ⟨chapter11RayClassProjection m x, ?_⟩
  change ClassGroup.mk K ((chapter11CanonicalIdeleIdealMap K).toIdeal x) =
    ClassGroup.mk K I
  rw [hx]

private noncomputable def chapter11SignInfiniteIdele
    (m : RayModulus K) (s : chapter11RaySignGroup m) :
    (LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09InfiniteAdele K)ˣ :=
  by
    classical
    exact (MulEquiv.piUnits).symm (fun v =>
      if hv : v ∈ m.infinitePart then
        Units.map (SignType.castHom : SignType →*₀ v.Completion).toMonoidHom
          (s ⟨v, hv⟩)
      else 1)

private noncomputable def chapter11InfiniteIdelePiUnits :
    (LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09InfiniteAdele K)ˣ ≃*
      (∀ v : NumberField.InfinitePlace K, v.Completionˣ) :=
  MulEquiv.piUnits

private theorem chapter11SignInfiniteIdele_mul
    (m : RayModulus K) (s t : chapter11RaySignGroup m) :
    chapter11SignInfiniteIdele m (s * t) =
      chapter11SignInfiniteIdele m s * chapter11SignInfiniteIdele m t := by
  classical
  let piUnits := chapter11InfiniteIdelePiUnits (K := K)
  let F0 : ∀ v : NumberField.InfinitePlace K, v.Completionˣ := fun v =>
    if hv : v ∈ m.infinitePart then
      Units.map (SignType.castHom : SignType →*₀ v.Completion).toMonoidHom
        ((s * t) ⟨v, hv⟩)
    else 1
  let F : ∀ v : NumberField.InfinitePlace K, v.Completionˣ := fun v =>
    if hv : v ∈ m.infinitePart then
      Units.map (SignType.castHom : SignType →*₀ v.Completion).toMonoidHom
        (s ⟨v, hv⟩) *
        Units.map (SignType.castHom : SignType →*₀ v.Completion).toMonoidHom
          (t ⟨v, hv⟩)
    else 1
  let G : ∀ v : NumberField.InfinitePlace K, v.Completionˣ := fun v =>
    if hv : v ∈ m.infinitePart then
      Units.map (SignType.castHom : SignType →*₀ v.Completion).toMonoidHom
        (s ⟨v, hv⟩)
    else 1
  let H : ∀ v : NumberField.InfinitePlace K, v.Completionˣ := fun v =>
    if hv : v ∈ m.infinitePart then
      Units.map (SignType.castHom : SignType →*₀ v.Completion).toMonoidHom
        (t ⟨v, hv⟩)
    else 1
  have hsF0 : piUnits (chapter11SignInfiniteIdele m (s * t)) = F0 := by
    change piUnits (piUnits.symm F0) = F0
    exact piUnits.apply_symm_apply F0
  have hsG : piUnits (chapter11SignInfiniteIdele m s) = G := by
    change piUnits (piUnits.symm G) = G
    exact piUnits.apply_symm_apply G
  have hsH : piUnits (chapter11SignInfiniteIdele m t) = H := by
    change piUnits (piUnits.symm H) = H
    exact piUnits.apply_symm_apply H
  have hFG : F = G * H := by
    funext v
    by_cases hv : v ∈ m.infinitePart
    · simp [F, G, H, hv, Pi.mul_apply]
    · simp [F, G, H, hv, Pi.mul_apply]
  have hF0 : F0 = F := by
    funext v
    by_cases hv : v ∈ m.infinitePart
    · simp [F0, F, hv]
    · simp [F0, F, hv]
  apply piUnits.injective
  rw [piUnits.map_mul, hsF0, hsG, hsH, hF0, hFG]

private theorem chapter11SignInfiniteIdele_one (m : RayModulus K) :
    chapter11SignInfiniteIdele m (1 : chapter11RaySignGroup m) = 1 := by
  classical
  let piUnits := chapter11InfiniteIdelePiUnits (K := K)
  let F : ∀ v : NumberField.InfinitePlace K, v.Completionˣ := fun v =>
    if hv : v ∈ m.infinitePart then
      Units.map (SignType.castHom : SignType →*₀ v.Completion).toMonoidHom
        ((1 : chapter11RaySignGroup m) ⟨v, hv⟩)
    else 1
  have hsF : piUnits (chapter11SignInfiniteIdele m (1 : chapter11RaySignGroup m)) = F := by
    change piUnits (piUnits.symm F) = F
    exact piUnits.apply_symm_apply F
  have hF : F = 1 := by
    funext v
    by_cases hv : v ∈ m.infinitePart
    · simp [F, hv]
    · simp [F, hv]
  apply piUnits.injective
  rw [hsF, hF, piUnits.map_one]

private theorem chapter11_residue_sign_representative_ratio_is_ray_unit
    (m : RayModulus K)
    (r₁ r₂ r₃ : chapter11RayResidueGroup m)
    (s₁ s₂ s₃ : chapter11RaySignGroup m)
    (hr : r₁ * r₂ = r₃) (hs : s₁ * s₂ = s₃)
    (y₁ y₂ y₃ : Chapter11FiniteIdeleGroup K)
    (hy₁ : ∀ v, chapter11FiniteIdeleComponent K v y₁ =
      chapter11ResidueFiniteComponent m r₁ v)
    (hy₂ : ∀ v, chapter11FiniteIdeleComponent K v y₂ =
      chapter11ResidueFiniteComponent m r₂ v)
    (hy₃ : ∀ v, chapter11FiniteIdeleComponent K v y₃ =
      chapter11ResidueFiniteComponent m r₃ v) :
    let e := LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K
    let x₁ := e.symm (chapter11SignInfiniteIdele m s₁, y₁)
    let x₂ := e.symm (chapter11SignInfiniteIdele m s₂, y₂)
    let x₃ := e.symm (chapter11SignInfiniteIdele m s₃, y₃)
    (x₁ * x₂ * x₃⁻¹) ∈ chapter11RayUnitSubgroup m := by
  classical
  let e := LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K
  let x₁ : Chapter11IdeleGroup K :=
    e.symm (chapter11SignInfiniteIdele m s₁, y₁)
  let x₂ : Chapter11IdeleGroup K :=
    e.symm (chapter11SignInfiniteIdele m s₂, y₂)
  let x₃ : Chapter11IdeleGroup K :=
    e.symm (chapter11SignInfiniteIdele m s₃, y₃)
  let w : Chapter11FiniteIdeleGroup K := y₁ * y₂ * y₃⁻¹
  have hdecomp : e (x₁ * x₂ * x₃⁻¹) =
      (chapter11SignInfiniteIdele m s₁ *
        chapter11SignInfiniteIdele m s₂ *
          (chapter11SignInfiniteIdele m s₃)⁻¹, w) := by
    dsimp [x₁, x₂, x₃, w]
    rw [e.map_mul, e.map_inv]
    simp
  have hfinite (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
      chapter11IdeleFiniteComponent K v (x₁ * x₂ * x₃⁻¹) =
        chapter11FiniteIdeleComponent K v w := by
    apply Units.ext
    exact congrArg
      (fun z => ((z.2 : Chapter11FiniteAdeleRing K) v)) hdecomp
  have hwcomp (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
      chapter11FiniteIdeleComponent K v w =
        chapter11ResidueFiniteComponent m r₁ v *
          chapter11ResidueFiniteComponent m r₂ v *
            (chapter11ResidueFiniteComponent m r₃ v)⁻¹ := by
    dsimp [w]
    rw [map_mul, map_mul, map_inv, hy₁ v, hy₂ v, hy₃ v]
  have hsign :
      chapter11SignInfiniteIdele m s₁ *
        chapter11SignInfiniteIdele m s₂ *
          (chapter11SignInfiniteIdele m s₃)⁻¹ = 1 := by
    rw [← hs, ← chapter11SignInfiniteIdele_mul m s₁ s₂]
    simp
  have hsign_component (v : NumberField.InfinitePlace K)
      (hv : v ∈ m.infinitePart) :
      chapter11RealSignComponent K v (m.infinitePart_isReal v hv)
          (x₁ * x₂ * x₃⁻¹) = 1 := by
    apply Units.ext
    change SignType.sign
      (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
        (m.infinitePart_isReal v hv)
        (((x₁ * x₂ * x₃⁻¹ : Chapter11IdeleGroup K) :
          Chapter11AdeleRing K).1 v)) = 1
    have hinf :
        (((x₁ * x₂ * x₃⁻¹ : Chapter11IdeleGroup K) :
          Chapter11AdeleRing K).1 v) = (1 : v.Completion) := by
      have hz := congrArg
        (fun z => ((z.1 : LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09InfiniteAdele K) v))
        hdecomp
      rw [hsign] at hz
      exact hz
    rw [hinf]
    simp
  constructor
  · intro v
    rw [hfinite v, hwcomp v]
    by_cases hv : v ∈ m.finiteExponent.support
    · simpa [chapter11ResidueFiniteComponent, hv] using
        chapter11_residue_representatives_multiply_is_local_unit m r₁ r₂ r₃ hr v hv
    · simp [chapter11ResidueFiniteComponent, hv]
  · intro v hv
    exact hsign_component v hv

private theorem chapter11_global_unit_of_finite_principal_mem
    (a : Kˣ)
    (ha : chapter11PrincipalIdeleHom (K := K) a ∈
      chapter11FullFiniteUnitSubgroup (K := K)) :
    ∃ u : (𝓞 K)ˣ,
      a = Units.map (algebraMap (𝓞 K) K).toMonoidHom u := by
  have hideal :
      (chapter11CanonicalIdeleIdealMap K).toIdeal
          (chapter11PrincipalIdeleHom (K := K) a) = 1 := by
    apply (MonoidHom.mem_ker).1
    rw [(chapter11CanonicalIdeleIdealMap K).kernel_eq_full_finite_units]
    exact ha
  have hprincipal : toPrincipalIdeal (𝓞 K) K a = 1 := by
    rw [← (chapter11CanonicalIdeleIdealMap K).map_principal a]
    exact hideal
  have hspan : Submodule.span (𝓞 K) {(a : K)} = 1 := by
    have hcoe := congrArg (fun I : Chapter11FractionalIdealUnitGroup K =>
        ((I : LastLib.Book04AdelesAndIdeles.Chapter08.Chapter08FractionalIdeal K) :
          Submodule (𝓞 K) K)) hprincipal
    simpa [coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton] using hcoe
  obtain ⟨u, hu⟩ := (Submodule.span_singleton_eq_one_iff).1 hspan
  refine ⟨u, ?_⟩
  apply Units.ext
  simpa using hu

private theorem chapter11_finite_global_component_of_integer_unit
    (u : (𝓞 K)ˣ) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    (chapter11FiniteGlobalComponent K v
      (Units.map (algebraMap (𝓞 K) K).toMonoidHom u) : v.adicCompletion K) =
      algebraMap (𝓞 K) (v.adicCompletion K) (u : 𝓞 K) := by
  change NumberField.FinitePlace.embedding v
      (Units.map (algebraMap (𝓞 K) K).toMonoidHom u : K) = _
  rw [show (Units.map (algebraMap (𝓞 K) K).toMonoidHom u : K) =
      algebraMap (𝓞 K) K (u : 𝓞 K) by rfl,
    NumberField.FinitePlace.embedding_apply]
  have hcoe (x : K) : algebraMap K (v.adicCompletion K) x = (x : v.adicCompletion K) := by
    change algebraMap K (v.adicCompletion K) x = (x : v.adicCompletion K)
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
    rfl
  rw [← hcoe]
  rw [IsScalarTower.algebraMap_apply (𝓞 K) K (v.adicCompletion K)]

private theorem chapter11_integer_mem_of_completion_power
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (n : ℕ) (d : 𝓞 K)
    (hd : algebraMap (𝓞 K) (v.adicCompletionIntegers K) d ∈
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n) :
    d ∈ v.asIdeal ^ n := by
  let A := v.adicCompletionIntegers K
  let L := v.adicCompletion K
  obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  let πI : A := algebraMap (𝓞 K) A π
  have hπv : Valued.v (πI : L) = WithZero.exp (-1 : ℤ) := by
    change Valued.v ((algebraMap (𝓞 K) A π : A) : L) = _
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
    change Valued.v ((π : K) : L) = _
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v,
      v.valuation_of_algebraMap, hπ]
  have hgen :
      Valuation.IsRankOneDiscrete.generator
          (Valued.v : Valuation L ℤᵐ⁰) =
        Units.mk0 (WithZero.exp (-1 : ℤ)) (by simp) := by
    apply Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_mem_range
    exact ⟨πI, hπv⟩
  have hπu : Valuation.IsUniformizer
      (Valued.v : Valuation L ℤᵐ⁰) πI := by
    change Valued.v (πI : L) =
      Valuation.IsRankOneDiscrete.generator (Valued.v : Valuation L ℤᵐ⁰)
    rw [hgen, hπv]
    simp
  change algebraMap (𝓞 K) A d ∈ (IsLocalRing.maximalIdeal A) ^ n at hd
  have hgenideal : IsLocalRing.maximalIdeal A = Ideal.span {πI} := by
    change IsLocalRing.maximalIdeal A = Ideal.span {(πI : A)}
    exact hπu.is_generator
  rw [hgenideal, Ideal.span_singleton_pow] at hd
  rcases (Ideal.mem_span_singleton.mp hd) with ⟨c, hc⟩
  have hvalc : Valued.v (c : L) ≤ 1 := c.property
  have hvald : Valued.v ((algebraMap (𝓞 K) A d : A) : L) ≤
      WithZero.exp (-(n : ℤ)) := by
    rw [hc]
    change Valued.v (πI ^ n * c : L) ≤ WithZero.exp (-(n : ℤ))
    rw [map_mul, map_pow, hπv]
    have hpow : (WithZero.exp (-1 : ℤ)) ^ n =
        WithZero.exp (-(n : ℤ)) := by
      symm
      rw [← WithZero.exp_nsmul]
      simp
    rw [hpow]
    have hmulc : WithZero.exp (-(n : ℤ)) * Valued.v (c : L) ≤
        WithZero.exp (-(n : ℤ)) * 1 :=
      mul_le_mul_of_nonneg_left hvalc
        (show 0 ≤ WithZero.exp (-(n : ℤ)) from WithZero.exp_pos.le)
    simpa using hmulc
  have hvald' : v.intValuation d ≤ WithZero.exp (-(n : ℤ)) := by
    have h := hvald
    change Valued.v ((algebraMap (𝓞 K) A d : A) : L) ≤
      WithZero.exp (-(n : ℤ)) at h
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      v.valuation_of_algebraMap] at h
    exact h
  exact (v.intValuation_le_pow_iff_mem d n).1 hvald'

private theorem chapter11_residue_eq_of_local_congruence
    (m : RayModulus K) (r : chapter11RayResidueGroup m) (u : (𝓞 K)ˣ)
    (h : ∀ v, v ∈ m.finiteExponent.support →
      chapter11FiniteGlobalComponent K v
          ((Units.map (algebraMap (𝓞 K) K).toMonoidHom u)⁻¹ *
            chapter11ResidueRepresentativeUnit m r) ∈
        chapter11FiniteLocalUnitGroup K v (m.finiteExponent v)) :
    Ideal.Quotient.mk m.finiteIdeal (u : 𝓞 K) = r := by
  classical
  by_cases hS : m.finiteExponent.support.Nonempty
  · letI : Nontrivial (𝓞 K ⧸ m.finiteIdeal) :=
      Ideal.Quotient.nontrivial_iff.mpr
        (chapter11_finite_ideal_ne_top_of_support_nonempty m hS)
    let a : 𝓞 K := chapter11ResidueRepresentative m r
    have hdiff : a - (u : 𝓞 K) ∈ m.finiteIdeal := by
      have hdiff_v : ∀ v, v ∈ m.finiteExponent.support →
          a - (u : 𝓞 K) ∈ v.asIdeal ^ m.finiteExponent v := by
        intro v hv
        let A := v.adicCompletionIntegers K
        let L := v.adicCompletion K
        rcases h v hv with ⟨w, hw, hwu⟩
        have hw' : (w : A) - 1 ∈
            (IsLocalRing.maximalIdeal A) ^ m.finiteExponent v :=
          (chapter11_local_unit_positive_level_is_one_plus_maximal_power
            (Finsupp.mem_support_iff.mp hv) w).1 hw
        have hwu : Units.map A.subtype.toMonoidHom w =
            chapter11FiniteGlobalComponent K v
              ((Units.map (algebraMap (𝓞 K) K).toMonoidHom u)⁻¹ *
                chapter11ResidueRepresentativeUnit m r) :=
          hwu
        let ua : Aˣ := Units.map (algebraMap (𝓞 K) A).toMonoidHom u
        have hua : (ua : A) = algebraMap (𝓞 K) A (u : 𝓞 K) := by
          rfl
        have hka : (chapter11ResidueRepresentativeUnit m r : K) =
            algebraMap (𝓞 K) K a := by
          simp [chapter11ResidueRepresentativeUnit, a, hS]
        have hka' :
            (chapter11FiniteGlobalComponent K v
              (chapter11ResidueRepresentativeUnit m r) : v.adicCompletion K) =
              algebraMap (𝓞 K) (v.adicCompletion K) a := by
          change NumberField.FinitePlace.embedding v
            (chapter11ResidueRepresentativeUnit m r : K) = _
          rw [hka, NumberField.FinitePlace.embedding_apply]
          change algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K a) =
            algebraMap (𝓞 K) (v.adicCompletion K) a
          simpa only [IsScalarTower.algebraMap_apply (𝓞 K) K
            (v.adicCompletion K)]
        have hku :
            (chapter11FiniteGlobalComponent K v
              (Units.map (algebraMap (𝓞 K) K).toMonoidHom u) :
                v.adicCompletion K) =
              algebraMap (𝓞 K) (v.adicCompletion K) (u : 𝓞 K) :=
          chapter11_finite_global_component_of_integer_unit u v
        have huaL : ((ua : A) : v.adicCompletion K) =
            algebraMap (𝓞 K) (v.adicCompletion K) (u : 𝓞 K) := by
          have huaC :
              ((algebraMap (𝓞 K) A (u : 𝓞 K) : A) : v.adicCompletion K) =
                ((u : 𝓞 K) : v.adicCompletion K) := by
            rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
          have hcoe (x : K) : algebraMap K (v.adicCompletion K) x =
              (x : v.adicCompletion K) := by
            change algebraMap K (v.adicCompletion K) x =
              (x : v.adicCompletion K)
            rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
            rfl
          have huAlg : algebraMap (𝓞 K) (v.adicCompletion K) (u : 𝓞 K) =
              ((u : 𝓞 K) : v.adicCompletion K) := by
            rw [← hcoe]
            rw [IsScalarTower.algebraMap_apply (𝓞 K) K (v.adicCompletion K)]
          exact huaC.trans huAlg.symm
        have huL : algebraMap (𝓞 K) (v.adicCompletion K) (u : 𝓞 K) ≠ 0 :=
          by
            intro hu
            have huK : algebraMap (𝓞 K) K (u : 𝓞 K) = 0 := by
              apply (FaithfulSMul.algebraMap_injective K (v.adicCompletion K))
              simpa only [IsScalarTower.algebraMap_apply (𝓞 K) K
                (v.adicCompletion K), map_zero] using hu
            have hu0 : (u : 𝓞 K) = 0 := by
              apply (FaithfulSMul.algebraMap_injective (𝓞 K) K)
              exact huK
            exact (Units.ne_zero u) hu0
        have hwu' := congrArg (fun z : Lˣ => (z : L)) hwu
        have hwu'' : ((w : A) : v.adicCompletion K) =
            (chapter11FiniteGlobalComponent K v
              (Units.map (algebraMap (𝓞 K) K).toMonoidHom u) :
                v.adicCompletion K)⁻¹ *
              (chapter11FiniteGlobalComponent K v
                (chapter11ResidueRepresentativeUnit m r) :
                  v.adicCompletion K) := by
          change ((w : A) : v.adicCompletion K) = _ at hwu'
          simpa only [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val] using hwu'
        have hdiffA : algebraMap (𝓞 K) A (a - (u : 𝓞 K)) ∈
            (IsLocalRing.maximalIdeal A) ^ m.finiteExponent v := by
          have hmul :
              algebraMap (𝓞 K) A (a - (u : 𝓞 K)) =
                (ua : A) * ((w : A) - 1) := by
            apply Subtype.ext
            change algebraMap (𝓞 K) (v.adicCompletion K) (a - (u : 𝓞 K)) =
              ((ua : A) : v.adicCompletion K) *
                (((w : A) : v.adicCompletion K) - 1)
            have hsub : algebraMap (𝓞 K) (v.adicCompletion K) (a - (u : 𝓞 K)) =
                algebraMap (𝓞 K) (v.adicCompletion K) a -
                  algebraMap (𝓞 K) (v.adicCompletion K) (u : 𝓞 K) :=
              map_sub (algebraMap (𝓞 K) (v.adicCompletion K)) a (u : 𝓞 K)
            rw [hsub, huaL, hwu'', hku, hka']
            rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ huL, one_mul, mul_one]
          rw [hmul]
          simpa [mul_comm] using
            (((IsLocalRing.maximalIdeal A) ^ m.finiteExponent v).mul_mem_right
              (ua : A) hw')
        exact chapter11_integer_mem_of_completion_power v
          (m.finiteExponent v) (a - (u : 𝓞 K)) hdiffA
      have hmem_inf : a - (u : 𝓞 K) ∈
          m.finiteExponent.support.inf
            (fun v => v.asIdeal ^ m.finiteExponent v) := by
        rw [Finset.inf_eq_iInf]
        exact (Ideal.mem_iInf).2 fun v => (Ideal.mem_iInf).2 fun hv =>
          hdiff_v v hv
      rw [RayModulus.finiteIdeal]
      rw [← IsDedekindDomain.HeightOneSpectrum.inf_pow_eq_prod
        m.finiteExponent.support (fun v => m.finiteExponent v)
        (fun v => v) (by
          intro v hv w hw hne
          exact hne)]
      exact hmem_inf
    have hzero : Ideal.Quotient.mk m.finiteIdeal (a - (u : 𝓞 K)) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).2 hdiff
    have hqa : Ideal.Quotient.mk m.finiteIdeal (u : 𝓞 K) =
        Ideal.Quotient.mk m.finiteIdeal a := by
      rw [map_sub] at hzero
      exact (sub_eq_zero.mp hzero).symm
    change Ideal.Quotient.mk m.finiteIdeal (u : 𝓞 K) = (r : 𝓞 K ⧸ m.finiteIdeal)
    rw [hqa]
    exact chapter11_residue_representative_spec m r
  · have hm : m.finiteIdeal = ⊤ := by
      have hS0 : m.finiteExponent.support = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hS
      simp [RayModulus.finiteIdeal, hS0]
    letI : Subsingleton (𝓞 K ⧸ m.finiteIdeal) := by
      rw [hm]
      infer_instance
    change Ideal.Quotient.mk m.finiteIdeal (u : 𝓞 K) = (r : 𝓞 K ⧸ m.finiteIdeal)
    exact Subsingleton.elim _ _

/-! ## 11.4 Finiteness of ray class groups -/

theorem chapter11_exists_residue_sign_to_ray_class_hom (m : RayModulus K) :
    ∃ f : chapter11RayResidueSignGroup m →* chapter11RayClassGroup m,
      Function.MulExact (chapter11GlobalUnitResidueSignHom m) f ∧
          Function.MulExact f (chapter11RayClassToOrdinaryClassHom m) ∧
            Function.Surjective (chapter11RayClassToOrdinaryClassHom m) := by
  classical
  let finiteRepresentative : chapter11RayResidueGroup m →
      Chapter11FiniteIdeleGroup K := fun r =>
    Classical.choose (chapter11_exists_residue_finite_idele m r)
  have finiteRepresentative_spec (r : chapter11RayResidueGroup m) (v) :
      chapter11FiniteIdeleComponent K v (finiteRepresentative r) =
        chapter11ResidueFiniteComponent m r v :=
    Classical.choose_spec (chapter11_exists_residue_finite_idele m r) v
  let e := LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K
  let representative : chapter11RayResidueSignGroup m → Chapter11IdeleGroup K :=
    fun z => e.symm (chapter11SignInfiniteIdele m z.2, finiteRepresentative z.1)
  have representative_ratio (z₁ z₂ : chapter11RayResidueSignGroup m) :
      representative z₁ * representative z₂ *
          (representative (z₁ * z₂))⁻¹ ∈ chapter11RayUnitSubgroup m := by
    dsimp [representative]
    apply chapter11_residue_sign_representative_ratio_is_ray_unit m
      z₁.1 z₂.1 (z₁ * z₂).1 z₁.2 z₂.2 (z₁ * z₂).2
      (by rfl) (by rfl)
      (finiteRepresentative z₁.1) (finiteRepresentative z₂.1)
        (finiteRepresentative (z₁ * z₂).1)
      (finiteRepresentative_spec z₁.1) (finiteRepresentative_spec z₂.1)
        (finiteRepresentative_spec (z₁ * z₂).1)
  have representative_one :
      representative (1 : chapter11RayResidueSignGroup m) ∈
        chapter11PrincipalIdeleSubgroup (K := K) ⊔ chapter11RayUnitSubgroup m := by
    have h := chapter11_residue_sign_representative_ratio_is_ray_unit m
      (1 : chapter11RayResidueGroup m) 1 1
      (1 : chapter11RaySignGroup m) 1 1 (by simp) (by simp)
      (finiteRepresentative 1) (finiteRepresentative 1) (finiteRepresentative 1)
      (finiteRepresentative_spec 1) (finiteRepresentative_spec 1)
        (finiteRepresentative_spec 1)
    exact Subgroup.mem_sup_right (by simpa [representative] using h)
  let f : chapter11RayResidueSignGroup m →* chapter11RayClassGroup m :=
    { toFun := fun z => chapter11RayClassProjection m (representative z)
      map_one' := by
        change QuotientGroup.mk'
          (chapter11PrincipalIdeleSubgroup (K := K) ⊔ chapter11RayUnitSubgroup m)
          (representative 1) = 1
        exact (QuotientGroup.eq_one_iff _).2 representative_one
      map_mul' := by
        intro z₁ z₂
        symm
        change chapter11RayClassProjection m (representative z₁) *
            chapter11RayClassProjection m (representative z₂) =
          chapter11RayClassProjection m (representative (z₁ * z₂))
        rw [← (chapter11RayClassProjection m).map_mul]
        apply (QuotientGroup.mk'_eq_mk'
          (chapter11PrincipalIdeleSubgroup (K := K) ⊔ chapter11RayUnitSubgroup m)).2
        let q := representative z₁ * representative z₂
        let r := representative (z₁ * z₂)
        have hq : q * r⁻¹ ∈ chapter11RayUnitSubgroup m := by
          simpa [q, r] using representative_ratio z₁ z₂
        have hz : q⁻¹ * r ∈
            chapter11PrincipalIdeleSubgroup (K := K) ⊔ chapter11RayUnitSubgroup m :=
          by
            have hqr : q⁻¹ * r = (q * r⁻¹)⁻¹ := by
              calc
                q⁻¹ * r = r * q⁻¹ := mul_comm _ _
                _ = (r⁻¹)⁻¹ * q⁻¹ := by rw [inv_inv]
                _ = (q * r⁻¹)⁻¹ := (mul_inv_rev q (r⁻¹)).symm
            exact Subgroup.mem_sup_right
              (by
                rw [hqr]
                exact (chapter11RayUnitSubgroup m).inv_mem hq)
        refine ⟨q⁻¹ * r, hz, ?_⟩
        rw [← mul_assoc]
        change q * q⁻¹ * r = r
        rw [mul_inv_cancel, one_mul] }
  sorry

noncomputable def chapter11ResidueSignToRayClassHom (m : RayModulus K) :
    chapter11RayResidueSignGroup m →* chapter11RayClassGroup m :=
  Classical.choose (chapter11_exists_residue_sign_to_ray_class_hom m)

theorem chapter11_ray_class_residue_sign_exact_sequence (m : RayModulus K) :
    Function.MulExact (chapter11GlobalUnitResidueSignHom m)
        (chapter11ResidueSignToRayClassHom m) ∧
      Function.MulExact (chapter11ResidueSignToRayClassHom m)
        (chapter11RayClassToOrdinaryClassHom m) ∧
      Function.Surjective (chapter11RayClassToOrdinaryClassHom m) := by
  exact Classical.choose_spec (chapter11_exists_residue_sign_to_ray_class_hom m)

/- The first arrow is deliberately only a homomorphism.  Its kernel is the
global-unit congruence subgroup, so no injectivity claim is made. -/

theorem chapter11_ray_residue_group_is_finite (m : RayModulus K) :
    Finite (chapter11RayResidueGroup m) := by
  have hI : m.finiteIdeal ≠ (⊥ : Ideal (𝓞 K)) := by
    classical
    have hprod : ∀ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
        (∀ v ∈ S, v.asIdeal ^ m.finiteExponent v ≠ (⊥ : Ideal (𝓞 K))) →
          (∏ v ∈ S, v.asIdeal ^ m.finiteExponent v) ≠ (⊥ : Ideal (𝓞 K)) := by
      intro S
      induction S using Finset.induction_on with
      | empty => simp
      | @insert v S hv ih =>
          intro hmem hzero
          rw [Finset.prod_insert hv, Ideal.mul_eq_bot] at hzero
          rcases hzero with hzero | hzero
          · exact (hmem v (Finset.mem_insert_self v S)) hzero
          · exact ih (fun w hw => hmem w (Finset.mem_insert_of_mem hw)) hzero
    rw [RayModulus.finiteIdeal]
    apply hprod
    intro v hv
    intro h
    exact v.ne_bot ((Ideal.pow_eq_bot (Finsupp.mem_support_iff.mp hv)).mp h)
  have hnorm : Ideal.absNorm m.finiteIdeal ≠ 0 := by
    intro h
    exact hI (Ideal.absNorm_eq_zero_iff.mp h)
  letI : Finite (𝓞 K ⧸ m.finiteIdeal) :=
    (Ideal.absNorm_ne_zero_iff m.finiteIdeal).mp hnorm
  infer_instance

theorem chapter11_ray_sign_group_is_finite (m : RayModulus K) :
    Finite (chapter11RaySignGroup m) := by
  infer_instance

theorem chapter11_ray_class_group_is_finite (m : RayModulus K) :
    Finite (chapter11RayClassGroup m) := by
  letI : Finite (chapter11RayResidueGroup m) :=
    chapter11_ray_residue_group_is_finite m
  letI : Finite (chapter11RaySignGroup m) :=
    chapter11_ray_sign_group_is_finite m
  letI : Finite (chapter11RayResidueSignGroup m) := by infer_instance
  letI : Finite ((chapter11ResidueSignToRayClassHom m).range) :=
    Finite.of_surjective
      (fun z : chapter11RayResidueSignGroup m =>
        ⟨chapter11ResidueSignToRayClassHom m z, ⟨z, rfl⟩⟩) (by
          rintro ⟨y, z, rfl⟩
          exact ⟨z, rfl⟩)
  have hker :
      (chapter11RayClassToOrdinaryClassHom m).ker =
        (chapter11ResidueSignToRayClassHom m).range := by
    exact (MonoidHom.mulExact_iff.mp
      (chapter11_ray_class_residue_sign_exact_sequence m).2.1)
  apply (MonoidHom.finite_iff_finite_ker_range
    (chapter11RayClassToOrdinaryClassHom m)).2
  constructor
  · rw [hker]
    infer_instance
  · infer_instance

noncomputable instance chapter11_ray_class_group_fintype (m : RayModulus K) :
    Fintype (chapter11RayClassGroup m) := by
  letI : Finite (chapter11RayClassGroup m) := chapter11_ray_class_group_is_finite m
  exact Fintype.ofFinite _

theorem chapter11_ray_class_group_is_finite_index_over_ordinary_class_group
    (m : RayModulus K) :
    Finite (chapter11RayResidueSignGroup m) ∧
      Finite (Chapter11OrdinaryClassGroup K) ∧
      Function.Surjective (chapter11RayClassToOrdinaryClassHom m) := by
  letI : Finite (chapter11RayResidueGroup m) :=
    chapter11_ray_residue_group_is_finite m
  letI : Finite (chapter11RaySignGroup m) :=
    chapter11_ray_sign_group_is_finite m
  refine ⟨inferInstance, inferInstance, chapter11_ray_class_to_ordinary_surjective m⟩

end
