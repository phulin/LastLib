import LastLib.Book04AdelesAndIdeles.Chapter11.Dependencies
import LastLib.Book04AdelesAndIdeles.Chapter11.Section02LocalCongruenceGroups
import LastLib.Book04AdelesAndIdeles.Chapter01.Section04Approximation
import LastLib.Book04AdelesAndIdeles.Chapter05.Section01TheDiagonalEmbedding

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

private theorem chapter11_completion_mem_of_valuation_le_pow
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (z : v.adicCompletion K)
    (hz : Valued.v z ≤ WithZero.exp (-(n : ℤ))) :
    ∃ zA : v.adicCompletionIntegers K,
      (zA : v.adicCompletion K) = z ∧
        zA ∈ (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n := by
  change ∃ zA : Valued.v.valuationSubring,
    zA.1 = z ∧
      zA ∈ (IsLocalRing.maximalIdeal Valued.v.valuationSubring) ^ n
  have hzle : Valued.v z ≤ 1 := by
    calc
      Valued.v z ≤ WithZero.exp (-(n : ℤ)) := hz
      _ ≤ WithZero.exp (0 : ℤ) := by
        rw [WithZero.exp_le_exp]
        omega
      _ = 1 := by simp
  have hzA : z ∈ Valued.v.valuationSubring := by
    exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
      (𝓞 K) K v).2 hzle
  let zA : Valued.v.valuationSubring := ⟨z, hzA⟩
  obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  let πI : Valued.v.valuationSubring := algebraMap (𝓞 K)
      (v.adicCompletionIntegers K) π
  have hπv : Valued.v (πI : v.adicCompletion K) =
      WithZero.exp (-1 : ℤ) := by
    change Valued.v ((algebraMap (𝓞 K) (v.adicCompletionIntegers K) π :
      v.adicCompletionIntegers K) : v.adicCompletion K) = _
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
    change Valued.v ((π : K) : v.adicCompletion K) = _
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v,
      v.valuation_of_algebraMap, hπ]
  have hgen :
      Valuation.IsRankOneDiscrete.generator
          (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) =
        Units.mk0 (WithZero.exp (-1 : ℤ)) (by simp) := by
    apply Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_mem_range
    exact ⟨πI, hπv⟩
  have hπu : Valuation.IsUniformizer
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) πI := by
    change Valued.v (πI : v.adicCompletion K) =
      Valuation.IsRankOneDiscrete.generator
        (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
    rw [hgen, hπv]
    simp
  let πU : Valuation.Uniformizer
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) := ⟨πI, hπu⟩
  by_cases hz0 : zA = 0
  · refine ⟨zA, ?_, ?_⟩
    · rfl
    · simp [hz0]
  · obtain ⟨k, u, hzu⟩ := Valuation.exists_pow_Uniformizer hz0 πU
    have huval : Valued.v (u : v.adicCompletion K) = 1 := by
      exact (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).1
        u.isUnit
    have hvz : Valued.v z = WithZero.exp (-(k : ℤ)) := by
      have hzuL : z = (πI : v.adicCompletion K) ^ k *
          (u : v.adicCompletion K) := by
        change z = _
        simpa using hzu
      rw [hzuL, map_mul, map_pow, hπv, huval]
      rw [← WithZero.exp_nsmul]
      simp
    have hkn : n ≤ k := by
      rw [hvz] at hz
      rw [WithZero.exp_le_exp] at hz
      omega
    have hpow :
        (IsLocalRing.maximalIdeal Valued.v.valuationSubring) ^ n =
          Ideal.span {πI ^ n} := by
      rw [← Ideal.span_singleton_pow, hπu.is_generator]
    refine ⟨zA, ?_, ?_⟩
    · rfl
    · rw [hpow, Ideal.mem_span_singleton]
      refine ⟨πI ^ (k - n) * (u : Valued.v.valuationSubring), ?_⟩
      calc
        zA = πI ^ k * (u : Valued.v.valuationSubring) := by
          apply Subtype.ext
          change z = _
          simpa using hzu
        _ = πI ^ (n + (k - n)) * (u : Valued.v.valuationSubring) := by
          rw [Nat.add_sub_of_le hkn]
        _ = πI ^ n * (πI ^ (k - n) * (u : Valued.v.valuationSubring)) := by
          rw [pow_add, mul_assoc]

private theorem chapter11_finite_local_unit_of_close
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (g a : (v.adicCompletion K)ˣ)
    (ga aa : (v.adicCompletionIntegers K)ˣ)
    (hga : Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom ga = g)
    (haa : Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom aa = a)
    (hclose : Valued.v ((g : v.adicCompletion K) - (a : v.adicCompletion K)) ≤
      WithZero.exp (-(n : ℤ))) :
    g * a⁻¹ ∈ chapter11FiniteLocalUnitGroup K v n := by
  let A := v.adicCompletionIntegers K
  let w : Aˣ := ga * aa⁻¹
  have hwmap : Units.map A.subtype.toMonoidHom w = g * a⁻¹ := by
    rw [map_mul, map_inv, hga, haa]
  change g * a⁻¹ ∈
    (chapter11LocalUnitFiltration (A := A) n).map
      (Units.map A.subtype.toMonoidHom)
  refine ⟨w, ?_, hwmap⟩
  by_cases hn : n = 0
  · rw [hn, chapter11LocalUnitFiltration_zero]
    simp
  have haa_val : Valued.v (a : v.adicCompletion K) = 1 := by
    have haa_val' : Valued.v
        (Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom aa :
          v.adicCompletion K) = 1 :=
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).1
        aa.isUnit
    rw [haa] at haa_val'
    exact haa_val'
  let z : v.adicCompletion K :=
    (a : v.adicCompletion K)⁻¹ *
      ((g : v.adicCompletion K) - (a : v.adicCompletion K))
  have hz : Valued.v z ≤ WithZero.exp (-(n : ℤ)) := by
    dsimp [z]
    rw [map_mul, map_inv₀, haa_val, inv_one, one_mul]
    exact hclose
  obtain ⟨zA, hzA, hzpow⟩ := chapter11_completion_mem_of_valuation_le_pow v n z hz
  have hga_val_eq : (ga : v.adicCompletion K) = (g : v.adicCompletion K) := by
    simpa using congrArg Units.val hga
  have haa_val_eq : (aa : v.adicCompletion K) = (a : v.adicCompletion K) := by
    simpa using congrArg Units.val haa
  have haa_inv_eq : ((aa⁻¹ : Aˣ) : v.adicCompletion K) =
      (a : v.adicCompletion K)⁻¹ := by
    have haa_inv_unit : Units.map
        (v.adicCompletionIntegers K).subtype.toMonoidHom (aa⁻¹) = a⁻¹ := by
      rw [map_inv, haa]
    have hmap_val (x : Aˣ) :
        ((Units.map A.subtype.toMonoidHom x : (v.adicCompletion K)ˣ) :
          v.adicCompletion K) = (x : v.adicCompletion K) := by
      rfl
    calc
      ((aa⁻¹ : Aˣ) : v.adicCompletion K) =
          ((Units.map A.subtype.toMonoidHom (aa⁻¹) :
            (v.adicCompletion K)ˣ) : v.adicCompletion K) :=
        (hmap_val (aa⁻¹)).symm
      _ = ((a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) :=
        congrArg Units.val haa_inv_unit
      _ = (a : v.adicCompletion K)⁻¹ := Units.val_inv_eq_inv_val a
  have hwsub : (w : A) - 1 = zA := by
    apply Subtype.ext
    dsimp [w]
    change ((ga : v.adicCompletion K) *
      ((aa⁻¹ : Aˣ) : v.adicCompletion K) - 1) = zA.1
    rw [hga_val_eq, haa_inv_eq]
    rw [hzA]
    dsimp [z]
    field_simp [Units.ne_zero a]
  apply (chapter11_local_unit_positive_level_is_one_plus_an_element_of_the_power hn w).2
  refine ⟨zA, hzpow, ?_⟩
  calc
    (w : A) = ((w : A) - 1) + 1 := by ring
    _ = zA + 1 := by rw [hwsub]
    _ = 1 + zA := by ring

private theorem chapter11_finite_local_unit_of_integer_congruence
    (m : RayModulus K) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hv : v ∈ m.finiteExponent.support) (u : (𝓞 K)ˣ)
    (r : chapter11RayResidueGroup m)
    (hdiff : (u : 𝓞 K) - chapter11ResidueRepresentative m r ∈
      v.asIdeal ^ m.finiteExponent v) :
    chapter11FiniteGlobalComponent K v
        ((Units.map (algebraMap (𝓞 K) K).toMonoidHom u)⁻¹ *
          chapter11ResidueRepresentativeUnit m r) ∈
      chapter11FiniteLocalUnitGroup K v (m.finiteExponent v) := by
  let A := v.adicCompletionIntegers K
  let L := v.adicCompletion K
  let g : Lˣ := chapter11FiniteGlobalComponent K v
    (Units.map (algebraMap (𝓞 K) K).toMonoidHom u)
  let a : Lˣ := chapter11FiniteGlobalComponent K v
    (chapter11ResidueRepresentativeUnit m r)
  let ga : Aˣ := Units.map (algebraMap (𝓞 K) A).toMonoidHom u
  have hga : Units.map A.subtype.toMonoidHom ga = g := by
    apply Units.ext
    change algebraMap (𝓞 K) L (u : 𝓞 K) = (g : L)
    exact (chapter11_finite_global_component_of_integer_unit u v).symm
  have haunit : a ∈ (Submonoid.ofClass A).units := by
    exact chapter11_residue_component_is_integral_unit m r v hv
  rcases (Submonoid.mem_units_iff (Submonoid.ofClass A) a).mp haunit with
    ⟨ha, hainv⟩
  let aa : Aˣ :=
    { val := ⟨(a : L), ha⟩
      inv := ⟨((a⁻¹ : Lˣ) : L), hainv⟩
      val_inv := by
        apply Subtype.ext
        exact a.val_inv
      inv_val := by
        apply Subtype.ext
        exact a.inv_val }
  have haa : Units.map A.subtype.toMonoidHom aa = a := by
    apply Units.ext
    rfl
  have haK : (chapter11ResidueRepresentativeUnit m r : K) =
      algebraMap (𝓞 K) K (chapter11ResidueRepresentative m r) := by
    simp [chapter11ResidueRepresentativeUnit,
      show m.finiteExponent.support.Nonempty from ⟨v, hv⟩]
  have haa_val : (a : L) = algebraMap (𝓞 K) L
      (chapter11ResidueRepresentative m r) := by
    change NumberField.FinitePlace.embedding v
        (chapter11ResidueRepresentativeUnit m r : K) = _
    rw [haK, NumberField.FinitePlace.embedding_apply]
    change algebraMap K L
        (algebraMap (𝓞 K) K (chapter11ResidueRepresentative m r)) = _
    simpa only [IsScalarTower.algebraMap_apply (𝓞 K) K L]
  have hclose : Valued.v ((g : L) - (a : L)) ≤
      WithZero.exp (-(m.finiteExponent v : ℤ)) := by
    have hval := (v.intValuation_le_pow_iff_mem
      ((u : 𝓞 K) - chapter11ResidueRepresentative m r)
      (m.finiteExponent v)).2 hdiff
    rw [show (g : L) = algebraMap (𝓞 K) L (u : 𝓞 K) by
      exact chapter11_finite_global_component_of_integer_unit u v,
      haa_val]
    have hcoe (x : K) : algebraMap K L x = (x : L) := by
      change algebraMap K L x = (x : L)
      rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
      rfl
    have hmap : algebraMap (𝓞 K) L
          ((u : 𝓞 K) - chapter11ResidueRepresentative m r) =
        ((((u : 𝓞 K) - chapter11ResidueRepresentative m r : 𝓞 K) : K) : L) := by
      rw [← hcoe, IsScalarTower.algebraMap_apply (𝓞 K) K L]
    rw [← map_sub (algebraMap (𝓞 K) L), hmap,
      LastLib.Book04AdelesAndIdeles.Chapter01.chapter01_completion_valuation_agrees_with_global K v
        (((u : 𝓞 K) - chapter11ResidueRepresentative m r : 𝓞 K) : K)]
    calc
      v.valuation K (((u : 𝓞 K) - chapter11ResidueRepresentative m r : 𝓞 K) : K) =
          v.intValuation ((u : 𝓞 K) - chapter11ResidueRepresentative m r) :=
        v.valuation_of_algebraMap _
      _ ≤ _ := hval
  have hlocal := chapter11_finite_local_unit_of_close v (m.finiteExponent v)
    g a ga aa hga haa hclose
  have hlocal_inv :=
    (chapter11FiniteLocalUnitGroup K v (m.finiteExponent v)).inv_mem hlocal
  simpa [g, a, map_mul, map_inv, mul_comm] using hlocal_inv

private theorem chapter11_finite_global_component_of_integer_unit_mem_units
    (u : (𝓞 K)ˣ) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    chapter11FiniteGlobalComponent K v
        (Units.map (algebraMap (𝓞 K) K).toMonoidHom u) ∈
      (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
  let A := v.adicCompletionIntegers K
  let ga : Aˣ := Units.map (algebraMap (𝓞 K) A).toMonoidHom u
  have hga : Units.map A.subtype.toMonoidHom ga =
      chapter11FiniteGlobalComponent K v
        (Units.map (algebraMap (𝓞 K) K).toMonoidHom u) := by
    apply Units.ext
    change algebraMap (𝓞 K) (v.adicCompletion K) (u : 𝓞 K) = _
    exact (chapter11_finite_global_component_of_integer_unit u v).symm
  rw [← hga]
  apply (Submonoid.mem_units_iff (Submonoid.ofClass A) _).2
  constructor
  · exact ga.1.property
  · exact ga⁻¹.1.property

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
  have representative_sign_component : ∀ (z : chapter11RayResidueSignGroup m)
      (v : NumberField.InfinitePlace K) (hv : v ∈ m.infinitePart),
      chapter11RealSignComponent K v (m.infinitePart_isReal v hv)
          (representative z) = z.2 ⟨v, hv⟩ := by
    intro z v hv
    have hrepdecomp : e (representative z) =
        (chapter11SignInfiniteIdele m z.2, finiteRepresentative z.1) := by
      dsimp [representative]
      exact e.apply_symm_apply _
    have hrepinfv :
        ((representative z : Chapter11AdeleRing K).1) v =
          ((chapter11SignInfiniteIdele m z.2 :
            LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09InfiniteAdele K) v) := by
      exact congrArg
        (fun w : LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09InfiniteAdele K => w v)
        (congrArg
          (fun w => (w.1 :
            LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09InfiniteAdele K)) hrepdecomp)
    apply Units.ext
    change SignType.sign
        (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
          (m.infinitePart_isReal v hv)
          (((representative z : Chapter11AdeleRing K).1) v)) = _
    rw [hrepinfv]
    dsimp [chapter11SignInfiniteIdele]
    have hcases : (z.2 ⟨v, hv⟩ : SignType) = -1 ∨
        (z.2 ⟨v, hv⟩ : SignType) = 1 := by
      rcases SignType.trichotomy (z.2 ⟨v, hv⟩ : SignType) with hneg | hzero | hpos
      · exact Or.inl hneg
      · exact False.elim ((z.2 ⟨v, hv⟩).ne_zero hzero)
      · exact Or.inr hpos
    rcases hcases with hneg | hpos
    · simp [hneg, hv, WithAbs.equiv,
        NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe]
    · simp [hpos, hv, WithAbs.equiv,
        NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe]
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
  refine ⟨f, ?_⟩
  have hunit_to_local_zero (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
      (x : (v.adicCompletion K)ˣ)
      (hx : x ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units) :
      x ∈ chapter11FiniteLocalUnitGroup K v 0 := by
    rw [chapter11FiniteLocalUnitGroup_zero]
    have hval : Valued.v (x : v.adicCompletion K) = 1 :=
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one).1 hx
    have hmem : x ∈ Valued.v.valuationSubring.unitGroup :=
      (Valuation.mem_unitGroup_iff (v.adicCompletion K) (Valued.v) _).2 hval
    simpa only [IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers] using hmem
  constructor
  · change ∀ z, f z = 1 ↔
      z ∈ Set.range (chapter11GlobalUnitResidueSignHom m)
    intro z
    constructor
    · intro hz
      change QuotientGroup.mk'
        (chapter11PrincipalIdeleSubgroup (K := K) ⊔ chapter11RayUnitSubgroup m)
          (representative z) = 1 at hz
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hz
      rcases Subgroup.mem_sup.mp hz with ⟨p, hp, u, hu, hpu⟩
      rcases hp with ⟨a, rfl⟩
      have hrepcomp (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
          chapter11IdeleFiniteComponent K v (representative z) =
            chapter11FiniteIdeleComponent K v (finiteRepresentative z.1) := by
        rfl
      have hrep_full : representative z ∈ chapter11FullFiniteUnitSubgroup := by
        change (∀ v, chapter11IdeleFiniteComponent K v (representative z) ∈
          chapter11FiniteLocalUnitGroup K v 0) ∧ _
        constructor
        · intro v
          rw [hrepcomp v, finiteRepresentative_spec z.1 v]
          by_cases hv : v ∈ m.finiteExponent.support
          · rw [chapter11ResidueFiniteComponent, dif_pos hv]
            exact hunit_to_local_zero v _
              (chapter11_residue_component_is_integral_unit m z.1 v hv)
          · rw [chapter11ResidueFiniteComponent, dif_neg hv]
            exact (chapter11FiniteLocalUnitGroup K v 0).one_mem
        · simp [RayModulus.trivial]
      have hu_full : (u : Chapter11IdeleGroup K) ∈
          chapter11FullFiniteUnitSubgroup := by
        change (∀ v, chapter11IdeleFiniteComponent K v (u : Chapter11IdeleGroup K) ∈
          chapter11FiniteLocalUnitGroup K v 0) ∧ _
        constructor
        · intro v
          rcases hu.1 v with ⟨w, hw, hwu⟩
          refine ⟨w, ?_, hwu⟩
          exact chapter11LocalUnitFiltration_antitone (Nat.zero_le _) hw
        · simp [RayModulus.trivial]
      have hprincipal_full : chapter11PrincipalIdeleHom (K := K) a ∈
          chapter11FullFiniteUnitSubgroup := by
        have hsolve : chapter11PrincipalIdeleHom (K := K) a =
            representative z * (u : Chapter11IdeleGroup K)⁻¹ := by
          rw [← hpu]
          simp [mul_assoc]
        rw [hsolve]
        exact chapter11FullFiniteUnitSubgroup.mul_mem hrep_full
          (chapter11FullFiniteUnitSubgroup.inv_mem hu_full)
      obtain ⟨uo, hao⟩ := chapter11_global_unit_of_finite_principal_mem a hprincipal_full
      have hsolve : chapter11PrincipalIdeleHom (K := K)
          (Units.map (algebraMap (𝓞 K) K).toMonoidHom uo)⁻¹ *
            representative z = (u : Chapter11IdeleGroup K) := by
        have ha' : chapter11PrincipalIdeleHom (K := K) a =
            chapter11PrincipalIdeleHom (K := K)
              (Units.map (algebraMap (𝓞 K) K).toMonoidHom uo) := by
          rw [hao]
        calc
          chapter11PrincipalIdeleHom (K := K)
              (Units.map (algebraMap (𝓞 K) K).toMonoidHom uo)⁻¹ *
              representative z =
              (chapter11PrincipalIdeleHom (K := K) a)⁻¹ * representative z := by
                have hainv := congrArg (fun q : Chapter11IdeleGroup K => q⁻¹) ha'
                congr 1
                exact hainv.symm
          _ = (u : Chapter11IdeleGroup K) := by
            rw [← hpu]
            simp [mul_assoc]
      have hlocal : ∀ v, v ∈ m.finiteExponent.support →
          chapter11FiniteGlobalComponent K v
              ((Units.map (algebraMap (𝓞 K) K).toMonoidHom uo)⁻¹ *
                chapter11ResidueRepresentativeUnit m z.1) ∈
              chapter11FiniteLocalUnitGroup K v (m.finiteExponent v) := by
        intro v hv
        have hcomp := congrArg (chapter11IdeleFiniteComponent K v) hsolve
        have hrepcomp' : chapter11IdeleFiniteComponent K v (representative z) =
            chapter11FiniteGlobalComponent K v
              (chapter11ResidueRepresentativeUnit m z.1) := by
          rw [hrepcomp v, finiteRepresentative_spec z.1 v]
          rw [chapter11ResidueFiniteComponent, dif_pos hv]
        rw [map_mul] at hcomp
        change chapter11FiniteGlobalComponent K v
            ((Units.map (algebraMap (𝓞 K) K).toMonoidHom uo))⁻¹ *
          chapter11IdeleFiniteComponent K v (representative z) =
            chapter11IdeleFiniteComponent K v (u : Chapter11IdeleGroup K) at hcomp
        rw [hrepcomp'] at hcomp
        rw [map_mul]
        rw [hcomp]
        exact hu.1 v
      have hres := chapter11_residue_eq_of_local_congruence m z.1 uo hlocal
      have hsign : ∀ v (hv : v ∈ m.infinitePart),
          chapter11RealSignHom
              (chapter11RealGlobalComponent K v (m.infinitePart_isReal v hv)
                (Units.map (algebraMap (𝓞 K) K).toMonoidHom uo)) =
            z.2 ⟨v, hv⟩ := by
        have hprincipal_sign (c : Kˣ) (w : NumberField.InfinitePlace K)
            (hw : w ∈ m.infinitePart) :
            chapter11RealSignComponent K w (m.infinitePart_isReal w hw)
                (chapter11PrincipalIdeleHom (K := K) c) =
              chapter11RealSignHom
                (chapter11RealGlobalComponent K w
                  (m.infinitePart_isReal w hw) c) := by
          apply Units.ext
          change SignType.sign
              (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
                (m.infinitePart_isReal w hw)
                (chapter11InfiniteIdeleComponent K w
                  (chapter11PrincipalIdeleHom (K := K) c) : w.Completion)) =
            SignType.sign
              (chapter11RealGlobalComponent K w
                (m.infinitePart_isReal w hw) c : ℝ)
          have hreal :
              NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
                  (m.infinitePart_isReal w hw)
                  (chapter11InfiniteIdeleComponent K w
                    (chapter11PrincipalIdeleHom (K := K) c) : w.Completion) =
                (chapter11RealGlobalComponent K w
                  (m.infinitePart_isReal w hw) c : ℝ) := by
            change NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
                (m.infinitePart_isReal w hw)
                (algebraMap K w.Completion (c : K)) =
              NumberField.InfinitePlace.embedding_of_isReal
                (m.infinitePart_isReal w hw) (c : K)
            simp [WithAbs.equiv,
              NumberField.InfinitePlace.Completion.algebraMap_apply,
              NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe]
          rw [hreal]
        intro v hv
        have hrepdecomp : e (representative z) =
            (chapter11SignInfiniteIdele m z.2, finiteRepresentative z.1) := by
          dsimp [representative]
          exact e.apply_symm_apply _
        have hrepinf :
            (representative z : Chapter11AdeleRing K).1 =
              (chapter11SignInfiniteIdele m z.2 :
                LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09InfiniteAdele K) := by
          exact congrArg
            (fun w =>
              (w.1 : LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09InfiniteAdele K))
            hrepdecomp
        have hrepinfv :
            ((representative z : Chapter11AdeleRing K).1) v =
              ((chapter11SignInfiniteIdele m z.2 :
                LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09InfiniteAdele K) v) := by
          exact congrArg
            (fun w : LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09InfiniteAdele K => w v)
            hrepinf
        have hrep_sign : chapter11RealSignComponent K v
              (m.infinitePart_isReal v hv) (representative z) = z.2 ⟨v, hv⟩ := by
          apply Units.ext
          change SignType.sign
              (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
                (m.infinitePart_isReal v hv)
                (((representative z : Chapter11AdeleRing K).1) v)) = _
          rw [hrepinfv]
          dsimp [chapter11SignInfiniteIdele]
          have hcases : (z.2 ⟨v, hv⟩ : SignType) = -1 ∨
              (z.2 ⟨v, hv⟩ : SignType) = 1 := by
            rcases SignType.trichotomy (z.2 ⟨v, hv⟩ : SignType) with hneg | hzero | hpos
            · exact Or.inl hneg
            · exact False.elim ((z.2 ⟨v, hv⟩).ne_zero hzero)
            · exact Or.inr hpos
          rcases hcases with hneg | hpos
          · simp [hneg, hv, WithAbs.equiv,
              NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe]
          · simp [hpos, hv, WithAbs.equiv,
              NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe]
        have hcomp := congrArg
          (chapter11RealSignComponent K v (m.infinitePart_isReal v hv)) hpu
        rw [map_mul, hu.2 v hv, mul_one] at hcomp
        rw [hao, hprincipal_sign _ _ hv] at hcomp
        rw [hrep_sign] at hcomp
        exact hcomp
      refine ⟨uo, ?_⟩
      apply Prod.ext
      · dsimp [chapter11GlobalUnitResidueSignHom]
        apply Units.ext
        exact hres
      · funext v
        apply Units.ext
        dsimp [chapter11GlobalUnitResidueSignHom]
        simpa [chapter11RealSignHom, chapter11RealGlobalComponent,
          LastLib.Book04AdelesAndIdeles.Chapter08.chapter08RealEmbedding,
          LastLib.Book04AdelesAndIdeles.Chapter08.chapter08SignOfUnit] using
          congrArg Units.val (hsign v v.property)
    · rintro ⟨uo, rfl⟩
      let z0 : chapter11RayResidueSignGroup m :=
        chapter11GlobalUnitResidueSignHom m uo
      change chapter11RayClassProjection m (representative z0) = 1
      apply (QuotientGroup.eq_one_iff _).2
      have hres0 : Ideal.Quotient.mk m.finiteIdeal
          (chapter11ResidueRepresentative m z0.1) =
          Ideal.Quotient.mk m.finiteIdeal (uo : 𝓞 K) := by
        rw [chapter11_residue_representative_spec m z0.1]
        simpa [z0, chapter11GlobalUnitResidueSignHom]
      have hq0 : Ideal.Quotient.mk m.finiteIdeal
          ((uo : 𝓞 K) - chapter11ResidueRepresentative m z0.1) = 0 := by
        rw [map_sub, hres0]
        simp
      have hdiff0 : (uo : 𝓞 K) - chapter11ResidueRepresentative m z0.1 ∈
          m.finiteIdeal := (Ideal.Quotient.eq_zero_iff_mem).mp hq0
      have hlocal0 : chapter11PrincipalIdeleHom (K := K)
            (Units.map (algebraMap (𝓞 K) K).toMonoidHom uo)⁻¹ *
              representative z0 ∈ chapter11RayUnitSubgroup m := by
        change
          (∀ v, chapter11IdeleFiniteComponent K v
              (chapter11PrincipalIdeleHom (K := K)
                (Units.map (algebraMap (𝓞 K) K).toMonoidHom uo)⁻¹ *
                representative z0) ∈
                chapter11FiniteLocalUnitGroup K v (m.finiteExponent v)) ∧
            ∀ v (hv : v ∈ m.infinitePart),
              chapter11RealSignComponent K v (m.infinitePart_isReal v hv)
                (chapter11PrincipalIdeleHom (K := K)
                  (Units.map (algebraMap (𝓞 K) K).toMonoidHom uo)⁻¹ *
                  representative z0) = 1
        constructor
        · intro v
          by_cases hv : v ∈ m.finiteExponent.support
          · have hdiffv : (uo : 𝓞 K) - chapter11ResidueRepresentative m z0.1 ∈
                v.asIdeal ^ m.finiteExponent v :=
              (chapter11_finite_ideal_le_prime_power m v hv) hdiff0
            rw [map_mul, map_inv]
            have hrepcomp0 : chapter11IdeleFiniteComponent K v (representative z0) =
                chapter11FiniteGlobalComponent K v
                  (chapter11ResidueRepresentativeUnit m z0.1) := by
              have hrepdecomp0 : e (representative z0) =
                  (chapter11SignInfiniteIdele m z0.2, finiteRepresentative z0.1) := by
                dsimp [representative]
                exact e.apply_symm_apply _
              rw [show chapter11IdeleFiniteComponent K v (representative z0) =
                    chapter11FiniteIdeleComponent K v (finiteRepresentative z0.1) by
                  apply Units.ext
                  exact congrArg
                    (fun w => ((w.2 :
                      LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09FiniteAdele K) v))
                    hrepdecomp0]
              rw [finiteRepresentative_spec z0.1 v,
                chapter11ResidueFiniteComponent, dif_pos hv]
            change chapter11FiniteGlobalComponent K v
                (Units.map (algebraMap (𝓞 K) K).toMonoidHom uo)⁻¹ *
              chapter11IdeleFiniteComponent K v (representative z0) ∈
                chapter11FiniteLocalUnitGroup K v (m.finiteExponent v)
            rw [hrepcomp0]
            simpa only [map_mul, map_inv] using
              (chapter11_finite_local_unit_of_integer_congruence m v hv uo z0.1 hdiffv)
          · have hunit :=
              chapter11_finite_global_component_of_integer_unit_mem_units uo v
            have hzero := hunit_to_local_zero v _ hunit
            have hinv :=
              (chapter11FiniteLocalUnitGroup K v 0).inv_mem hzero
            have hrepone : chapter11IdeleFiniteComponent K v (representative z0) = 1 := by
              have hrepdecomp0 : e (representative z0) =
                  (chapter11SignInfiniteIdele m z0.2, finiteRepresentative z0.1) := by
                dsimp [representative]
                exact e.apply_symm_apply _
              rw [show chapter11IdeleFiniteComponent K v (representative z0) =
                    chapter11FiniteIdeleComponent K v (finiteRepresentative z0.1) by
                  apply Units.ext
                  exact congrArg
                    (fun w => ((w.2 :
                      LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09FiniteAdele K) v))
                    hrepdecomp0]
              rw [finiteRepresentative_spec z0.1 v,
                chapter11ResidueFiniteComponent, dif_neg hv]
            rw [map_mul, map_inv]
            change chapter11FiniteGlobalComponent K v
                (Units.map (algebraMap (𝓞 K) K).toMonoidHom uo)⁻¹ *
              chapter11IdeleFiniteComponent K v (representative z0) ∈
                chapter11FiniteLocalUnitGroup K v (m.finiteExponent v)
            rw [hrepone, mul_one]
            have hv0 : m.finiteExponent v = 0 := by
              by_contra hne
              exact hv (Finsupp.mem_support_iff.mpr hne)
            rw [hv0]
            exact hinv
        · intro v hv
          rw [map_mul, map_inv]
          have hsign := representative_sign_component z0 v hv
          have hprincipal_sign :
              chapter11RealSignComponent K v (m.infinitePart_isReal v hv)
                (chapter11PrincipalIdeleHom (K := K)
                  (Units.map (algebraMap (𝓞 K) K).toMonoidHom uo)) =
                z0.2 ⟨v, hv⟩ := by
            apply Units.ext
            change SignType.sign
                (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
                  (m.infinitePart_isReal v hv)
                  (chapter11InfiniteIdeleComponent K v
                    (chapter11PrincipalIdeleHom (K := K)
                      (Units.map (algebraMap (𝓞 K) K).toMonoidHom uo)) : v.Completion)) = _
            have hreal :
                NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
                    (m.infinitePart_isReal v hv)
                    (chapter11InfiniteIdeleComponent K v
                      (chapter11PrincipalIdeleHom (K := K)
                        (Units.map (algebraMap (𝓞 K) K).toMonoidHom uo)) : v.Completion) =
                  (chapter11RealGlobalComponent K v (m.infinitePart_isReal v hv)
                    (Units.map (algebraMap (𝓞 K) K).toMonoidHom uo) : ℝ) := by
              change NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
                  (m.infinitePart_isReal v hv)
                  (algebraMap K v.Completion
                    ((Units.map (algebraMap (𝓞 K) K).toMonoidHom uo : Kˣ) : K)) =
                NumberField.InfinitePlace.embedding_of_isReal
                  (m.infinitePart_isReal v hv)
                  ((Units.map (algebraMap (𝓞 K) K).toMonoidHom uo : Kˣ) : K)
              simp [WithAbs.equiv,
                NumberField.InfinitePlace.Completion.algebraMap_apply,
                NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe]
            rw [hreal]
            simpa [z0, chapter11GlobalUnitResidueSignHom,
              LastLib.Book04AdelesAndIdeles.Chapter08.chapter08RealEmbedding,
              LastLib.Book04AdelesAndIdeles.Chapter08.chapter08SignOfUnit,
              chapter11RealSignHom, chapter11RealGlobalComponent]
          rw [map_inv, hprincipal_sign, hsign]
          simp
      have hp : chapter11PrincipalIdeleHom (K := K)
          (Units.map (algebraMap (𝓞 K) K).toMonoidHom uo) ∈
            chapter11PrincipalIdeleSubgroup (K := K) :=
        ⟨_, rfl⟩
      refine Subgroup.mem_sup.mpr ⟨
        chapter11PrincipalIdeleHom (K := K)
          (Units.map (algebraMap (𝓞 K) K).toMonoidHom uo), hp,
        chapter11PrincipalIdeleHom (K := K)
          (Units.map (algebraMap (𝓞 K) K).toMonoidHom uo)⁻¹ *
            representative z0,
        hlocal0, ?_⟩
      simp [mul_assoc]
  · constructor
    · change ∀ z, chapter11RayClassToOrdinaryClassHom m z = 1 ↔
        z ∈ Set.range f
      intro z
      constructor
      · intro hz
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
          (chapter11PrincipalIdeleSubgroup (K := K) ⊔ chapter11RayUnitSubgroup m) z
        change ClassGroup.mk K
            ((chapter11CanonicalIdeleIdealMap K).toIdeal x) = 1 at hz
        have hclass' := congrArg (ClassGroup.equiv K) hz
        rw [ClassGroup.equiv_mk, map_one] at hclass'
        let I : Chapter11FractionalIdealUnitGroup K :=
          (chapter11CanonicalIdeleIdealMap K).toIdeal x
        have hI : QuotientGroup.mk'
            (toPrincipalIdeal (𝓞 K) K).range I = 1 := by
          simpa [I] using hclass'
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hI
        obtain ⟨a, ha⟩ := hI
        have hpa : (chapter11CanonicalIdeleIdealMap K).toIdeal
              (chapter11PrincipalIdeleHom (K := K) a) =
            toPrincipalIdeal (𝓞 K) K a :=
          (chapter11CanonicalIdeleIdealMap K).map_principal a
        let y : Chapter11IdeleGroup K :=
          x * (chapter11PrincipalIdeleHom (K := K) a)⁻¹
        have hyideal : (chapter11CanonicalIdeleIdealMap K).toIdeal y = 1 := by
          simp [y]
          rw [hpa, ha]
          change I * I⁻¹ = 1
          simp
        have hyfull : y ∈ chapter11FullFiniteUnitSubgroup := by
          rw [← (chapter11CanonicalIdeleIdealMap K).kernel_eq_full_finite_units]
          exact (MonoidHom.mem_ker).2 hyideal
        have hyfull' := hyfull
        change (∀ v, chapter11IdeleFiniteComponent K v y ∈
            chapter11FiniteLocalUnitGroup K v 0) ∧ _ at hyfull'
        let S := m.finiteExponent.support
        obtain ⟨b, hbS, hbout⟩ :=
          LastLib.Book04AdelesAndIdeles.Chapter01.chapter01_finite_approximation K S
            (fun v _ => (chapter11IdeleFiniteComponent K v y : v.adicCompletion K))
            (fun v _ => (m.finiteExponent v : ℤ))
        have hbintegral : b ∈
            LastLib.Book04AdelesAndIdeles.Chapter05.chapter05RingOfIntegersSet K := by
          apply (LastLib.Book04AdelesAndIdeles.Chapter05.chapter05_diagonal_integrality_iff K b).2
          intro v
          change Valued.v ((b : K) : v.adicCompletion K) ≤ 1
          by_cases hv : v ∈ S
          · have hy0 : Valued.v
                (chapter11IdeleFiniteComponent K v y : v.adicCompletion K) = 1 := by
              have hy0' := hyfull'.1 v
              rw [chapter11FiniteLocalUnitGroup_zero K v] at hy0'
              have hmem : chapter11IdeleFiniteComponent K v y ∈
                  Valued.v.valuationSubring.unitGroup := by
                simpa only [IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers] using hy0'
              exact (Valuation.mem_unitGroup_iff (v.adicCompletion K) (Valued.v) _).1 hmem
            have hsmall : Valued.v
                ((chapter11IdeleFiniteComponent K v y : v.adicCompletion K) -
                  (b : v.adicCompletion K)) <
                Valued.v (chapter11IdeleFiniteComponent K v y : v.adicCompletion K) := by
              change Valued.v
                  ((chapter11IdeleFiniteComponent K v y : v.adicCompletion K) -
                    (b : v.adicCompletion K)) < _
              have hclose := hbS v hv
              rw [LastLib.Book04AdelesAndIdeles.Chapter01.chapter01LocallyClose] at hclose
              change Valued.v
                  ((chapter11IdeleFiniteComponent K v y : v.adicCompletion K) -
                    (b : v.adicCompletion K)) ≤
                WithZero.exp (-(m.finiteExponent v : ℤ)) at hclose
              calc
                _ ≤ WithZero.exp (-(m.finiteExponent v : ℤ)) := hclose
                _ < 1 := by
                  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
                  have hn := Finsupp.mem_support_iff.mp hv
                  omega
                _ = _ := hy0.symm
            have hval : Valued.v ((b : K) : v.adicCompletion K) =
                Valued.v (chapter11IdeleFiniteComponent K v y : v.adicCompletion K) := by
              apply Valuation.map_eq_of_sub_lt (Valued.v :
                Valuation (v.adicCompletion K) ℤᵐ⁰)
              rw [Valuation.map_sub_swap]
              exact hsmall
            rw [hval, hy0]
          · have horder := hbout v hv
            by_cases hb0 : b = 0
            · simp [hb0]
            · rw [LastLib.Book04AdelesAndIdeles.Chapter01.chapter01_completion_valuation_agrees_with_global
                K v b]
              have hval :=
                LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent_valuation
                  v hb0
              rw [hval, ← WithZero.exp_zero, WithZero.exp_le_exp]
              simpa [LastLib.Book04AdelesAndIdeles.Chapter01.chapter01Order,
                LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent] using horder
        change b ∈ Set.range (algebraMap (𝓞 K) K) at hbintegral
        obtain ⟨o, rfl⟩ := hbintegral
        have hunitv : ∀ v, v ∈ m.finiteExponent.support →
            (o : 𝓞 K) ∉ v.asIdeal := by
          intro v hv
          have hy0 : Valued.v
                (chapter11IdeleFiniteComponent K v y : v.adicCompletion K) = 1 := by
            have hy0' := hyfull'.1 v
            rw [chapter11FiniteLocalUnitGroup_zero K v] at hy0'
            have hmem : chapter11IdeleFiniteComponent K v y ∈
                Valued.v.valuationSubring.unitGroup := by
              simpa only [IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers] using hy0'
            exact (Valuation.mem_unitGroup_iff (v.adicCompletion K) (Valued.v) _).1 hmem
          have hsmall : Valued.v
                ((chapter11IdeleFiniteComponent K v y : v.adicCompletion K) -
                  (algebraMap (𝓞 K) (v.adicCompletion K) o)) <
                Valued.v (chapter11IdeleFiniteComponent K v y : v.adicCompletion K) := by
            have hclose := hbS v hv
            rw [LastLib.Book04AdelesAndIdeles.Chapter01.chapter01LocallyClose] at hclose
            change Valued.v
                ((chapter11IdeleFiniteComponent K v y : v.adicCompletion K) -
                  (algebraMap (𝓞 K) (v.adicCompletion K) o)) ≤
              WithZero.exp (-(m.finiteExponent v : ℤ)) at hclose
            calc
              _ ≤ WithZero.exp (-(m.finiteExponent v : ℤ)) := hclose
              _ < 1 := by
                rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
                have hn := Finsupp.mem_support_iff.mp hv
                omega
              _ = _ := hy0.symm
          have hval : Valued.v (algebraMap (𝓞 K) (v.adicCompletion K) o) = 1 := by
            have hval' : Valued.v (algebraMap (𝓞 K) (v.adicCompletion K) o) =
                Valued.v (chapter11IdeleFiniteComponent K v y : v.adicCompletion K) := by
              apply Valuation.map_eq_of_sub_lt (Valued.v :
                Valuation (v.adicCompletion K) ℤᵐ⁰)
              rw [Valuation.map_sub_swap]
              exact hsmall
            rw [hy0] at hval'
            exact hval'
          have hval' : v.intValuation o = 1 := by
            have hcoe : algebraMap (𝓞 K) (v.adicCompletion K) o =
                ((algebraMap (𝓞 K) K o : K) : v.adicCompletion K) := by
              calc
                algebraMap (𝓞 K) (v.adicCompletion K) o =
                    algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K o) :=
                  (IsScalarTower.algebraMap_apply (𝓞 K) K (v.adicCompletion K) o).symm
                _ = ((algebraMap (𝓞 K) K o : K) : v.adicCompletion K) := by
                  rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
                  rfl
            calc
              v.intValuation o = v.valuation K (algebraMap (𝓞 K) K o) :=
                (v.valuation_of_algebraMap o).symm
              _ =
                  Valued.v ((algebraMap (𝓞 K) K o : K) : v.adicCompletion K) :=
                (LastLib.Book04AdelesAndIdeles.Chapter01.chapter01_completion_valuation_agrees_with_global
                  K v (algebraMap (𝓞 K) K o)).symm
              _ = Valued.v (algebraMap (𝓞 K) (v.adicCompletion K) o) := by rw [← hcoe]
              _ = 1 := hval
          have hcomp : o ∈ v.asIdeal.primeCompl :=
            (v.intValuation_eq_one_iff_mem_primeCompl o).mp hval'
          change o ∉ v.asIdeal
          exact hcomp
        have hquotv (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
            (hv : v ∈ m.finiteExponent.support) :
            IsUnit (Ideal.Quotient.mk (v.asIdeal ^ m.finiteExponent v) o) :=
          Ideal.Quotient.isUnit_mk_pow_of_notMem (I := v.asIdeal)
            (n := m.finiteExponent v) (x := o) (hunitv v hv)
        let ι := {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) // v ∈ S}
        let I : ι → Ideal (𝓞 K) := fun v =>
          v.1.asIdeal ^ m.finiteExponent v.1
        have hpair : Pairwise (fun i j => IsCoprime (I i) (I j)) := by
          intro i j hij
          apply IsDedekindDomain.HeightOneSpectrum.isCoprime_pow_of_ne
          · intro h
            exact hij (Subtype.ext h)
        let E := Ideal.quotientInfRingEquivPiQuotient I hpair
        have htuple : IsUnit (fun i : ι =>
            Ideal.Quotient.mk (I i) o) := by
          rw [Pi.isUnit_iff]
          intro i
          exact hquotv i.1 i.2
        have hmapped : IsUnit (E
            (Ideal.Quotient.mk (⨅ i, I i) o)) := by
          have hmk' : E (Ideal.Quotient.mk (⨅ i, I i) o) =
              (fun i : ι => Ideal.Quotient.mk (I i) o) := by
            rfl
          rw [hmk']
          exact htuple
        have hmkInf : IsUnit (Ideal.Quotient.mk (⨅ i, I i) o) := by
          exact (isUnit_map_of_leftInverse E.symm E.left_inv).mp hmapped
        have hInf : (⨅ i, I i) = m.finiteIdeal := by
          rw [RayModulus.finiteIdeal]
          rw [← IsDedekindDomain.HeightOneSpectrum.inf_pow_eq_prod
            S (fun v => m.finiteExponent v) (fun v => v) (by
              intro v hv w hw hne
              exact hne)]
          rw [Finset.inf_eq_iInf, iInf_subtype']
        rw [hInf] at hmkInf
        let r : chapter11RayResidueGroup m := hmkInf.unit
        have hr : (r : 𝓞 K ⧸ m.finiteIdeal) =
            Ideal.Quotient.mk m.finiteIdeal o := hmkInf.unit_spec
        have hmk : Ideal.Quotient.mk m.finiteIdeal o =
            Ideal.Quotient.mk m.finiteIdeal
              (chapter11ResidueRepresentative m r) := by
          calc
            Ideal.Quotient.mk m.finiteIdeal o = (r : 𝓞 K ⧸ m.finiteIdeal) := hr.symm
            _ = Ideal.Quotient.mk m.finiteIdeal
                (chapter11ResidueRepresentative m r) :=
              (chapter11_residue_representative_spec m r).symm
        have hdiff (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
            (hv : v ∈ m.finiteExponent.support) :
            o - chapter11ResidueRepresentative m r ∈
              v.asIdeal ^ m.finiteExponent v := by
          have hzero : Ideal.Quotient.mk m.finiteIdeal
              (o - chapter11ResidueRepresentative m r) = 0 := by
            rw [map_sub, hmk]
            simp
          have hmem : o - chapter11ResidueRepresentative m r ∈
              m.finiteIdeal := (Ideal.Quotient.eq_zero_iff_mem).mp hzero
          exact (chapter11_finite_ideal_le_prime_power m v hv) hmem
        have hclose (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
            (hv : v ∈ m.finiteExponent.support) :
            Valued.v ((chapter11IdeleFiniteComponent K v y : v.adicCompletion K) -
              algebraMap (𝓞 K) (v.adicCompletion K)
                (chapter11ResidueRepresentative m r)) ≤
              WithZero.exp (-(m.finiteExponent v : ℤ)) := by
          have hyo := hbS v hv
          rw [LastLib.Book04AdelesAndIdeles.Chapter01.chapter01LocallyClose] at hyo
          change Valued.v ((chapter11IdeleFiniteComponent K v y : v.adicCompletion K) -
              algebraMap (𝓞 K) (v.adicCompletion K) o) ≤
            WithZero.exp (-(m.finiteExponent v : ℤ)) at hyo
          have hoa : Valued.v (algebraMap (𝓞 K) (v.adicCompletion K)
              (o - chapter11ResidueRepresentative m r)) ≤
              WithZero.exp (-(m.finiteExponent v : ℤ)) := by
            have hval := (v.intValuation_le_pow_iff_mem
              (o - chapter11ResidueRepresentative m r)
              (m.finiteExponent v)).2 (hdiff v hv)
            have hcoe (x : K) : algebraMap K (v.adicCompletion K) x =
                (x : v.adicCompletion K) := by
              rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
              rfl
            have hmap : algebraMap (𝓞 K) (v.adicCompletion K)
                  (o - chapter11ResidueRepresentative m r) =
                ((((o - chapter11ResidueRepresentative m r : 𝓞 K) : K) :
                  v.adicCompletion K)) := by
              rw [← hcoe, IsScalarTower.algebraMap_apply (𝓞 K) K
                (v.adicCompletion K)]
            rw [hmap,
              LastLib.Book04AdelesAndIdeles.Chapter01.chapter01_completion_valuation_agrees_with_global
                K v (((o - chapter11ResidueRepresentative m r : 𝓞 K) : K))]
            calc
              v.valuation K ((o - chapter11ResidueRepresentative m r : 𝓞 K) : K) =
                  v.intValuation (o - chapter11ResidueRepresentative m r) :=
                v.valuation_of_algebraMap _
              _ ≤ _ := hval
          calc
            Valued.v ((chapter11IdeleFiniteComponent K v y : v.adicCompletion K) -
                algebraMap (𝓞 K) (v.adicCompletion K)
                  (chapter11ResidueRepresentative m r)) =
                Valued.v (((chapter11IdeleFiniteComponent K v y : v.adicCompletion K) -
                  algebraMap (𝓞 K) (v.adicCompletion K) o) +
                  (algebraMap (𝓞 K) (v.adicCompletion K) o -
                    algebraMap (𝓞 K) (v.adicCompletion K)
                      (chapter11ResidueRepresentative m r))) := by
              rw [sub_add_sub_cancel]
            _ ≤ max
                (Valued.v ((chapter11IdeleFiniteComponent K v y : v.adicCompletion K) -
                  algebraMap (𝓞 K) (v.adicCompletion K) o))
                (Valued.v (algebraMap (𝓞 K) (v.adicCompletion K)
                  (o - chapter11ResidueRepresentative m r))) := by
              have hsum := Valued.v.map_add
                ((chapter11IdeleFiniteComponent K v y : v.adicCompletion K) -
                  algebraMap (𝓞 K) (v.adicCompletion K) o)
                (algebraMap (𝓞 K) (v.adicCompletion K) o -
                  algebraMap (𝓞 K) (v.adicCompletion K)
                    (chapter11ResidueRepresentative m r))
              simpa only [map_sub] using hsum
            _ ≤ WithZero.exp (-(m.finiteExponent v : ℤ)) := max_le hyo hoa
        have hfinite (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
            (hv : v ∈ m.finiteExponent.support) :
            chapter11IdeleFiniteComponent K v y *
                (chapter11FiniteIdeleComponent K v
                  (finiteRepresentative r))⁻¹ ∈
              chapter11FiniteLocalUnitGroup K v (m.finiteExponent v) := by
          let A := v.adicCompletionIntegers K
          let L := v.adicCompletion K
          let g : Lˣ := chapter11IdeleFiniteComponent K v y
          let a : Lˣ := chapter11FiniteGlobalComponent K v
            (chapter11ResidueRepresentativeUnit m r)
          have hrepcomp : chapter11FiniteIdeleComponent K v
                (finiteRepresentative r) = a := by
            rw [finiteRepresentative_spec r v,
              chapter11ResidueFiniteComponent, dif_pos hv]
          have hgy0 : g ∈ A.unitGroup := by
            have hgy0' := hyfull'.1 v
            rw [chapter11FiniteLocalUnitGroup_zero K v] at hgy0'
            exact hgy0'
          let ga : Aˣ := A.unitGroupMulEquiv ⟨g, hgy0⟩
          have hga : Units.map A.subtype.toMonoidHom ga = g := by
            apply Units.ext
            change ((A.unitGroupMulEquiv ⟨g, hgy0⟩ : Aˣ) : A) = (g : L)
            exact A.coe_unitGroupMulEquiv_apply ⟨g, hgy0⟩
          have haunit : a ∈ (Submonoid.ofClass A).units := by
            exact chapter11_residue_component_is_integral_unit m r v hv
          rcases (Submonoid.mem_units_iff (Submonoid.ofClass A) a).mp haunit with
            ⟨ha, hainv⟩
          let aa : Aˣ :=
            { val := ⟨(a : L), ha⟩
              inv := ⟨((a⁻¹ : Lˣ) : L), hainv⟩
              val_inv := by
                apply Subtype.ext
                exact a.val_inv
              inv_val := by
                apply Subtype.ext
                exact a.inv_val }
          have haa : Units.map A.subtype.toMonoidHom aa = a := by
            apply Units.ext
            rfl
          have haK : (chapter11ResidueRepresentativeUnit m r : K) =
              algebraMap (𝓞 K) K (chapter11ResidueRepresentative m r) := by
            simp [chapter11ResidueRepresentativeUnit,
              show m.finiteExponent.support.Nonempty from ⟨v, hv⟩]
          have haa_val : (a : L) = algebraMap (𝓞 K) L
              (chapter11ResidueRepresentative m r) := by
            change NumberField.FinitePlace.embedding v
                (chapter11ResidueRepresentativeUnit m r : K) = _
            rw [haK, NumberField.FinitePlace.embedding_apply]
            change algebraMap K L
                (algebraMap (𝓞 K) K (chapter11ResidueRepresentative m r)) = _
            simpa only [IsScalarTower.algebraMap_apply (𝓞 K) K L]
          have hclose' : Valued.v ((g : L) - (a : L)) ≤
              WithZero.exp (-(m.finiteExponent v : ℤ)) := by
            change Valued.v ((chapter11IdeleFiniteComponent K v y : L) - (a : L)) ≤ _
            rw [haa_val]
            exact hclose v hv
          have hlocal := chapter11_finite_local_unit_of_close v
            (m.finiteExponent v) g a ga aa hga haa hclose'
          simpa [g, hrepcomp] using hlocal
        let s : chapter11RaySignGroup m := fun v =>
          chapter11RealSignComponent K v (m.infinitePart_isReal v v.property) y
        let z0 : chapter11RayResidueSignGroup m := (r, s)
        have hrepcompz (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
            chapter11IdeleFiniteComponent K v (representative z0) =
              chapter11FiniteIdeleComponent K v (finiteRepresentative r) := by
          have hrepdecomp : e (representative z0) =
              (chapter11SignInfiniteIdele m z0.2, finiteRepresentative z0.1) := by
            dsimp [representative]
            exact e.apply_symm_apply _
          apply Units.ext
          exact congrArg
            (fun w => ((w.2 :
              LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09FiniteAdele K) v))
            hrepdecomp
        have hray : y * (representative z0)⁻¹ ∈
            chapter11RayUnitSubgroup m := by
          change
            (∀ v, chapter11IdeleFiniteComponent K v
                (y * (representative z0)⁻¹) ∈
              chapter11FiniteLocalUnitGroup K v (m.finiteExponent v)) ∧
            ∀ v (hv : v ∈ m.infinitePart),
              chapter11RealSignComponent K v (m.infinitePart_isReal v hv)
                (y * (representative z0)⁻¹) = 1
          constructor
          · intro v
            by_cases hv : v ∈ m.finiteExponent.support
            · rw [map_mul, map_inv, hrepcompz]
              exact hfinite v hv
            · have hv0 : m.finiteExponent v = 0 := by
                by_contra hne
                exact hv (Finsupp.mem_support_iff.mpr hne)
              have hy0 := hyfull'.1 v
              rw [map_mul, map_inv, hrepcompz,
                finiteRepresentative_spec r v,
                chapter11ResidueFiniteComponent, dif_neg hv, hv0]
              simpa using hy0
          · intro v hv
            rw [map_mul, map_inv]
            have hsign := representative_sign_component z0 v hv
            rw [show chapter11RealSignComponent K v
                (m.infinitePart_isReal v hv) y = z0.2 ⟨v, hv⟩ by
                  rfl, hsign]
            simp
        have hprincipal : chapter11PrincipalIdeleHom (K := K) a ∈
            chapter11PrincipalIdeleSubgroup (K := K) := ⟨a, rfl⟩
        have hxy : chapter11RayClassProjection m x =
            chapter11RayClassProjection m y := by
          change QuotientGroup.mk'
              (chapter11PrincipalIdeleSubgroup (K := K) ⊔
                chapter11RayUnitSubgroup m) x =
            QuotientGroup.mk'
              (chapter11PrincipalIdeleSubgroup (K := K) ⊔
                chapter11RayUnitSubgroup m) y
          apply (QuotientGroup.mk'_eq_mk'
            (chapter11PrincipalIdeleSubgroup (K := K) ⊔
              chapter11RayUnitSubgroup m)).2
          have hmem : x⁻¹ * y ∈
              chapter11PrincipalIdeleSubgroup (K := K) ⊔
                chapter11RayUnitSubgroup m := by
            change x⁻¹ * (x * (chapter11PrincipalIdeleHom (K := K) a)⁻¹) ∈
              chapter11PrincipalIdeleSubgroup (K := K) ⊔
                chapter11RayUnitSubgroup m
            rw [← mul_assoc, inv_mul_cancel, one_mul]
            exact Subgroup.mem_sup_left
              ((chapter11PrincipalIdeleSubgroup (K := K)).inv_mem hprincipal)
          refine ⟨x⁻¹ * y, hmem, ?_⟩
          rw [← mul_assoc]
          change x * x⁻¹ * y = y
          rw [mul_inv_cancel, one_mul]
        have hyr : chapter11RayClassProjection m y =
            chapter11RayClassProjection m (representative z0) := by
          change QuotientGroup.mk'
              (chapter11PrincipalIdeleSubgroup (K := K) ⊔
                chapter11RayUnitSubgroup m) y =
            QuotientGroup.mk'
              (chapter11PrincipalIdeleSubgroup (K := K) ⊔
                chapter11RayUnitSubgroup m) (representative z0)
          apply (QuotientGroup.mk'_eq_mk'
            (chapter11PrincipalIdeleSubgroup (K := K) ⊔
              chapter11RayUnitSubgroup m)).2
          have hmem : y⁻¹ * representative z0 ∈
              chapter11PrincipalIdeleSubgroup (K := K) ⊔
                chapter11RayUnitSubgroup m := by
            have hinv := (chapter11RayUnitSubgroup m).inv_mem hray
            have heq : y⁻¹ * representative z0 =
                (y * (representative z0)⁻¹)⁻¹ := by
              calc
                y⁻¹ * representative z0 = representative z0 * y⁻¹ :=
                  mul_comm _ _
                _ = (representative z0)⁻¹⁻¹ * y⁻¹ := by rw [inv_inv]
                _ = (y * (representative z0)⁻¹)⁻¹ :=
                  (mul_inv_rev y (representative z0)⁻¹).symm
            rw [heq]
            exact Subgroup.mem_sup_right hinv
          refine ⟨y⁻¹ * representative z0, hmem, ?_⟩
          rw [← mul_assoc]
          change y * y⁻¹ * representative z0 = representative z0
          rw [mul_inv_cancel, one_mul]
        refine ⟨z0, ?_⟩
        change chapter11RayClassProjection m (representative z0) =
          chapter11RayClassProjection m x
        exact hyr.symm.trans hxy.symm
      · rintro ⟨r, rfl⟩
        change ClassGroup.mk K
            ((chapter11CanonicalIdeleIdealMap K).toIdeal (representative r)) = 1
        have hfull : representative r ∈ chapter11FullFiniteUnitSubgroup := by
          change (∀ v, chapter11IdeleFiniteComponent K v (representative r) ∈
              chapter11FiniteLocalUnitGroup K v 0) ∧ _
          constructor
          · intro v
            have hrepdecomp : e (representative r) =
                (chapter11SignInfiniteIdele m r.2, finiteRepresentative r.1) := by
              dsimp [representative]
              exact e.apply_symm_apply _
            have hrepcomp : chapter11IdeleFiniteComponent K v (representative r) =
                chapter11FiniteIdeleComponent K v (finiteRepresentative r.1) := by
              apply Units.ext
              exact congrArg
                (fun w => ((w.2 :
                  LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09FiniteAdele K) v))
                hrepdecomp
            rw [hrepcomp, finiteRepresentative_spec r.1 v]
            by_cases hv : v ∈ m.finiteExponent.support
            · rw [chapter11ResidueFiniteComponent, dif_pos hv]
              exact hunit_to_local_zero v _
                (chapter11_residue_component_is_integral_unit m r.1 v hv)
            · rw [chapter11ResidueFiniteComponent, dif_neg hv]
              exact (chapter11FiniteLocalUnitGroup K v 0).one_mem
          · simp [RayModulus.trivial]
        have hideal : (chapter11CanonicalIdeleIdealMap K).toIdeal
              (representative r) = 1 := by
          apply (MonoidHom.mem_ker).mp
          rw [(chapter11CanonicalIdeleIdealMap K).kernel_eq_full_finite_units]
          exact hfull
        rw [hideal]
        simp
    · exact chapter11_ray_class_to_ordinary_surjective m

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
