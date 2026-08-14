import LastLib.Book03RamificationTheory.Chapter05.Section01ANumberingDesignedForQuotients
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.Section04FixedFieldsOfInertia
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.RingTheory.Valuation.Discrete.RankOne

namespace LastLib.Book03RamificationTheory.Chapter05

noncomputable section

open scoped Classical

open scoped BigOperators

universe u

/-! ## 5.2. Herbrand's quotient theorem -/

/-- The canonical quotient homomorphism by a normal subgroup. -/
def chapter05QuotientMap
    {G : Type*} [Group G] (H : Subgroup G) [H.Normal] : G →* G ⧸ H :=
  QuotientGroup.mk' H

/-- The image in a quotient of an upper-numbered subgroup upstairs. -/
def chapter05UpperQuotientImage
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (D : Chapter05RamificationFiltration G) (v : ℝ) : Subgroup (G ⧸ H) :=
  (chapter05UpperRamificationGroup D v).map (chapter05QuotientMap H)

/-
 The local input used to derive the quotient displacement identity.  The
 abstract profiles are tied to a finite Galois tower and to the orbit
 polynomial whose norm factorization supplies the product of the conjugate
 displacements.  The displacement identity itself is deliberately not a
 field of the quotient setup.
-/
structure Chapter05QuotientLocalFieldOrbitRealization
    {G : Type u} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (upstairs : Chapter05RamificationFiltration G)
    (downstairs : Chapter05RamificationFiltration (G ⧸ H))
    (eLM : ℕ) where
  eLM_pos : 0 < eLM
  K : Type u
  M : Type u
  /- `M0` is the unramified enlargement of the quotient field `M` used in
     the orbit-polynomial argument.  The source proof forms the orbit
     polynomial over `M0`, not over `M` itself: `H0 = H ∩ G0` fixes `M0`,
     while `M0/M` is the unramified part of the tower. -/
  M0 : Type u
  L : Type u
  [field_K : Field K]
  [field_M : Field M]
  [field_M0 : Field M0]
  [field_L : Field L]
  [algebra_KM : Algebra K M]
  [algebra_KM0 : Algebra K M0]
  [algebra_KL : Algebra K L]
  [algebra_MM0 : Algebra M M0]
  [algebra_ML : Algebra M L]
  [algebra_M0L : Algebra M0 L]
  [scalar_tower_KML : IsScalarTower K M L]
  [scalar_tower_KMM0 : IsScalarTower K M M0]
  [scalar_tower_KM0L : IsScalarTower K M0 L]
  [scalar_tower_MM0L : IsScalarTower M M0 L]
  [finite_dimensional_KM : FiniteDimensional K M]
  [finite_dimensional_KM0 : FiniteDimensional K M0]
  [finite_dimensional_KL : FiniteDimensional K L]
  [finite_dimensional_ML : FiniteDimensional M L]
  [finite_dimensional_M0L : FiniteDimensional M0 L]
  [galois_KM : IsGalois K M]
  [galois_KM0 : IsGalois K M0]
  [galois_KL : IsGalois K L]
  [galois_M0L : IsGalois M0 L]
  [gal_finite : Fintype (Gal(L / K))]
  group_equiv : G ≃* Gal(L / K)
  quotient_equiv : G ⧸ H ≃* Gal(M / K)
  [inertia_intersection_normal :
    (H ⊓ upstairs.lowerGroup 0 : Subgroup G).Normal]
  quotient0_equiv :
    G ⧸ (H ⊓ upstairs.lowerGroup 0 : Subgroup G) ≃* Gal(M0 / K)
  fixed_field_equiv :
    M ≃ₐ[K] IntermediateField.fixedField (H.map group_equiv.toMonoidHom)
  fixed_field_equiv_M0 :
    M0 ≃ₐ[K]
      IntermediateField.fixedField
        ((H ⊓ upstairs.lowerGroup 0 : Subgroup G).map
          group_equiv.toMonoidHom)
  fixed_field_inclusion :
    ∀ x : M,
      (fixed_field_equiv_M0 (algebraMap M M0 x) : L) = algebraMap M L x
  vM : AddValuation M (WithTop ℤ)
  vM0 : AddValuation M0 (WithTop ℤ)
  vL : AddValuation L (WithTop ℤ)
  valuations_compatible :
    vM.IsEquiv (AddValuation.comap (algebraMap M L) vL)
  valuations_M0_over_M :
    vM.IsEquiv (AddValuation.comap (algebraMap M M0) vM0)
  valuation_scale_M_M0 :
    ∀ x : M, vM0 (algebraMap M M0 x) = vM x
  valuation_scale_M0_L :
    ∀ x : M0, vL (algebraMap M0 L x) = eLM • vM0 x
  /- The orbit group acts over `M0`; this is the subgroup corresponding to
     `H ∩ G0` in the source proof. -/
  H0 : Subgroup (L ≃ₐ[M0] L)
  [H0_finite : Fintype H0]
  H0_eq_top : H0 = ⊤
  H0_equiv : H0 ≃* (H ⊓ upstairs.lowerGroup 0 : Subgroup G)
  eLM_eq_H0_card : eLM = Nat.card H0
  α : L
  α_integral : IsIntegral M0 α
  α_in_valuation_ring : α ∈ vL.toValuation.valuationSubring
  /- The orbit-polynomial valuation argument uses that `α` is a uniformizer
     of `L` over the unramified coefficient field `M0`: the constant term is
     then the unique least-valuation term after evaluation at `α`. -/
  α_uniformizer : vL α = (1 : WithTop ℤ)
  H0_action_compat :
    ∀ τ : (H ⊓ upstairs.lowerGroup 0 : Subgroup G),
      ((H0_equiv.symm τ : H0) : L ≃ₐ[M0] L) α =
        (group_equiv (τ : G) : Gal(L / K)) α
  β : M
  β_integral : IsIntegral K β
  β_in_valuation_ring : β ∈ vM.toValuation.valuationSubring
  orbit_polynomial : Polynomial M0
  orbit_polynomial_map_eq :
    Polynomial.map (algebraMap M0 L) orbit_polynomial =
      ∏ τ : H0,
        (Polynomial.X -
          Polynomial.C ((τ : L ≃ₐ[M0] L) α))
  orbit_polynomial_monic : orbit_polynomial.Monic
  orbit_coefficients_integral :
    ∀ n : ℕ, orbit_polynomial.coeff n ∈ vM0.toValuation.valuationSubring
  norm_factorization :
    ∀ x : L,
      algebraMap M0 L (Algebra.norm M0 x) =
        ∏ τ : H0, (τ : L ≃ₐ[M0] L) x
  coefficient_action : G →* (M0 ≃+* M0)
  coefficient_action_quotient :
    ∀ σ : G,
      coefficient_action σ =
        (quotient0_equiv
          (QuotientGroup.mk' (H ⊓ upstairs.lowerGroup 0 : Subgroup G) σ)).toRingEquiv
  orbit_polynomial_conjugation :
    ∀ σ : G,
      Polynomial.map (algebraMap M0 L)
          (Polynomial.map (coefficient_action σ).toRingHom orbit_polynomial) =
        ∏ τ : H0,
          (Polynomial.X -
            Polynomial.C
              ((group_equiv σ : Gal(L / K))
                ((τ : L ≃ₐ[M0] L) α)))
  coefficient_displacement_lower_bound :
    ∀ {σ : G}, σ ∉ H → σ ∈ upstairs.lowerGroup 0 → ∀ n : ℕ,
      vM0 ((coefficient_action σ) (orbit_polynomial.coeff n) -
        orbit_polynomial.coeff n) ≥
        vM ((quotient_equiv (chapter05QuotientMap H σ) : Gal(M / K)) β - β)
  coefficient_displacement_constant :
    ∀ {σ : G}, σ ∉ H → σ ∈ upstairs.lowerGroup 0 →
      vM0 ((coefficient_action σ) (orbit_polynomial.coeff 0) -
        orbit_polynomial.coeff 0) =
        vM ((quotient_equiv (chapter05QuotientMap H σ) : Gal(M / K)) β - β)
  upstairs_displacement_lower_bound :
    ∀ {σ : G}, σ ≠ 1 →
      ∀ x : vL.toValuation.valuationSubring,
        vL ((group_equiv σ : Gal(L / K)) (x : L) - (x : L)) ≥
          (upstairs.displacement σ : WithTop ℤ)
  /- A uniformizer of `L/M0` realizes the displacement only for inertial
     automorphisms.  A residue-moving automorphism has displacement zero on
     the integral ring, while it still moves a uniformizer inside the maximal
     ideal, so imposing the equality for all `σ` would be false in an
     unramified stage. -/
  upstairs_displacement :
    ∀ {σ : G}, σ ≠ 1 → σ ∈ upstairs.lowerGroup 0 →
      vL ((group_equiv σ : Gal(L / K)) α - α) =
        (upstairs.displacement σ : WithTop ℤ)
  downstairs_displacement_lower_bound :
    ∀ {σ : G ⧸ H}, σ ≠ 1 →
      ∀ x : vM.toValuation.valuationSubring,
        vM ((quotient_equiv σ : Gal(M / K)) (x : M) - (x : M)) ≥
          (downstairs.displacement σ : WithTop ℤ)
  downstairs_displacement :
    ∀ {σ : G ⧸ H}, σ ≠ 1 →
      vM ((quotient_equiv σ : Gal(M / K)) β - β) =
        (downstairs.displacement σ : WithTop ℤ)

/-
 The finite data used by the quotient theorem.  The lower profiles are the
 actual profiles of the two valued extensions.  `eLM` is the ramification
 index of `L/M`, and its cardinality field records the local subgroup
 interpretation `e(L/M)=|H ∩ G_0|`.  The local field/orbit-polynomial
 realization is kept as input so that (5.1) is derived by the theorem below,
 rather than stored as setup data.
 -/
structure Chapter05QuotientRamificationSetup
    (G : Type*) [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal] where
  upstairs : Chapter05RamificationFiltration G
  downstairs : Chapter05RamificationFiltration (G ⧸ H)
  /- The quotient's level-zero group is the image of upstairs inertia.  This
     is the residue-separability input needed for the non-inertial case of
     (5.1), and it is also the zero-level instance of the quotient theorem. -/
  downstairs_lower_zero_eq_inertia_image :
    downstairs.lowerGroup 0 =
      (upstairs.lowerGroup 0).map (chapter05QuotientMap H)
  eLM : ℕ
  eLM_pos : 0 < eLM
  eLM_eq_inertia_card :
    eLM = Nat.card (H ⊓ upstairs.lowerGroup 0 : Subgroup G)
  local_field_realization :
    Chapter05QuotientLocalFieldOrbitRealization H upstairs downstairs eLM

namespace Chapter05QuotientRamificationSetup

variable {G : Type*} [Group G]
variable (H : Subgroup G) [H.Normal]

theorem quotient_map_surjective :
    Function.Surjective (chapter05QuotientMap H) := by
  exact QuotientGroup.mk'_surjective H

theorem quotient_map_kernel :
    MonoidHom.ker (chapter05QuotientMap H) = H := by
  rw [chapter05QuotientMap]
  exact QuotientGroup.ker_mk' H

theorem quotient_exact_sequence :
    Function.MulExact (Subgroup.subtype H) (chapter05QuotientMap H) ∧
      Function.Surjective (chapter05QuotientMap H) := by
  refine ⟨?_, ?_⟩
  · apply MonoidHom.mulExact_iff.mpr
    rw [chapter05QuotientMap, QuotientGroup.ker_mk']
    simp
  · exact QuotientGroup.mk'_surjective H

end Chapter05QuotientRamificationSetup

/-
 The orbit polynomial used in the coefficient proof of (5.1).  The
 coefficient descent to `M` is a separate theorem because it needs the
 valuation-ring integrality hypotheses of the chosen local generator.
-/
noncomputable def chapter05OrbitPolynomial
    {M L : Type*} [CommRing M] [CommRing L] [Algebra M L]
    (H : Subgroup (L ≃ₐ[M] L)) [Fintype H] (α : L) : Polynomial L :=
  ∏ τ : H,
    (Polynomial.X - Polynomial.C ((τ : L ≃ₐ[M] L) α))

theorem chapter05OrbitPolynomial_is_monic
    {M L : Type*} [CommRing M] [CommRing L] [Algebra M L]
    (H : Subgroup (L ≃ₐ[M] L)) [Fintype H] (α : L) :
    (chapter05OrbitPolynomial H α).Monic := by
  simpa [chapter05OrbitPolynomial] using
    Polynomial.monic_prod_of_monic Finset.univ
      (fun τ : H => Polynomial.X - Polynomial.C ((τ : L ≃ₐ[M] L) α))
      (fun τ _ => Polynomial.monic_X_sub_C _)

/-- A coefficient descent witness for the orbit polynomial in the proof of (5.1). -/
structure Chapter05OrbitPolynomialCoefficientWitness
    {M L : Type*} [Field M] [Field L] [Algebra M L]
    (A_M : ValuationSubring M)
    (H : Subgroup (L ≃ₐ[M] L)) [Fintype H] (α : L) where
  F : Polynomial M
  map_eq_orbit :
    Polynomial.map (algebraMap M L) F = chapter05OrbitPolynomial H α
  coefficients_in_valuation_ring : ∀ n : ℕ, F.coeff n ∈ A_M

/- The descent witness is not just coefficient bookkeeping: because the orbit
   polynomial is monic, its descended polynomial is monic as well.  This is
   the generator-level fact used before comparing coefficient valuations. -/
theorem chapter05_orbit_polynomial_coefficient_witness_monic
    {M L : Type*} [Field M] [Field L] [Algebra M L]
    (A_M : ValuationSubring M)
    (H : Subgroup (L ≃ₐ[M] L)) [Fintype H] (α : L)
    (W : Chapter05OrbitPolynomialCoefficientWitness A_M H α) :
    W.F.Monic := by
  exact Polynomial.monic_of_injective (algebraMap M L).injective
    (W.map_eq_orbit ▸ chapter05OrbitPolynomial_is_monic H α)

/-
 The next theorem is the displacement identity quoted in the source.  We
 state it both in the exact reciprocal form and as the derived integral form;
 the local norm/orbit-polynomial realization is carried by the setup.
-/
theorem chapter05_coset_displacement_identity
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (S : Chapter05QuotientRamificationSetup G H)
    {σ : G} (hσ : σ ∉ H) :
    (S.downstairs.displacement (chapter05QuotientMap H σ) : ℚ) =
      (1 / (S.eLM : ℚ)) *
        ∑ τ : H, (S.upstairs.displacement (σ * (τ : G)) : ℚ) := by
  sorry

theorem chapter05_coset_displacement_identity_integral_form
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (S : Chapter05QuotientRamificationSetup G H)
    {σ : G} (hσ : σ ∉ H) :
    S.eLM * S.downstairs.displacement (chapter05QuotientMap H σ) =
      ∑ τ : H, S.upstairs.displacement (σ * (τ : G)) := by
  have he : (S.eLM : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt S.eLM_pos)
  have hrat := chapter05_coset_displacement_identity H S hσ
  have hrat' :
      (S.eLM : ℚ) * (S.downstairs.displacement (chapter05QuotientMap H σ) : ℚ) =
        ∑ τ : H, (S.upstairs.displacement (σ * (τ : G)) : ℚ) := by
    rw [hrat]
    field_simp
  exact_mod_cast hrat'

/- The threshold form of the source's equation (5.2).  The explicit maximum
   hypotheses keep the finite coset count available without introducing a
   second choice of finite-index maximum into the setup. -/
theorem chapter05_coset_threshold_identity
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (S : Chapter05QuotientRamificationSetup G H)
    {σ : G} (hσ : σ ∉ H)
    (n : ℕ)
    (hn_upper : ∀ τ : H,
      S.upstairs.displacement (σ * (τ : G)) ≤ n)
    (hn_attained : ∃ τ : H,
      S.upstairs.displacement (σ * (τ : G)) = n)
    (hinertial : 1 ≤ S.downstairs.displacement (chapter05QuotientMap H σ)) :
    ((S.downstairs.displacement (chapter05QuotientMap H σ) - 1 : ℕ) : ℚ) =
      (1 / (S.eLM : ℚ)) *
        Finset.sum (Finset.Icc 1 (n - 1))
          (fun j =>
            (Nat.card (H ⊓ S.upstairs.lowerGroup (j : ℝ) : Subgroup G) : ℚ)) := by
  classical
  let d : ℕ := S.downstairs.displacement (chapter05QuotientMap H σ)
  have hdisp : S.eLM * d =
      ∑ τ : H, S.upstairs.displacement (σ * (τ : G)) := by
    exact chapter05_coset_displacement_identity_integral_form H S hσ
  have hdn : 0 < d := by
    dsimp [d]
    omega
  have hn_pos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    have hzero : ∀ τ : H,
        S.upstairs.displacement (σ * (τ : G)) = 0 := by
      intro τ
      have hτ := hn_upper τ
      omega
    have hsum_zero :
        (∑ τ : H, S.upstairs.displacement (σ * (τ : G))) = 0 := by
      simp [hzero]
    have hprod_pos : 0 < S.eLM * d :=
      Nat.mul_pos S.eLM_pos hdn
    omega
  obtain ⟨τ₀, hτ₀⟩ := hn_attained
  have hcoset_ne_one : ∀ τ : H, σ * (τ : G) ≠ 1 := by
    intro τ hτ
    apply hσ
    rw [eq_inv_of_mul_eq_one_left hτ]
    exact H.inv_mem τ.property
  have hcoset_mem : ∀ {j : ℕ}, j < n →
      σ * (τ₀ : G) ∈ S.upstairs.lowerGroup (j : ℝ) := by
    intro j hj
    apply (S.upstairs.lower_nat_mem_iff (hcoset_ne_one τ₀) j).2
    omega
  have hcount : ∀ {j : ℕ}, j < n →
      (∑ τ : H,
        if σ * (τ : G) ∈ S.upstairs.lowerGroup (j : ℝ) then 1 else 0) =
        Nat.card (H ⊓ S.upstairs.lowerGroup (j : ℝ) : Subgroup G) := by
    intro j hj
    let K : Subgroup G := S.upstairs.lowerGroup (j : ℝ)
    let A := {τ : H // σ * (τ : G) ∈ K}
    let B := H ⊓ K
    have hmem₀ : σ * (τ₀ : G) ∈ K := by
      exact hcoset_mem hj
    let e : A ≃ B :=
      { toFun := fun τ =>
          ⟨(τ₀ : G)⁻¹ * (τ : G),
            H.mul_mem (H.inv_mem τ₀.property) τ.1.property,
            by
              have hmem := K.mul_mem (K.inv_mem hmem₀) τ.property
              simpa [K, mul_assoc] using hmem⟩
        invFun := fun h =>
          ⟨⟨(τ₀ : G) * (h : G),
              H.mul_mem τ₀.property h.property.1⟩,
            by
              have hmem := K.mul_mem hmem₀ h.property.2
              simpa [K, mul_assoc] using hmem⟩
        left_inv := by
          intro τ
          apply Subtype.ext
          simp
        right_inv := by
          intro h
          apply Subtype.ext
          simp }
    have hsumA :
        (∑ τ : H,
          if σ * (τ : G) ∈ K then 1 else 0) = Fintype.card A := by
      rw [Finset.sum_boole]
      simp [A, Fintype.card_subtype]
    calc
      (∑ τ : H,
          if σ * (τ : G) ∈ S.upstairs.lowerGroup (j : ℝ) then 1 else 0) =
          Fintype.card A := by simpa [A, K] using hsumA
      _ = Fintype.card B := Fintype.card_congr e
      _ = Nat.card B := Nat.card_eq_fintype_card.symm
      _ = Nat.card (H ⊓ S.upstairs.lowerGroup (j : ℝ) : Subgroup G) := by
        rfl
  have hpoint : ∀ τ : H,
      S.upstairs.displacement (σ * (τ : G)) =
        (∑ j ∈ Finset.Icc 0 (n - 1),
          if σ * (τ : G) ∈ S.upstairs.lowerGroup (j : ℝ) then 1 else 0) := by
    intro τ
    let q : ℕ := S.upstairs.displacement (σ * (τ : G))
    have hqle : q ≤ n := hn_upper τ
    have hfilter :
        (Finset.Icc 0 (n - 1)).filter (fun j => j + 1 ≤ q) =
          Finset.range q := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
      omega
    have hsumq :
        (∑ j ∈ Finset.Icc 0 (n - 1), if j + 1 ≤ q then 1 else 0) = q := by
      rw [Finset.sum_boole, hfilter, Finset.card_range]
      rfl
    calc
      S.upstairs.displacement (σ * (τ : G)) = q := rfl
      _ = ∑ j ∈ Finset.Icc 0 (n - 1),
          if j + 1 ≤ q then 1 else 0 := hsumq.symm
      _ = ∑ j ∈ Finset.Icc 0 (n - 1),
          if σ * (τ : G) ∈ S.upstairs.lowerGroup (j : ℝ) then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [S.upstairs.lower_nat_mem_iff (hcoset_ne_one τ) j]
        simp [q]
  have hsum_card :
      (∑ τ : H, S.upstairs.displacement (σ * (τ : G))) =
        ∑ j ∈ Finset.Icc 0 (n - 1),
          Nat.card (H ⊓ S.upstairs.lowerGroup (j : ℝ) : Subgroup G) := by
    calc
      (∑ τ : H, S.upstairs.displacement (σ * (τ : G))) =
          ∑ τ : H, ∑ j ∈ Finset.Icc 0 (n - 1),
            if σ * (τ : G) ∈ S.upstairs.lowerGroup (j : ℝ) then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro τ hτ
        exact hpoint τ
      _ = ∑ j ∈ Finset.Icc 0 (n - 1),
          ∑ τ : H,
            if σ * (τ : G) ∈ S.upstairs.lowerGroup (j : ℝ) then 1 else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ j ∈ Finset.Icc 0 (n - 1),
          Nat.card (H ⊓ S.upstairs.lowerGroup (j : ℝ) : Subgroup G) := by
        apply Finset.sum_congr rfl
        intro j hj
        apply hcount
        have hj' := Finset.mem_Icc.mp hj
        omega
  have hsplit :
      (∑ j ∈ Finset.Icc 0 (n - 1),
          Nat.card (H ⊓ S.upstairs.lowerGroup (j : ℝ) : Subgroup G)) =
        Nat.card (H ⊓ S.upstairs.lowerGroup 0 : Subgroup G) +
          ∑ j ∈ Finset.Icc 1 (n - 1),
            Nat.card (H ⊓ S.upstairs.lowerGroup (j : ℝ) : Subgroup G) := by
    have hfin : Finset.Icc 0 (n - 1) =
        insert 0 (Finset.Icc 1 (n - 1)) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hfin, Finset.sum_insert]
    · simp
    · simp
  have hnat :
      S.eLM * (d - 1) =
        ∑ j ∈ Finset.Icc 1 (n - 1),
          Nat.card (H ⊓ S.upstairs.lowerGroup (j : ℝ) : Subgroup G) := by
    have hsum := hdisp.trans hsum_card
    rw [hsplit, ← S.eLM_eq_inertia_card] at hsum
    calc
      S.eLM * (d - 1) = S.eLM * d - S.eLM := by
        rw [Nat.mul_sub_left_distrib, Nat.mul_one]
      _ = ∑ j ∈ Finset.Icc 1 (n - 1),
          Nat.card (H ⊓ S.upstairs.lowerGroup (j : ℝ) : Subgroup G) := by
        omega
  have he : (S.eLM : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt S.eLM_pos)
  have hrat :
      (S.eLM : ℚ) * (d - 1 : ℕ) =
        ∑ j ∈ Finset.Icc 1 (n - 1),
          (Nat.card (H ⊓ S.upstairs.lowerGroup (j : ℝ) : Subgroup G) : ℚ) := by
    exact_mod_cast hnat
  calc
    ((S.downstairs.displacement (chapter05QuotientMap H σ) - 1 : ℕ) : ℚ) =
        (1 / (S.eLM : ℚ)) * ((S.eLM : ℚ) *
          (S.downstairs.displacement (chapter05QuotientMap H σ) - 1 : ℕ)) := by
      field_simp
    _ = (1 / (S.eLM : ℚ)) *
        ∑ j ∈ Finset.Icc 1 (n - 1),
          (Nat.card (H ⊓ S.upstairs.lowerGroup (j : ℝ) : Subgroup G) : ℚ) := by
      rw [hrat]

/- Once the local coefficient calculation has identified a coefficient
   minimum with the downstairs displacement, the following is the purely
   algebraic transport to the coset sum.  The local coefficient hypotheses
   live on `Chapter05QuotientLocalFieldOrbitRealization`; this helper does
   not pretend that arbitrary functions are themselves coefficient minima.
-/
theorem chapter05_coset_displacement_identity_of_coefficient_minimum
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (S : Chapter05QuotientRamificationSetup G H)
    (coefficientMinimum quotientDisplacement : (G ⧸ H) → ℕ)
    (hcoefficient : ∀ {σ : G}, σ ∉ H →
      coefficientMinimum (chapter05QuotientMap H σ) =
        quotientDisplacement (chapter05QuotientMap H σ))
    (hquotient : ∀ {σ : G}, σ ∉ H →
      quotientDisplacement (chapter05QuotientMap H σ) =
        S.downstairs.displacement (chapter05QuotientMap H σ))
    {σ : G} (hσ : σ ∉ H) :
    S.eLM * coefficientMinimum (chapter05QuotientMap H σ) =
      ∑ τ : H, S.upstairs.displacement (σ * (τ : G)) := by
  rw [hcoefficient hσ, hquotient hσ]
  exact chapter05_coset_displacement_identity_integral_form H S hσ

/-!
 The quotient theorem itself.  This is the book-facing equality
 `(G/H)^v = G^v H/H`; the membership form below is often the more useful API.
-/
theorem chapter05_herbrand_quotient_theorem
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (S : Chapter05QuotientRamificationSetup G H)
    (hup : Function.Bijective (chapter05HerbrandFunction S.upstairs))
    (hdown : Function.Bijective (chapter05HerbrandFunction S.downstairs))
    {v : ℝ} (hv : (-1 : ℝ) ≤ v) :
    chapter05UpperRamificationGroup S.downstairs v =
      chapter05UpperQuotientImage H S.upstairs v := by
  sorry

theorem chapter05_herbrand_quotient_membership_iff
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (S : Chapter05QuotientRamificationSetup G H)
    (hup : Function.Bijective (chapter05HerbrandFunction S.upstairs))
    (hdown : Function.Bijective (chapter05HerbrandFunction S.downstairs))
    {v : ℝ} (hv : (-1 : ℝ) ≤ v) (σ : G) :
    chapter05QuotientMap H σ ∈
        chapter05UpperRamificationGroup S.downstairs v ↔
      ∃ τ : H, σ * (τ : G) ∈
        chapter05UpperRamificationGroup S.upstairs v := by
  rw [chapter05_herbrand_quotient_theorem H S hup hdown hv]
  rw [chapter05UpperQuotientImage, Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, hq⟩
    let τ : G := σ⁻¹ * g
    have hτ : τ ∈ H := by
      apply (QuotientGroup.eq_one_iff _).mp
      change chapter05QuotientMap H τ = 1
      dsimp [τ]
      rw [map_mul, map_inv]
      rw [← hq]
      simp
    refine ⟨⟨τ, hτ⟩, ?_⟩
    simpa [τ] using hg
  · rintro ⟨τ, hτ⟩
    refine ⟨σ * (τ : G), hτ, ?_⟩
    rw [map_mul]
    have hτq : chapter05QuotientMap H (τ : G) = 1 :=
      (QuotientGroup.eq_one_iff _).2 τ.property
    rw [hτq, mul_one]

/-- The fixed-field identification used to read the quotient as `Gal(M/K)`. -/
theorem chapter05_fixed_field_quotient_galois_equiv
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup (Gal(L / K))) [H.Normal] :
    Nonempty
      ((Gal(L / K) ⧸ H) ≃* Gal(
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FixedField H / K)) := by
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.residue_quotient_is_fixed_field_galois_group H

/-!
 The field-facing form of the quotient theorem.  The abstract setup above is
 useful for the displacement calculation, but later applications need the
 same data on the actual fixed field `M = Lᴴ`: the normalized valuation on
 `M`, completeness and uniqueness at all three stages, and the canonical
 congruence profiles for `L/M` and `M/K`.
-/
structure Chapter05FixedFieldSubextensionTransfer
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    (H : Subgroup (Gal(L / K))) [H.Normal]
    [FiniteDimensional K
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FixedField H)]
    [IsGalois K
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FixedField H)]
    [Finite
      (Gal(
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FixedField H / K))]
    [FiniteDimensional
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FixedField H) L]
    [IsGalois
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FixedField H) L]
    [Finite
      (Gal(
        L /
          LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FixedField H))]
    (upstairs : Chapter05RamificationFiltration (Gal(L / K))) where
  vK : AddValuation K (WithTop ℤ)
  vM : AddValuation
    (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FixedField H)
    (WithTop ℤ)
  vL : AddValuation L (WithTop ℤ)
  vK_rank_one_discrete : Valuation.IsRankOneDiscrete vK.toValuation
  vM_rank_one_discrete : Valuation.IsRankOneDiscrete vM.toValuation
  vL_rank_one_discrete : Valuation.IsRankOneDiscrete vL.toValuation
  vK_restriction_to_M :
    vK.IsEquiv
      (AddValuation.comap
        (algebraMap K
          (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FixedField H))
        vM)
  vK_restriction_to_L :
    vK.IsEquiv (AddValuation.comap (algebraMap K L) vL)
  vM_restriction_to_L :
    vM.IsEquiv
      (AddValuation.comap
        (algebraMap
          (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FixedField H) L)
        vL)
  eMK : ℕ
  eLM : ℕ
  eMK_pos : 0 < eMK
  eLM_pos : 0 < eLM
  vM_on_K :
    ∀ x : K,
      vM (algebraMap K
        (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FixedField H) x) =
        eMK • vK x
  vL_on_M :
    ∀ x :
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FixedField H,
      vL (algebraMap
        (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FixedField H) L x) =
        eLM • vM x
  base_complete :
    IsAdicComplete (IsLocalRing.maximalIdeal vK.toValuation.valuationSubring)
      vK.toValuation.valuationSubring
  fixed_field_complete :
    IsAdicComplete (IsLocalRing.maximalIdeal vM.toValuation.valuationSubring)
      vM.toValuation.valuationSubring
  extension_complete :
    IsAdicComplete (IsLocalRing.maximalIdeal vL.toValuation.valuationSubring)
      vL.toValuation.valuationSubring
  unique_normalized_KM :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05UniqueValuationExtension
      vK.toValuation vM.toValuation
  unique_normalized_KL :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05UniqueValuationExtension
      vK.toValuation vL.toValuation
  unique_normalized_ML :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05UniqueValuationExtension
      vM.toValuation vL.toValuation
  decomposition_top_KM :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
      K vM.toValuation.valuationSubring = ⊤
  decomposition_top_ML :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FixedField H)
      vL.toValuation.valuationSubring = ⊤
  subextension_profile :
    Chapter05RamificationFiltration
      (Gal(
        L /
          LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FixedField H))
  quotient_profile :
    Chapter05RamificationFiltration
      (Gal(
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FixedField H / K))
  subextension_lower_canonical :
    ∀ n : ℕ,
      subextension_profile.lowerGroup (n : ℝ) =
        chapter05RamificationGroupInG (F :=
          LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FixedField H)
          vL.toValuation.valuationSubring (n + 1)
  quotient_lower_canonical :
    ∀ n : ℕ,
      quotient_profile.lowerGroup (n : ℝ) =
        chapter05RamificationGroupInG (F := K)
          vM.toValuation.valuationSubring (n + 1)
  subextension_galois_equiv :
    H ≃* Gal(
      L /
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FixedField H)
  quotient_galois_equiv :
    (Gal(L / K) ⧸ H) ≃* Gal(
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FixedField H / K)

/-- Herbrand's theorem in the fixed-field notation of the source. -/
theorem chapter05_herbrand_fixed_field_quotient_theorem
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (H : Subgroup (Gal(L / K))) [H.Normal]
    (S : Chapter05QuotientRamificationSetup (Gal(L / K)) H)
    (hup : Function.Bijective (chapter05HerbrandFunction S.upstairs))
    (hdown : Function.Bijective (chapter05HerbrandFunction S.downstairs))
    {v : ℝ} (hv : (-1 : ℝ) ≤ v) :
    Nonempty
        ((Gal(L / K) ⧸ H) ≃* Gal(
          LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FixedField H / K)) ∧
      chapter05UpperRamificationGroup S.downstairs v =
        chapter05UpperQuotientImage H S.upstairs v := by
  refine ⟨chapter05_fixed_field_quotient_galois_equiv H,
    chapter05_herbrand_quotient_theorem H S hup hdown hv⟩

end
end LastLib.Book03RamificationTheory.Chapter05
