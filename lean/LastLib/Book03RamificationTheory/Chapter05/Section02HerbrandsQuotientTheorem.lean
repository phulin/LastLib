import LastLib.Book03RamificationTheory.Chapter05.Section01ANumberingDesignedForQuotients
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.Section04FixedFieldsOfInertia
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.RingTheory.Valuation.Discrete.RankOne

namespace LastLib.Book03RamificationTheory.Chapter05

noncomputable section

open scoped Classical

open scoped BigOperators
open scoped Topology

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
  classical
  let R := S.local_field_realization
  letI : Field R.K := R.field_K
  letI := R.field_M
  letI := R.field_M0
  letI := R.field_L
  letI := R.algebra_KM
  letI := R.algebra_KM0
  letI := R.algebra_KL
  letI := R.algebra_MM0
  letI := R.algebra_ML
  letI := R.algebra_M0L
  letI := R.scalar_tower_KML
  letI := R.scalar_tower_KMM0
  letI := R.scalar_tower_KM0L
  letI := R.scalar_tower_MM0L
  letI := R.H0_finite
  have hq_ne : chapter05QuotientMap H σ ≠ 1 := by
    intro hq
    apply hσ
    rw [← Chapter05QuotientRamificationSetup.quotient_map_kernel H]
    exact MonoidHom.mem_ker.mpr hq
  by_cases hq0 : chapter05QuotientMap H σ ∈ S.downstairs.lowerGroup 0
  · have hsum_representative : ∀ {ρ : G},
        chapter05QuotientMap H ρ = chapter05QuotientMap H σ →
          (∑ τ : H, (S.upstairs.displacement (ρ * (τ : G)) : ℚ)) =
            ∑ τ : H, (S.upstairs.displacement (σ * (τ : G)) : ℚ) := by
      intro ρ hρ
      have hρσ : σ⁻¹ * ρ ∈ H := by
        have hmap : chapter05QuotientMap H (σ⁻¹ * ρ) = 1 := by
          rw [map_mul, map_inv, hρ]
          simp
        have hker : σ⁻¹ * ρ ∈ MonoidHom.ker (chapter05QuotientMap H) :=
          MonoidHom.mem_ker.mpr hmap
        rw [Chapter05QuotientRamificationSetup.quotient_map_kernel H] at hker
        exact hker
      let τ₀ : H := ⟨σ⁻¹ * ρ, hρσ⟩
      have hρ_eq : ρ = σ * (τ₀ : G) := by
        dsimp [τ₀]
        group
      calc
        (∑ τ : H, (S.upstairs.displacement (ρ * (τ : G)) : ℚ)) =
            ∑ τ : H,
              (S.upstairs.displacement
                (σ * ((τ₀ : G) * (τ : G))) : ℚ) := by
          apply Finset.sum_congr rfl
          intro τ hτ
          rw [hρ_eq]
          congr 2
          simp [mul_assoc]
        _ = ∑ τ : H, (S.upstairs.displacement (σ * (τ : G)) : ℚ) := by
          exact Fintype.sum_equiv (Equiv.mulLeft τ₀) _ _ (fun τ => by
            rfl)
    rcases (show chapter05QuotientMap H σ ∈
        (S.upstairs.lowerGroup 0).map (chapter05QuotientMap H) by
      simpa [S.downstairs_lower_zero_eq_inertia_image] using hq0) with
      ⟨ρ, hρ0, hρmap⟩
    have hprod_ne : ∀ τ : H, ρ * (τ : G) ≠ 1 := by
      intro τ hτ
      have htq : chapter05QuotientMap H (τ : G) = 1 := by
        have hker : (τ : G) ∈ MonoidHom.ker (chapter05QuotientMap H) := by
          rw [Chapter05QuotientRamificationSetup.quotient_map_kernel H]
          exact τ.property
        exact MonoidHom.mem_ker.mp hker
      apply hq_ne
      calc
        chapter05QuotientMap H σ =
            chapter05QuotientMap H ρ := hρmap.symm
        _ = chapter05QuotientMap H ρ * 1 := by simp
        _ = chapter05QuotientMap H ρ * chapter05QuotientMap H (τ : G) := by
          rw [htq]
        _ = chapter05QuotientMap H (ρ * (τ : G)) := by rw [map_mul]
        _ = 1 := by rw [hτ]; simp
    have hzero_of_not_mem : ∀ {g : G}, g ≠ 1 →
        g ∉ S.upstairs.lowerGroup 0 →
          S.upstairs.displacement g = 0 := by
      intro g hgne hg0
      by_contra hdz
      have hdzpos : 1 ≤ S.upstairs.displacement g := by omega
      exact hg0 (by simpa using
        ((S.upstairs.lower_nat_mem_iff hgne 0).2 hdzpos))
    let P : H → Prop := fun τ => (τ : G) ∈ S.upstairs.lowerGroup (0 : ℝ)
    let A := {τ : H // P τ}
    let eK : A ≃ (H ⊓ S.upstairs.lowerGroup (0 : ℝ) : Subgroup G) :=
      { toFun := fun τ =>
          ⟨(τ : G), τ.1.property, τ.2⟩
        invFun := fun γ =>
          ⟨⟨(γ : G), γ.2.1⟩, γ.2.2⟩
        left_inv := by
          intro τ
          apply Subtype.ext
          rfl
        right_inv := by
          intro γ
          apply Subtype.ext
          rfl }
    have hsum_compl :
        (∑ τ : {τ : H // ¬P τ},
          (S.upstairs.displacement (ρ * (τ.1 : G)) : ℚ)) = 0 := by
      apply Finset.sum_eq_zero
      intro τ hτ
      have hz : S.upstairs.displacement (ρ * (τ.1 : G)) = 0 := by
        apply hzero_of_not_mem (hprod_ne τ.1)
        intro hmem
        apply τ.2
        have hinv : ρ⁻¹ ∈ S.upstairs.lowerGroup (0 : ℝ) :=
          (S.upstairs.lowerGroup (0 : ℝ)).inv_mem hρ0
        simpa [P] using (S.upstairs.lowerGroup (0 : ℝ)).mul_mem hinv hmem
      exact_mod_cast hz
    have hsum_subtype :
        (∑ τ : A,
          (S.upstairs.displacement (ρ * (τ.1 : G)) : ℚ)) =
          ∑ γ : (H ⊓ S.upstairs.lowerGroup (0 : ℝ) : Subgroup G),
            (S.upstairs.displacement (ρ * (γ : G)) : ℚ) := by
      exact Fintype.sum_equiv eK _ _ (fun τ => by rfl)
    have hsum_K :
        (∑ τ : H, (S.upstairs.displacement (ρ * (τ : G)) : ℚ)) =
          ∑ γ : (H ⊓ S.upstairs.lowerGroup (0 : ℝ) : Subgroup G),
            (S.upstairs.displacement (ρ * (γ : G)) : ℚ) := by
      calc
        (∑ τ : H, (S.upstairs.displacement (ρ * (τ : G)) : ℚ)) =
            (∑ τ : A,
              (S.upstairs.displacement (ρ * (τ.1 : G)) : ℚ)) +
              ∑ τ : {τ : H // ¬P τ},
                (S.upstairs.displacement (ρ * (τ.1 : G)) : ℚ) := by
          exact (Fintype.sum_subtype_add_sum_subtype P
            (fun τ : H => (S.upstairs.displacement (ρ * (τ : G)) : ℚ))).symm
        _ = ∑ τ : A,
              (S.upstairs.displacement (ρ * (τ.1 : G)) : ℚ) := by
          rw [hsum_compl, add_zero]
        _ = ∑ γ : (H ⊓ S.upstairs.lowerGroup (0 : ℝ) : Subgroup G),
              (S.upstairs.displacement (ρ * (γ : G)) : ℚ) := hsum_subtype
    have hdpos : 1 ≤ S.downstairs.displacement (chapter05QuotientMap H σ) := by
      apply (S.downstairs.lower_nat_mem_iff hq_ne (0 : ℕ)).1
      simpa only [Nat.cast_zero] using hq0
    have hρ_notH : ρ ∉ H := by
      intro hρH
      apply hq_ne
      have hρker : chapter05QuotientMap H ρ = 1 := by
        apply MonoidHom.mem_ker.mp
        rw [Chapter05QuotientRamificationSetup.quotient_map_kernel H]
        exact hρH
      exact hρmap.symm.trans hρker
    have hρq_ne : chapter05QuotientMap H ρ ≠ 1 := by
      intro hρq
      apply hq_ne
      exact hρmap.symm.trans hρq
    have hcoset_ne : ∀ γ : (H ⊓ S.upstairs.lowerGroup (0 : ℝ) : Subgroup G),
        ρ * (γ : G) ≠ 1 := by
      intro γ hγ
      apply hρq_ne
      have hγq : chapter05QuotientMap H (γ : G) = 1 := by
        apply MonoidHom.mem_ker.mp
        rw [Chapter05QuotientRamificationSetup.quotient_map_kernel H]
        exact γ.property.1
      calc
        chapter05QuotientMap H ρ = chapter05QuotientMap H ρ * 1 := by simp
        _ = chapter05QuotientMap H ρ * chapter05QuotientMap H (γ : G) := by
          rw [hγq]
        _ = chapter05QuotientMap H (ρ * (γ : G)) := by rw [map_mul]
        _ = 1 := by rw [hγ]; simp
    let F := R.orbit_polynomial
    let a := R.coefficient_action ρ
    let I := Fin (F.natDegree + 1)
    let terms : I → R.L := fun i =>
      algebraMap R.M0 R.L (a (F.coeff (i : ℕ)) - F.coeff (i : ℕ)) *
        R.α ^ (i : ℕ)
    have hdown :
        R.vM ((R.quotient_equiv (chapter05QuotientMap H ρ) : Gal(R.M / R.K)) R.β - R.β) =
          (S.downstairs.displacement (chapter05QuotientMap H σ) : WithTop ℤ) := by
      rw [hρmap]
      exact R.downstairs_displacement hq_ne
    have hconst_eq :
        R.vM0 (a (F.coeff 0) - F.coeff 0) =
          (S.downstairs.displacement (chapter05QuotientMap H σ) : WithTop ℤ) := by
      calc
        R.vM0 (a (F.coeff 0) - F.coeff 0) =
            R.vM ((R.quotient_equiv (chapter05QuotientMap H ρ) : Gal(R.M / R.K)) R.β - R.β) := by
              simpa [F, a] using
                (R.coefficient_displacement_constant (σ := ρ) hρ_notH hρ0)
        _ = (S.downstairs.displacement (chapter05QuotientMap H σ) : WithTop ℤ) := hdown
    have hconst_ne : a (F.coeff 0) - F.coeff 0 ≠ 0 := by
      intro hzero
      have htop : R.vM0 (a (F.coeff 0) - F.coeff 0) = (⊤ : WithTop ℤ) := by
        simp [hzero]
      rw [hconst_eq] at htop
      exact WithTop.coe_ne_top htop
    have hterm0_ne : terms (0 : I) ≠ 0 := by
      intro hzero
      have hmapzero : algebraMap R.M0 R.L (a (F.coeff 0) - F.coeff 0) = 0 := by
        simpa [terms] using hzero
      exact hconst_ne ((algebraMap R.M0 R.L).injective (by simpa using hmapzero))
    have hterm_val (i : I) :
        R.vL (terms i) =
          S.eLM • R.vM0 (a (F.coeff (i : ℕ)) - F.coeff (i : ℕ)) +
            (i : ℕ) • (1 : WithTop ℤ) := by
      change R.vL ((algebraMap R.M0 R.L)
          (a (F.coeff (i : ℕ)) - F.coeff (i : ℕ)) * R.α ^ (i : ℕ)) = _
      rw [AddValuation.map_mul, AddValuation.map_pow,
        R.valuation_scale_M0_L, R.α_uniformizer]
    have hterm0val :
        R.vL (terms (0 : I)) =
          S.eLM • (S.downstairs.displacement (chapter05QuotientMap H σ) : WithTop ℤ) := by
      rw [hterm_val]
      simp [hconst_eq]
    have hcoeff_bound (i : I) :
        (S.downstairs.displacement (chapter05QuotientMap H σ) : WithTop ℤ) ≤
          R.vM0 (a (F.coeff (i : ℕ)) - F.coeff (i : ℕ)) := by
      have hi := R.coefficient_displacement_lower_bound (σ := ρ) hρ_notH hρ0 (i : ℕ)
      rw [hρmap, R.downstairs_displacement hq_ne] at hi
      exact hi
    have hterm_strict (i : I) (hi : i ≠ 0) :
        S.eLM • (S.downstairs.displacement (chapter05QuotientMap H σ) : WithTop ℤ) <
          R.vL (terms i) := by
      have hi_pos : 0 < (i : ℕ) := Fin.pos_iff_ne_zero.mpr hi
      have hone_pos : (0 : WithTop ℤ) < (i : ℕ) • (1 : WithTop ℤ) := by
        simpa [nsmul_eq_mul] using
          (show (0 : ℤ) < (i : ℤ) by exact_mod_cast hi_pos)
      have hlt :
          S.eLM • (S.downstairs.displacement (chapter05QuotientMap H σ) : WithTop ℤ) <
            S.eLM • R.vM0 (a (F.coeff (i : ℕ)) - F.coeff (i : ℕ)) +
              (i : ℕ) • (1 : WithTop ℤ) := by
        calc
          S.eLM • (S.downstairs.displacement (chapter05QuotientMap H σ) : WithTop ℤ) <
              S.eLM • (S.downstairs.displacement (chapter05QuotientMap H σ) : WithTop ℤ) +
                (i : ℕ) • (1 : WithTop ℤ) := by
            have hle :
                S.eLM • (S.downstairs.displacement (chapter05QuotientMap H σ) : WithTop ℤ) ≤
                  S.eLM • R.vM0 (a (F.coeff (i : ℕ)) - F.coeff (i : ℕ)) :=
              nsmul_le_nsmul_right (hcoeff_bound i) S.eLM
            have hfinite :
                S.eLM • (S.downstairs.displacement (chapter05QuotientMap H σ) : WithTop ℤ) ≠
                  (⊤ : WithTop ℤ) := by
              have hnsmul :
                  S.eLM • (S.downstairs.displacement (chapter05QuotientMap H σ) : WithTop ℤ) =
                    ((S.eLM * S.downstairs.displacement (chapter05QuotientMap H σ) : ℕ) : WithTop ℤ) := by
                change S.eLM •
                    ((S.downstairs.displacement (chapter05QuotientMap H σ) : ℤ) : WithTop ℤ) =
                  ((S.eLM * S.downstairs.displacement (chapter05QuotientMap H σ) : ℤ) : WithTop ℤ)
                rw [← WithTop.coe_nsmul]
                congr 1
              rw [hnsmul]
              exact WithTop.coe_ne_top
            simpa using
              (WithTop.add_lt_add_of_le_of_lt hfinite le_rfl hone_pos)
          _ ≤ S.eLM • R.vM0 (a (F.coeff (i : ℕ)) - F.coeff (i : ℕ)) +
                (i : ℕ) • (1 : WithTop ℤ) := by
            exact add_le_add_left (nsmul_le_nsmul_right (hcoeff_bound i) S.eLM) _
      rw [hterm_val]
      exact hlt
    have hterm0_val_ne : R.vL (terms (0 : I)) ≠ 0 := by
      rw [hterm0val]
      have hprod_pos : 0 < S.eLM * S.downstairs.displacement (chapter05QuotientMap H σ) :=
        Nat.mul_pos S.eLM_pos (lt_of_lt_of_le Nat.zero_lt_one hdpos)
      intro hzero
      apply Nat.ne_of_gt hprod_pos
      have hnsmul :
            S.eLM • (S.downstairs.displacement (chapter05QuotientMap H σ) : WithTop ℤ) =
            ((S.eLM * S.downstairs.displacement (chapter05QuotientMap H σ) : ℕ) : WithTop ℤ) := by
        change S.eLM •
            ((S.downstairs.displacement (chapter05QuotientMap H σ) : ℤ) : WithTop ℤ) =
          ((S.eLM * S.downstairs.displacement (chapter05QuotientMap H σ) : ℤ) : WithTop ℤ)
        rw [← WithTop.coe_nsmul]
        congr 1
      rw [hnsmul] at hzero
      have hzero' :
          ((S.eLM * S.downstairs.displacement (chapter05QuotientMap H σ) : ℕ) : WithTop ℤ) = 0 := hzero
      exact_mod_cast hzero'
    have hsum_val : R.vL (∑ i : I, terms i) = R.vL (terms (0 : I)) := by
      have hlt : R.vL (terms (0 : I)) <
          R.vL (∑ i ∈ (Finset.univ : Finset I) \ {0}, terms i) := by
        apply R.vL.map_lt_sum
        · exact R.vL.ne_top_iff.mpr hterm0_ne
        · intro i hi
          have hi0 : i ≠ 0 := by
            intro hi0
            subst hi0
            exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_singleton.mpr rfl)
          rw [hterm0val]
          exact hterm_strict i hi0
      rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem
        (Finset.mem_univ (0 : I))]
      exact AddValuation.map_add_eq_of_lt_left R.vL hlt
    have hmap_deg :
        (Polynomial.map a.toRingHom F).natDegree = F.natDegree :=
      Polynomial.natDegree_map_eq_of_injective a.toRingHom.injective F
    have heval_map :
        (Polynomial.map (algebraMap R.M0 R.L)
            (Polynomial.map a.toRingHom F)).eval R.α =
          ∑ i : I,
            algebraMap R.M0 R.L (a (F.coeff (i : ℕ))) * R.α ^ (i : ℕ) := by
      rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range, hmap_deg,
        ← Fin.sum_univ_eq_sum_range]
      simp [Polynomial.coeff_map]
      rfl
    have heval :
        (Polynomial.map (algebraMap R.M0 R.L) F).eval R.α =
          ∑ i : I,
            algebraMap R.M0 R.L (F.coeff (i : ℕ)) * R.α ^ (i : ℕ) := by
      rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range,
        ← Fin.sum_univ_eq_sum_range]
    have heval_diff :
        (∑ i : I, terms i) =
          (Polynomial.map (algebraMap R.M0 R.L)
              (Polynomial.map a.toRingHom F)).eval R.α -
            (Polynomial.map (algebraMap R.M0 R.L) F).eval R.α := by
      calc
        (∑ i : I, terms i) =
            ∑ i : I,
              (algebraMap R.M0 R.L (a (F.coeff (i : ℕ))) * R.α ^ (i : ℕ) -
                algebraMap R.M0 R.L (F.coeff (i : ℕ)) * R.α ^ (i : ℕ)) := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [terms]
          rw [sub_mul]
        _ =
            (∑ i : I,
              algebraMap R.M0 R.L (a (F.coeff (i : ℕ))) * R.α ^ (i : ℕ)) -
              ∑ i : I,
                algebraMap R.M0 R.L (F.coeff (i : ℕ)) * R.α ^ (i : ℕ) := by
          rw [Finset.sum_sub_distrib]
        _ =
            (Polynomial.map (algebraMap R.M0 R.L)
                (Polynomial.map a.toRingHom F)).eval R.α -
              (Polynomial.map (algebraMap R.M0 R.L) F).eval R.α := by
          rw [heval_map, heval]
    have horbit_zero :
        (Polynomial.map (algebraMap R.M0 R.L) F).eval R.α = 0 := by
      rw [show Polynomial.map (algebraMap R.M0 R.L) F =
          ∏ τ : R.H0,
            (Polynomial.X - Polynomial.C ((τ : R.L ≃ₐ[R.M0] R.L) R.α)) by
        simpa [F] using R.orbit_polynomial_map_eq]
      rw [Polynomial.eval_prod]
      apply Finset.prod_eq_zero (Finset.mem_univ (1 : R.H0))
      simp
    have hconj :
        Polynomial.map (algebraMap R.M0 R.L)
            (Polynomial.map a.toRingHom F) =
          ∏ τ : R.H0,
            (Polynomial.X -
              Polynomial.C
                ((R.group_equiv ρ : Gal(R.L / R.K))
                  ((τ : R.L ≃ₐ[R.M0] R.L) R.α))) := by
      simpa [F, a] using R.orbit_polynomial_conjugation ρ
    have hroot_eval :
        (Polynomial.map (algebraMap R.M0 R.L)
              (Polynomial.map a.toRingHom F)).eval R.α -
            (Polynomial.map (algebraMap R.M0 R.L) F).eval R.α =
          ∏ τ : R.H0,
            (R.α -
              (R.group_equiv ρ : Gal(R.L / R.K))
                ((τ : R.L ≃ₐ[R.M0] R.L) R.α)) := by
      rw [hconj, horbit_zero, Polynomial.eval_prod]
      simp
    have hroot_val :
        R.vL (∏ τ : R.H0,
          (R.α -
            (R.group_equiv ρ : Gal(R.L / R.K))
              ((τ : R.L ≃ₐ[R.M0] R.L) R.α))) =
          S.eLM •
            (S.downstairs.displacement (chapter05QuotientMap H σ) : WithTop ℤ) := by
      calc
        R.vL (∏ τ : R.H0,
          (R.α -
            (R.group_equiv ρ : Gal(R.L / R.K))
              ((τ : R.L ≃ₐ[R.M0] R.L) R.α))) =
            R.vL ((Polynomial.map (algebraMap R.M0 R.L)
              (Polynomial.map a.toRingHom F)).eval R.α -
              (Polynomial.map (algebraMap R.M0 R.L) F).eval R.α) := by
                rw [hroot_eval]
        _ = R.vL (∑ i : I, terms i) := by rw [heval_diff]
        _ = R.vL (terms (0 : I)) := hsum_val
        _ = S.eLM •
            (S.downstairs.displacement (chapter05QuotientMap H σ) : WithTop ℤ) := hterm0val
    have hfactor (τ : R.H0) :
        R.vL (R.α -
          (R.group_equiv ρ : Gal(R.L / R.K))
            ((τ : R.L ≃ₐ[R.M0] R.L) R.α)) =
          (S.upstairs.displacement
            (ρ * ((R.H0_equiv τ : (H ⊓ S.upstairs.lowerGroup (0 : ℝ) : Subgroup G)) : G)) :
            WithTop ℤ) := by
      have hτaction :
          (τ : R.L ≃ₐ[R.M0] R.L) R.α =
            (R.group_equiv
              ((R.H0_equiv τ : (H ⊓ S.upstairs.lowerGroup (0 : ℝ) : Subgroup G)) : G) :
              Gal(R.L / R.K)) R.α := by
        simpa using R.H0_action_compat (R.H0_equiv τ)
      have hmulaction :
          (R.group_equiv
              (ρ * ((R.H0_equiv τ : (H ⊓ S.upstairs.lowerGroup (0 : ℝ) : Subgroup G)) : G)) :
              Gal(R.L / R.K)) R.α =
            (R.group_equiv ρ : Gal(R.L / R.K))
              ((R.group_equiv
                ((R.H0_equiv τ : (H ⊓ S.upstairs.lowerGroup (0 : ℝ) : Subgroup G)) : G) :
                Gal(R.L / R.K)) R.α) := by
        rw [map_mul]
        rfl
      have hmem :
          ρ * ((R.H0_equiv τ :
            (H ⊓ S.upstairs.lowerGroup (0 : ℝ) : Subgroup G)) : G) ∈
            S.upstairs.lowerGroup (0 : ℝ) := by
        exact (S.upstairs.lowerGroup (0 : ℝ)).mul_mem hρ0
          (R.H0_equiv τ).property.2
      have hdisp := R.upstairs_displacement (hcoset_ne (R.H0_equiv τ)) hmem
      calc
        R.vL (R.α -
            (R.group_equiv ρ : Gal(R.L / R.K))
              ((τ : R.L ≃ₐ[R.M0] R.L) R.α)) =
            R.vL (R.α -
              (R.group_equiv
                (ρ * ((R.H0_equiv τ :
                  (H ⊓ S.upstairs.lowerGroup (0 : ℝ) : Subgroup G)) : G)) :
                Gal(R.L / R.K)) R.α) := by
                  rw [hτaction, hmulaction]
        _ = R.vL (-((R.group_equiv
              (ρ * ((R.H0_equiv τ :
                (H ⊓ S.upstairs.lowerGroup (0 : ℝ) : Subgroup G)) : G)) :
              Gal(R.L / R.K)) R.α - R.α)) := by
                congr 1
                ring
        _ = (S.upstairs.displacement
            (ρ * ((R.H0_equiv τ :
              (H ⊓ S.upstairs.lowerGroup (0 : ℝ) : Subgroup G)) : G)) : WithTop ℤ) := by
                rw [R.vL.map_neg, hdisp]
    have hroot_product_val :
        R.vL (∏ τ : R.H0,
          (R.α -
            (R.group_equiv ρ : Gal(R.L / R.K))
              ((τ : R.L ≃ₐ[R.M0] R.L) R.α))) =
          ∑ τ : R.H0,
            (S.upstairs.displacement
              (ρ * ((R.H0_equiv τ :
                (H ⊓ S.upstairs.lowerGroup (0 : ℝ) : Subgroup G)) : G)) : WithTop ℤ) := by
      have hmap_prod (s : Finset R.H0) :
          R.vL (s.prod (fun τ =>
            R.α -
              (R.group_equiv ρ : Gal(R.L / R.K))
                ((τ : R.L ≃ₐ[R.M0] R.L) R.α))) =
            s.sum (fun τ => R.vL (R.α -
              (R.group_equiv ρ : Gal(R.L / R.K))
                ((τ : R.L ≃ₐ[R.M0] R.L) R.α))) := by
        induction s using Finset.induction_on with
        | empty => simp
        | @insert τ s hτ ih =>
            rw [Finset.prod_insert hτ, AddValuation.map_mul, ih,
              Finset.sum_insert hτ]
      calc
        R.vL (∏ τ : R.H0,
          (R.α -
            (R.group_equiv ρ : Gal(R.L / R.K))
              ((τ : R.L ≃ₐ[R.M0] R.L) R.α))) =
            ∑ τ : R.H0, R.vL (R.α -
              (R.group_equiv ρ : Gal(R.L / R.K))
                ((τ : R.L ≃ₐ[R.M0] R.L) R.α)) := hmap_prod Finset.univ
        _ = _ := by
          apply Finset.sum_congr rfl
          intro τ hτ
          exact hfactor τ
    have hroot_value_sum :
        S.eLM •
            (S.downstairs.displacement (chapter05QuotientMap H σ) : WithTop ℤ) =
          ∑ τ : R.H0,
            (S.upstairs.displacement
              (ρ * ((R.H0_equiv τ :
                (H ⊓ S.upstairs.lowerGroup (0 : ℝ) : Subgroup G)) : G)) : WithTop ℤ) := by
      calc
        S.eLM •
            (S.downstairs.displacement (chapter05QuotientMap H σ) : WithTop ℤ) =
            R.vL (∏ τ : R.H0,
              (R.α -
                (R.group_equiv ρ : Gal(R.L / R.K))
                  ((τ : R.L ≃ₐ[R.M0] R.L) R.α))) := hroot_val.symm
        _ = _ := hroot_product_val
    have hsum_H0 :
        (∑ τ : R.H0,
          (S.upstairs.displacement
            (ρ * ((R.H0_equiv τ :
              (H ⊓ S.upstairs.lowerGroup (0 : ℝ) : Subgroup G)) : G)) : WithTop ℤ)) =
          ∑ γ : (H ⊓ S.upstairs.lowerGroup (0 : ℝ) : Subgroup G),
            (S.upstairs.displacement (ρ * (γ : G)) : WithTop ℤ) := by
      exact Fintype.sum_equiv R.H0_equiv _ _ (fun τ => rfl)
    have hvalue_K :
        S.eLM •
            (S.downstairs.displacement (chapter05QuotientMap H σ) : WithTop ℤ) =
          ∑ γ : (H ⊓ S.upstairs.lowerGroup (0 : ℝ) : Subgroup G),
            (S.upstairs.displacement (ρ * (γ : G)) : WithTop ℤ) :=
      hroot_value_sum.trans hsum_H0
    have hnsmul_ed :
        S.eLM •
            (S.downstairs.displacement (chapter05QuotientMap H σ) : WithTop ℤ) =
          ((S.eLM * S.downstairs.displacement (chapter05QuotientMap H σ) : ℕ) : WithTop ℤ) := by
      change S.eLM •
          ((S.downstairs.displacement (chapter05QuotientMap H σ) : ℤ) : WithTop ℤ) =
        ((S.eLM * S.downstairs.displacement (chapter05QuotientMap H σ) : ℤ) : WithTop ℤ)
      rw [← WithTop.coe_nsmul]
      congr 1
    have hnat_K :
        S.eLM * S.downstairs.displacement (chapter05QuotientMap H σ) =
          ∑ γ : (H ⊓ S.upstairs.lowerGroup (0 : ℝ) : Subgroup G),
            S.upstairs.displacement (ρ * (γ : G)) := by
      have h := hvalue_K
      rw [hnsmul_ed] at h
      exact_mod_cast h
    have hsum_K_nat :
        (∑ τ : H, S.upstairs.displacement (ρ * (τ : G))) =
          ∑ γ : (H ⊓ S.upstairs.lowerGroup (0 : ℝ) : Subgroup G),
            S.upstairs.displacement (ρ * (γ : G)) := by
      exact_mod_cast hsum_K
    have hnat_H :
        S.eLM * S.downstairs.displacement (chapter05QuotientMap H σ) =
          ∑ τ : H, S.upstairs.displacement (ρ * (τ : G)) :=
      hnat_K.trans hsum_K_nat.symm
    have hrat_sum :
        (S.eLM : ℚ) * (S.downstairs.displacement (chapter05QuotientMap H σ) : ℚ) =
          ∑ τ : H, (S.upstairs.displacement (ρ * (τ : G)) : ℚ) := by
      have h := congrArg (fun n : ℕ => (n : ℚ)) hnat_H
      simpa [Nat.cast_mul] using h
    have hrat_sum_sigma :
        (S.eLM : ℚ) * (S.downstairs.displacement (chapter05QuotientMap H σ) : ℚ) =
          ∑ τ : H, (S.upstairs.displacement (σ * (τ : G)) : ℚ) := by
      calc
        (S.eLM : ℚ) *
            (S.downstairs.displacement (chapter05QuotientMap H σ) : ℚ) =
            ∑ τ : H, (S.upstairs.displacement (ρ * (τ : G)) : ℚ) := hrat_sum
        _ = ∑ τ : H, (S.upstairs.displacement (σ * (τ : G)) : ℚ) :=
          hsum_representative hρmap
    have he : (S.eLM : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt S.eLM_pos)
    calc
      (S.downstairs.displacement (chapter05QuotientMap H σ) : ℚ) =
          (1 / (S.eLM : ℚ)) *
            ((S.eLM : ℚ) *
              (S.downstairs.displacement (chapter05QuotientMap H σ) : ℚ)) := by
                field_simp
      _ = (1 / (S.eLM : ℚ)) *
          ∑ τ : H, (S.upstairs.displacement (σ * (τ : G)) : ℚ) := by
            rw [hrat_sum_sigma]
  · have hqdisp0 : S.downstairs.displacement (chapter05QuotientMap H σ) = 0 := by
      by_contra hd
      have hdpos : 1 ≤ S.downstairs.displacement (chapter05QuotientMap H σ) := by
        omega
      exact hq0 (by simpa using
        ((S.downstairs.lower_nat_mem_iff hq_ne 0).2 hdpos))
    have hupper_zero : ∀ τ : H,
        S.upstairs.displacement (σ * (τ : G)) = 0 := by
      intro τ
      have htq : chapter05QuotientMap H (τ : G) = 1 := by
        apply MonoidHom.mem_ker.mp
        rw [Chapter05QuotientRamificationSetup.quotient_map_kernel H]
        exact τ.property
      have hne : σ * (τ : G) ≠ 1 := by
        intro hτ
        apply hq_ne
        calc
          chapter05QuotientMap H σ =
              chapter05QuotientMap H σ * 1 := by simp
          _ = chapter05QuotientMap H σ * chapter05QuotientMap H (τ : G) := by
            rw [htq]
          _ = chapter05QuotientMap H (σ * (τ : G)) := by
            rw [map_mul]
          _ = 1 := by rw [hτ]; simp
      by_contra hd
      have hdpos : 1 ≤ S.upstairs.displacement (σ * (τ : G)) := by
        omega
      have hmem := (S.upstairs.lower_nat_mem_iff hne 0).2 hdpos
      apply hq0
      rw [S.downstairs_lower_zero_eq_inertia_image]
      exact ⟨σ * (τ : G), (by simpa using hmem), by
          simp [chapter05QuotientMap, map_mul]⟩
    simp [hqdisp0, hupper_zero]

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

private def chapter05SubgroupRamificationFiltration
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (D : Chapter05RamificationFiltration G) :
    Chapter05RamificationFiltration H :=
  { lowerGroup := fun u => (D.lowerGroup u).comap H.subtype
    lower_antitone := by
      intro u v huv
      exact Subgroup.comap_mono (D.lower_antitone huv)
    lower_normal := by
      intro u
      exact (D.lower_normal u).comap H.subtype
    lower_neg := by
      intro u hu hneg
      rw [D.lower_neg u hu hneg]
      rfl
    lower_real_convention := by
      intro m u hmu hu
      rw [D.lower_real_convention m u hmu hu]
    lower_eventually_trivial := by
      obtain ⟨b, hb⟩ := D.lower_eventually_trivial
      refine ⟨b, ?_⟩
      intro m hm
      rw [hb m hm]
      rw [MonoidHom.comap_bot, Subgroup.ker_subtype]
    displacement := fun σ => D.displacement (σ : G)
    displacement_one := by
      simpa using D.displacement_one
    lower_nat_mem_iff := by
      intro σ hσ n
      rw [Subgroup.mem_comap]
      apply D.lower_nat_mem_iff
      intro hσ1
      apply hσ
      exact Subtype.ext hσ1 }

private theorem chapter05_herbrand_slope_interval_integrable_for_clock
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (a b : ℝ) :
    IntervalIntegrable (chapter05HerbrandSlope D) MeasureTheory.volume a b := by
  have hpiece : ∀ j : ℕ,
      IntervalIntegrable (chapter05HerbrandSlope D) MeasureTheory.volume
        (j : ℝ) ((j + 1 : ℕ) : ℝ) := by
    intro j
    have hconst : Set.EqOn (chapter05HerbrandSlope D)
        (fun _ : ℝ =>
          (Nat.card (D.lowerGroup (j + 1 : ℕ)) : ℝ) /
            Nat.card (D.lowerGroup 0))
        (Set.uIoo (j : ℝ) ((j + 1 : ℕ) : ℝ)) := by
      intro t ht
      have ht' : (j : ℝ) < t ∧ t < ((j + 1 : ℕ) : ℝ) := by
        simpa [Set.uIoo_of_le (by norm_num :
          (j : ℝ) ≤ ((j + 1 : ℕ) : ℝ))] using ht
      have ht0 : ¬t ≤ 0 := by
        have hj : (0 : ℝ) ≤ (j : ℝ) := by positivity
        linarith
      rw [chapter05HerbrandSlope, if_neg ht0]
      rw [D.lower_real_convention j t ht'.1 ht'.2.le]
    exact (intervalIntegrable_congr_uIoo hconst).mpr intervalIntegrable_const
  have hnat : ∀ j : ℕ,
      IntervalIntegrable (chapter05HerbrandSlope D) MeasureTheory.volume
        0 (j : ℝ) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        have htrans := ih.trans (hpiece j)
        simpa [Nat.cast_add, Nat.cast_one] using htrans
  have hneg : ∀ x y : ℝ, x ≤ 0 → y ≤ 0 →
      IntervalIntegrable (chapter05HerbrandSlope D) MeasureTheory.volume x y := by
    intro x y hx hy
    rcases le_total x y with hxy | hyx
    · have hconst : Set.EqOn (chapter05HerbrandSlope D)
          (fun _ : ℝ => (1 : ℝ)) (Set.uIoo x y) := by
        intro t ht
        have ht' : x < t ∧ t < y := by
          simpa [Set.uIoo_of_le hxy] using ht
        rw [chapter05HerbrandSlope, if_pos (le_trans ht'.2.le hy)]
      exact (intervalIntegrable_congr_uIoo hconst).mpr intervalIntegrable_const
    · have hconst : Set.EqOn (chapter05HerbrandSlope D)
          (fun _ : ℝ => (1 : ℝ)) (Set.uIoo x y) := by
        intro t ht
        have ht' : y < t ∧ t < x := by
          simpa [Set.uIoo_of_ge hyx] using ht
        rw [chapter05HerbrandSlope, if_pos (le_trans ht'.2.le hx)]
      exact (intervalIntegrable_congr_uIoo hconst).mpr intervalIntegrable_const
  have hpos : ∀ {x y : ℝ}, 0 ≤ x → x ≤ y →
      IntervalIntegrable (chapter05HerbrandSlope D) MeasureTheory.volume x y := by
    intro x y hx hxy
    obtain ⟨N, hN⟩ := exists_nat_ge y
    have h0N : (0 : ℝ) ≤ (N : ℝ) := le_trans hx (hxy.trans hN)
    apply (hnat N).mono_set
    intro t ht
    have htab : t ∈ Set.Icc x y := by
      simpa [Set.uIcc_of_le hxy] using ht
    have ht0N : t ∈ Set.Icc (0 : ℝ) (N : ℝ) := by
      exact ⟨le_trans hx htab.1, le_trans htab.2 hN⟩
    simpa [Set.uIcc_of_le h0N] using ht0N
  have hle : ∀ {x y : ℝ}, x ≤ y →
      IntervalIntegrable (chapter05HerbrandSlope D) MeasureTheory.volume x y := by
    intro x y hxy
    by_cases hy : y ≤ 0
    · exact hneg x y (hxy.trans hy) hy
    · have hy' : 0 ≤ y := le_of_not_ge hy
      by_cases hx : x ≤ 0
      · exact (hneg x 0 hx le_rfl).trans (hpos (x := 0) (y := y) le_rfl hy')
      · exact hpos (x := x) (y := y) (le_of_not_ge hx) hxy
  rcases le_total a b with hab | hba
  · exact hle hab
  · exact (hle hba).symm

private theorem chapter05_herbrand_function_sub_eq_integral_for_clock
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    chapter05HerbrandFunction D b - chapter05HerbrandFunction D a =
      ∫ t in a..b, chapter05HerbrandSlope D t := by
  have hFa : chapter05HerbrandFunction D a =
      ∫ t in (0 : ℝ)..a, chapter05HerbrandSlope D t := by
    by_cases ha0 : a = 0
    · subst a
      simp [chapter05HerbrandFunction]
    · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      rw [chapter05HerbrandFunction, if_neg (not_le.mpr ha_pos)]
  have hFb : chapter05HerbrandFunction D b =
      ∫ t in (0 : ℝ)..b, chapter05HerbrandSlope D t := by
    by_cases hb0 : b = 0
    · subst b
      simp [chapter05HerbrandFunction]
    · have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      rw [chapter05HerbrandFunction, if_neg (not_le.mpr hb_pos)]
  rw [hFb, hFa]
  exact intervalIntegral.integral_interval_sub_left
    (chapter05_herbrand_slope_interval_integrable_for_clock D 0 b)
    (chapter05_herbrand_slope_interval_integrable_for_clock D 0 a)

private theorem chapter05_herbrand_clock_of_cardinality_transport
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (Dtop : Chapter05RamificationFiltration G)
    (Dsub : Chapter05RamificationFiltration H)
    (Ddown : Chapter05RamificationFiltration (G ⧸ H))
    (hcard_mul : ∀ {t : ℝ}, 0 < t →
      Nat.card (Ddown (chapter05HerbrandFunction Dsub t)) *
          Nat.card (Dsub t) = Nat.card (Dtop t))
    (hcard_zero :
      Nat.card (Ddown 0) * Nat.card (Dsub 0) = Nat.card (Dtop 0))
    (u : ℝ) :
    chapter05HerbrandFunction Dtop u =
      chapter05HerbrandFunction Ddown
        (chapter05HerbrandFunction Dsub u) := by
  have hsub_pos {t : ℝ} (ht : 0 < t) :
      0 < chapter05HerbrandFunction Dsub t := by
    have hmono : StrictMonoOn (chapter05HerbrandFunction Dsub)
        (Set.Ici (-1 : ℝ)) :=
      (chapter05_herbrand_function_is_continuous_increasing_piecewise_linear
        Dsub).2.1
    have hstrict : chapter05HerbrandFunction Dsub 0 <
        chapter05HerbrandFunction Dsub t := by
      apply hmono
      · norm_num
      · change (-1 : ℝ) ≤ t
        linarith
      · exact ht
    simpa [chapter05_herbrand_function_zero Dsub] using hstrict
  have hslope_comp {t : ℝ} (ht : 0 < t) :
      chapter05HerbrandSlope Ddown (chapter05HerbrandFunction Dsub t) *
          chapter05HerbrandSlope Dsub t =
        chapter05HerbrandSlope Dtop t := by
    have hcard := congrArg (fun n : ℕ => (n : ℝ)) (hcard_mul ht)
    have hcard0 := congrArg (fun n : ℕ => (n : ℝ)) hcard_zero
    have hpos_down : 0 < (Nat.card (Ddown
        (chapter05HerbrandFunction Dsub t)) : ℝ) := by
      exact_mod_cast Nat.card_pos
    have hpos_sub : 0 < (Nat.card (Dsub t) : ℝ) := by
      exact_mod_cast Nat.card_pos
    have hpos_up : 0 < (Nat.card (Dtop t) : ℝ) := by
      exact_mod_cast Nat.card_pos
    have hpos_down0 : 0 < (Nat.card (Ddown 0) : ℝ) := by
      exact_mod_cast Nat.card_pos
    have hpos_sub0 : 0 < (Nat.card (Dsub 0) : ℝ) := by
      exact_mod_cast Nat.card_pos
    have hpos_up0 : 0 < (Nat.card (Dtop 0) : ℝ) := by
      exact_mod_cast Nat.card_pos
    rw [chapter05HerbrandSlope, if_neg (not_le.mpr (hsub_pos ht)),
      chapter05HerbrandSlope, if_neg (not_le.mpr ht),
      chapter05HerbrandSlope, if_neg (not_le.mpr ht)]
    norm_num at hcard hcard0 ⊢
    field_simp [ne_of_gt hpos_down0, ne_of_gt hpos_sub0,
      ne_of_gt hpos_up0]
    nlinarith
  have hsub_nonneg {t : ℝ} (ht : 0 ≤ t) :
      0 ≤ chapter05HerbrandFunction Dsub t := by
    have hmono : MonotoneOn (chapter05HerbrandFunction Dsub)
        (Set.Ici (-1 : ℝ)) :=
      (chapter05_herbrand_function_is_continuous_increasing_piecewise_linear
        Dsub).2.1.monotoneOn
    have hzero : (0 : ℝ) ∈ Set.Ici (-1 : ℝ) := by norm_num
    have ht' : t ∈ Set.Ici (-1 : ℝ) := by
      change (-1 : ℝ) ≤ t
      linarith
    have hle := hmono hzero ht' ht
    simpa [chapter05_herbrand_function_zero Dsub] using hle
  have hsegment : ∀ (m : ℕ) {x : ℝ},
      (m : ℝ) ≤ x → x ≤ ((m + 1 : ℕ) : ℝ) →
      chapter05HerbrandFunction Ddown (chapter05HerbrandFunction Dsub x) -
          chapter05HerbrandFunction Ddown
            (chapter05HerbrandFunction Dsub (m : ℝ)) =
        chapter05HerbrandFunction Dtop x -
          chapter05HerbrandFunction Dtop (m : ℝ) := by
    intro m x hmx hxnext
    by_cases hxeq : x = (m : ℝ)
    · subst x
      ring
    have hmlt : (m : ℝ) < x := lt_of_le_of_ne hmx (Ne.symm hxeq)
    have hxpos : 0 < x := by
      have hmnonneg : (0 : ℝ) ≤ (m : ℝ) := by positivity
      linarith
    have hm_dom : (m : ℝ) ∈ Set.Ici (-1 : ℝ) := by
      change (-1 : ℝ) ≤ (m : ℝ)
      linarith
    have hsub_m_nonneg : 0 ≤ chapter05HerbrandFunction Dsub (m : ℝ) := by
      have hmono : MonotoneOn (chapter05HerbrandFunction Dsub)
          (Set.Ici (-1 : ℝ)) :=
        (chapter05_herbrand_function_is_continuous_increasing_piecewise_linear
          Dsub).2.1.monotoneOn
      have hzero_dom : (0 : ℝ) ∈ Set.Ici (-1 : ℝ) := by norm_num
      have hle := hmono hzero_dom hm_dom (by positivity)
      simpa [chapter05_herbrand_function_zero Dsub] using hle
    have hsub_x_nonneg : 0 ≤ chapter05HerbrandFunction Dsub x :=
      hsub_nonneg (le_of_lt hxpos)
    have hcont_sub : ContinuousOn (chapter05HerbrandFunction Dsub)
        (Set.uIcc (m : ℝ) x) := by
      apply (chapter05_herbrand_function_is_continuous_increasing_piecewise_linear
        Dsub).1.mono
      intro y hy
      have hy' : y ∈ Set.Icc (m : ℝ) x := by
        simpa [Set.uIcc_of_le hmx] using hy
      have hm_dom' : (-1 : ℝ) ≤ y := le_trans hm_dom hy'.1
      exact hm_dom'
    have hderiv_sub : ∀ y ∈ Set.Ioo (m : ℝ) x,
        HasDerivAt (chapter05HerbrandFunction Dsub)
          (chapter05HerbrandSlope Dsub y) y := by
      intro y hy
      have hypos : 0 < y := by
        have hmnonneg : (0 : ℝ) ≤ (m : ℝ) := by positivity
        linarith [hy.1]
      have hy_upper : y ≤ ((m + 1 : ℕ) : ℝ) :=
        le_trans hy.2.le hxnext
      let c : ℝ :=
        (Nat.card (Dsub.lowerGroup (m + 1 : ℕ)) : ℝ) /
          (Nat.card (Dsub.lowerGroup 0) : ℝ)
      have hlocal : (fun z : ℝ => chapter05HerbrandFunction Dsub z) =ᶠ[𝓝 y]
          (fun z : ℝ => chapter05HerbrandFunction Dsub (m : ℝ) +
            (z - (m : ℝ)) * c) := by
        have hnhds : Set.Ioo (m : ℝ) ((m + 1 : ℕ) : ℝ) ∈ 𝓝 y :=
          Ioo_mem_nhds hy.1 (lt_of_lt_of_le hy.2 hxnext)
        filter_upwards [hnhds] with z hz
        have hdiff :=
          (chapter05_herbrand_function_is_continuous_increasing_piecewise_linear
            Dsub).2.2 m hz.1.le hz.2.le le_rfl (by norm_num)
        dsimp [c]
        linarith
      have haffine : HasDerivAt (fun z : ℝ =>
          chapter05HerbrandFunction Dsub (m : ℝ) +
            (z - (m : ℝ)) * c) c y := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
          mul_comm, mul_left_comm, mul_assoc] using
          (((hasDerivAt_id' y).sub_const (m : ℝ)).mul_const c).const_add
            (chapter05HerbrandFunction Dsub (m : ℝ))
      have hderiv := haffine.congr_of_eventuallyEq hlocal
      have hc : chapter05HerbrandSlope Dsub y = c := by
        rw [chapter05HerbrandSlope, if_neg (not_le.mpr hypos)]
        rw [Dsub.lower_real_convention m y hy.1 hy_upper]
      exact hderiv.congr_deriv hc.symm
    have hderiv_nonneg : ∀ y ∈ Set.Ioo (m : ℝ) x,
        0 ≤ chapter05HerbrandSlope Dsub y := by
      intro y hy
      rw [chapter05HerbrandSlope]
      split_ifs with hy0
      · positivity
      · have hnum : 0 ≤ (Nat.card (Dsub.lowerGroup y) : ℝ) := by
          positivity
        have hden : 0 < (Nat.card (Dsub.lowerGroup 0) : ℝ) := by
          exact_mod_cast Nat.card_pos
        positivity
    have hchange :
        (∫ y in (m : ℝ)..x,
          (chapter05HerbrandSlope Ddown ∘ chapter05HerbrandFunction Dsub) y *
            chapter05HerbrandSlope Dsub y) =
          ∫ z in chapter05HerbrandFunction Dsub (m : ℝ)..
            chapter05HerbrandFunction Dsub x,
            chapter05HerbrandSlope Ddown z := by
      simpa only [Function.comp_apply] using
        (intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
          (f := chapter05HerbrandFunction Dsub)
          (f' := chapter05HerbrandSlope Dsub)
          (g := chapter05HerbrandSlope Ddown)
          hcont_sub
          (by simpa [min_eq_left hmx, max_eq_right hmx] using hderiv_sub)
          (by simpa [min_eq_left hmx, max_eq_right hmx] using hderiv_nonneg))
    have hintegrand :
        (∫ y in (m : ℝ)..x,
          (chapter05HerbrandSlope Ddown ∘ chapter05HerbrandFunction Dsub) y *
            chapter05HerbrandSlope Dsub y) =
          ∫ y in (m : ℝ)..x, chapter05HerbrandSlope Dtop y := by
      apply intervalIntegral.integral_congr_Ioo_of_le hmx
      intro y hy
      exact hslope_comp (by
        have hmnonneg : (0 : ℝ) ≤ (m : ℝ) := by positivity
        linarith [hy.1])
    have hdown_diff := chapter05_herbrand_function_sub_eq_integral_for_clock
      Ddown hsub_m_nonneg hsub_x_nonneg
    have htop_diff := chapter05_herbrand_function_sub_eq_integral_for_clock
      Dtop (a := (m : ℝ)) (b := x) (by positivity) (by positivity)
    calc
      chapter05HerbrandFunction Ddown (chapter05HerbrandFunction Dsub x) -
          chapter05HerbrandFunction Ddown
            (chapter05HerbrandFunction Dsub (m : ℝ)) =
          ∫ z in chapter05HerbrandFunction Dsub (m : ℝ)..
            chapter05HerbrandFunction Dsub x,
            chapter05HerbrandSlope Ddown z := hdown_diff
      _ = ∫ y in (m : ℝ)..x,
          (chapter05HerbrandSlope Ddown ∘ chapter05HerbrandFunction Dsub) y *
            chapter05HerbrandSlope Dsub y := hchange.symm
      _ = ∫ y in (m : ℝ)..x, chapter05HerbrandSlope Dtop y := hintegrand
      _ = chapter05HerbrandFunction Dtop x -
          chapter05HerbrandFunction Dtop (m : ℝ) := htop_diff.symm
  have hclock_nat : ∀ m : ℕ,
      chapter05HerbrandFunction Dtop (m : ℝ) =
        chapter05HerbrandFunction Ddown
          (chapter05HerbrandFunction Dsub (m : ℝ)) := by
    intro m
    induction m with
    | zero => simp [chapter05_herbrand_function_zero]
    | succ m ihm =>
        have hseg := hsegment m (x := ((m + 1 : ℕ) : ℝ))
          (by norm_num) (by norm_num)
        calc
          chapter05HerbrandFunction Dtop ((m + 1 : ℕ) : ℝ) =
              chapter05HerbrandFunction Dtop (m : ℝ) +
                (chapter05HerbrandFunction Dtop ((m + 1 : ℕ) : ℝ) -
                  chapter05HerbrandFunction Dtop (m : ℝ)) := by ring
          _ = chapter05HerbrandFunction Dtop (m : ℝ) +
                (chapter05HerbrandFunction Ddown
                  (chapter05HerbrandFunction Dsub ((m + 1 : ℕ) : ℝ)) -
                chapter05HerbrandFunction Ddown
                  (chapter05HerbrandFunction Dsub (m : ℝ))) := by
              rw [hseg]
          _ = chapter05HerbrandFunction Ddown
                (chapter05HerbrandFunction Dsub ((m + 1 : ℕ) : ℝ)) := by
              rw [ihm]
              ring
  by_cases hu : u ≤ 0
  · simp [chapter05_herbrand_function_of_nonpositive _ hu]
  · let m : ℕ := ⌊u⌋₊
    have hmu : (m : ℝ) ≤ u := Nat.floor_le (le_of_not_ge hu)
    have hum : u ≤ ((m + 1 : ℕ) : ℝ) := by
      simpa [m] using (Nat.lt_floor_add_one u).le
    have hseg := hsegment m hmu hum
    calc
      chapter05HerbrandFunction Dtop u =
          chapter05HerbrandFunction Dtop (m : ℝ) +
            (chapter05HerbrandFunction Dtop u -
              chapter05HerbrandFunction Dtop (m : ℝ)) := by ring
      _ = chapter05HerbrandFunction Dtop (m : ℝ) +
            (chapter05HerbrandFunction Ddown
              (chapter05HerbrandFunction Dsub u) -
              chapter05HerbrandFunction Ddown
                (chapter05HerbrandFunction Dsub (m : ℝ))) := by
          rw [hseg]
      _ = chapter05HerbrandFunction Ddown
          (chapter05HerbrandFunction Dsub u) := by
          rw [hclock_nat m]
          ring

private theorem chapter05_comap_subtype_card
    {G : Type*} [Group G] [Fintype G]
    (H K : Subgroup G) :
    Nat.card (K.comap H.subtype) = Nat.card (H ⊓ K : Subgroup G) := by
  rw [Subgroup.comap_subtype]
  exact Nat.card_congr
    { toFun := fun x =>
        ⟨(x : G), And.intro x.1.property x.property⟩
      invFun := fun y =>
        ⟨⟨(y : G), y.property.1⟩, y.property.2⟩
      left_inv := by
        intro x
        rfl
      right_inv := by
        intro y
        rfl }

private theorem chapter05_lower_mem_iff_real_quotient
    {G : Type*} [Group G] [Fintype G]
    (D : Chapter05RamificationFiltration G) {σ : G} (hσ : σ ≠ 1)
    {t : ℝ} (ht : 0 < t) :
    σ ∈ D.lowerGroup t ↔
      t ≤ ((D.displacement σ - 1 : ℕ) : ℝ) := by
  let d : ℕ := D.displacement σ
  by_cases hnat : ∃ n : ℕ, t = (n : ℝ)
  · obtain ⟨n, rfl⟩ := hnat
    rw [D.lower_nat_mem_iff hσ n]
    have hnpos : 0 < n := by exact_mod_cast ht
    constructor
    · intro h
      have hn : n ≤ d - 1 := by
        dsimp [d]
        omega
      exact_mod_cast hn
    · intro h
      have hn : n ≤ d - 1 := by
        exact_mod_cast h
      dsimp [d] at hn
      have hn' : n + 1 ≤ D.displacement σ := by omega
      simpa [d] using hn'
  · let n : ℕ := ⌊t⌋₊
    have ht_nonneg : 0 ≤ t := le_of_lt ht
    have hn_le : (n : ℝ) ≤ t := by
      exact Nat.floor_le ht_nonneg
    have hn_lt : (n : ℝ) < t := by
      exact lt_of_le_of_ne hn_le (Ne.symm (by
        intro h
        apply hnat
        exact ⟨n, h⟩))
    have ht_upper : t ≤ ((n + 1 : ℕ) : ℝ) := by
      simpa [Nat.cast_add, Nat.cast_one, n] using
        (Nat.lt_floor_add_one t).le
    rw [D.lower_real_convention n t hn_lt ht_upper,
      D.lower_nat_mem_iff hσ (n + 1)]
    have ht_upper' : t ≤ (n : ℝ) + 1 := by
      simpa [Nat.cast_add, Nat.cast_one] using ht_upper
    constructor
    · intro h
      have hd : n + 2 ≤ d := by
        dsimp [d]
        exact h
      have hd_one : 1 ≤ d := by omega
      have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
        rw [Nat.cast_sub hd_one]
        norm_num
      have hd_real : (n : ℝ) + 2 ≤ (d : ℝ) := by
        exact_mod_cast hd
      rw [hcast]
      linarith
    · intro h
      by_contra hnot
      have hd : d ≤ n + 1 := by
        dsimp [d] at h ⊢
        omega
      have hd_real : (d : ℝ) ≤ (n : ℝ) + 1 := by
        exact_mod_cast hd
      have ht_pos : 0 < t := lt_of_le_of_lt (by positivity) hn_lt
      have h' : t ≤ ((d - 1 : ℕ) : ℝ) := by
        simpa [d] using h
      have hd_one : 1 ≤ d := by
        by_contra hd0
        have hdzero : d = 0 := Nat.eq_zero_of_not_pos hd0
        rw [hdzero] at h'
        norm_num at h'
        linarith
      have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
        rw [Nat.cast_sub hd_one]
        norm_num
      rw [hcast] at h
      linarith

private theorem chapter05_map_card_mul_inf_kernel
    {G G' : Type*} [Group G] [Group G'] [Fintype G]
    (f : G →* G') (K : Subgroup G) :
    Nat.card (K.map f) * Nat.card (K ⊓ f.ker : Subgroup G) = Nat.card K := by
  have hcard := Subgroup.card_mul_index
    ((K ⊓ f.ker).subgroupOf K)
  have hindex : ((K ⊓ f.ker).subgroupOf K).index =
      Nat.card (K.map f) := by
    change (K ⊓ f.ker).relIndex K = Nat.card (K.map f)
    rw [inf_comm K f.ker, Subgroup.inf_relIndex_right, Subgroup.relIndex_ker]
  have hker_card :
      Nat.card ((K ⊓ f.ker).subgroupOf K) =
        Nat.card (K ⊓ f.ker : Subgroup G) := by
    calc
      Nat.card ((K ⊓ f.ker).subgroupOf K) =
          Nat.card (((K ⊓ f.ker).subgroupOf K).map K.subtype) :=
        (Subgroup.card_subtype K ((K ⊓ f.ker).subgroupOf K)).symm
      _ = Nat.card (K ⊓ f.ker : Subgroup G) := by
        rw [Subgroup.subgroupOf_map_subtype]
        rw [inf_eq_left.mpr inf_le_left]
  rw [hindex] at hcard
  rw [hker_card] at hcard
  simpa [Nat.mul_comm] using hcard

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
  classical
  let Dsub : Chapter05RamificationFiltration H :=
    chapter05SubgroupRamificationFiltration H S.upstairs
  have hsub_card (m : ℕ) :
      Nat.card (Dsub.lowerGroup (m : ℝ)) =
        Nat.card (H ⊓ S.upstairs.lowerGroup (m : ℝ) : Subgroup G) := by
    calc
      Nat.card (Dsub.lowerGroup (m : ℝ)) =
          Nat.card ((S.upstairs.lowerGroup (m : ℝ)).comap H.subtype) := by
        rfl
      _ = Nat.card (H ⊓ S.upstairs.lowerGroup (m : ℝ) : Subgroup G) :=
        chapter05_comap_subtype_card H _
  have hsub_card0 : Nat.card (Dsub.lowerGroup 0) = S.eLM := by
    calc
      Nat.card (Dsub.lowerGroup 0) =
          Nat.card (H ⊓ S.upstairs.lowerGroup 0 : Subgroup G) := by
            simpa using hsub_card 0
      _ = S.eLM := S.eLM_eq_inertia_card.symm
  have hFsub_nat (m : ℕ) :
      chapter05HerbrandFunction Dsub (m : ℝ) =
        (1 / (S.eLM : ℝ)) *
          ∑ j ∈ Finset.Icc 1 m,
            (Nat.card (H ⊓ S.upstairs.lowerGroup (j : ℝ) :
              Subgroup G) : ℝ) := by
    rw [chapter05_herbrand_function_interval_formula Dsub m
      le_rfl (by norm_num)]
    have hsum :
        (∑ j ∈ Finset.Icc 1 m,
          (Nat.card (Dsub.lowerGroup (j : ℝ)) : ℝ)) =
          ∑ j ∈ Finset.Icc 1 m,
            (Nat.card (H ⊓ S.upstairs.lowerGroup (j : ℝ) :
              Subgroup G) : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hsub_card j]
    simp only [sub_self, hsum, hsub_card0]
    ring
  have hcoset_max (σ : G) :
      ∃ n : ℕ,
        (∀ τ : H,
          S.upstairs.displacement (σ * (τ : G)) ≤ n) ∧
        (∃ τ : H,
          S.upstairs.displacement (σ * (τ : G)) = n) := by
    let U : Finset ℕ := Finset.univ.image (fun τ : H =>
      S.upstairs.displacement (σ * (τ : G)))
    have hUne : U.Nonempty := by
      refine ⟨S.upstairs.displacement (σ * (1 : H)), ?_⟩
      exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
    let n : ℕ := U.max' hUne
    have hnU : n ∈ U := Finset.max'_mem U hUne
    obtain ⟨τ₀, hτ₀, hτ₀eq⟩ := Finset.mem_image.mp hnU
    refine ⟨n, ?_, ⟨τ₀, hτ₀eq⟩⟩
    intro τ
    exact Finset.le_max' U _
      (Finset.mem_image.mpr ⟨τ, Finset.mem_univ _, rfl⟩)
  have hmap_lower (σ : G) (t : ℝ) :
      chapter05QuotientMap H σ ∈
          (S.upstairs.lowerGroup t).map (chapter05QuotientMap H) ↔
        ∃ τ : H, σ * (τ : G) ∈ S.upstairs.lowerGroup t := by
    rw [Subgroup.mem_map]
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
      simp [hτq]
  have hlower_image {σ : G} {t : ℝ} (ht : 0 < t) :
      chapter05QuotientMap H σ ∈
          S.downstairs.lowerGroup (chapter05HerbrandFunction Dsub t) ↔
        chapter05QuotientMap H σ ∈
          (S.upstairs.lowerGroup t).map (chapter05QuotientMap H) := by
    obtain ⟨n, hn_upper, hn_attained⟩ := hcoset_max σ
    by_cases hq1 : chapter05QuotientMap H σ = 1
    · simp [hq1]
    · have hσ : σ ∉ H := by
        intro hσH
        apply hq1
        exact (QuotientGroup.eq_one_iff _).2 hσH
      have hcoset_ne_one : ∀ τ : H, σ * (τ : G) ≠ 1 := by
        intro τ hτ
        apply hσ
        rw [eq_inv_of_mul_eq_one_left hτ]
        exact H.inv_mem τ.property
      have hmax_iff :
          (∃ τ : H, σ * (τ : G) ∈ S.upstairs.lowerGroup t) ↔
            t ≤ ((n - 1 : ℕ) : ℝ) := by
        constructor
        · rintro ⟨τ, hτ⟩
          have hmem :=
            (chapter05_lower_mem_iff_real_quotient
              S.upstairs (hcoset_ne_one τ) ht).mp hτ
          have hsub :
              S.upstairs.displacement (σ * (τ : G)) - 1 ≤ n - 1 := by
            exact Nat.sub_le_sub_right (hn_upper τ) 1
          have hsub' :
              ((S.upstairs.displacement
                (σ * (τ : G)) - 1 : ℕ) : ℝ) ≤
                ((n - 1 : ℕ) : ℝ) := by
            exact_mod_cast hsub
          linarith
        · intro htn
          obtain ⟨τ₀, hτ₀⟩ := hn_attained
          have hmem :
              t ≤ ((S.upstairs.displacement
                (σ * (τ₀ : G)) - 1 : ℕ) : ℝ) := by
            simpa [hτ₀] using htn
          exact ⟨τ₀,
            (chapter05_lower_mem_iff_real_quotient
              S.upstairs (hcoset_ne_one τ₀) ht).mpr hmem⟩
      have hFsub_pos : 0 < chapter05HerbrandFunction Dsub t := by
        have hmono : StrictMonoOn
            (chapter05HerbrandFunction Dsub)
            (Set.Ici (-1 : ℝ)) :=
          (chapter05_herbrand_function_is_continuous_increasing_piecewise_linear
            Dsub).2.1
        have hstrict :
            chapter05HerbrandFunction Dsub 0 <
              chapter05HerbrandFunction Dsub t := by
          apply hmono
          · norm_num
          · change (-1 : ℝ) ≤ t
            linarith
          · exact ht
        simpa [chapter05_herbrand_function_zero Dsub] using hstrict
      rw [chapter05_lower_mem_iff_real_quotient S.downstairs
        hq1 hFsub_pos, hmap_lower σ t]
      by_cases hn0 : n = 0
      · have hallzero : ∀ τ : H,
            S.upstairs.displacement (σ * (τ : G)) = 0 := by
          intro τ
          have := hn_upper τ
          omega
        have hsumzero :
            (∑ τ : H, S.upstairs.displacement (σ * (τ : G))) = 0 := by
          simp [hallzero]
        have hdisp := chapter05_coset_displacement_identity_integral_form
          H S (σ := σ) hσ
        have hdzero :
            S.downstairs.displacement (chapter05QuotientMap H σ) = 0 := by
          have : S.eLM *
              S.downstairs.displacement
                (chapter05QuotientMap H σ) = 0 := by
            rw [hdisp]
            exact hsumzero
          exact (Nat.mul_eq_zero.mp this).resolve_left
            (Nat.ne_of_gt S.eLM_pos)
        constructor
        · intro h
          exfalso
          rw [hdzero] at h
          norm_num at h
          exact (not_lt_of_ge h) hFsub_pos
        · intro h
          rw [hdzero]
          have htn := hmax_iff.mp h
          rw [hn0] at htn
          norm_num at htn
          exfalso
          linarith
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        have hn_attained' := hn_attained
        obtain ⟨τ₀, hτ₀⟩ := hn_attained
        have hsum_ge :
            S.upstairs.displacement (σ * (τ₀ : G)) ≤
              ∑ τ : H, S.upstairs.displacement (σ * (τ : G)) := by
          simpa using (Finset.single_le_sum
            (s := Finset.univ)
            (f := fun τ : H =>
              S.upstairs.displacement (σ * (τ : G)))
            (a := τ₀)
            (fun τ _ => Nat.zero_le _) (Finset.mem_univ τ₀))
        have hsum_pos :
            0 < ∑ τ : H,
              S.upstairs.displacement (σ * (τ : G)) := by
          rw [hτ₀] at hsum_ge
          exact lt_of_lt_of_le hnpos hsum_ge
        have hdisp := chapter05_coset_displacement_identity_integral_form
          H S (σ := σ) hσ
        have hdpos :
            0 < S.downstairs.displacement
              (chapter05QuotientMap H σ) := by
          have hprod : 0 < S.eLM *
              S.downstairs.displacement
                (chapter05QuotientMap H σ) := by
            rw [hdisp]
            exact hsum_pos
          by_contra hdnot
          have hdzero :
              S.downstairs.displacement
                (chapter05QuotientMap H σ) = 0 :=
            Nat.eq_zero_of_not_pos hdnot
          rw [hdzero] at hprod
          norm_num at hprod
        have hthreshold := chapter05_coset_threshold_identity
          H S hσ n hn_upper hn_attained' (by omega)
        have hthreshold_real :
            ((S.downstairs.displacement
              (chapter05QuotientMap H σ) - 1 : ℕ) : ℝ) =
              (1 / (S.eLM : ℝ)) *
                ∑ j ∈ Finset.Icc 1 (n - 1),
                  (Nat.card (H ⊓ S.upstairs.lowerGroup (j : ℝ) :
                    Subgroup G) : ℝ) := by
          have h := congrArg (fun q : ℚ => (q : ℝ)) hthreshold
          norm_num at h ⊢
          exact h
        have hFthreshold :
            ((S.downstairs.displacement
              (chapter05QuotientMap H σ) - 1 : ℕ) : ℝ) =
              chapter05HerbrandFunction Dsub ((n - 1 : ℕ) : ℝ) := by
          rw [hFsub_nat (n - 1)]
          exact hthreshold_real
        have hmono : StrictMonoOn
            (chapter05HerbrandFunction Dsub)
            (Set.Ici (-1 : ℝ)) :=
          (chapter05_herbrand_function_is_continuous_increasing_piecewise_linear
            Dsub).2.1
        rw [hFthreshold]
        constructor
        · intro h
          apply hmax_iff.mpr
          by_contra hnot
          have hlt : ((n - 1 : ℕ) : ℝ) < t := by
            exact lt_of_not_ge hnot
          have hxdom : ((n - 1 : ℕ) : ℝ) ∈ Set.Ici (-1) := by
            change (-1 : ℝ) ≤ ((n - 1 : ℕ) : ℝ)
            have hxnonneg : (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
              exact_mod_cast (Nat.zero_le (n - 1))
            exact le_trans (by norm_num) hxnonneg
          have htdom : t ∈ Set.Ici (-1) := by
            exact le_trans (by norm_num) ht.le
          have hstrict := hmono hxdom htdom hlt
          linarith
        · intro h
          have htn := hmax_iff.mp h
          by_cases heq : t = ((n - 1 : ℕ) : ℝ)
          · simp [heq]
          · have hlt : t < ((n - 1 : ℕ) : ℝ) :=
              lt_of_le_of_ne htn heq
            have hxdom : ((n - 1 : ℕ) : ℝ) ∈ Set.Ici (-1) := by
              change (-1 : ℝ) ≤ ((n - 1 : ℕ) : ℝ)
              have hxnonneg : (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
                exact_mod_cast (Nat.zero_le (n - 1))
              exact le_trans (by norm_num) hxnonneg
            have htdom : t ∈ Set.Ici (-1) := by
              exact le_trans (by norm_num) ht.le
            have hstrict := hmono htdom hxdom hlt
            exact hstrict.le
  have hsub_card_real {t : ℝ} (ht : 0 < t) :
      Nat.card (Dsub.lowerGroup t) =
        Nat.card (H ⊓ S.upstairs.lowerGroup t : Subgroup G) := by
    rw [show Dsub.lowerGroup t =
      (S.upstairs.lowerGroup t).comap H.subtype by rfl]
    exact chapter05_comap_subtype_card H _
  have hgroup_image {t : ℝ} (ht : 0 < t) :
      S.downstairs.lowerGroup (chapter05HerbrandFunction Dsub t) =
        (S.upstairs.lowerGroup t).map (chapter05QuotientMap H) := by
    ext x
    obtain ⟨σ, rfl⟩ :=
      Chapter05QuotientRamificationSetup.quotient_map_surjective H x
    exact hlower_image ht
  have hcard_mul {t : ℝ} (ht : 0 < t) :
      Nat.card (S.downstairs.lowerGroup
          (chapter05HerbrandFunction Dsub t)) *
        Nat.card (Dsub.lowerGroup t) =
      Nat.card (S.upstairs.lowerGroup t) := by
    rw [hgroup_image ht]
    have hmap := chapter05_map_card_mul_inf_kernel
      (chapter05QuotientMap H) (S.upstairs.lowerGroup t)
    rw [Chapter05QuotientRamificationSetup.quotient_map_kernel H] at hmap
    calc
      Nat.card ((S.upstairs.lowerGroup t).map
          (chapter05QuotientMap H)) * Nat.card (Dsub.lowerGroup t) =
          Nat.card ((S.upstairs.lowerGroup t).map
            (chapter05QuotientMap H)) *
            Nat.card (H ⊓ S.upstairs.lowerGroup t : Subgroup G) := by
              rw [hsub_card_real ht]
      _ = Nat.card (S.upstairs.lowerGroup t) := by
        simpa [inf_comm] using hmap
  have hcard_zero :
      Nat.card (S.downstairs.lowerGroup 0) *
          Nat.card (Dsub.lowerGroup 0) =
        Nat.card (S.upstairs.lowerGroup 0) := by
    have hmap := chapter05_map_card_mul_inf_kernel
      (chapter05QuotientMap H) (S.upstairs.lowerGroup 0)
    rw [Chapter05QuotientRamificationSetup.quotient_map_kernel H] at hmap
    calc
      Nat.card (S.downstairs.lowerGroup 0) *
          Nat.card (Dsub.lowerGroup 0) =
        Nat.card ((S.upstairs.lowerGroup 0).map
            (chapter05QuotientMap H)) *
            Nat.card (H ⊓ S.upstairs.lowerGroup 0 : Subgroup G) := by
              rw [S.downstairs_lower_zero_eq_inertia_image,
                hsub_card0, S.eLM_eq_inertia_card]
      _ = Nat.card (S.upstairs.lowerGroup 0) := by
        simpa [inf_comm] using hmap
  have hlower_image_all {t : ℝ} (ht : (-1 : ℝ) ≤ t) :
      S.downstairs.lowerGroup (chapter05HerbrandFunction Dsub t) =
        (S.upstairs.lowerGroup t).map (chapter05QuotientMap H) := by
    by_cases ht0 : t ≤ 0
    · by_cases htneg : t < 0
      · rw [chapter05_herbrand_function_of_nonpositive Dsub ht0,
          S.downstairs.lower_neg t ht htneg,
          S.upstairs.lower_neg t ht htneg]
        exact (Subgroup.map_top_of_surjective (chapter05QuotientMap H)
          (Chapter05QuotientRamificationSetup.quotient_map_surjective H)).symm
      · have ht_eq : t = 0 := le_antisymm ht0 (le_of_not_gt htneg)
        subst t
        rw [chapter05_herbrand_function_zero Dsub,
          S.downstairs_lower_zero_eq_inertia_image]
    · exact hgroup_image (lt_of_not_ge ht0)
  have hclock (x : ℝ) :
      chapter05HerbrandFunction S.upstairs x =
        chapter05HerbrandFunction S.downstairs
          (chapter05HerbrandFunction Dsub x) :=
    chapter05_herbrand_clock_of_cardinality_transport H S.upstairs Dsub
      S.downstairs hcard_mul hcard_zero x
  let u : ℝ := chapter05HerbrandInverse S.upstairs v
  have hu_spec : chapter05HerbrandFunction S.upstairs u = v := by
    dsimp [u]
    exact chapter05_herbrand_inverse_spec S.upstairs hup v
  have hu : (-1 : ℝ) ≤ u := by
    by_contra hnot
    have hu_lt : u < (-1 : ℝ) := lt_of_not_ge hnot
    have hu_nonpos : u ≤ 0 := by linarith
    have hidentity :=
      chapter05_herbrand_function_of_nonpositive S.upstairs hu_nonpos
    have huv : u = v := by
      calc
        u = chapter05HerbrandFunction S.upstairs u := hidentity.symm
        _ = v := hu_spec
    linarith
  have hdown_inv :
      chapter05HerbrandInverse S.downstairs v =
        chapter05HerbrandFunction Dsub u := by
    apply hdown.1
    calc
      chapter05HerbrandFunction S.downstairs
          (chapter05HerbrandInverse S.downstairs v) = v :=
        chapter05_herbrand_inverse_spec S.downstairs hdown v
      _ = chapter05HerbrandFunction S.upstairs u := hu_spec.symm
      _ = chapter05HerbrandFunction S.downstairs
          (chapter05HerbrandFunction Dsub u) := hclock u
  rw [chapter05_upper_group_eq_lower_at_inverse S.downstairs hdown hv,
    chapter05UpperQuotientImage,
    chapter05_upper_group_eq_lower_at_inverse S.upstairs hup hv,
    hdown_inv]
  change S.downstairs.lowerGroup (chapter05HerbrandFunction Dsub u) =
    (S.upstairs.lowerGroup u).map (chapter05QuotientMap H)
  exact hlower_image_all hu

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
