import LastLib.Book03RamificationTheory.Chapter05.Section01ANumberingDesignedForQuotients
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.Section04FixedFieldsOfInertia
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace LastLib.Book03RamificationTheory.Chapter05

noncomputable section

open scoped Classical

open scoped BigOperators

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

/--
 The finite data used by the quotient theorem.  The lower profiles are the
 actual profiles of the two valued extensions; the last field is the norm/
 displacement identity (5.1), written in integral form to avoid division in
 the data structure.  `eLM` is the ramification index of `L/M`, and its
 cardinality field records the local subgroup interpretation
 `e(L/M)=|H ∩ G_0|`.
-/
structure Chapter05QuotientRamificationSetup
    (G : Type*) [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal] where
  upstairs : Chapter05RamificationFiltration G
  downstairs : Chapter05RamificationFiltration (G ⧸ H)
  eLM : ℕ
  eLM_pos : 0 < eLM
  eLM_eq_inertia_card :
    eLM = Nat.card (H ⊓ upstairs.lowerGroup 0 : Subgroup G)
  coset_displacement_identity :
    ∀ {σ : G}, σ ∉ H →
      eLM * downstairs.displacement (chapter05QuotientMap H σ) =
        ∑ τ : H, upstairs.displacement (σ * (τ : G))

namespace Chapter05QuotientRamificationSetup

variable {G : Type*} [Group G] [Fintype G]
variable (H : Subgroup G) [H.Normal]

theorem quotient_map_surjective :
    Function.Surjective (chapter05QuotientMap H) := by
  sorry

theorem quotient_map_kernel :
    MonoidHom.ker (chapter05QuotientMap H) = H := by
  sorry

theorem quotient_exact_sequence :
    Function.MulExact (Subgroup.subtype H) (chapter05QuotientMap H) ∧
      Function.Surjective (chapter05QuotientMap H) := by
  sorry

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
  sorry

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
  sorry

/-
 The next theorem is the displacement identity quoted in the source.  We
 state it both in the exact reciprocal form and as the integral form stored
 in `Chapter05QuotientRamificationSetup`.
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
  exact S.coset_displacement_identity hσ

/- The coefficient calculation in the source is written with
   `e(L/M) * min_c v_M(σ(c)-c)` on the left.  The witness above is the local
   interface for the chosen mixed integral generator and its coefficient
   descent to `M`.
-/
theorem chapter05_orbit_polynomial_coefficient_minimum_identity
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
  sorry

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
  sorry

/-- The fixed-field identification used to read the quotient as `Gal(M/K)`. -/
theorem chapter05_fixed_field_quotient_galois_equiv
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup (Gal(L / K))) [H.Normal] :
    Nonempty
      ((Gal(L / K) ⧸ H) ≃* Gal(
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FixedField H / K)) := by
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.residue_quotient_is_fixed_field_galois_group H

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
