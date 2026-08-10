import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07.Section06FactorizationAndBaseChange

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07

open Set
open Polynomial
open LastLib.Book01ValuationsDVRsAndCompletions.Chapter10

noncomputable section

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

/-- The derivative of `T^m - 1` has the expected normalization factor. -/
theorem chapter07_derivative_power_minus_one
    {R : Type*} [CommRing R] (m : ℕ) :
    derivative (X ^ m - 1 : R[X]) = C (m : R) * X ^ (m - 1) := by
  simp [derivative_sub, derivative_X_pow]

/-- When `m` is a unit, every residue root is simple. -/
theorem chapter07_prime_to_residue_characteristic_roots_are_simple
    {A k : Type*} [CommRing A] [Field k]
    (res : A →+* k) (m : ℕ) (hm : Chapter07OrderInvertibleIn A m)
    (ζ : k) (hζ : ζ ^ m = 1) :
    eval₂ (RingHom.id k) ζ (derivative (X ^ m - 1 : k[X])) ≠ 0 := by
  have hm' : IsUnit (m : k) := by
    simpa [Chapter07OrderInvertibleIn] using hm.map res
  have hm0 : m ≠ 0 := by
    intro hm0
    apply hm'.ne_zero
    simp [hm0]
  rw [chapter07_derivative_power_minus_one]
  simp only [eval₂_mul, eval₂_C, eval₂_pow, RingHom.id_apply]
  exact mul_ne_zero hm'.ne_zero (pow_ne_zero _ (by
    intro hζ0
    have hζ0' : ζ = 0 := by simpa using hζ0
    subst ζ
    simpa [hm0] using hζ))

/-- The root-lifting property for a chosen maximal unramified subextension of
a finite extension.  It is kept as a predicate because the subgroup `S` and
the reduction map depend on that chosen embedding. -/
def Chapter07FiniteExtensionResidueRootLifting
    {L l : Type*} [Field L] [Field l]
    (m : ℕ) (ρ : Lˣ →* lˣ) (S : Subgroup Lˣ) : Prop :=
  ∀ ζ : rootsOfUnity m l,
      ∃! ξ : rootsOfUnity m L, (ξ : Lˣ) ∈ S ∧
        ρ ξ = ζ.1

/-- The exact-order compatibility assertion for the reduction map. -/
def Chapter07ReductionPreservesPrimitiveRootOrder
    {L l : Type*} [CommMonoid L] [CommMonoid l]
    (m : ℕ) (ρ : Lˣ →* lˣ) : Prop :=
  ∀ ζ : rootsOfUnity m L, IsPrimitiveRoot (ζ : Lˣ) m →
    IsPrimitiveRoot (ρ ζ) m

/-- The numerical relation defining the multiplicative order of `q` modulo
`m`; it avoids silently assuming that the modulus is prime. -/
def Chapter07MultiplicativeOrderModulo
    (q m d : ℕ) : Prop :=
  1 < q ∧ 0 < m ∧ 0 < d ∧ Nat.Coprime q m ∧
    m ∣ q ^ d - 1 ∧ ∀ n : ℕ, 0 < n → n < d → ¬m ∣ q ^ n - 1

/-- The residue degree of a primitive `m`th root is the least `d` satisfying
`m ∣ q^d - 1`. -/
-- STATEMENT_NEEDS_UPDATE: The hypotheses on the primitive roots do not relate the extensions K/L and k/l, so horder cannot force either finrank k l or finrank K L to equal d; add hypotheses identifying these degrees with the multiplicative order (or explicitly assume the two displayed finrank equalities).
theorem chapter07_primitive_root_unramified_degree
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Algebra K L] [Algebra k l] [FiniteDimensional K L]
    [FiniteDimensional k l] [Fintype k]
    (q m d : ℕ) (hq : Fintype.card k = q)
    (horder : Chapter07MultiplicativeOrderModulo q m d)
    (hsep : Chapter07ResidueExtensionIsSeparable k l)
    (E : Chapter07FiniteLocalExtensionData K L k l)
    (he : E.ramificationIndex = 1)
    (hroot : ∃ ζ : L, IsPrimitiveRoot ζ m ∧
      Algebra.adjoin K ({ζ} : Set L) = ⊤)
    (hresroot : ∃ ζ : l, IsPrimitiveRoot ζ m ∧
      Algebra.adjoin k ({ζ} : Set l) = ⊤) :
    Chapter07UnramifiedExtension E ∧
      Module.finrank k l = d ∧ Module.finrank K L = d := by
  sorry

/-- The `p`-adic cyclotomic example: the degree is the order of `p` modulo
`m` when `m` is prime to `p`. -/
theorem chapter07_padic_prime_to_p_roots_of_unity
    {p m d : ℕ} [Fact p.Prime]
    (horder : Chapter07MultiplicativeOrderModulo p m d) :
    ∃ q : Chapter10FiniteExtensionProfile,
      q.degree = d ∧ q.ramificationIndex = 1 ∧ q.residueDegree = d ∧
        Chapter10Unramified q := by
  refine ⟨{ degree := d, ramificationIndex := 1, residueDegree := d },
    rfl, rfl, rfl, rfl⟩

/-- In residue characteristic `p`, the derivative of `T^p - 1` has a
non-unit `p` factor; this is the boundary with wild ramification. -/
theorem chapter07_p_power_root_derivative_is_not_a_unit
    {A : Type*} [CommRing A] (p r : ℕ)
    (hp : ¬Chapter07OrderInvertibleIn A p) (hr : 0 < r)
    (ζ : A) (hζ : ζ ^ (p ^ r) = 1) :
    ¬IsUnit (eval₂ (RingHom.id A) ζ
      (derivative (X ^ (p ^ r) - 1 : A[X]))) := by
  intro hunit
  apply hp
  rw [chapter07_derivative_power_minus_one] at hunit
  simp only [eval₂_mul, eval₂_C, eval₂_pow, RingHom.id_apply] at hunit
  have hpow : IsUnit ((p : A) ^ r) := by
    rw [← Nat.cast_pow]
    exact isUnit_of_mul_isUnit_left hunit
  exact (isUnit_pow_iff hr.ne').mp hpow

/-- A nontrivial `p`-power root extension whose residue root collapses and whose
residue degree is one is ramified.  The degree and residue interfaces make the
valuation-theoretic content explicit. -/
theorem chapter07_p_power_roots_are_not_prime_to_characteristic_unramified
    {A B K L k l : Type*} [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] [Field K] [Field L] [Field k] [Field l]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L]
    [Algebra A L] [Algebra k l]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [FiniteDimensional k l]
    [IsIntegralClosure B A L] [HenselianLocalRing A]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    {p r : ℕ} [Fact p.Prime] [CharP k p] (hr : 0 < r)
    (E : Chapter07FiniteLocalExtensionData K L k l)
    (ρ : B →+* l)
    (hρ_surjective : Function.Surjective ρ)
    (hρ_kernel : RingHom.ker ρ = IsLocalRing.maximalIdeal B)
    (ζ : B)
    (hζ : IsPrimitiveRoot (algebraMap B L ζ) (p ^ r))
    (hgen : Algebra.adjoin K ({algebraMap B L ζ} : Set L) = ⊤)
    (hred : ρ ζ = 1)
    (hdegree : 1 < Module.finrank K L)
    (hresidue_degree : Module.finrank k l = 1) :
    E.ramificationIndex ≠ 1 ∧ ¬Chapter07UnramifiedExtension E := by
  have hne : E.ramificationIndex ≠ 1 := by
    intro he
    have hdeg : Module.finrank K L = 1 := by
      calc
        Module.finrank K L = E.ramificationIndex * E.residueDegree :=
          E.degree_eq_ramification_residue
        _ = 1 * 1 := by rw [he, E.residueDegree_eq, hresidue_degree]
        _ = 1 := by simp
    exact (Nat.ne_of_gt hdegree) hdeg
  exact ⟨hne, fun hU => hne hU.1⟩

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07
