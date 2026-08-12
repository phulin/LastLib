import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
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

/-- A bijective reduction map induces a bijection on the prime-to-
residue-characteristic roots of unity. -/
theorem chapter07_roots_of_unity_reduction_bijective
    {K k : Type*} [CommMonoid K] [CommMonoid k]
    (m : ℕ) (ρ : K →* k) (hρ : Function.Bijective ρ) :
    Function.Bijective (chapter07RootsOfUnityReduction m ρ) := by
  sorry

/-- The derivative of `T^m - 1` has the expected normalization factor. -/
theorem chapter07_derivative_power_minus_one
    {R : Type*} [CommRing R] (m : ℕ) :
    derivative (X ^ m - 1 : R[X]) = C (m : R) * X ^ (m - 1) := by
  sorry

/-- When `m` is a unit, every residue root is simple. -/
theorem chapter07_prime_to_residue_characteristic_roots_are_simple
    {A k : Type*} [CommRing A] [Field k]
    (res : A →+* k) (m : ℕ) (hm : Chapter07OrderInvertibleIn A m)
    (ζ : k) (hζ : ζ ^ m = 1) :
    eval₂ (RingHom.id k) ζ (derivative (X ^ m - 1 : k[X])) ≠ 0 := by
  sorry

/-- The root-lifting property for a chosen maximal unramified subextension of
a finite extension.  It is kept as a predicate because the subgroup `S` and
the reduction map depend on that chosen embedding. -/
def Chapter07FiniteExtensionResidueRootLifting
    {L l : Type*} [Field L] [Field l]
    (m : ℕ) (ρ : Lˣ →* lˣ) (S : Subgroup Lˣ) : Prop :=
  ∀ ζ : rootsOfUnity m l,
      ∃! ξ : rootsOfUnity m L, (ξ : Lˣ) ∈ S ∧
        ρ ξ = ζ.1

/-- The chosen unramified subgroup supplies the unique lift of each residue
root. -/
theorem chapter07_finite_extension_residue_root_lifting
    {L l : Type*} [Field L] [Field l]
    (m : ℕ) (ρ : Lˣ →* lˣ) (S : Subgroup Lˣ)
    (hρ : Chapter07FiniteExtensionResidueRootLifting m ρ S) :
    ∀ ζ : rootsOfUnity m l,
      ∃! ξ : rootsOfUnity m L, (ξ : Lˣ) ∈ S ∧ ρ ξ = ζ.1 := by
  sorry

/-- Hensel's simple-root criterion lifts every residue `m`th root when `m` is
invertible in the local ring. -/
theorem chapter07_prime_to_residue_characteristic_root_lifts_uniquely
    {B l : Type*} [CommRing B] [Field l] [HenselianLocalRing B]
    (res : B →+* l) (m : ℕ) (hm : Chapter07OrderInvertibleIn B m)
    (hres : Function.Surjective res)
    (hker : RingHom.ker res = IsLocalRing.maximalIdeal B)
    (ζ : l) (hζ : ζ ^ m = 1) :
    ∃! ξ : B, ξ ^ m = 1 ∧ res ξ = ζ := by
  sorry

/-- The exact-order compatibility assertion for the reduction map. -/
def Chapter07ReductionPreservesPrimitiveRootOrder
    {L l : Type*} [CommMonoid L] [CommMonoid l]
    (m : ℕ) (ρ : Lˣ →* lˣ) : Prop :=
  ∀ ζ : rootsOfUnity m L, IsPrimitiveRoot (ζ : Lˣ) m →
    IsPrimitiveRoot (ρ ζ) m

/-- The primitive-root clause is a reusable consequence of the reduction
compatibility interface. -/
theorem chapter07_reduction_preserves_primitive_root_order
    {L l : Type*} [CommMonoid L] [CommMonoid l]
    (m : ℕ) (ρ : Lˣ →* lˣ)
    (hρ : Chapter07ReductionPreservesPrimitiveRootOrder m ρ)
    (ζ : rootsOfUnity m L) (hζ : IsPrimitiveRoot (ζ : Lˣ) m) :
    IsPrimitiveRoot (ρ ζ) m := by
  sorry

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
  sorry

/-- The residue degree of a primitive `m`th root is the least `d` satisfying
`m ∣ q^d - 1`. -/
-- SOURCE_ISSUE: The source suppresses the identifications between the field
-- extensions and the residue-field root fields.  The two degree equalities
-- are therefore explicit hypotheses in this proof-ready interface.
theorem chapter07_primitive_root_unramified_degree
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Algebra K L] [Algebra k l] [FiniteDimensional K L]
    [FiniteDimensional k l] [Fintype k]
    (q m d : ℕ) (hq : Fintype.card k = q)
    (horder : Chapter07MultiplicativeOrderModulo q m d)
    (hsep : Chapter07ResidueExtensionIsSeparable k l)
    (E : Chapter07FiniteLocalExtensionData K L k l)
    (he : E.ramificationIndex = 1)
    (hres_degree : Module.finrank k l = d)
    (hfield_degree : Module.finrank K L = d)
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
  sorry

/-- In residue characteristic `p`, the derivative of `T^p - 1` has a
non-unit `p` factor; this is the boundary with wild ramification. -/
theorem chapter07_p_power_root_derivative_is_not_a_unit
    {A : Type*} [CommRing A] (p r : ℕ)
    (hp : ¬Chapter07OrderInvertibleIn A p) (hr : 0 < r)
    (ζ : A) (hζ : ζ ^ (p ^ r) = 1) :
    ¬IsUnit (eval₂ (RingHom.id A) ζ
      (derivative (X ^ (p ^ r) - 1 : A[X]))) := by
  sorry

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
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07
