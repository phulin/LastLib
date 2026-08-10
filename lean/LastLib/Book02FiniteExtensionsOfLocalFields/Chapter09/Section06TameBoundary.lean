import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.Section05TwoStageIntegralDescription

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09

open scoped BigOperators Polynomial
open Ideal IsLocalRing Polynomial

noncomputable section

/-! ## Book 2, Chapter 9.6: the tame boundary -/

/-- Tameness at the exponential characteristic of the residue field.  The
use of coprimality makes the characteristic-zero case automatic because
ringExpChar is one there. -/
def chapter09Tame (k : Type*) [Ring k] (e : ℕ) : Prop :=
  Nat.Coprime e (ringExpChar k)

/-- Wild ramification in the separable-residue setting. -/
def chapter09Wild (k : Type*) [Ring k] (e : ℕ)
    (residueSeparable : Prop) : Prop :=
  residueSeparable ∧ ¬ chapter09Tame k e

/-- In the separable setting every finite ramification index is either tame or
wild. -/
theorem chapter09_tame_or_wild
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    (e : ℕ) (hseparable : Algebra.IsSeparable k l) :
    chapter09Tame k e ∨ chapter09Wild k e (Algebra.IsSeparable k l) := by
  by_cases ht : chapter09Tame k e
  · exact Or.inl ht
  · exact Or.inr ⟨hseparable, ht⟩

/-- A characteristic-exponent form of the wild condition.  The hypothesis
that p is the positive residue characteristic is kept explicit, so no
characteristic-zero assertion is silently treated as wild. -/
theorem chapter09_wild_iff_prime_dvd
    (k : Type*) [Field k] (p e : ℕ) [Fact p.Prime] [CharP k p]
    (hchar : ringExpChar k = p) :
    (¬ chapter09Tame k e) ↔ p ∣ e := by
  sorry

/-- Group-theoretic content of the finite-Galois assertion: inertia has order
e, wild inertia is the maximal normal p-subgroup, and the quotient is cyclic
of order prime to p. -/
structure Chapter09WildInertiaStructure
    (G : Type*) [Group G] [Finite G] (p e : ℕ) where
  inertia : Subgroup G
  inertia_order : Nat.card inertia = e
  wild_inertia : Subgroup G
  wild_normal : wild_inertia.Normal
  wild_is_p_group : IsPGroup p wild_inertia
  wild_maximal :
    ∀ H : Subgroup G, H.Normal → IsPGroup p H → H ≤ wild_inertia
  quotient_cyclic :
    letI : wild_inertia.Normal := wild_normal
    IsCyclic (G ⧸ wild_inertia)
  quotient_prime_to_p :
    letI : wild_inertia.Normal := wild_normal
    Nat.Coprime (Nat.card (G ⧸ wild_inertia)) p

/-- Finite-Galois ramification data over a perfect residue field. -/
structure Chapter09FiniteGaloisRamificationData
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsDomain A] [IsDomain B] [IsLocalRing A] [IsLocalRing B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsLocalHom (algebraMap A B)] [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [Module.Finite A B] [Module.IsTorsionFree A B]
    [FaithfulSMul A B] [IsIntegralClosure B A L]
    [Module.Finite (chapter09BaseResidueField A)
      (chapter09ExtensionResidueField B)]
    [Chapter09FiniteLocalExtension A B K L] [IsGalois K L]
    [PerfectField (chapter09BaseResidueField A)]
    [Finite (L ≃ₐ[K] L)] where
  group_data : Chapter09WildInertiaStructure (L ≃ₐ[K] L)
    (ringExpChar (chapter09BaseResidueField A))
    (LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex A B
      (IsLocalRing.maximalIdeal B))

/-- The finite-Galois perfect-residue theorem in the form consumed by later
proofs. -/
theorem chapter09_finite_galois_inertia_and_wild_quotient
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsDomain A] [IsDomain B] [IsLocalRing A] [IsLocalRing B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsLocalHom (algebraMap A B)] [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [Module.Finite A B] [Module.IsTorsionFree A B]
    [FaithfulSMul A B] [IsIntegralClosure B A L]
    [Module.Finite (chapter09BaseResidueField A)
      (chapter09ExtensionResidueField B)]
    [Chapter09FiniteLocalExtension A B K L] [IsGalois K L]
    [PerfectField (chapter09BaseResidueField A)]
    [Finite (L ≃ₐ[K] L)] :
    Nonempty (Chapter09FiniteGaloisRamificationData A B K L) := by
  sorry

/-- A post-base-change Kummer presentation of a totally tamely ramified
extension.  The fields in this structure are the fields after adjoining the
needed roots of unity or making the suitable unramified base change. -/
structure Chapter09TameKummerPresentation
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (e : ℕ) (π : K) where
  tame : chapter09Tame K e
  alpha : L
  alpha_pow_eq_uniformizer : alpha ^ e = algebraMap K L π
  generates : Algebra.adjoin K ({alpha} : Set L) = ⊤
  degree : Module.finrank K L = e

/-- The elementary prime-to-p power-map interface on principal units. -/
structure Chapter09TamePrincipalUnitNormData
    (U V : Type*) [Group U] [Group V] (e : ℕ) where
  power_map_bijective : Function.Bijective (fun u : U => u ^ e)
  norm : U →* V
  norm_surjective : Function.Surjective norm

/-- Tameness is the exact interface used in the chapter for invertibility of
the principal-unit power map and the well-behaved norm map. -/
theorem chapter09_tame_principal_unit_interface
    (U V : Type*) [Group U] [Group V] (e : ℕ)
    (d : Chapter09TamePrincipalUnitNormData U V e) :
    Function.Bijective (fun u : U => u ^ e) ∧ Function.Surjective d.norm := by
  exact ⟨d.power_map_bijective, d.norm_surjective⟩

/- The chapter deliberately stops before introducing higher ramification
filtrations, jumps, different ideals, or discriminants. -/

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09
