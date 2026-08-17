import LastLib.Book01ValuationsDVRsAndCompletions.Chapter13.Section05CohenRingsExistence
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Derivation.ToSquareZero

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter13

open Filter Ideal IsLocalRing

noncomputable section

/-! # Book 1, Chapter 13, Section 13.6: The lifting property and uniqueness of Cohen rings -/

universe u v

/-- A square-zero thickening with nilpotent prime. -/
def Chapter13SquareZeroPrimeExtension
    (R : Type u) [CommRing R] (I : Ideal R) (p : ℕ) : Prop :=
  I ^ 2 = ⊥ ∧ ∃ M : ℕ, (p : R) ^ M = 0

/-- Compatibility of a ring map with specified residue-field identifications. -/
def Chapter13ResidueMapCompatibility
    {C A k ℓ : Type*}
    [CommRing C] [IsLocalRing C] [CommRing A] [IsLocalRing A]
    [Field k] [Field ℓ]
    (eC : Chapter13ResidueRing C ≃+* k)
    (eA : Chapter13ResidueRing A ≃+* ℓ)
    (φ : k →+* ℓ) (u : C →+* A) : Prop :=
  ∀ c : C,
    eA (Chapter13ResidueMap A (u c)) = φ (eC (Chapter13ResidueMap C c))

/-- Convergence of a sequence for an adic filtration. -/
def Chapter13AdicSequenceConverges
    {A : Type*} [CommRing A] (I : Ideal A)
    (z : ℕ → A) (x : A) : Prop :=
  ∀ n : ℕ, Filter.Eventually
    (fun m : ℕ => z m - x ∈ I ^ n) (atTop : Filter ℕ)

/-- The completed polynomial ring used as a smooth presentation of a Cohen ring. -/
abbrev Chapter13CohenSmoothPresentation
    (k : Type u) (p : ℕ) : Type u :=
  AdicCompletion (Ideal.span {(p : MvPolynomial k ℤ)}) (MvPolynomial k ℤ)

/-- The variable indexed by a residue-field element in the smooth presentation. -/
def Chapter13CohenSmoothVariable
    (k : Type u) (p : ℕ) (x : k) : Chapter13CohenSmoothPresentation k p :=
  algebraMap (MvPolynomial k ℤ) (Chapter13CohenSmoothPresentation k p)
    (MvPolynomial.X x)

/-- Rigidity of Cohen-ring maps with fixed residue map and fixed `p`-basis lifts. -/
theorem chapter13_cohen_lift_rigidity
    {C R : Type u} [CommRing C] [IsLocalRing C] [CommRing R]
    {k : Type v} [Field k] (p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (hC : Chapter13IsCohenRing C k p)
    (I : Ideal R) (hI : Chapter13SquareZeroPrimeExtension R I p)
    (B : Set k) (hB : Chapter13PBasis (Chapter13PthPowerSubfield k p) B p)
    (γ : B → C) (eC : Chapter13ResidueRing C ≃+* k)
    (hγ : ∀ b : B, eC (Chapter13ResidueMap C (γ b)) = b)
    (u u' : C →+* R)
    (hquot : (Ideal.Quotient.mk I).comp u = (Ideal.Quotient.mk I).comp u')
    (hlift : ∀ b : B, u (γ b) = u' (γ b)) :
    u = u' := by
  sorry

/-- The completed polynomial presentation has the expected finite-level quotients. -/
theorem chapter13_cohen_smooth_presentation_quotients
    (k : Type u) [Field k] (p n : ℕ) [Fact (Nat.Prime p)] [CharP k p] :
    Nonempty
      (Chapter13CohenSmoothPresentation k p ⧸
          Ideal.span {((p : Chapter13CohenSmoothPresentation k p) ^ n)} ≃+*
        MvPolynomial k (ZMod (p ^ n))) := by
  sorry

/-- Homomorphisms out of the smooth presentation are arbitrary on its variables. -/
theorem chapter13_cohen_smooth_presentation_ring_homs
    {k R : Type u} [Field k] [CommRing R] (p M : ℕ)
    [Fact (Nat.Prime p)] [CharP k p]
    (hM : (p : R) ^ M = 0) :
    Function.Bijective
      (fun f : Chapter13CohenSmoothPresentation k p →+* R =>
        fun x : k => f (Chapter13CohenSmoothVariable k p x)) := by
  sorry

/-- Derivations out of the smooth presentation are arbitrary on its variables. -/
theorem chapter13_cohen_smooth_presentation_derivations
    {k N : Type u} [Field k] [AddCommGroup N]
    (p M : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    [Module (Chapter13CohenSmoothPresentation k p) N]
    (hM : ∀ n : N,
      (p : Chapter13CohenSmoothPresentation k p) ^ M • n = 0) :
    Function.Bijective
      (fun D : Derivation ℤ (Chapter13CohenSmoothPresentation k p) N =>
        fun x : k => D (Chapter13CohenSmoothVariable k p x)) := by
  sorry

/-- A chosen set of residue lifts gives a surjective map from the smooth presentation. -/
theorem chapter13_cohen_smooth_presentation_surjective
    {C k : Type u} [CommRing C] [IsLocalRing C] [Field k] (p : ℕ)
    [Fact (Nat.Prime p)] [CharP k p]
    (hC : Chapter13IsCohenRing C k p)
    (eC : Chapter13ResidueRing C ≃+* k) (c : k → C)
    (hc : ∀ x : k, eC (Chapter13ResidueMap C (c x)) = x) :
    ∃ π : Chapter13CohenSmoothPresentation k p →+* C,
      Function.Surjective π ∧
        (∀ x : k, π (Chapter13CohenSmoothVariable k p x) = c x) ∧
        ∃ J : Ideal (Chapter13CohenSmoothPresentation k p),
          J = RingHom.ker π ∧
            ∀ n : ℕ, ∀ z,
              z ∈ J ∧ z ∈ Ideal.span {((p : Chapter13CohenSmoothPresentation k p) ^ n)} ↔
              ∃ y ∈ J, z = (p : Chapter13CohenSmoothPresentation k p) ^ n * y := by
  sorry

/-- Cohen rings lift maps across square-zero thickenings with nilpotent prime. -/
theorem chapter13_cohen_lift_across_square_zero
    {C R : Type u} [CommRing C] [IsLocalRing C] [CommRing R]
    {k : Type v} [Field k] (p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (hC : Chapter13IsCohenRing C k p)
    (I : Ideal R) (hI : Chapter13SquareZeroPrimeExtension R I p)
    (v : C →+* (R ⧸ I)) :
    ∃ u : C →+* R, (Ideal.Quotient.mk I).comp u = v := by
  sorry

/-- The mapping property of a Cohen ring into a complete local ring. -/
theorem chapter13_cohen_ring_mapping_property
    {C A : Type u} [CommRing C] [IsLocalRing C] [CommRing A] [IsLocalRing A]
    {k ℓ : Type v} [Field k] [Field ℓ] (p : ℕ)
    [Fact (Nat.Prime p)] [CharP k p] [CharP ℓ p]
    (hC : Chapter13IsCohenRing C k p)
    (hA : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (eC : Chapter13ResidueRing C ≃+* k)
    (eA : Chapter13ResidueRing A ≃+* ℓ)
    (φ : k →+* ℓ) :
    ∃ u : C →+* A,
      IsLocalHom u ∧ Chapter13ResidueMapCompatibility eC eA φ u := by
  sorry

/-- Uniqueness of the mapping property after fixing lifts of a `p`-basis. -/
theorem chapter13_cohen_ring_mapping_property_unique
    {C A : Type u} [CommRing C] [IsLocalRing C] [CommRing A] [IsLocalRing A]
    {k ℓ : Type v} [Field k] [Field ℓ] (p : ℕ)
    [Fact (Nat.Prime p)] [CharP k p] [CharP ℓ p]
    (hC : Chapter13IsCohenRing C k p)
    (hA : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (eC : Chapter13ResidueRing C ≃+* k)
    (eA : Chapter13ResidueRing A ≃+* ℓ)
    (φ : k →+* ℓ) (B : Set k)
    (hB : Chapter13PBasis (Chapter13PthPowerSubfield k p) B p)
    (γ : B → C) (u u' : C →+* A)
    (hγ : ∀ b : B, eC (Chapter13ResidueMap C (γ b)) = b)
    (hu : IsLocalHom u ∧ Chapter13ResidueMapCompatibility eC eA φ u)
    (hu' : IsLocalHom u' ∧ Chapter13ResidueMapCompatibility eC eA φ u')
    (hlift : ∀ b : B, u (γ b) = u' (γ b)) :
    u = u' := by
  sorry

/-- Existence and isomorphism of maps between Cohen rings with the same residue field. -/
theorem chapter13_cohen_ring_uniqueness
    {C C' k : Type u} [CommRing C] [IsLocalRing C]
    [CommRing C'] [IsLocalRing C'] [Field k] (p : ℕ)
    [Fact (Nat.Prime p)] [CharP k p]
    (hC : Chapter13IsCohenRing C k p)
    (hC' : Chapter13IsCohenRing C' k p)
    (eC : Chapter13ResidueRing C ≃+* k)
    (eC' : Chapter13ResidueRing C' ≃+* k) :
    (∃ u : C →+* C', IsLocalHom u ∧
      Chapter13ResidueMapCompatibility eC eC' (RingHom.id k) u) ∧
      (∀ u : C →+* C', IsLocalHom u →
        Chapter13ResidueMapCompatibility eC eC' (RingHom.id k) u →
        ∃ e : C ≃+* C', e.toRingHom = u) := by
  sorry

/-- An imperfect residue field permits nontrivial Cohen-ring automorphisms over the residue map. -/
theorem chapter13_imperfect_cohen_noncanonical_automorphism
    {C k : Type u} [CommRing C] [IsLocalRing C] [Field k] (p : ℕ)
    [Fact (Nat.Prime p)] [CharP k p]
    (hC : Chapter13IsCohenRing C k p)
    (eC : Chapter13ResidueRing C ≃+* k)
    (B : Set k) (hB : Chapter13PBasis (Chapter13PthPowerSubfield k p) B p)
    (b : B) (γ : B → C) (hp : (p : C) ≠ 0)
    (hγ : ∀ x : B, eC (Chapter13ResidueMap C (γ x)) = x) :
    ∃ σ : C →+* C,
      IsLocalHom σ ∧
        Chapter13ResidueMapCompatibility eC eC (RingHom.id k) σ ∧
        σ (γ b) = γ b + (p : C) ∧
        Function.Bijective σ ∧ σ ≠ RingHom.id C := by
  sorry

/-- Perfect residue fields have unique Cohen-ring maps. -/
theorem chapter13_perfect_cohen_mapping_unique
    {C A : Type u} [CommRing C] [IsLocalRing C] [CommRing A] [IsLocalRing A]
    {k ℓ : Type v} [Field k] [Field ℓ] (p : ℕ)
    [Fact (Nat.Prime p)] [CharP k p] [CharP ℓ p]
    (hC : Chapter13IsCohenRing C k p)
    (hperfect : Chapter13PerfectAtPrime k p)
    (hA : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (eC : Chapter13ResidueRing C ≃+* k)
    (eA : Chapter13ResidueRing A ≃+* ℓ) (φ : k →+* ℓ) :
    ∃! u : C →+* A,
      IsLocalHom u ∧ Chapter13ResidueMapCompatibility eC eA φ u := by
  obtain ⟨u, hu, hcompat⟩ := chapter13_cohen_ring_mapping_property
    p hC hA eC eA φ
  refine ⟨u, ⟨hu, hcompat⟩, ?_⟩
  intro v hv
  let B : Set k := ∅
  have hB : Chapter13PBasis (Chapter13PthPowerSubfield k p) B p :=
    chapter13_perfect_field_empty_p_basis p hperfect
  symm
  apply chapter13_cohen_ring_mapping_property_unique
    p hC hA eC eA φ B hB (fun b => b.property.elim) u v
  · intro b
    exact b.property.elim
  · exact ⟨hu, hcompat⟩
  · exact hv
  · intro b
    exact b.property.elim

/-- The multiplicative Teichmuller section in the perfect case. -/
theorem chapter13_teichmuller_lift
    {C k : Type u} [CommRing C] [IsLocalRing C] [Field k] (p : ℕ)
    [Fact (Nat.Prime p)] [CharP k p]
    (hC : Chapter13IsCohenRing C k p)
    (hperfect : Chapter13PerfectAtPrime k p)
    (eC : Chapter13ResidueRing C ≃+* k) :
    ∃ τ : k →* C,
      (∀ x : k, eC (Chapter13ResidueMap C (τ x)) = x) ∧
        (∀ x : k, ∃ y : ℕ → C,
          (∀ n : ℕ,
            eC (Chapter13ResidueMap C (y n)) ^ (p ^ n) = x) ∧
          Chapter13AdicSequenceConverges
            (IsLocalRing.maximalIdeal C)
            (fun n : ℕ => (y n) ^ (p ^ n)) (τ x)) := by
  sorry

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter13
