import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.Section03ResidueActionAndInertia
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.Section04FixedFieldsOfInertia
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section05SeveralExtensionsAndTheFundamentalEquality
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Valuation.Discrete.RankOne

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05

noncomputable section

universe u

open scoped BigOperators

/-! ## 5.7. Three instructive Galois patterns -/

/-- A residue exact sequence is split when it has a group-homomorphic section. -/
def chapter05ExtensionSplits
    {G Q : Type*} [Group G] [Group Q] (ρ : G →* Q) : Prop :=
  ∃ s : Q →* G, ρ.comp s = MonoidHom.id Q

/-- The set of lifts in `G` of a specified quotient element. -/
def chapter05QuotientLiftSet
    {G Q : Type*} [Group G] [Group Q] (ρ : G →* Q) (q : Q) : Set G :=
  {g | ρ g = q}

/-- Surjectivity supplies at least one lift of every quotient element. -/
theorem chapter05QuotientLiftSet_nonempty
    {G Q : Type*} [Group G] [Group Q] (ρ : G →* Q)
    (hρ : Function.Surjective ρ) (q : Q) :
    (chapter05QuotientLiftSet ρ q).Nonempty := by
  obtain ⟨g, hg⟩ := hρ q
  exact ⟨g, hg⟩

/-- Any two lifts of one quotient element differ by an inertia element. -/
theorem chapter05Lifts_differ_by_inertia
    {G Q : Type*} [Group G] [Group Q] (ρ : G →* Q)
    (q : Q) (g₁ g₂ : G)
    (h₁ : g₁ ∈ chapter05QuotientLiftSet ρ q)
    (h₂ : g₂ ∈ chapter05QuotientLiftSet ρ q) :
    g₂⁻¹ * g₁ ∈ MonoidHom.ker ρ := by
  change ρ g₁ = q at h₁
  change ρ g₂ = q at h₂
  change ρ (g₂⁻¹ * g₁) = 1
  rw [map_mul, map_inv, h₂, h₁, inv_mul_cancel]

/-- In an unramified Galois pattern, the residue action is an isomorphism. -/
theorem unramified_residue_action_isomorphism
    {G Q : Type*} [Group G] [Group Q] [Finite G] [Finite Q]
    (ρ : G →* Q) (hρ : Function.Surjective ρ)
    (hI : MonoidHom.ker ρ = ⊥) :
    Nonempty (G ≃* Q) := by
  exact ⟨MulEquiv.ofBijective ρ ⟨ρ.ker_eq_bot_iff.mp hI, hρ⟩⟩

/-- In a totally ramified pattern, reduction is trivial on every automorphism. -/
theorem totally_ramified_residue_action_is_trivial
    {G Q : Type*} [Group G] [Group Q] (ρ : G →* Q)
    (hI : MonoidHom.ker ρ = ⊤) :
    ∀ g : G, ρ g = 1 := by
  intro g
  change g ∈ MonoidHom.ker ρ
  rw [hI]
  simp

/-- Fixing every integral element is stronger than being invisible after reduction. -/
def chapter05IntegralActionFixed
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) (σ : chapter05DecompositionGroup F A) : Prop :=
  ∀ x : A, σ • x = x

/-- The chapter's residue-invisibility predicate for an automorphism. -/
def chapter05ResiduallyInvisible
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) (σ : chapter05DecompositionGroup F A) : Prop :=
  σ ∈ chapter05InertiaGroup F A

/-- The warning in the totally ramified case is a strict distinction of predicates. -/
theorem integral_fixing_implies_residue_invisibility
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) (σ : chapter05DecompositionGroup F A)
    (hσ : chapter05IntegralActionFixed A σ) :
    chapter05ResiduallyInvisible A σ := by
  change σ ∈ chapter05InertiaGroup F A
  apply (inertia_mem_iff_residue_fixed A σ).mpr
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  rw [← residue_action_commutes_with_reduction A σ x, hσ x]

/-- A mixed pattern records nontrivial ramification and residue factors. -/
def chapter05MixedGaloisPattern
    {G Q : Type*} [Group G] [Group Q]
    (ρ : G →* Q) (e f : ℕ) : Prop :=
  Function.Surjective ρ ∧
    Nat.card (MonoidHom.ker ρ) = e ∧
    Nat.card Q = f ∧ 1 < e ∧ 1 < f

/-- Additive sections are used for a concrete finite non-split extension example. -/
def chapter05AdditiveExtensionSplits
    {G Q : Type*} [AddGroup G] [AddGroup Q] (ρ : G →+ Q) : Prop :=
  ∃ s : Q →+ G, ρ.comp s = AddMonoidHom.id Q

/-- The reduction of the cyclic group of order four onto the cyclic group of order two. -/
def chapter05ZModFourToTwo : ZMod 4 →+ ZMod 2 :=
  (ZMod.castHom (show 2 ∣ 4 by decide) (ZMod 2)).toAddMonoidHom

/-- The concrete quotient map is surjective. -/
theorem chapter05ZModFourToTwo_surjective :
    Function.Surjective chapter05ZModFourToTwo := by
  exact ZMod.castHom_surjective (show 2 ∣ 4 by decide)

/-- This exact finite-group quotient has no additive section. -/
theorem chapter05ZModFourToTwo_does_not_split :
    ¬chapter05AdditiveExtensionSplits chapter05ZModFourToTwo := by
  rintro ⟨s, hs⟩
  have htwo : s (1 : ZMod 2) + s (1 : ZMod 2) = 0 := by
    calc
      s (1 : ZMod 2) + s (1 : ZMod 2) = s ((1 : ZMod 2) + 1) :=
        (map_add s (1 : ZMod 2) 1).symm
      _ = s 0 := by
        rw [show (1 : ZMod 2) + 1 = 0 by decide]
      _ = 0 := map_zero s
  have hres : chapter05ZModFourToTwo (s (1 : ZMod 2)) = 1 := by
    have h := congrArg (fun f : ZMod 2 →+ ZMod 2 => f 1) hs
    simpa using h
  let z : ZMod 4 := s (1 : ZMod 2)
  change z + z = 0 at htwo
  change chapter05ZModFourToTwo z = 1 at hres
  have hz : z = (z.val : ZMod 4) := (ZMod.natCast_zmod_val z).symm
  rw [hz] at htwo hres
  have hzlt : z.val < 4 := ZMod.val_lt z
  have hzcases : z.val = 0 ∨ z.val = 1 ∨ z.val = 2 ∨ z.val = 3 := by
    omega
  rcases hzcases with h | h | h | h
  · rw [h] at hres
    exact (show chapter05ZModFourToTwo (0 : ZMod 4) ≠ 1 by decide) hres
  · rw [h] at htwo
    exact (show (1 : ZMod 4) + 1 ≠ 0 by decide) htwo
  · rw [h] at hres
    exact (show chapter05ZModFourToTwo (2 : ZMod 4) ≠ 1 by decide) hres
  · rw [h] at htwo
    exact (show (3 : ZMod 4) + 3 ≠ 0 by decide) htwo

/-- The normal closure of an intermediate field in a chosen ambient field. -/
abbrev chapter05NormalClosure
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (S : IntermediateField K Ω) : IntermediateField K Ω :=
  IntermediateField.normalClosure K S Ω

/-- The subgroup fixing the original field inside its normal closure. -/
abbrev chapter05NormalClosureStabilizer
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (S : IntermediateField K Ω) : Subgroup (Gal(Ω / K)) :=
  IntermediateField.fixingSubgroup S

/-- A finite separable intermediate extension has a Galois normal closure. -/
theorem normal_closure_of_galois_ambient_is_galois
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (S : IntermediateField K Ω) [FiniteDimensional K S] [IsGalois K Ω] :
    IsGalois K (chapter05NormalClosure S) := by
  change IsGalois K (IntermediateField.normalClosure K S Ω)
  infer_instance

/-- The fixing subgroup in the ambient Galois group recovers the original field. -/
theorem normal_closure_stabilizer_fixed_field_recovers_original
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    [FiniteDimensional K Ω] [IsGalois K Ω]
    (S : IntermediateField K Ω) :
    chapter05FixedField (chapter05NormalClosureStabilizer S) = S := by
  exact IsGalois.fixedField_fixingSubgroup S

/-- Ramification and residue degrees multiply through the normal-closure tower. -/
theorem normal_closure_tower_ramification_and_residue_multiplicativity
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (p : Ideal R) (q : Ideal S) (r : Ideal T)
    [p.IsPrime] [q.IsPrime] [r.IsPrime]
    [q.LiesOver p] [r.LiesOver q] [Module.Flat S T] :
    r.ramificationIdx R = q.ramificationIdx R * r.ramificationIdx S ∧
      r.inertiaDeg R = q.inertiaDeg R * r.inertiaDeg S := by
  exact ⟨Ideal.ramificationIdx_tower q r, Ideal.inertiaDeg_tower q r⟩

/-- The valuation on an algebraic normal closure is unique up to equivalence. -/
-- SOURCE_ISSUE: The source's phrase "unique valuation" is interpreted up to
-- Mathlib's valuation equivalence.  Henselianity gives uniqueness of the
-- branch, but literal equality in a fixed value group additionally needs a
-- normalization hypothesis, so the exact normalized predicate is not claimed
-- here.
theorem normal_closure_valuation_extension_is_unique_under_local_hypothesis
    {K Ω Γ : Type u} [Field K] [Field Ω] [Algebra K Ω]
    [LinearOrderedCommGroupWithZero Γ]
    (S : IntermediateField K Ω)
    (v : Valuation K Γ)
    (w : Valuation (chapter05NormalClosure S) Γ)
    (hwe : v.IsEquiv (w.comap
      (algebraMap K (chapter05NormalClosure S))))
    (hH :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10IsHenselianValuedField v)
    [Valuation.IsRankOneDiscrete v]
    [Algebra.IsAlgebraic K (chapter05NormalClosure S)] :
    chapter05UniqueValuationExtension v w := by
  constructor
  · exact hwe
  · intro w' hwe'
    exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_henselian_valuation_has_unique_branch
      v hH w' w hwe' hwe

/-- A finite separable but non-normal extension is not Galois in its own right. -/
theorem finite_separable_nonnormal_extension_is_not_galois
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hnormal : ¬Normal K L) :
    ¬IsGalois K L := by
  intro hG
  exact hnormal hG.to_normal

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05
