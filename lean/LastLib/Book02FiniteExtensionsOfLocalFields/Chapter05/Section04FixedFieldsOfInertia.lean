import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.Section03ResidueActionAndInertia
import Mathlib.NumberTheory.RamificationInertia.HilbertTheory

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05

noncomputable section

open scoped BigOperators

/-! ## 5.4. Fixed fields of inertia -/

/-- The fixed field of a subgroup of a finite Galois group. -/
abbrev chapter05FixedField
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (H : Subgroup Gal(L / K)) : IntermediateField K L :=
  IntermediateField.fixedField H

/-- A branch invariant profile using Mathlib's intrinsic ideal invariants. -/
structure Chapter05LocalEFProfile
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (P : Ideal B) [P.IsPrime] [P.IsMaximal] where
  e : ℕ
  f : ℕ
  e_eq : e = P.ramificationIdx A
  f_eq : f = P.inertiaDeg A

/-- The foundational unramified predicate used for an `e = 1` layer. -/
def chapter05Unramified
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (P : Ideal B) [P.IsPrime] [P.IsMaximal]
    [Algebra (P.under A).ResidueField P.ResidueField] : Prop :=
  P.ramificationIdx A = 1 ∧
    Algebra.IsSeparable (P.under A).ResidueField P.ResidueField

/-- Total ramification is the actual residue-degree-one condition. -/
def chapter05TotallyRamified
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (P : Ideal B) [P.IsPrime] [P.IsMaximal] : Prop :=
  P.inertiaDeg A = 1

/-- The kernel of a residue action is a normal subgroup. -/
theorem inertia_kernel_is_normal
    {D Q : Type*} [Group D] [Group Q] (ρ : D →* Q) :
    (MonoidHom.ker ρ).Normal := by
  sorry

/-- The fixed field of the inertia kernel has the quotient and kernel degrees. -/
theorem fixed_field_of_residue_kernel_has_two_degrees
    {K L Q : Type*} [Field K] [Field L] [Algebra K L] [Group Q]
    [FiniteDimensional K L] [IsGalois K L] [Finite Q]
    (ρ : Gal(L / K) →* Q) (hρ : Function.Surjective ρ)
    (e f : ℕ)
    (he : Nat.card (MonoidHom.ker ρ) = e)
    (hf : Nat.card Q = f) :
    Module.finrank K (chapter05FixedField (MonoidHom.ker ρ)) = f ∧
      Module.finrank (chapter05FixedField (MonoidHom.ker ρ)) L = e := by
  sorry

/-- The quotient of the Galois group by inertia is the Galois group of the fixed field. -/
theorem residue_quotient_is_fixed_field_galois_group
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (I : Subgroup Gal(L / K)) [I.Normal] :
    Nonempty
      ((Gal(L / K) ⧸ I) ≃* Gal(chapter05FixedField I / K)) := by
  sorry

/-- Inertia is the Galois group of the totally ramified fixed-field layer. -/
theorem inertia_is_fixed_field_layer_galois_group
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (I : Subgroup Gal(L / K)) :
    Nonempty
      (I ≃* Gal(L / chapter05FixedField I)) := by
  sorry

/-- The degree allocation forced by the inertia fixed field. -/
theorem fixed_field_inertia_degree_allocation
    {K L Q : Type*} [Field K] [Field L] [Algebra K L] [Group Q]
    [FiniteDimensional K L] [IsGalois K L] [Finite Q]
    (ρ : Gal(L / K) →* Q) (hρ : Function.Surjective ρ)
    (e f : ℕ)
    (he : Nat.card (MonoidHom.ker ρ) = e)
    (hf : Nat.card Q = f) :
    Module.finrank K (chapter05FixedField (MonoidHom.ker ρ)) = f ∧
      Module.finrank (chapter05FixedField (MonoidHom.ker ρ)) L = e := by
  sorry

/--
The inertia fixed field has the unramified and totally ramified local layers.

The ring data make the two assertions refer to the actual branch ideals: `pE`
is the branch in the fixed field and `P` is the branch upstairs.  The
`IsInertiaField` and fraction-ring hypotheses identify these rings with the
field tower, rather than merely recording four unrelated natural numbers.  The
single-branch hypothesis is the local condition needed to identify the
inertia-field degree with the residue degree `f`.
-/
-- SOURCE_ISSUE: The source asserts the `e`/`f` allocation from completeness
-- and discreteness alone.  Over an imperfect residue field finite defect
-- extensions can violate the fundamental equality, and without one branch
-- the inertia-field degree also contains the branch-count factor.  The
-- corrected local interface below assumes perfect residue fields, the
-- canonical ring-level Galois actions, and explicitly records one branch.
theorem fixed_field_inertia_has_unramified_and_totally_ramified_layers
    {A C B K E L : Type*}
    [CommRing A] [CommRing C] [CommRing B]
    [IsDomain C]
    (p : Ideal A) (pE : Ideal C) (P : Ideal B)
    [Field K] [Field E] [Field L]
    [Algebra A K] [Algebra A E] [Algebra A L]
    [Algebra A C] [Algebra C B] [Algebra A B]
    [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower A C B] [IsScalarTower K E L]
    [Algebra B L] [Algebra C E] [Algebra C L]
    [IsScalarTower A C E] [IsScalarTower A B L] [IsScalarTower C B L]
    [IsScalarTower A K L]
    [IsGalois K L] [FiniteDimensional K L]
    [MulSemiringAction (Gal(L / K)) B]
    [IsGaloisGroup (Gal(L / K)) A B]
    [IsGaloisGroup (Ideal.inertia (Gal(L / K)) P) C B]
    [IsDedekindDomain A] [IsDedekindDomain B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Module.Finite C B] [Module.Flat C B]
    [Ring.HasFiniteQuotients A] [IsFractionRing A K]
    [IsFractionRing B L] [IsFractionRing C E]
    [p.IsPrime] [p.IsMaximal] [pE.IsPrime] [pE.IsMaximal]
    [P.IsPrime] [P.IsMaximal] [pE.LiesOver p] [P.LiesOver p]
    [P.LiesOver pE]
    [Algebra (pE.under A).ResidueField pE.ResidueField]
    [IsInertiaField K L P E]
    [PerfectField p.ResidueField] [PerfectField pE.ResidueField]
    (hE : Nonempty
      (E ≃ₐ[K] chapter05FixedField (Ideal.inertia (Gal(L / K)) P)))
    (hp : p ≠ ⊥)
    (hbranches : (p.primesOver B).ncard = 1)
    (hinertia :
      Ideal.inertia (Ideal.inertia (Gal(L / K)) P) P = ⊤)
    (e f : ℕ)
    (he : p.ramificationIdxIn B = e)
    (hf : p.inertiaDegIn B = f)
    (hresidueSeparable :
      Algebra.IsSeparable (pE.under A).ResidueField pE.ResidueField) :
      Module.finrank K E = f ∧
      Module.finrank E L = e ∧
      chapter05Unramified A C pE ∧
      chapter05TotallyRamified C B P := by
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05
