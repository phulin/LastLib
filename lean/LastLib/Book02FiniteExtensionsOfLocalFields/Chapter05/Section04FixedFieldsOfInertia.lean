import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Section07UnramifiedAndTotallyRamifiedEndpoints
import Mathlib.NumberTheory.RamificationInertia.HilbertTheory
import Mathlib.Algebra.Ring.Action.Subobjects

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05

noncomputable section

open scoped BigOperators Pointwise

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

/-- The unramified predicate specialized to the chosen branch ideal. -/
def chapter05Unramified
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (P : Ideal B) [P.IsPrime] [P.IsMaximal]
    [Algebra (P.under A).ResidueField P.ResidueField] : Prop :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.foundationalUnramified
    (P.ramificationIdx A)
    (Algebra.IsSeparable (P.under A).ResidueField P.ResidueField)

/-- The totally ramified predicate specialized to the chosen branch ideal. -/
def chapter05TotallyRamified
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (P : Ideal B) [P.IsPrime] [P.IsMaximal] : Prop :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.foundationalTotallyRamified
    (P.inertiaDeg A)

/-- The kernel of a residue action is a normal subgroup. -/
theorem inertia_kernel_is_normal
    {D Q : Type*} [Group D] [Group Q] (ρ : D →* Q) :
    (MonoidHom.ker ρ).Normal := by
  infer_instance

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
  have hidx : (MonoidHom.ker ρ).index = Nat.card Q := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hρ]
    simp
  have hbase : Module.finrank K (chapter05FixedField (MonoidHom.ker ρ)) =
      (MonoidHom.ker ρ).index := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index,
      IntermediateField.fixingSubgroup_fixedField]
  constructor
  · calc
      Module.finrank K (chapter05FixedField (MonoidHom.ker ρ)) =
          (MonoidHom.ker ρ).index := hbase
      _ = Nat.card Q := hidx
      _ = f := hf
  · rw [IntermediateField.finrank_fixedField_eq_card, he]

/-- The quotient of the Galois group by inertia is the Galois group of the fixed field. -/
theorem residue_quotient_is_fixed_field_galois_group
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (I : Subgroup Gal(L / K)) [I.Normal] :
    Nonempty
      ((Gal(L / K) ⧸ I) ≃* Gal(chapter05FixedField I / K)) := by
  exact ⟨IsGalois.normalAutEquivQuotient I⟩

/-- Inertia is the Galois group of the totally ramified fixed-field layer. -/
theorem inertia_is_fixed_field_layer_galois_group
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (I : Subgroup Gal(L / K)) :
    Nonempty
      (I ≃* Gal(L / chapter05FixedField I)) := by
  exact ⟨
    (MulEquiv.subgroupCongr (IntermediateField.fixingSubgroup_fixedField I).symm).trans
      (IntermediateField.fixingSubgroupEquiv (chapter05FixedField I))⟩

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
  exact fixed_field_of_residue_kernel_has_two_degrees ρ hρ e f he hf

/-- An abstract inertia field is algebra-equivalent over the base to its fixed field.

Mathlib's intrinsic `IsInertiaField` interface supplies a ring equivalence; the
chapter records the stronger over-`K` field identification needed for the
displayed field tower. -/
theorem inertia_field_is_algebra_equivalent_to_fixed_field
    {B K E L : Type*} [CommRing B] (P : Ideal B)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L]
    [MulSemiringAction (Gal(L / K)) B]
    [FiniteDimensional K L] [IsGalois K L]
    [IsInertiaField K L P E] :
    Nonempty (E ≃ₐ[K] chapter05FixedField (Ideal.inertia (Gal(L / K)) P)) := by
  have hfixed : IsInertiaField K L P
      (chapter05FixedField (Ideal.inertia (Gal(L / K)) P)) := by
    exact {
      toIsGaloisGroup :=
        IsGaloisGroup.subgroup (Gal(L / K)) K L
          (Ideal.inertia (Gal(L / K)) P) }
  let e := @IsInertiaField.ringEquiv K L B _ _ _ _ P E _ _ _
    (chapter05FixedField (Ideal.inertia (Gal(L / K)) P)) _ _ _ hfixed
  refine ⟨AlgEquiv.ofRingEquiv (f := e) ?_⟩
  intro x
  apply FaithfulSMul.algebraMap_injective
    (chapter05FixedField (Ideal.inertia (Gal(L / K)) P)) L
  rw [@IsInertiaField.algebraMap_ringEquiv_apply K L B _ _ _ _ P E _ _ _
    (chapter05FixedField (Ideal.inertia (Gal(L / K)) P)) _ _ _ hfixed]
  rw [← IsScalarTower.algebraMap_apply K E L,
    ← IsScalarTower.algebraMap_apply K
      (chapter05FixedField (Ideal.inertia (Gal(L / K)) P)) L]

/--
The inertia fixed field has the unramified and totally ramified local layers.

The ring data make the two assertions refer to the actual branch ideals: `pE`
is the branch in the fixed field and `P` is the branch upstairs.  The
`IsInertiaField` and fraction-ring hypotheses identify these rings with the
field tower, rather than merely recording four unrelated natural numbers.  The
single-branch hypothesis is the local condition needed to identify the
inertia-field degree with the residue degree `f`.
-/
/- The branch and fraction-ring hypotheses below connect the intrinsic ideal
   invariants to the displayed field tower.  The one-branch condition is
   retained because the inertia-field degree is a selected local factor, not
   the degree of the whole global extension. -/
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
    (hp : p ≠ ⊥)
    (hbranches : (p.primesOver B).ncard = 1)
    (e f : ℕ)
    (he : p.ramificationIdxIn B = e)
    (hf : p.inertiaDegIn B = f)
    (hresidueSeparable :
      Algebra.IsSeparable (pE.under A).ResidueField pE.ResidueField) :
      Nonempty (E ≃ₐ[K] chapter05FixedField (Ideal.inertia (Gal(L / K)) P)) ∧
      Module.finrank K E = f ∧
      Module.finrank E L = e ∧
      chapter05Unramified A C pE ∧
      chapter05TotallyRamified C B P := by
  have hE : Nonempty
      (E ≃ₐ[K] chapter05FixedField (Ideal.inertia (Gal(L / K)) P)) :=
    inertia_field_is_algebra_equivalent_to_fixed_field (B := B) P
  have hKE : Module.finrank K E = f := by
    calc
      Module.finrank K E = (p.primesOver B).ncard * p.inertiaDegIn B :=
        IsInertiaField.rank_right A K L P E hp
      _ = 1 * f := by rw [hbranches, hf]
      _ = f := Nat.one_mul f
  have hEL : Module.finrank E L = e := by
    calc
      Module.finrank E L = p.ramificationIdxIn B :=
        IsInertiaField.rank_left A K L P E hp
      _ = e := he
  have hinertia :
      Ideal.inertia (Ideal.inertia (Gal(L / K)) P) P = ⊤ := by
    apply le_antisymm le_top
    intro σ _
    change ∀ x : B, (σ : Gal(L / K)) • x - x ∈ P
    exact σ.property
  have hunder : pE.under A = p := (pE.over_def p).symm
  let _ : Algebra.IsSeparable (pE.under A).ResidueField pE.ResidueField :=
    hresidueSeparable
  let _ : Finite (A ⧸ pE.under A) := by
    simpa [hunder] using (Ring.HasFiniteQuotients.finiteQuotient hp)
  let _ : PerfectField (pE.under A).ResidueField := inferInstance
  let _ : PerfectField pE.ResidueField :=
    Algebra.IsAlgebraic.perfectField (pE.under A).ResidueField
  let _ : Finite (Ideal.inertia (Gal(L / K)) P) := by infer_instance
  let _ : Nonempty (Ideal.inertia (Gal(L / K)) P) :=
    ⟨⟨1, by simp⟩⟩
  have hramC : P.ramificationIdx C = e := by
    calc
      P.ramificationIdx C = pE.ramificationIdxIn B :=
        (Ideal.ramificationIdxIn_eq_ramificationIdx pE P
          (Ideal.inertia (Gal(L / K)) P)).symm
      _ = Nat.card (Ideal.inertia (Ideal.inertia (Gal(L / K)) P) P) := by
        exact (Ideal.card_inertia_eq_ramificationIdxIn
          (G := Ideal.inertia (Gal(L / K)) P) pE P).symm
      _ = Nat.card (Ideal.inertia (Gal(L / K)) P) := by
        rw [hinertia]
        simp
      _ = Module.finrank E L :=
        IsGaloisGroup.card_eq_finrank (Ideal.inertia (Gal(L / K)) P) E L
      _ = e := hEL
  have hramA : P.ramificationIdx A = e := by
    calc
      P.ramificationIdx A = p.ramificationIdxIn B :=
        (Ideal.ramificationIdxIn_eq_ramificationIdx p P (Gal(L / K))).symm
      _ = e := he
  have htower : P.ramificationIdx A =
      pE.ramificationIdx A * P.ramificationIdx C :=
    Ideal.ramificationIdx_tower (R := A) pE P
  have hepos : 0 < e := by
    rw [← hramC]
    exact P.ramificationIdx_pos C
  have hpEram : pE.ramificationIdx A = 1 := by
    apply Nat.mul_right_cancel hepos
    calc
      pE.ramificationIdx A * e = P.ramificationIdx A := by
        rw [hramC] at htower
        exact htower.symm
      _ = e := hramA
      _ = 1 * e := (Nat.one_mul e).symm
  refine ⟨hE, hKE, hEL, ?_, ?_⟩
  · change pE.ramificationIdx A = 1 ∧
      Algebra.IsSeparable (pE.under A).ResidueField pE.ResidueField
    exact ⟨hpEram, hresidueSeparable⟩
  · change P.inertiaDeg C = 1
    have hcard := Ideal.card_stabilizer_eq_card_inertia_mul_finrank
      (G := Ideal.inertia (Gal(L / K)) P) pE P
    have hstab : MulAction.stabilizer (Ideal.inertia (Gal(L / K)) P) P = ⊤ := by
      apply le_antisymm le_top
      intro σ hσ
      change (σ : Gal(L / K)) • P = P
      exact (Ideal.inertia_le_stabilizer (M := Gal(L / K)) P) σ.property
    have hstabcard :
        Nat.card (MulAction.stabilizer (Ideal.inertia (Gal(L / K)) P) P) =
          Nat.card (Ideal.inertia (Gal(L / K)) P) := by
      calc
        Nat.card (MulAction.stabilizer (Ideal.inertia (Gal(L / K)) P) P) =
            Nat.card (⊤ : Subgroup (Ideal.inertia (Gal(L / K)) P)) :=
          by rw [hstab]
        _ = Nat.card (Ideal.inertia (Gal(L / K)) P) := by simp
    have hintercard :
        Nat.card (Ideal.inertia (Ideal.inertia (Gal(L / K)) P) P) =
          Nat.card (Ideal.inertia (Gal(L / K)) P) := by
      rw [hinertia]
      simp
    have hcard' :
        Nat.card (Ideal.inertia (Gal(L / K)) P) =
          Nat.card (Ideal.inertia (Gal(L / K)) P) * P.inertiaDeg C := by
      calc
        Nat.card (Ideal.inertia (Gal(L / K)) P) =
            Nat.card (MulAction.stabilizer (Ideal.inertia (Gal(L / K)) P) P) :=
          hstabcard.symm
        _ = Nat.card (Ideal.inertia (Ideal.inertia (Gal(L / K)) P) P) *
            P.inertiaDeg C := hcard
        _ = Nat.card (Ideal.inertia (Gal(L / K)) P) * P.inertiaDeg C := by
          rw [hintercard]
    have hIpos : 0 < Nat.card (Ideal.inertia (Gal(L / K)) P) := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_left hIpos
    calc
      Nat.card (Ideal.inertia (Gal(L / K)) P) * P.inertiaDeg C =
          Nat.card (Ideal.inertia (Gal(L / K)) P) := hcard'.symm
      _ = Nat.card (Ideal.inertia (Gal(L / K)) P) * 1 :=
        (Nat.mul_one _).symm

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05
