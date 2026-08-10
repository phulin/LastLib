import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.Section01TheStructuralQuestion

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09

open scoped BigOperators Polynomial
open Ideal IsLocalRing Polynomial

noncomputable section

/-! ## The intermediate field interface used by Theorem 9.1 -/

/-- A local presentation of an intermediate field with a specified residue
field.  The ring field is deliberately an explicit subalgebra: later proof
passes can identify it with the integral closure of `A` in `K₀`. -/
structure Chapter09UnramifiedIntermediateData
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
    [Chapter09FiniteLocalExtension A B K L]
    (K₀ : IntermediateField K L)
    (s : IntermediateField (chapter09BaseResidueField A)
      (chapter09ExtensionResidueField B)) where
  ring : Subalgebra A K₀
  local_ring : IsLocalRing ring
  local_hom : IsLocalHom (algebraMap A ring)
  dvr : IsDiscreteValuationRing ring
  complete : IsAdicComplete (IsLocalRing.maximalIdeal ring) ring
  finite : Module.Finite A ring
  torsion_free : Module.IsTorsionFree A ring
  fraction_field : IsFractionRing ring K₀
  integral_closure : IsIntegralClosure ring A K₀
  residue_separable : Algebra.IsSeparable (chapter09BaseResidueField A) s
  residue_identification :
    letI : IsLocalRing ring := local_ring
    letI : IsLocalHom (algebraMap A ring) := local_hom
    Nonempty
      (IsLocalRing.ResidueField ring ≃ₐ[chapter09BaseResidueField A]
        (s : Type _))
  residue_inclusion :
    letI : IsLocalRing ring := local_ring
    letI : IsLocalHom (algebraMap A ring) := local_hom
    ∃ ρ : IsLocalRing.ResidueField ring →ₐ[chapter09BaseResidueField A]
        chapter09ExtensionResidueField B,
      Function.Injective ρ ∧ Set.range ρ = (s : Set _)
  ramification_index_eq_one :
    letI : IsLocalRing ring := local_ring
    letI : IsDiscreteValuationRing ring := dvr
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex A ring
        (IsLocalRing.maximalIdeal ring) = 1

/-- The property “`K₀/K` is an unramified intermediate field”.  The residue
field is existential here because an arbitrary unramified intermediate field
need only have a separable residue subextension of `l/k`; the maximal field
will impose `s = l_s` separately. -/
def chapter09UnramifiedIntermediate
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
    [Chapter09FiniteLocalExtension A B K L]
    (K₀ : IntermediateField K L) : Prop :=
  ∃ s : IntermediateField (chapter09BaseResidueField A)
      (chapter09ExtensionResidueField B),
    Nonempty (Chapter09UnramifiedIntermediateData A B K L K₀ s)

/-- The maximal unramified subextension is characterized internally by
containment of every other unramified intermediate field. -/
def chapter09MaximalUnramifiedSubextension
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
    [Chapter09FiniteLocalExtension A B K L]
    (K₀ : IntermediateField K L) : Prop :=
  Nonempty (Chapter09UnramifiedIntermediateData A B K L K₀
    (chapter09MaximalSeparableResidueSubfield
      (chapter09BaseResidueField A) (chapter09ExtensionResidueField B))) ∧
    ∀ E : IntermediateField K L,
      chapter09UnramifiedIntermediate A B K L E → E ≤ K₀

/-! ## Theorem 9.1 and its residue-lifting construction -/

/- Theorem 9.1 (maximal unramified subextension). -/
theorem chapter09_maximal_unramified_subextension
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
    [Chapter09FiniteLocalExtension A B K L] :
    ∃! K₀ : IntermediateField K L,
      chapter09MaximalUnramifiedSubextension A B K L K₀ := by
  sorry

/-- Any two fields satisfying the maximal characterization are equal; this is
the internal canonicity assertion in the source text. -/
theorem chapter09_maximal_unramified_is_canonical
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
    [Chapter09FiniteLocalExtension A B K L]
    (K₀ K₁ : IntermediateField K L)
    (h₀ : chapter09MaximalUnramifiedSubextension A B K L K₀)
    (h₁ : chapter09MaximalUnramifiedSubextension A B K L K₁) :
    K₀ = K₁ := by
  apply le_antisymm
  · exact h₁.2 K₀ ⟨_, h₀.1⟩
  · exact h₀.2 K₁ ⟨_, h₁.1⟩

/-- The field generated by a lifted residue generator. -/
def chapter09LiftedIntermediateField
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] (θ : B) : IntermediateField K L :=
  IntermediateField.adjoin K ({algebraMap B L θ} : Set L)

/- Hensel lifting of a primitive separable residue generator. -/
theorem chapter09_hensel_lifts_separable_residue_generator
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
    [Chapter09FiniteLocalExtension A B K L] [HenselianLocalRing B]
    (θbar : chapter09MaximalSeparableResidueSubfield
      (chapter09BaseResidueField A) (chapter09ExtensionResidueField B))
    (gbar : (chapter09BaseResidueField A)[X]) (g : A[X])
    (hprimitive : Algebra.adjoin (chapter09BaseResidueField A)
      ({θbar} : Set (chapter09MaximalSeparableResidueSubfield
        (chapter09BaseResidueField A) (chapter09ExtensionResidueField B))) = ⊤)
    (hmonic : gbar.Monic ∧ g.Monic) (hirreducible : Irreducible gbar)
    (hseparable : gbar.Separable)
    (hminimal : gbar = minpoly (chapter09BaseResidueField A) (θbar :
      chapter09ExtensionResidueField B))
    (hlift : g.map (algebraMap A (chapter09BaseResidueField A)) = gbar) :
    ∃ θ : B,
      aeval θ (g.map (algebraMap A B)) = 0 ∧
        IsLocalRing.residue B θ = (θbar : chapter09ExtensionResidueField B) := by
  have hres :
      (algebraMap (chapter09BaseResidueField A)
          (chapter09ExtensionResidueField B)).comp
          (algebraMap A (chapter09BaseResidueField A)) =
        (IsLocalRing.residue B).comp (algebraMap A B) := by
    simpa only [IsLocalRing.ResidueField.algebraMap_eq] using
      (show
          (algebraMap (chapter09BaseResidueField A)
              (chapter09ExtensionResidueField B)).comp
              (IsLocalRing.residue A) =
            (IsLocalRing.residue B).comp (algebraMap A B) by
        ext a
        exact IsLocalRing.ResidueField.algebraMap_residue (R := A) (S := B) a)
  have hrootbar :
      gbar.eval₂ (algebraMap (chapter09BaseResidueField A)
        (chapter09ExtensionResidueField B)) (θbar : chapter09ExtensionResidueField B) = 0 := by
    have hrootbar' :
        aeval (θbar : chapter09ExtensionResidueField B) gbar = 0 := by
      rw [hminimal]
      exact minpoly.aeval _ _
    simpa [Polynomial.aeval_def] using hrootbar'
  have hroot :
      (g.map (algebraMap A B)).eval₂ (IsLocalRing.residue B)
          (θbar : chapter09ExtensionResidueField B) = 0 := by
    rw [Polynomial.eval₂_map, ← hres, ← Polynomial.eval₂_map, hlift]
    exact hrootbar
  have hderivbar :
      gbar.derivative.eval₂ (algebraMap (chapter09BaseResidueField A)
        (chapter09ExtensionResidueField B)) (θbar : chapter09ExtensionResidueField B) ≠ 0 :=
    hseparable.eval₂_derivative_ne_zero
      (algebraMap (chapter09BaseResidueField A)
        (chapter09ExtensionResidueField B)) hrootbar
  have hderiv_map :
      g.derivative.map (algebraMap A (chapter09BaseResidueField A)) = gbar.derivative := by
    rw [← Polynomial.derivative_map, hlift]
  have hderiv :
      (g.map (algebraMap A B)).derivative.eval₂ (IsLocalRing.residue B)
          (θbar : chapter09ExtensionResidueField B) ≠ 0 := by
    rw [Polynomial.derivative_map, Polynomial.eval₂_map, ← hres,
      ← Polynomial.eval₂_map, hderiv_map]
    exact hderivbar
  have hhensel :
      ∀ f : B[X], f.Monic → ∀ a₀ : chapter09ExtensionResidueField B,
        aeval a₀ f = 0 → aeval a₀ f.derivative ≠ 0 →
          ∃ a : B, f.IsRoot a ∧ IsLocalRing.residue B a = a₀ :=
    ((HenselianLocalRing.TFAE B).out 0 1).mp
      (inferInstance : HenselianLocalRing B)
  obtain ⟨θ, hθroot, hθresidue⟩ :=
    hhensel
      (g.map (algebraMap A B)) (hmonic.2.map (algebraMap A B))
      (θbar : chapter09ExtensionResidueField B) hroot hderiv
  exact ⟨θ, by simpa [Polynomial.aeval_def] using hθroot, hθresidue⟩

/- The residue-lifting construction produces the canonical intermediate field. -/
theorem chapter09_lifted_generator_constructs_maximal_unramified_subextension
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
    [Chapter09FiniteLocalExtension A B K L]
    (θbar : chapter09MaximalSeparableResidueSubfield
      (chapter09BaseResidueField A) (chapter09ExtensionResidueField B))
    (gbar : (chapter09BaseResidueField A)[X]) (g : A[X]) (θ : B)
    (hprimitive : Algebra.adjoin (chapter09BaseResidueField A)
      ({θbar} : Set (chapter09MaximalSeparableResidueSubfield
        (chapter09BaseResidueField A) (chapter09ExtensionResidueField B))) = ⊤)
    (hmonic : gbar.Monic ∧ g.Monic) (hirreducible : Irreducible gbar)
    (hseparable : gbar.Separable)
    (hminimal : gbar = minpoly (chapter09BaseResidueField A) (θbar :
      chapter09ExtensionResidueField B))
    (hlift : g.map (algebraMap A (chapter09BaseResidueField A)) = gbar)
    (hroot : aeval θ (g.map (algebraMap A B)) = 0)
    (hresidue : IsLocalRing.residue B θ =
      (θbar : chapter09ExtensionResidueField B)) :
    chapter09MaximalUnramifiedSubextension A B K L
      (chapter09LiftedIntermediateField A B K L θ) := by
  sorry

/-! ## Invariants of the remainder -/

/-- The numerical remainder data records the source identities for `L/K₀`.
Its residue field is the purely inseparable extension `l/l_s`. -/
structure Chapter09RemainderInvariantData
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
    [Chapter09FiniteLocalExtension A B K L]
    (K₀ : IntermediateField K L) where
  ramification_index : ℕ
  residue_degree : ℕ
  ramification_index_eq : ramification_index =
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex A B
      (IsLocalRing.maximalIdeal B)
  residue_degree_eq : residue_degree =
    Module.finrank
      (chapter09MaximalSeparableResidueSubfield
        (chapter09BaseResidueField A) (chapter09ExtensionResidueField B))
      (chapter09ExtensionResidueField B)
  residue_extension_purely_inseparable :
    IsPurelyInseparable
      (chapter09MaximalSeparableResidueSubfield
        (chapter09BaseResidueField A) (chapter09ExtensionResidueField B))
      (chapter09ExtensionResidueField B)

/- The remaining extension has unchanged `e` and purely inseparable residue part. -/
theorem chapter09_remainder_invariants
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
    [Chapter09FiniteLocalExtension A B K L]
    (K₀ : IntermediateField K L)
    (hK₀ : chapter09MaximalUnramifiedSubextension A B K L K₀) :
    Nonempty (Chapter09RemainderInvariantData A B K L K₀) := by
  refine ⟨{
    ramification_index :=
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex A B
        (IsLocalRing.maximalIdeal B),
    residue_degree :=
      Module.finrank
        (chapter09MaximalSeparableResidueSubfield
          (chapter09BaseResidueField A) (chapter09ExtensionResidueField B))
        (chapter09ExtensionResidueField B),
    ramification_index_eq := rfl,
    residue_degree_eq := rfl,
    residue_extension_purely_inseparable := ?_ }⟩
  change IsPurelyInseparable
    (separableClosure (chapter09BaseResidueField A)
      (chapter09ExtensionResidueField B))
    (chapter09ExtensionResidueField B)
  exact separableClosure.isPurelyInseparable
    (chapter09BaseResidueField A) (chapter09ExtensionResidueField B)

/-- The remainder is totally ramified precisely when the original residue
extension is separable. -/
theorem chapter09_remainder_totally_ramified_iff_residue_separable
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
    [Chapter09FiniteLocalExtension A B K L]
    (K₀ : IntermediateField K L)
    (hK₀ : chapter09MaximalUnramifiedSubextension A B K L K₀) :
    (∃ r : Chapter09RemainderInvariantData A B K L K₀,
      r.residue_degree = 1) ↔
      Algebra.IsSeparable (chapter09BaseResidueField A)
        (chapter09ExtensionResidueField B) := by
  constructor
  · rintro ⟨r, hr⟩
    have hfin : Module.finrank
        (chapter09MaximalSeparableResidueSubfield
          (chapter09BaseResidueField A) (chapter09ExtensionResidueField B))
        (chapter09ExtensionResidueField B) = 1 := by
      calc
        Module.finrank
            (chapter09MaximalSeparableResidueSubfield
              (chapter09BaseResidueField A) (chapter09ExtensionResidueField B))
            (chapter09ExtensionResidueField B) = r.residue_degree :=
          r.residue_degree_eq.symm
        _ = 1 := hr
    exact (chapter09_separable_residue_part_eq_top_iff
      (chapter09BaseResidueField A) (chapter09ExtensionResidueField B)).mp
      (IntermediateField.finrank_eq_one_iff_eq_top.mp hfin)
  · intro hseparable
    obtain ⟨r⟩ := chapter09_remainder_invariants A B K L K₀ hK₀
    refine ⟨r, ?_⟩
    rw [r.residue_degree_eq]
    rw [((chapter09_separable_residue_part_eq_top_iff
      (chapter09BaseResidueField A) (chapter09ExtensionResidueField B)).mpr
      hseparable)]
    exact IntermediateField.finrank_top

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09
