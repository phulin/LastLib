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
    [IsDomain A] [IsDomain B]
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
  /-- The chosen integral model is the subring of `B` induced by the
  inclusion `K₀ ⊆ L`.  This compatibility is needed before a residue-field
  inclusion can be interpreted as the one inside `l`. -/
  ring_to_extension : ring →ₐ[A] B
  ring_to_extension_local : IsLocalHom ring_to_extension.toRingHom
  ring_to_extension_compatible : ∀ x : ring,
    algebraMap B L (ring_to_extension x) = algebraMap K₀ L (x : K₀)
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
      Function.Injective ρ ∧ Set.range ρ = (s : Set _) ∧
        ∀ x : ring,
          ρ (IsLocalRing.residue ring x) =
            IsLocalRing.residue B (ring_to_extension x)
  ramification_index_eq_one :
    letI : IsLocalRing ring := local_ring
    letI : IsDiscreteValuationRing ring := dvr
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex A ring
        (IsLocalRing.maximalIdeal ring) = 1
  /-- The unramified stage has field degree equal to the degree of its
  identified residue field. -/
  field_degree_eq_residue_degree :
    Module.finrank K K₀ = Module.finrank (chapter09BaseResidueField A) s
  /-- Removing the unramified stage does not change the ramification index. -/
  remainder_ramification_index_eq :
    letI : Algebra ring B := ring_to_extension.toRingHom.toAlgebra
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
        ring B (IsLocalRing.maximalIdeal B) =
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
        A B (IsLocalRing.maximalIdeal B)
  /-- The residue degree of the remainder is the degree over the selected
  separable residue subfield. -/
  remainder_residue_degree_eq :
    letI : Algebra ring B := ring_to_extension.toRingHom.toAlgebra
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree
        ring B (IsLocalRing.maximalIdeal B) =
      Module.finrank s (chapter09ExtensionResidueField B)
  /-- The field degree of the remainder is accounted for by its actual local
  invariants. -/
  remainder_degree_formula :
    letI : Algebra ring B := ring_to_extension.toRingHom.toAlgebra
    Module.finrank K₀ L =
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
          ring B (IsLocalRing.maximalIdeal B) *
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree
          ring B (IsLocalRing.maximalIdeal B)

/-- The property “`K₀/K` is an unramified intermediate field”.  The residue
field is existential here because an arbitrary unramified intermediate field
need only have a separable residue subextension of `l/k`; the maximal field
will impose `s = l_s` separately. -/
def chapter09UnramifiedIntermediate
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsDomain A] [IsDomain B]
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
    [IsDomain A] [IsDomain B]
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

/-- The maximality predicate packages that its distinguished field is itself
unramified. -/
theorem chapter09_maximal_unramified_is_unramified
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsLocalHom (algebraMap A B)] [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [Module.Finite A B] [Module.IsTorsionFree A B]
    [FaithfulSMul A B] [IsIntegralClosure B A L]
    [Module.Finite (chapter09BaseResidueField A)
      (chapter09ExtensionResidueField B)]
    [Chapter09FiniteLocalExtension A B K L]
    (K₀ : IntermediateField K L)
    (hK₀ : chapter09MaximalUnramifiedSubextension A B K L K₀) :
    chapter09UnramifiedIntermediate A B K L K₀ := by
  exact ⟨_, hK₀.1⟩

/-- Every unramified intermediate field is contained in the distinguished
maximal field. -/
theorem chapter09_unramified_intermediate_le_maximal
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsLocalHom (algebraMap A B)] [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [Module.Finite A B] [Module.IsTorsionFree A B]
    [FaithfulSMul A B] [IsIntegralClosure B A L]
    [Module.Finite (chapter09BaseResidueField A)
      (chapter09ExtensionResidueField B)]
    [Chapter09FiniteLocalExtension A B K L]
    (K₀ E : IntermediateField K L)
    (hK₀ : chapter09MaximalUnramifiedSubextension A B K L K₀)
    (hE : chapter09UnramifiedIntermediate A B K L E) : E ≤ K₀ := by
  exact hK₀.2 E hE

/-! ## Theorem 9.1 and its residue-lifting construction -/

/- Theorem 9.1 (maximal unramified subextension). -/
theorem chapter09_maximal_unramified_subextension
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsDomain A] [IsDomain B]
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
    [IsDomain A] [IsDomain B]
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
  have h₀' : chapter09UnramifiedIntermediate A B K L K₀ := ⟨_, h₀.1⟩
  have h₁' : chapter09UnramifiedIntermediate A B K L K₁ := ⟨_, h₁.1⟩
  exact le_antisymm (h₁.2 K₀ h₀') (h₀.2 K₁ h₁')

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
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsLocalHom (algebraMap A B)] [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [Module.Finite A B] [Module.IsTorsionFree A B]
    [FaithfulSMul A B] [IsIntegralClosure B A L]
    [Module.Finite (chapter09BaseResidueField A)
      (chapter09ExtensionResidueField B)]
    [Chapter09FiniteLocalExtension A B K L]
    (θbar : chapter09MaximalSeparableResidueSubfield
      (chapter09BaseResidueField A) (chapter09ExtensionResidueField B))
    (gbar : (chapter09BaseResidueField A)[X]) (g : A[X])
    (_hprimitive : Algebra.adjoin (chapter09BaseResidueField A)
      ({θbar} : Set (chapter09MaximalSeparableResidueSubfield
        (chapter09BaseResidueField A) (chapter09ExtensionResidueField B))) = ⊤)
    (_hmonic : gbar.Monic ∧ g.Monic) (_hirreducible : Irreducible gbar)
    (hseparable : gbar.Separable)
    (hminimal : gbar = minpoly (chapter09BaseResidueField A) (θbar :
      chapter09ExtensionResidueField B))
    (hlift : g.map (algebraMap A (chapter09BaseResidueField A)) = gbar) :
    ∃ θ : B,
      aeval θ (g.map (algebraMap A B)) = 0 ∧
        IsLocalRing.residue B θ = (θbar : chapter09ExtensionResidueField B) := by
  let F : B[X] := g.map (algebraMap A B)
  have hcomp :
      (IsLocalRing.residue B).comp (algebraMap A B) =
        (algebraMap (chapter09BaseResidueField A)
          (chapter09ExtensionResidueField B)).comp
          (algebraMap A (chapter09BaseResidueField A)) := by
    ext x
    simp
  have hred : F.map (IsLocalRing.residue B) =
      gbar.map (algebraMap (chapter09BaseResidueField A)
        (chapter09ExtensionResidueField B)) := by
    change (g.map (algebraMap A B)).map (IsLocalRing.residue B) =
      gbar.map (algebraMap (chapter09BaseResidueField A)
        (chapter09ExtensionResidueField B))
    rw [Polynomial.map_map, hcomp, ← Polynomial.map_map, hlift]
  have hrootbar :
      aeval (θbar : chapter09ExtensionResidueField B)
        (gbar.map (algebraMap (chapter09BaseResidueField A)
          (chapter09ExtensionResidueField B))) = 0 := by
    have hmap := Polynomial.map_aeval_eq_aeval_map
      (φ := algebraMap (chapter09BaseResidueField A)
        (chapter09ExtensionResidueField B))
      (ψ := RingHom.id (chapter09ExtensionResidueField B)) (by simp) gbar
        (θbar : chapter09ExtensionResidueField B)
    rw [hminimal] at hmap
    simpa only [RingHom.id_apply, minpoly.aeval, hminimal] using hmap.symm
  have hrootbase : aeval (θbar : chapter09ExtensionResidueField B) gbar = 0 := by
    rw [hminimal]
    exact minpoly.aeval _ _
  have hderivbase :
      aeval (θbar : chapter09ExtensionResidueField B) gbar.derivative ≠ 0 :=
    hseparable.aeval_derivative_ne_zero hrootbase
  have hderivbar :
      aeval (θbar : chapter09ExtensionResidueField B)
        (gbar.map (algebraMap (chapter09BaseResidueField A)
          (chapter09ExtensionResidueField B))).derivative ≠ 0 := by
    rw [Polynomial.derivative_map]
    simpa [aeval_def] using hderivbase
  obtain ⟨a₀, ha₀⟩ := Ideal.Quotient.mk_surjective
    (θbar : chapter09ExtensionResidueField B)
  have ha₀' : IsLocalRing.residue B a₀ =
      (θbar : chapter09ExtensionResidueField B) := ha₀
  have hfa : F.eval a₀ ∈ IsLocalRing.maximalIdeal B := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change IsLocalRing.residue B (F.eval a₀) = 0
    rw [← Polynomial.eval_map_apply, ha₀', hred]
    simpa [aeval_def] using hrootbar
  have hredderiv : (F.map (IsLocalRing.residue B)).derivative =
      (gbar.map (algebraMap (chapter09BaseResidueField A)
        (chapter09ExtensionResidueField B))).derivative :=
    congrArg Polynomial.derivative hred
  have hunit : IsUnit (F.derivative.eval a₀) := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    rw [← Polynomial.eval_map_apply, ← Polynomial.derivative_map, hredderiv, ha₀']
    exact hderivbar
  let : LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.CompleteDVR B :=
    { isAdicComplete' :=
        Chapter09FiniteLocalExtension.extension_complete A K L }
  obtain ⟨θ, hθ, _⟩ :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.hensel_simple_root
      F a₀ hfa hunit
  refine ⟨θ, ?_, ?_⟩
  · simpa [F] using hθ.1
  · have hresθ : IsLocalRing.residue B θ = IsLocalRing.residue B a₀ := by
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
      exact hθ.2
    exact Eq.trans hresθ ha₀'

/- The residue-lifting construction produces the canonical intermediate field. -/
theorem chapter09_lifted_generator_constructs_maximal_unramified_subextension
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsDomain A] [IsDomain B]
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
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsLocalHom (algebraMap A B)] [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [Module.Finite A B] [Module.IsTorsionFree A B]
    [FaithfulSMul A B] [IsIntegralClosure B A L]
    [Module.Finite (chapter09BaseResidueField A)
      (chapter09ExtensionResidueField B)]
    [Chapter09FiniteLocalExtension A B K L]
    (K₀ : IntermediateField K L) where
  /-- The remainder data retains the actual integral model of `K₀`; without
  this field the numerical fields below could be supplied independently of
  the distinguished intermediate field. -/
  base_data : Nonempty (Chapter09UnramifiedIntermediateData A B K L K₀
    (chapter09MaximalSeparableResidueSubfield
      (chapter09BaseResidueField A) (chapter09ExtensionResidueField B)))
  ramification_index : ℕ
  residue_degree : ℕ
  /-- The numerical ramification index is the canonical index for the
  induced integral extension from the selected unramified coefficient ring
  to `B`, not merely a copy of the original index. -/
  remainder_ramification_index_is_actual :
    let d := Classical.choice base_data
    letI : Algebra d.ring B := d.ring_to_extension.toRingHom.toAlgebra
    ramification_index =
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
        d.ring B (IsLocalRing.maximalIdeal B)
  /-- The numerical residue degree is the canonical residue degree for the
  actual remainder extension. -/
  remainder_residue_degree_is_actual :
    let d := Classical.choice base_data
    letI : Algebra d.ring B := d.ring_to_extension.toRingHom.toAlgebra
    residue_degree =
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree
        d.ring B (IsLocalRing.maximalIdeal B)
  ramification_index_eq : ramification_index =
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex A B
      (IsLocalRing.maximalIdeal B)
  residue_degree_eq : residue_degree =
    Module.finrank
      (chapter09MaximalSeparableResidueSubfield
        (chapter09BaseResidueField A) (chapter09ExtensionResidueField B))
      (chapter09ExtensionResidueField B)
  /-- The remainder still satisfies the fundamental degree formula. -/
  remainder_degree_formula :
    Module.finrank K₀ L = ramification_index * residue_degree
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
    [IsDomain A] [IsDomain B]
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
  let d := Classical.choice hK₀.1
  refine ⟨{
    base_data := hK₀.1
    ramification_index :=
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
        A B (IsLocalRing.maximalIdeal B)
    residue_degree := Module.finrank
      (chapter09MaximalSeparableResidueSubfield
        (chapter09BaseResidueField A) (chapter09ExtensionResidueField B))
      (chapter09ExtensionResidueField B)
    remainder_ramification_index_is_actual := d.remainder_ramification_index_eq.symm
    remainder_residue_degree_is_actual := d.remainder_residue_degree_eq.symm
    ramification_index_eq := rfl
    residue_degree_eq := rfl
    remainder_degree_formula := by
      rw [d.remainder_degree_formula, d.remainder_ramification_index_eq,
        d.remainder_residue_degree_eq]
    residue_extension_purely_inseparable :=
      (chapter09_separable_residue_part_properties
        (chapter09BaseResidueField A) (chapter09ExtensionResidueField B)).2
  }⟩

/-- The remainder is totally ramified precisely when the original residue
extension is separable. -/
theorem chapter09_remainder_totally_ramified_iff_residue_separable
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsDomain A] [IsDomain B]
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
  let s := chapter09MaximalSeparableResidueSubfield
    (chapter09BaseResidueField A) (chapter09ExtensionResidueField B)
  constructor
  · rintro ⟨r, hr⟩
    have hsfinrank : Module.finrank s (chapter09ExtensionResidueField B) = 1 := by
      rw [← r.residue_degree_eq]
      exact hr
    have hs : s = ⊤ :=
      (IntermediateField.finrank_eq_one_iff_eq_top (K := s)).mp hsfinrank
    exact (chapter09_separable_residue_part_eq_top_iff
      (chapter09BaseResidueField A) (chapter09ExtensionResidueField B)).mp hs
  · intro hsep
    obtain ⟨r⟩ := chapter09_remainder_invariants A B K L K₀ hK₀
    refine ⟨r, ?_⟩
    rw [r.residue_degree_eq]
    have hs : s = ⊤ :=
      (chapter09_separable_residue_part_eq_top_iff
        (chapter09BaseResidueField A) (chapter09ExtensionResidueField B)).mpr hsep
    rw [show chapter09MaximalSeparableResidueSubfield
      (chapter09BaseResidueField A) (chapter09ExtensionResidueField B) = s from rfl,
      hs]
    simp

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09
