import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.Section03CleanDecomposition

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09

open scoped BigOperators Polynomial
open Ideal IsLocalRing Polynomial

noncomputable section

/-! ## Book 2, Chapter 9.5: a two-stage integral description -/

/-- The explicit set of monomials theta^j pi_L^i appearing in the integral basis. -/
def chapter09ExplicitIntegralBasis
    (K₀ L : Type*) [Field K₀] [Field L] [Algebra K₀ L]
    (θ : K₀) (πL : L) (f e : ℕ) : Set L :=
  {x | ∃ j : Fin f, ∃ i : Fin e,
    x = algebraMap K₀ L (θ ^ (j : ℕ)) * πL ^ (i : ℕ)}

/-- Membership in the displayed monomial set is the expected finite-index
existential, which is convenient for rewriting coordinate statements. -/
theorem chapter09_mem_explicit_integral_basis_iff
    (K₀ L : Type*) [Field K₀] [Field L] [Algebra K₀ L]
    (θ : K₀) (πL : L) (f e : ℕ) (x : L) :
    x ∈ chapter09ExplicitIntegralBasis K₀ L θ πL f e ↔
      ∃ j : Fin f, ∃ i : Fin e,
        x = algebraMap K₀ L (θ ^ (j : ℕ)) * πL ^ (i : ℕ) := by
  rfl

/-- A presentation of the two integral stages.  The first polynomial is
unramified because its derivative is a unit; the second is Eisenstein and has
the ramification degree.  The coordinate fields record both uniqueness claims
from the source, and basis makes the final displayed set a genuine linear
basis. -/
structure Chapter09TwoStageIntegralDescription
    (A B K K₀ L : Type*) [CommRing A] [CommRing B] [IsDomain A]
    [Field K] [Field K₀] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K K₀] [Algebra A K₀]
    [Algebra K₀ L] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K K₀] [IsScalarTower K K₀ L]
    [IsScalarTower A K L] [IsScalarTower A K₀ L] [IsScalarTower A B L]
    [IsLocalHom (algebraMap A B)] [IsFractionRing B L]
    [IsDomain B] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing A] [Module.Finite A B]
    [Module.IsTorsionFree A B] [FaithfulSMul A B] [IsIntegralClosure B A L]
    [FiniteDimensional K K₀]
    [FiniteDimensional K₀ L] [IsLocalRing K₀]
    (θ : K₀) (πL : L) (e f : ℕ) where
  positive_e : 0 < e
  positive_f : 0 < f
  O₀ : Subalgebra A K₀
  O₁ : Subalgebra A L
  O₀_eq_adjoin : O₀ = Algebra.adjoin A ({θ} : Set K₀)
  O₁_eq_adjoin : O₁ = Algebra.adjoin A
    ({algebraMap K₀ L θ, πL} : Set L)
  /-- `O₀` is the actual integral model of the unramified intermediate
  field, not merely an auxiliary local subalgebra. -/
  O₀_finite : Module.Finite A O₀
  O₀_torsion_free : Module.IsTorsionFree A O₀
  O₀_fraction_field : IsFractionRing O₀ K₀
  O₀_integral_closure : IsIntegralClosure O₀ A K₀
  integral_ring_eq : Set.range (algebraMap B L) = (O₁ : Set L)
  theta_mem_O₀ : θ ∈ O₀
  piL_mem_O₁ : πL ∈ O₁
  /-- The coefficient ring acts on the integral ring.  This map is kept as
  data because `O₀` and `O₁` are subalgebra subtypes rather than fixed
  ambient rings. -/
  coefficient_algebra : Algebra O₀ O₁
  /-- The coefficient action is the one induced by the inclusions into `L`. -/
  coefficient_algebra_compatible :
    letI : Algebra O₀ O₁ := coefficient_algebra
    ∀ c : O₀,
      ((algebraMap O₀ O₁ c : O₁) : L) = algebraMap K₀ L (c : K₀)
  /-- The valuation ring is generated over the unramified coefficient ring
  by the chosen uniformizer.  This is the adjoin form of
  `B = 𝓞_{K₀}[π_L]` needed by later ramification arguments. -/
  O₁_eq_adjoin_coefficient_uniformizer :
    letI : Algebra O₀ O₁ := coefficient_algebra
    Algebra.adjoin O₀
      ({⟨πL, piL_mem_O₁⟩} : Set O₁) = ⊤
  O₁_local : IsLocalRing O₁
  O₁_dvr : IsDiscreteValuationRing O₁
  O₁_complete : IsAdicComplete (IsLocalRing.maximalIdeal O₁) O₁
  piL_generates_maximal_ideal :
    Ideal.span ({⟨πL, piL_mem_O₁⟩} : Set O₁) = IsLocalRing.maximalIdeal O₁
  O₀_local : IsLocalRing O₀
  O₀_local_hom : IsLocalHom (algebraMap A O₀)
  /-- The chosen coefficient generator remains primitive after reduction. -/
  first_residue_generator :
    letI : IsLocalRing O₀ := O₀_local
    letI : IsLocalHom (algebraMap A O₀) := O₀_local_hom
    Algebra.adjoin (chapter09BaseResidueField A)
      ({IsLocalRing.residue O₀ ⟨θ, theta_mem_O₀⟩} :
        Set (IsLocalRing.ResidueField O₀)) = ⊤
  O₀_dvr : IsDiscreteValuationRing O₀
  O₀_complete : IsAdicComplete (IsLocalRing.maximalIdeal O₀) O₀
  pi₀ : O₀
  pi₀_generates_maximal_ideal :
    Ideal.span ({pi₀} : Set O₀) = IsLocalRing.maximalIdeal O₀
  first_polynomial : A[X]
  first_polynomial_monic : first_polynomial.Monic
  first_polynomial_root :
    aeval θ first_polynomial = 0
  first_polynomial_is_minimal :
    minpoly K θ = first_polynomial.map (algebraMap A K)
  first_derivative_is_unit :
    IsUnit (eval₂ (algebraMap A K₀) θ
      (Polynomial.derivative first_polynomial))
  first_derivative_is_unit_in_O₀ :
    IsUnit (eval₂ (algebraMap A O₀) ⟨θ, theta_mem_O₀⟩
      (Polynomial.derivative first_polynomial))
  first_degree : first_polynomial.natDegree = f
  second_polynomial : O₀[X]
  second_polynomial_monic : second_polynomial.Monic
  second_polynomial_root :
    eval₂ ((algebraMap K₀ L).comp (algebraMap O₀ K₀)) πL second_polynomial = 0
  second_polynomial_is_minimal :
    minpoly K₀ πL = second_polynomial.map (algebraMap O₀ K₀)
  second_polynomial_eisenstein :
    letI : IsLocalRing O₀ := O₀_local
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt pi₀ second_polynomial
  second_degree : second_polynomial.natDegree = e
  coordinate_expansion :
    ∀ x : L, x ∈ O₁ → ∃! c : Fin e → K₀,
      (∀ i, c i ∈ O₀) ∧
        x = ∑ i, algebraMap K₀ L (c i) * πL ^ (i : ℕ)
  coefficient_expansion :
    ∀ c : K₀, c ∈ O₀ → ∃! d : Fin f → A,
      c = ∑ j, algebraMap A K₀ (d j) * θ ^ (j : ℕ)
  field_degree : Module.finrank K L = e * f
  /-- The presentation indices are the intrinsic residue and ramification
  degrees, rather than merely auxiliary polynomial degrees. -/
  residue_degree_index :
    f = LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree A B
      (IsLocalRing.maximalIdeal B)
  ramification_index :
    e = LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex A B
      (IsLocalRing.maximalIdeal B)
  basis : Module.Basis (Fin f × Fin e) A B
  basis_apply :
    ∀ ji, algebraMap B L (basis ji) =
      algebraMap K₀ L (θ ^ (ji.1 : ℕ)) * πL ^ (ji.2 : ℕ)
  basis_in_O₁ :
    ∀ ji, algebraMap B L (basis ji) ∈ O₁

/-! ### Galois refinement of the two-stage presentation -/

/-- The two-stage integral presentation together with the local Galois data
needed by later ramification chapters.  The subgroup `I` is tied to the
residue action and to the fixed field `K₀`; the final field records the
pointwise fixing of the unramified coefficient algebra. -/
structure Chapter09GaloisTwoStageIntegralBridge
    (A B K K₀ L : Type*) [CommRing A] [CommRing B] [IsDomain A]
    [Field K] [Field K₀] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K K₀] [Algebra A K₀]
    [Algebra K₀ L] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K K₀] [IsScalarTower K K₀ L]
    [IsScalarTower A K L] [IsScalarTower A K₀ L] [IsScalarTower A B L]
    [IsLocalHom (algebraMap A B)] [IsFractionRing A K] [IsFractionRing B L]
    [IsDomain B] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing A] [Module.Finite A B]
    [Module.IsTorsionFree A B] [FaithfulSMul A B] [IsIntegralClosure B A L]
    [Module.Finite (chapter09BaseResidueField A)
      (chapter09ExtensionResidueField B)]
    [FiniteDimensional K L] [FiniteDimensional K K₀]
    [FiniteDimensional K₀ L] [IsLocalRing K₀]
    [Chapter09FiniteLocalExtension A B K L]
    [IsGalois K L]
    (θ : K₀) (πL : L) (e f : ℕ)
    (I : Subgroup (L ≃ₐ[K] L)) where
  presentation : Chapter09TwoStageIntegralDescription A B K K₀ L θ πL e f
  /-- The actual maximal unramified intermediate field represented by the
  coefficient field of the presentation. -/
  maximal_field : IntermediateField K L
  maximal : chapter09MaximalUnramifiedSubextension A B K L maximal_field
  fixed_field_eq : chapter09InertiaFixedField K L I = maximal_field
  /-- The coefficient field in the presentation has exactly the displayed
  maximal-unramified image inside `L`. -/
  coefficient_field_range :
    (maximal_field : Set L) = Set.range (algebraMap K₀ L)
  residue_action : Chapter09ResidueActionData A B K L
  inertia_eq_kernel : I = MonoidHom.ker residue_action.action
  inertia_order : Nat.card I =
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex A B
      (IsLocalRing.maximalIdeal B)
  /-- Every element of the coefficient algebra is fixed pointwise by
  inertia.  This is stronger than merely saying that inertia is invisible
  after reduction and is the exact hypothesis used in coefficient-adjoin
  displacement arguments. -/
  inertia_fixes_coefficient_algebra :
    ∀ σ : I, ∀ c : presentation.O₀,
      σ.1 (algebraMap K₀ L (c : K₀)) = algebraMap K₀ L (c : K₀)

/-- The coordinate statements and the explicit monomial set extracted from a
two-stage presentation. -/
theorem chapter09_two_stage_coordinates
    (A B K K₀ L : Type*) [CommRing A] [CommRing B] [IsDomain A]
    [Field K] [Field K₀] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K K₀] [Algebra A K₀]
    [Algebra K₀ L] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K K₀] [IsScalarTower K K₀ L]
    [IsScalarTower A K L] [IsScalarTower A K₀ L] [IsScalarTower A B L]
    [IsLocalHom (algebraMap A B)] [IsFractionRing B L]
    [IsDomain B] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing A] [Module.Finite A B]
    [Module.IsTorsionFree A B] [FaithfulSMul A B] [IsIntegralClosure B A L]
    [FiniteDimensional K K₀] [FiniteDimensional K₀ L]
    (θ : K₀) (πL : L) (e f : ℕ)
    (d : Chapter09TwoStageIntegralDescription A B K K₀ L θ πL e f) :
    (∀ x : L, x ∈ d.O₁ → ∃! c : Fin e → K₀,
      (∀ i, c i ∈ d.O₀) ∧
        x = ∑ i, algebraMap K₀ L (c i) * πL ^ (i : ℕ)) ∧
    (∀ c : K₀, c ∈ d.O₀ → ∃! q : Fin f → A,
      c = ∑ j, algebraMap A K₀ (q j) * θ ^ (j : ℕ)) ∧
    ∀ ji, algebraMap B L (d.basis ji) ∈
      chapter09ExplicitIntegralBasis K₀ L θ πL f e := by
  refine ⟨d.coordinate_expansion, d.coefficient_expansion, ?_⟩
  intro ji
  exact ⟨ji.1, ji.2, d.basis_apply ji⟩

/-- The basis images are exactly the monomials displayed in the source, not
merely elements of that set. -/
theorem chapter09_two_stage_basis_image_eq_explicit_integral_basis
    (A B K K₀ L : Type*) [CommRing A] [CommRing B] [IsDomain A]
    [Field K] [Field K₀] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K K₀] [Algebra A K₀]
    [Algebra K₀ L] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K K₀] [IsScalarTower K K₀ L]
    [IsScalarTower A K L] [IsScalarTower A K₀ L] [IsScalarTower A B L]
    [IsLocalHom (algebraMap A B)] [IsFractionRing B L]
    [IsDomain B] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing A] [Module.Finite A B]
    [Module.IsTorsionFree A B] [FaithfulSMul A B] [IsIntegralClosure B A L]
    [FiniteDimensional K K₀] [FiniteDimensional K₀ L]
    (θ : K₀) (πL : L) (e f : ℕ)
    (d : Chapter09TwoStageIntegralDescription A B K K₀ L θ πL e f) :
    Set.range (fun ji : Fin f × Fin e => algebraMap B L (d.basis ji)) =
      chapter09ExplicitIntegralBasis K₀ L θ πL f e := by
  ext x
  constructor
  · rintro ⟨ji, rfl⟩
    exact ⟨ji.1, ji.2, d.basis_apply ji⟩
  · rintro ⟨j, i, rfl⟩
    exact ⟨(j, i), d.basis_apply (j, i)⟩

/-- Existence interface for the two-stage integral description under the
separable-residue hypothesis.  The local-field and finite-dimensional
hypotheses are explicit so later proof passes can identify the abstract
presentation with the valuation rings of K₀ and L. -/
theorem chapter09_two_stage_integral_description_exists
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
    (d : Chapter09Corollary92Data A B K L)
    [FiniteDimensional K d.K₀] [FiniteDimensional d.K₀ L]
    [Algebra A d.K₀]
    [IsScalarTower A K d.K₀]
    [IsScalarTower A d.K₀ L]
    (hseparable : Algebra.IsSeparable (chapter09BaseResidueField A)
      (chapter09ExtensionResidueField B)) :
    ∃ (θ : d.K₀) (πL : L) (e f : ℕ),
      Nonempty (Chapter09TwoStageIntegralDescription A B K d.K₀ L
        θ πL e f) := by
  sorry

/-- The complete finite-Galois branch interface needed by the later
ramification chapters.  The supplied clean-decomposition datum chooses the
maximal unramified field; the output packages its integral presentation with
the inertia subgroup and the pointwise coefficient-fixing statement. -/
theorem chapter09_galois_two_stage_integral_bridge_exists
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
    [Chapter09FiniteLocalExtension A B K L] [IsGalois K L]
    (d : Chapter09Corollary92Data A B K L)
    [FiniteDimensional K d.K₀] [FiniteDimensional d.K₀ L]
    [Algebra A d.K₀] [IsScalarTower A K d.K₀]
    [IsScalarTower A d.K₀ L]
    (hseparable : Algebra.IsSeparable (chapter09BaseResidueField A)
      (chapter09ExtensionResidueField B)) :
    ∃ (θ : d.K₀) (πL : L) (e f : ℕ)
      (I : Subgroup (L ≃ₐ[K] L)),
      Nonempty (Chapter09GaloisTwoStageIntegralBridge A B K d.K₀ L
        θ πL e f I) := by
  sorry

/-- The coordinate basis has e*f vectors, realizing the multiplicative
degree allocation at the level of coordinates. -/
theorem chapter09_two_stage_basis_cardinality
    (e f : ℕ) :
    Fintype.card (Fin f × Fin e) = f * e := by
  simp [Fintype.card_prod]

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09
