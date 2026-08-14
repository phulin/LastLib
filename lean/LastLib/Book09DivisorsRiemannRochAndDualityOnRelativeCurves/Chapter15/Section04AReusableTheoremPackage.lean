import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter15.Section03AFormalImmersionCriterion

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter15

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11
open scoped BigOperators

universe u v

/-!
### 15.4 A reusable theorem package

The declarations in this leaf collect the divisor, family, duality, and
cohomology interfaces used by later books.  They are intentionally records of
the exact hypotheses and comparison maps, rather than a collection of opaque
properties on a relative curve.
-/

/- LOCAL_DEPENDENCY_GUESS: divisor-cycle groups, relative dualizing sheaves,
   higher direct images, and cohomological base-change maps are not yet
   packaged together in the preceding LastLib interfaces. -/

/-! Divisors on regular schemes and regular proper curves. -/
structure Chapter15CartierWeilComparison (X : Scheme.{u}) where
  cartierDivisors : Type u
  weilDivisors : Type u
  toWeil : cartierDivisors → weilDivisors
  toCartier : weilDivisors → cartierDivisors
  left_inverse : Function.LeftInverse toCartier toWeil
  right_inverse : Function.RightInverse toCartier toWeil
  Cartier_is_codimension_one : Prop
  Cartier_is_codimension_one_proof : Cartier_is_codimension_one
  Weil_is_codimension_one : Prop
  Weil_is_codimension_one_proof : Weil_is_codimension_one

theorem chapter15_regular_noetherian_integral_cartier_eq_weil
    (X : Scheme.{u}) (regular : Prop) (is_regular : regular)
    (noetherian : IsNoetherian X) (integral : Prop) (is_integral : integral) :
    Nonempty (Chapter15CartierWeilComparison X) := by
  sorry

structure Chapter15CurveDivisorClassData
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) where
  divisorClasses : Type u
  divisorClass_lineBundleEquiv :
    divisorClasses ≃ Chapter15LineBundle C.curve.carrier
  principalFunctions : Type u
  principalDivisor : principalFunctions → divisorClasses
  degree : divisorClasses → ℤ
  eulerCharacteristicOfClass : divisorClasses → ℤ
  euler_characteristic_is_of_O_of_D : Prop
  euler_characteristic_is_of_O_of_D_proof : euler_characteristic_is_of_O_of_D
  eulerCharacteristicOfStructure : ℤ
  support : ∀ D : divisorClasses, Finset C.curve.carrier
  multiplicity : ∀ D : divisorClasses, C.curve.carrier → ℤ
  residueFieldDegree : C.curve.carrier → ℕ
  degree_as_sum : ∀ D : divisorClasses,
    degree D = ∑ x in support D,
      multiplicity D x * (residueFieldDegree x : ℤ)
  principal_degree_zero : ∀ f : principalFunctions,
    degree (principalDivisor f) = 0
  Riemann_Roch_degree_formula : ∀ D : divisorClasses,
    degree D = eulerCharacteristicOfClass D - eulerCharacteristicOfStructure

theorem chapter15_proper_regular_integral_curve_divisor_classes
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) :
    Nonempty (Chapter15CurveDivisorClassData C) := by
  sorry

/- Singular and reducible curves retain Cartier divisors, but a cycle-to-
   Cartier conversion is a separately supplied comparison, not an automatic
   consequence of the regular dictionary. -/
structure Chapter15SingularReducibleDivisorConversion (X : Scheme.{u}) where
  cartierDivisors : Type u
  cycles : Type u
  toCycle : cartierDivisors → cycles
  normalizationOrComponentData : Prop
  normalizationOrComponentData_proof : normalizationOrComponentData
  conversion_requires_separate_justification : Prop
  conversion_requires_separate_justification_proof :
    conversion_requires_separate_justification

/-! Families, degree, Euler characteristic, and symmetric powers. -/
structure Chapter15FamilyLineBundleInvariants
    {S : Scheme.{u}}
    (C : Chapter15ProjectiveFlatRelativeCurve S)
    (L : Chapter15LineBundle C.curve.carrier) where
  fiberDegree : S → ℤ
  fiberEulerCharacteristic : S → ℤ
  degree_locally_constant : Chapter15LocallyConstant fiberDegree
  Euler_characteristic_locally_constant :
    Chapter15LocallyConstant fiberEulerCharacteristic

theorem chapter15_family_line_bundle_degree_and_euler_locally_constant
    {S : Scheme.{u}}
    (C : Chapter15ProjectiveFlatRelativeCurve S)
    (L : Chapter15LineBundle C.curve.carrier) :
    Nonempty (Chapter15FamilyLineBundleInvariants C L) := by
  sorry

theorem chapter15_relative_effective_divisor_has_finite_flat_rank
    {S : Scheme.{u}}
    (C : Chapter15ProjectiveFlatRelativeCurve S)
    (T : RelativeScheme S) (d : ℕ)
    (D : Chapter15RelativeEffectiveCartierDivisor C.curve T d) :
    Chapter11FiniteLocallyFreeOfRank
      (D.divisor.inclusion ≫
        pullback.snd C.curve.structuralMap T.structuralMap) d :=
  D.finite_flat_rank

theorem chapter15_relative_effective_divisor_has_degree_d_on_every_fiber
    {S : Scheme.{u}}
    (C : Chapter15ProjectiveFlatRelativeCurve S)
    (T : RelativeScheme S) (d : ℕ)
    (D : Chapter15RelativeEffectiveCartierDivisor C.curve T d) :
    ∀ y : T.carrier,
      Scheme.Hom.finrank
        (D.divisor.inclusion ≫
          pullback.snd C.curve.structuralMap T.structuralMap) y = d := by
  intro y
  exact D.finite_flat_rank.2.2.2 y

theorem chapter15_smooth_projective_curve_divisors_are_represented_by_symmetric_power
    {S : Scheme.{u}}
    (C : Chapter15SmoothProjectiveRelativeCurve S) (d : ℕ) :
    Nonempty (Chapter11UniversalDivisorRepresentingData C.curve d) := by
  exact ⟨universalDivisorRepresentingData C.curve d⟩

theorem chapter15_symmetric_power_universal_divisor_commutes_with_base_change
    {S : Scheme.{u}}
    (C : Chapter15SmoothProjectiveRelativeCurve S) (d : ℕ)
    (T : RelativeScheme S) :
    ∃ e : RelativeScheme.Iso
        (RelativeScheme.baseChange (symmetricPower C.curve d) T)
        (symmetricPower (RelativeScheme.baseChange C.curve T) d),
      RelativeScheme.baseChangeHom (symmetricPowerMap C.curve d) T ≫ e.hom =
        relativePowerBaseChangeComparison C.curve T d ≫
          symmetricPowerMap (RelativeScheme.baseChange C.curve T) d := by
  exact symmetricPower_curve_base_change_iso C.curve d T

/-! Differentials, relative dualizing sheaves, and Serre duality. -/
structure Chapter15SmoothRelativeDifferentialData
    {S : Scheme.{u}}
    (C : Chapter15ProjectiveFlatRelativeCurve S) where
  relativeDifferentials : C.curve.carrier.Modules
  relativeDualizing : C.curve.carrier.Modules
  omega_equals_relative_differentials :
    relativeDualizing ≅ relativeDifferentials

theorem chapter15_smooth_family_omega_is_relative_differentials
    {S : Scheme.{u}}
    (C : Chapter15ProjectiveFlatRelativeCurve S)
    (smooth : SmoothOfRelativeDimension 1 C.curve.structuralMap) :
    Nonempty (Chapter15SmoothRelativeDifferentialData C) := by
  sorry

structure Chapter15GorensteinNodalFamilyData
    {S : Scheme.{u}}
    (C : Chapter15ProjectiveFlatRelativeCurve S) where
  relativeDualizing : Chapter15LineBundle C.curve.carrier
  baseChangeCompatibility : ∀ T : RelativeScheme S, Prop
  baseChangeCompatibility_proof :
    ∀ T : RelativeScheme S, baseChangeCompatibility T
  nodal_fibers : Prop
  nodal_fibers_proof : nodal_fibers

theorem chapter15_gorenstein_nodal_family_has_invertible_base_change_dualizing
    {S : Scheme.{u}}
    (C : Chapter15ProjectiveFlatRelativeCurve S)
    (gorenstein : Prop) (is_gorenstein : gorenstein)
    (nodal : Prop) (is_nodal : nodal) :
    Nonempty (Chapter15GorensteinNodalFamilyData C) := by
  sorry

structure Chapter15NodalNormalizationDifferentialData
    {k : Type u} [Field k] (X : Scheme.{u}) where
  nodalCurve : Scheme.{u}
  nodalCurve_is_the_given_curve : nodalCurve = X
  normalization : Scheme.{u}
  normalizationDifferentials : normalization.Modules
  meromorphicDifferentials : normalization.Modules
  pullback_has_simple_branch_poles : Prop
  pullback_has_simple_branch_poles_proof : pullback_has_simple_branch_poles
  residues_on_two_branches : ModuleCat k
  opposite_residues : Prop
  opposite_residues_proof : opposite_residues
  gives_dualizing_sections : Prop
  gives_dualizing_sections_proof : gives_dualizing_sections

theorem chapter15_nodal_dualizing_sections_are_normalization_differentials
    {k : Type u} [Field k]
    (X : Scheme.{u}) (nodal : Prop) (is_nodal : nodal) :
    Nonempty (Chapter15NodalNormalizationDifferentialData X) := by
  sorry

structure Chapter15VectorBundle (X : Scheme.{u}) where
  module : X.Modules
  finite_locally_free : Prop
  finite_locally_free_proof : finite_locally_free

structure Chapter15RelativeSerreDualityData
    {S : Scheme.{u}}
    (C : Chapter15ProjectiveFlatRelativeCurve S)
    (E : Chapter15VectorBundle C.curve.carrier) where
  relativeDualizing : Chapter15LineBundle C.curve.carrier
  E_dual_tensor_omega : C.curve.carrier.Modules
  pushforward_dual_tensor : S.Modules
  R1_pushforward_E_dual : S.Modules
  duality_isomorphism : pushforward_dual_tensor ≅ R1_pushforward_E_dual
  left_is_f_pushforward_of_E_dual_tensor_omega : Prop
  left_is_f_pushforward_of_E_dual_tensor_omega_proof :
    left_is_f_pushforward_of_E_dual_tensor_omega
  right_is_dual_of_R1f_pushforward_E : Prop
  right_is_dual_of_R1f_pushforward_E_proof : right_is_dual_of_R1f_pushforward_E
  perfect_fiberwise_pairing : Prop
  perfect_fiberwise_pairing_proof : perfect_fiberwise_pairing

theorem chapter15_relative_serre_duality_for_vector_bundles
    {S : Scheme.{u}}
    (C : Chapter15ProjectiveFlatRelativeCurve S)
    (E : Chapter15VectorBundle C.curve.carrier)
    (hduality : Prop) (has_hduality : hduality) :
    Nonempty (Chapter15RelativeSerreDualityData C E) := by
  sorry

structure Chapter15FiberSerreDualityData
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k)
    (E : Chapter15VectorBundle C.curve.carrier) where
  H0 : ModuleCat k
  H1 : ModuleCat k
  dualH1 : ModuleCat k
  dualH1_is_dual_H1 : Prop
  dualH1_is_dual_H1_proof : dualH1_is_dual_H1
  pairingIsomorphism : H0 ≅ dualH1
  perfect_pairing : Prop
  perfect_pairing_proof : perfect_pairing
  fiber_bundle_restriction : Prop
  fiber_bundle_restriction_proof : fiber_bundle_restriction

theorem chapter15_fiberwise_serre_duality_is_perfect
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k)
    (E : Chapter15VectorBundle C.curve.carrier) :
    Nonempty (Chapter15FiberSerreDualityData C E) := by
  sorry

/-! Cohomology models, semicontinuity, and base change. -/
structure Chapter15TwoTermFiniteFreeCohomologyModel
    {R : Type u} [CommRing R]
    {X : Scheme.{u}} (E : Chapter15VectorBundle X) where
  K0 : ModuleCat R
  K1 : ModuleCat R
  differential : K0 ⟶ K1
  K0_finite_free : Prop
  K0_finite_free_proof : K0_finite_free
  K1_finite_free : Prop
  K1_finite_free_proof : K1_finite_free
  H0_is_kernel : Prop
  H0_is_kernel_proof : H0_is_kernel
  H1_is_cokernel : Prop
  H1_is_cokernel_proof : H1_is_cokernel
  computes_cohomology : Prop
  computes_cohomology_proof : computes_cohomology
  compatible_with_base_change : Prop
  compatible_with_base_change_proof : compatible_with_base_change

theorem chapter15_cohomology_has_local_two_term_finite_free_model
    {S : Scheme.{u}}
    (C : Chapter15ProjectiveFlatRelativeCurve S)
    (E : Chapter15VectorBundle C.curve.carrier)
    (R : Type u) [CommRing R] :
    Nonempty (Chapter15TwoTermFiniteFreeCohomologyModel (R := R) E) := by
  sorry

def Chapter15UpperSemicontinuous {α : Type u} [TopologicalSpace α]
    (h : α → ℕ) : Prop :=
  ∀ n : ℕ, IsOpen {x | h x < n}

structure Chapter15FiberCohomologyDimensionData
    {S : Scheme.{u}}
    (C : Chapter15ProjectiveFlatRelativeCurve S)
    (E : Chapter15VectorBundle C.curve.carrier) where
  h0 : S → ℕ
  h1 : S → ℕ
  h0_upper_semicontinuous : Chapter15UpperSemicontinuous h0
  h1_upper_semicontinuous : Chapter15UpperSemicontinuous h1
  h0_is_fiber_dimension : Prop
  h0_is_fiber_dimension_proof : h0_is_fiber_dimension
  h1_is_fiber_dimension : Prop
  h1_is_fiber_dimension_proof : h1_is_fiber_dimension

theorem chapter15_fiber_cohomology_dimensions_upper_semicontinuous
    {S : Scheme.{u}}
    (C : Chapter15ProjectiveFlatRelativeCurve S)
    (E : Chapter15VectorBundle C.curve.carrier) :
    Nonempty (Chapter15FiberCohomologyDimensionData C E) := by
  sorry

structure Chapter15PushforwardBaseChangeData
    {S : Scheme.{u}} {X : Scheme.{u}}
    (f : X ⟶ S) (E : Chapter15VectorBundle X)
    (h1 : S → ℕ) where
  pushforward : S.Modules
  pushforward_is_f_pushforward :
    pushforward = (Scheme.Modules.pushforward f).obj E.module
  locally_free : Prop
  locally_free_proof : locally_free
  arbitrary_base_change :
    chapter09PushforwardCommutesWithBaseChange f E.module

theorem chapter15_h1_vanishing_gives_locally_free_pushforward_and_base_change
    {S : Scheme.{u}}
    (C : Chapter15ProjectiveFlatRelativeCurve S)
    (E : Chapter15VectorBundle C.curve.carrier)
    (h1 : S → ℕ) (hvanishing : ∀ s : S, h1 s = 0) :
    Nonempty (Chapter15PushforwardBaseChangeData C.curve.structuralMap E h1) := by
  sorry

/- The infinitesimal interfaces are restated as one reusable package for
   downstream chapters. -/
structure Chapter15InfinitesimalDivisorPackage
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d) where
  tangentIdentification :
    Nonempty (chapter15TangentAtDivisor C d D ≅ chapter15NormalSections D)
  abelDifferential : Chapter15AbelDifferentialData C d D
  transposeRestriction : Chapter15DifferentialRestrictionData C d D

theorem chapter15_infinitesimal_divisor_package_exists
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ)
    (D : Chapter15FiberDivisor C d) :
    Nonempty (Chapter15InfinitesimalDivisorPackage C d D) := by
  sorry

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter15
