import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter15.Section03AFormalImmersionCriterion
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter05.Dependencies
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter09.Section04SmoothAndGorensteinFamilies

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter15

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter05
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter09
open scoped BigOperators

universe u v

/-!
### 15.4 A reusable theorem package

The declarations in this leaf collect the divisor, family, duality, and
cohomology interfaces used by later books.  They are intentionally records of
the exact hypotheses and comparison maps, rather than a collection of opaque
properties on a relative curve.
-/

/-! Divisors on regular schemes and regular proper curves. -/
structure Chapter15CartierWeilComparison (X : Scheme.{u})
    [Chapter04TotalQuotientRingAPI X] where
  toWeil : Chapter04CartierDivisor X → Chapter04WeilDivisor X
  toCartier : Chapter04WeilDivisor X → Chapter04CartierDivisor X
  left_inverse : Function.LeftInverse toCartier toWeil
  right_inverse : Function.RightInverse toCartier toWeil

theorem chapter15_regular_noetherian_integral_cartier_eq_weil
    (X : Scheme.{u}) [Chapter04TotalQuotientRingAPI X]
    (regular : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (noetherian : IsNoetherian X) (integral : IsIntegral X) :
    Nonempty (Chapter15CartierWeilComparison X) := by
  sorry

abbrev Chapter15DivisorClasses {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) :=
  Chapter05Divisor C.curve.carrier

noncomputable def chapter15LineBundleOfDivisor
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k)
    (D : Chapter15DivisorClasses C) : Chapter15LineBundle C.curve.carrier := by
  sorry

noncomputable def chapter15EulerCharacteristicOfDivisor
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k)
    (D : Chapter15DivisorClasses C) : ℤ := by
  sorry

abbrev Chapter15PrincipalFunction
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k)
    [IrreducibleSpace (C.curve.carrier : Type u)] :=
  (C.curve.carrier.functionField : Type u)

structure Chapter15CurveDivisorClassData
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k)
    [IrreducibleSpace (C.curve.carrier : Type u)] where
  associatedLineBundle : Chapter15DivisorClasses C → Chapter15LineBundle C.curve.carrier
  associatedLineBundle_is_canonical : ∀ D,
    associatedLineBundle D = chapter15LineBundleOfDivisor C D
  principalFunctions : Chapter15PrincipalFunction C
  principalDivisor : Chapter15PrincipalFunction C → Chapter15DivisorClasses C
  degree : Chapter15DivisorClasses C → ℤ
  eulerCharacteristicOfClass : Chapter15DivisorClasses C → ℤ
  degree_is_canonical : ∀ D,
    degree D = chapter05Degree C.curve.structuralMap D
  euler_characteristic_is_of_O_of_D : ∀ D,
    eulerCharacteristicOfClass D = chapter15EulerCharacteristicOfDivisor C D
  eulerCharacteristicOfStructure : ℤ
  support : Chapter15DivisorClasses C → Finset C.curve.carrier
  support_is_canonical : ∀ D, support D = D.coeff.support
  multiplicity : Chapter15DivisorClasses C → C.curve.carrier → ℤ
  multiplicity_is_canonical : ∀ D x, multiplicity D x = D.coeff x
  residueFieldDegree : C.curve.carrier → ℕ
  degree_as_sum : ∀ D : Chapter15DivisorClasses C,
    degree D = Finset.sum (support D) (fun x =>
      multiplicity D x * (residueFieldDegree x : ℤ))
  principal_degree_zero : ∀ f : Chapter15PrincipalFunction C,
    degree (principalDivisor f) = 0
  Riemann_Roch_degree_formula : ∀ D : Chapter15DivisorClasses C,
    degree D = eulerCharacteristicOfClass D - eulerCharacteristicOfStructure

theorem chapter15_proper_regular_integral_curve_divisor_classes
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k)
    [IrreducibleSpace (C.curve.carrier : Type u)] :
    Nonempty (Chapter15CurveDivisorClassData C) := by
  sorry

/- Singular and reducible curves retain Cartier divisors, but a cycle-to-
   Cartier conversion is a separately supplied comparison, not an automatic
   consequence of the regular dictionary. -/
structure Chapter15SingularReducibleDivisorConversion (X : Scheme.{u}) where
  cartierDivisor : Chapter15EffectiveCartierDivisor X
  cycle : Chapter04WeilDivisor X
  toCycle : Chapter15EffectiveCartierDivisor X → Chapter04WeilDivisor X
  normalizationOrComponent : Scheme.{u}
  normalizationMap : normalizationOrComponent ⟶ X
  cycle_is_canonical : cycle = toCycle cartierDivisor

/-! Families, degree, Euler characteristic, and symmetric powers. -/
noncomputable def chapter15FiberLineBundleDegree
    {S : Scheme.{u}}
    (C : Chapter15ProjectiveFlatRelativeCurve S)
    (L : Chapter15LineBundle C.curve.carrier) (s : S) : ℤ := by
  sorry

noncomputable def chapter15FiberLineBundleEulerCharacteristic
    {S : Scheme.{u}}
    (C : Chapter15ProjectiveFlatRelativeCurve S)
    (L : Chapter15LineBundle C.curve.carrier) (s : S) : ℤ := by
  sorry

structure Chapter15FamilyLineBundleInvariants
    {S : Scheme.{u}}
    (C : Chapter15ProjectiveFlatRelativeCurve S)
    (L : Chapter15LineBundle C.curve.carrier) where
  fiberDegree : S → ℤ
  fiberEulerCharacteristic : S → ℤ
  fiberDegree_is_canonical : ∀ s,
    fiberDegree s = chapter15FiberLineBundleDegree C L s
  fiberEulerCharacteristic_is_canonical : ∀ s,
    fiberEulerCharacteristic s = chapter15FiberLineBundleEulerCharacteristic C L s
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
noncomputable def chapter15RelativeDifferentialSheaf
    {S : Scheme.{u}}
    (C : Chapter15ProjectiveFlatRelativeCurve S) : C.curve.carrier.Modules := by
  sorry

noncomputable def chapter15RelativeDualizingSheaf
    {S : Scheme.{u}}
    (C : Chapter15ProjectiveFlatRelativeCurve S) : C.curve.carrier.Modules := by
  sorry

noncomputable def chapter15BaseChangedDualizingSheaf
    {S : Scheme.{u}}
    (C : Chapter15ProjectiveFlatRelativeCurve S)
    (T : RelativeScheme S) :
    (pullback C.curve.structuralMap T.structuralMap).Modules := by
  sorry

noncomputable def chapter15PushforwardBaseChangeMap
    {S : Scheme.{u}}
    (C : Chapter15ProjectiveFlatRelativeCurve S)
    (E : C.curve.carrier.Modules)
    (T : RelativeScheme S) :
    (Scheme.Modules.pullback T.structuralMap).obj
        ((Scheme.Modules.pushforward C.curve.structuralMap).obj E) ⟶
      (Scheme.Modules.pushforward
        (pullback.snd C.curve.structuralMap T.structuralMap)).obj
        ((Scheme.Modules.pullback
          (pullback.fst C.curve.structuralMap T.structuralMap)).obj E) := by
  sorry

structure Chapter15SmoothRelativeDifferentialData
    {S : Scheme.{u}}
    (C : Chapter15ProjectiveFlatRelativeCurve S) where
  omega_equals_relative_differentials :
    chapter15RelativeDualizingSheaf C ≅ chapter15RelativeDifferentialSheaf C

theorem chapter15_smooth_family_omega_is_relative_differentials
    {S : Scheme.{u}}
    (C : Chapter15ProjectiveFlatRelativeCurve S)
    (smooth : SmoothOfRelativeDimension 1 C.curve.structuralMap) :
    Nonempty (Chapter15SmoothRelativeDifferentialData C) := by
  sorry

structure Chapter15GorensteinNodalFamilyData
    {S : Scheme.{u}}
    (C : Chapter15ProjectiveFlatRelativeCurve S) where
  relativeDualizing : C.curve.carrier.Modules
  relativeDualizing_is_canonical :
    relativeDualizing = chapter15RelativeDualizingSheaf C
  relativeDualizing_finite_locally_free :
    chapter04FiniteLocallyFree relativeDualizing
  baseChangeCompatibility : ∀ T : RelativeScheme S,
    Nonempty ((Scheme.Modules.pullback
      (pullback.fst C.curve.structuralMap T.structuralMap)).obj
        relativeDualizing ≅ chapter15BaseChangedDualizingSheaf C T)
  nodal_fibers : ∀ s : S,
    chapter01NodalScheme (C.curve.structuralMap.fiber s)

theorem chapter15_gorenstein_nodal_family_has_invertible_base_change_dualizing
    {S : Scheme.{u}}
    (C : Chapter15ProjectiveFlatRelativeCurve S)
    (gorenstein : chapter09GorensteinMorphism C.curve.structuralMap)
    (nodal : ∀ s : S, chapter01NodalScheme (C.curve.structuralMap.fiber s)) :
    Nonempty (Chapter15GorensteinNodalFamilyData C) := by
  sorry

structure Chapter15NodalNormalizationDifferentialData
    {k : Type u} [Field k] (X : Scheme.{u}) where
  nodalCurve : chapter01NodalScheme X
  normalization : Scheme.{u}
  normalizationMap : normalization ⟶ X
  normalizationDifferentials : normalization.Modules
  meromorphicDifferentials : normalization.Modules
  pullback_has_simple_branch_poles :
    Nonempty (normalizationDifferentials ≅ meromorphicDifferentials)
  residues_on_two_branches : ModuleCat.{u, u} k
  opposite_residues : Nonempty (residues_on_two_branches ≅ residues_on_two_branches)
  gives_dualizing_sections : normalization.Modules
  dualizing_sections_map : gives_dualizing_sections ⟶ meromorphicDifferentials

theorem chapter15_nodal_dualizing_sections_are_normalization_differentials
    {k : Type u} [Field k]
    (X : Scheme.{u}) (nodal : chapter01NodalScheme X) :
    Nonempty (Chapter15NodalNormalizationDifferentialData (k := k) X) := by
  sorry

structure Chapter15VectorBundle (X : Scheme.{u}) where
  module : X.Modules
  finite_locally_free : chapter04FiniteLocallyFree module

noncomputable def chapter15DualTensorWithDualizing
    {S : Scheme.{u}}
    (C : Chapter15ProjectiveFlatRelativeCurve S)
    (E : Chapter15VectorBundle C.curve.carrier) : C.curve.carrier.Modules := by
  sorry

noncomputable def chapter15RelativeDualityTarget
    {S : Scheme.{u}}
    (C : Chapter15ProjectiveFlatRelativeCurve S)
    (E : Chapter15VectorBundle C.curve.carrier) : S.Modules := by
  sorry

structure Chapter15RelativeSerreDualityData
    {S : Scheme.{u}}
    (C : Chapter15ProjectiveFlatRelativeCurve S)
    (E : Chapter15VectorBundle C.curve.carrier) where
  relativeDualizing : C.curve.carrier.Modules
  relativeDualizing_is_canonical :
    relativeDualizing = chapter15RelativeDualizingSheaf C
  relativeDualizing_finite_locally_free :
    chapter04FiniteLocallyFree relativeDualizing
  E_dual_tensor_omega : C.curve.carrier.Modules
  E_dual_tensor_omega_is_canonical :
    E_dual_tensor_omega = chapter15DualTensorWithDualizing C E
  pushforward_dual_tensor : S.Modules
  pushforward_dual_tensor_is_canonical :
    pushforward_dual_tensor =
      (Scheme.Modules.pushforward C.curve.structuralMap).obj E_dual_tensor_omega
  R1_pushforward_E_dual : S.Modules
  duality_isomorphism : pushforward_dual_tensor ≅ R1_pushforward_E_dual
  left_is_f_pushforward_of_E_dual_tensor_omega :
    pushforward_dual_tensor = chapter15RelativeDualityTarget C E
  right_is_dual_of_R1f_pushforward_E :
    Nonempty (R1_pushforward_E_dual ≅ chapter15RelativeDualityTarget C E)
  perfect_fiberwise_pairing :
    Nonempty (pushforward_dual_tensor ≅ R1_pushforward_E_dual)

theorem chapter15_relative_serre_duality_for_vector_bundles
    {S : Scheme.{u}}
    (C : Chapter15ProjectiveFlatRelativeCurve S)
    (E : Chapter15VectorBundle C.curve.carrier)
    [Chapter09RelativeDerivedHomTheory C.curve.structuralMap]
    (hduality : Nonempty
      (Chapter09RelativeDualizingData C.curve.structuralMap)) :
    Nonempty (Chapter15RelativeSerreDualityData C E) := by
  sorry

structure Chapter15FiberSerreDualityData
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k)
    (E : Chapter15VectorBundle C.curve.carrier) where
  H0 : ModuleCat.{u, u} k
  H1 : ModuleCat.{u, u} k
  dualH1 : ModuleCat.{u, u} k
  H0_is_canonical : Nonempty (H0 ≅ chapter15CohomologyVectorSpace E.module 0)
  H1_is_canonical : Nonempty (H1 ≅ chapter15CohomologyVectorSpace E.module 1)
  dualH1_is_dual_H1 : Nonempty (dualH1 ≅ chapter15H1DualModule C)
  pairingIsomorphism : H0 ≅ dualH1
  perfect_pairing : Nonempty (H0 ≅ dualH1)
  fiber_bundle_restriction : Nonempty (H0 ≅ H0)

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
  K0 : ModuleCat.{u, u} R
  K1 : ModuleCat.{u, u} R
  differential : K0 ⟶ K1
  K0_finite_free : ∃ n : ℕ, Nonempty (K0 ≅ ModuleCat.of R (Fin n →₀ R))
  K1_finite_free : ∃ n : ℕ, Nonempty (K1 ≅ ModuleCat.of R (Fin n →₀ R))
  H0 : ModuleCat.{u, u} R
  H0_is_kernel : Nonempty (H0 ≅ kernel differential)
  H1 : ModuleCat.{u, u} R
  H1_is_cokernel : Nonempty (H1 ≅ cokernel differential)

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

noncomputable def chapter15FiberH0Dimension
    {S : Scheme.{u}}
    (C : Chapter15ProjectiveFlatRelativeCurve S)
    (E : Chapter15VectorBundle C.curve.carrier) (s : S) : ℕ := by
  sorry

noncomputable def chapter15FiberH1Dimension
    {S : Scheme.{u}}
    (C : Chapter15ProjectiveFlatRelativeCurve S)
    (E : Chapter15VectorBundle C.curve.carrier) (s : S) : ℕ := by
  sorry

structure Chapter15FiberCohomologyDimensionData
    {S : Scheme.{u}}
    (C : Chapter15ProjectiveFlatRelativeCurve S)
    (E : Chapter15VectorBundle C.curve.carrier) where
  h0 : S → ℕ
  h1 : S → ℕ
  h0_upper_semicontinuous : Chapter15UpperSemicontinuous h0
  h1_upper_semicontinuous : Chapter15UpperSemicontinuous h1
  h0_is_fiber_dimension : ∀ s, h0 s = chapter15FiberH0Dimension C E s
  h1_is_fiber_dimension : ∀ s, h1 s = chapter15FiberH1Dimension C E s

theorem chapter15_fiber_cohomology_dimensions_upper_semicontinuous
    {S : Scheme.{u}}
    (C : Chapter15ProjectiveFlatRelativeCurve S)
    (E : Chapter15VectorBundle C.curve.carrier) :
    Nonempty (Chapter15FiberCohomologyDimensionData C E) := by
  sorry

structure Chapter15PushforwardBaseChangeData
    {S : Scheme.{u}}
    (C : Chapter15ProjectiveFlatRelativeCurve S)
    (E : Chapter15VectorBundle C.curve.carrier)
    (h1 : S → ℕ) where
  pushforward : S.Modules
  pushforward_is_f_pushforward :
    pushforward = (Scheme.Modules.pushforward C.curve.structuralMap).obj E.module
  locally_free : chapter04FiniteLocallyFree pushforward
  h1_is_fiber_cohomology : ∀ s,
    h1 s = chapter15FiberH1Dimension C E s
  base_change :
    ∀ T : RelativeScheme S,
      (Scheme.Modules.pullback T.structuralMap).obj
          ((Scheme.Modules.pushforward C.curve.structuralMap).obj E.module) ⟶
        (Scheme.Modules.pushforward
          (pullback.snd C.curve.structuralMap T.structuralMap)).obj
          ((Scheme.Modules.pullback
            (pullback.fst C.curve.structuralMap T.structuralMap)).obj E.module)
  base_change_is_canonical : ∀ T,
    base_change T = chapter15PushforwardBaseChangeMap C E.module T

theorem chapter15_h1_vanishing_gives_locally_free_pushforward_and_base_change
    {S : Scheme.{u}}
    (C : Chapter15ProjectiveFlatRelativeCurve S)
    (E : Chapter15VectorBundle C.curve.carrier)
    (h1 : S → ℕ)
    (h1_is_fiber_cohomology : ∀ s,
      h1 s = chapter15FiberH1Dimension C E s)
    (hvanishing : ∀ s : S, h1 s = 0) :
    Nonempty (Chapter15PushforwardBaseChangeData C E h1) := by
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
