import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter01.Section02TheTwoDimensionsInAnArithmeticSurface
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter02.Section02EffectiveCartierDivisors

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter01

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter02
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter13
open scoped AlgebraicGeometry BigOperators

universe u v

/-! ## 1.3. Standing conventions and a hypothesis ledger -/

theorem chapter01_base_generic_point_is_generic
    {K : Type u} [Field K]
    (B : Chapter01ExcellentConnectedDedekindBaseData K) :
    IsGenericPoint (chapter01GenericPoint B) Set.univ :=
  B.genericPoint.eta_is_generic

theorem chapter01_base_generic_point_has_function_field_presentation
    {K : Type u} [Field K]
    (B : Chapter01ExcellentConnectedDedekindBaseData K) :
    CommRingCat.of K ≅ B.carrier.residueField (chapter01GenericPoint B) :=
  B.genericPoint.residueFieldIso

theorem chapter01_regular_arithmetic_surface_has_absolute_dimension_two
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    (X : Chapter01RegularArithmeticSurface B) :
    Chapter13AbsoluteDimensionTwo X.carrier :=
  X.absoluteDimensionTwo

theorem chapter01_regular_arithmetic_surface_has_relative_dimension_one
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    (X : Chapter01RegularArithmeticSurface B) :
    Chapter13RelativeDimensionOne X.structureMap :=
  X.relativeDimensionOne

theorem chapter01_generic_fiber_is_smooth_and_geometrically_connected
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    (G : Chapter01GenericFiberProperties X) :
    Smooth (pullback.snd X.structureMap (chapter01GenericPointMap B)) ∧
      Chapter13GeometricallyConnected (chapter01GenericFiber X) :=
  ⟨G.smooth, G.geometricallyConnected⟩

/- LOCAL_DEPENDENCY_GUESS: the codimension-one dichotomy is the Book 9
horizontal/vertical prime-divisor theorem specialized to the present regular
arithmetic-surface package. -/
theorem chapter01_curve_is_horizontal_or_vertical
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    (C : Chapter01Curve X.carrier) :
    chapter01CurveIsHorizontal C ∨ chapter01CurveIsVertical C := by
  sorry

/-! ### Local replacement by a discrete valuation ring -/

abbrev chapter01LocalBaseRing
    {K : Type u} [Field K]
    (B : Chapter01ExcellentConnectedDedekindBaseData K)
    (s : B.carrier) :=
  B.carrier.presheaf.stalk s

abbrev chapter01LocalBaseScheme
    {K : Type u} [Field K]
    (B : Chapter01ExcellentConnectedDedekindBaseData K)
    (s : B.carrier) : Scheme.{u} :=
  AlgebraicGeometry.Spec (CommRingCat.of (chapter01LocalBaseRing B s))

def chapter01LocalDVRAt
    {K : Type u} [Field K]
    (B : Chapter01ExcellentConnectedDedekindBaseData K)
    (s : B.carrier) : Prop :=
  IsLocalRing (chapter01LocalBaseRing B s) ∧
    IsDiscreteValuationRing (chapter01LocalBaseRing B s)

structure Chapter01LocalDVRData
    {K : Type u} [Field K]
    (B : Chapter01ExcellentConnectedDedekindBaseData K)
    (s : B.carrier)
    [IsLocalRing (chapter01LocalBaseRing B s)]
    [IsDiscreteValuationRing (chapter01LocalBaseRing B s)] where
  uniformizer : chapter01LocalBaseRing B s
  uniformizer_span :
    Ideal.span ({uniformizer} : Set (chapter01LocalBaseRing B s)) =
      maximalIdeal (chapter01LocalBaseRing B s)

/- LOCAL_DEPENDENCY_GUESS: the stalk of a Dedekind scheme at a closed point
is the local DVR used by the source. -/
theorem chapter01_closed_point_local_ring_is_dvr
    {K : Type u} [Field K]
    (B : Chapter01ExcellentConnectedDedekindBaseData K)
    (s : B.carrier) (hs : IsClosed ({s} : Set B.carrier)) :
    chapter01LocalDVRAt B s := by
  sorry

/-! ### Regularity and the Cartier--Weil dictionary -/

instance chapter01_regular_surface_is_chapter03Regular
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    (X : Chapter01RegularArithmeticSurface B) :
    Chapter03Regular X.carrier where
  regular_stalk := fun x => X.regular.regular_at x

/- LOCAL_DEPENDENCY_GUESS: normality of a noetherian integral regular surface
is the standard regular-implies-normal bridge, kept as a theorem because the
book-facing Chapter 3 normality class is not a Mathlib instance. -/
theorem chapter01_regular_surface_is_normal
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    (X : Chapter01RegularArithmeticSurface B) :
    Chapter03Normal X.carrier := by
  sorry

instance chapter01_regular_surface_is_chapter03Normal
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    (X : Chapter01RegularArithmeticSurface B) :
    Chapter03Normal X.carrier :=
  chapter01_regular_surface_is_normal X

theorem chapter01_regular_surface_weil_divisor_is_cartier
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    [Chapter03CartierDivisorTheory X.carrier]
    (D : Chapter01Divisor X.carrier) :
    ∃ C : Chapter03CartierDivisor X.carrier,
      chapter03CartierDivisorToWeil X.carrier C = D := by
  letI : Chapter03Normal X.carrier := chapter01_regular_surface_is_normal X
  rcases chapter03_regular_relative_totalSpace_all_prime_divisors_cartier
      X.structureMap D with ⟨C, hC⟩
  exact ⟨C, hC⟩

/-! ### Flat fibers and the special-fiber decomposition -/

structure Chapter01FiberCartierData
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    (X : Chapter01RegularArithmeticSurface B)
    (s : B.carrier) where
  ideal : X.carrier.IdealSheafData
  support_eq_fiber :
    (ideal.support : Set X.carrier) = X.structureMap ⁻¹' ({s} : Set B.carrier)
  effective_cartier : Chapter02IsEffectiveCartierIdeal ideal

/- LOCAL_DEPENDENCY_GUESS: flatness over the Dedekind base supplies the
effective Cartier ideal of a scheme-theoretic fiber. -/
theorem chapter01_flat_surface_fiber_is_effective_cartier
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    (s : B.carrier) :
    Nonempty (Chapter01FiberCartierData X s) := by
  sorry

structure Chapter01SpecialFiberData
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    (X : Chapter01RegularArithmeticSurface B)
    (s : B.carrier) where
  base_closed : IsClosed ({s} : Set B.carrier)
  index : Type u
  [finiteIndex : Fintype index]
  component : index → Chapter01Curve X.carrier
  component_vertical : ∀ i, chapter01CurveIsVertical (component i)
  multiplicity : index → ℕ
  multiplicity_pos : ∀ i, 0 < multiplicity i
  fiberDivisor : Chapter01Divisor X.carrier
  fiber_eq_sum :
    fiberDivisor = ∑ i, (multiplicity i : ℤ) • Finsupp.single (component i) 1
  principalFunction : X.carrier.functionField
  principalFunction_ne_zero : principalFunction ≠ 0
  principalFunction_is_uniformizer_pullback : Prop
  principalDivisor_eq_fiber :
    chapter03PrincipalWeilDivisor principalFunction = fiberDivisor
  associatedLineBundle : Chapter01LineBundle X.carrier
  associatedLineBundle_trivial :
    chapter04LineBundleIsomorphic associatedLineBundle
      (chapter04TrivialLineBundle X.carrier)
  associatedLineBundle_represents_fiber : Prop
  intersectionContext : Chapter01NumericalIntersectionContext X

attribute [instance] Chapter01SpecialFiberData.finiteIndex

def chapter01SpecialFiberComponentDivisor
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    {s : B.carrier}
    (F : Chapter01SpecialFiberData X s) (i : F.index) : Chapter01Divisor X.carrier :=
  Finsupp.single (F.component i) 1

theorem chapter01_special_fiber_decomposition
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    {s : B.carrier}
    (F : Chapter01SpecialFiberData X s) :
    F.fiberDivisor =
      ∑ i, (F.multiplicity i : ℤ) • chapter01SpecialFiberComponentDivisor F i := by
  exact F.fiber_eq_sum

/- LOCAL_DEPENDENCY_GUESS: the normalized local uniformizer divisor and the
component decomposition are supplied by the Cartier divisor/fiber package. -/
theorem chapter01_special_fiber_data_exists
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    (s : B.carrier)
    (hs : IsClosed ({s} : Set B.carrier)) :
    Nonempty (Chapter01SpecialFiberData X s) := by
  sorry

theorem chapter01_special_fiber_intersects_each_vertical_component_zero
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    {s : B.carrier}
    (F : Chapter01SpecialFiberData X s) (i : F.index) :
    F.intersectionContext.pairing F.fiberDivisor
        (Finsupp.single (F.component i) 1) = 0 := by
  sorry

/-! ### Sections and the boundary contribution -/

structure Chapter01HorizontalSection
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    (X : Chapter01RegularArithmeticSurface B) where
  curve : Chapter01Curve X.carrier
  sectionMap : B.carrier ⟶ curve.closedSubscheme.subscheme
  section_over :
    sectionMap ≫ curve.closedSubscheme.subschemeι ≫ X.structureMap =
      𝟙 B.carrier
  horizontal : chapter01CurveIsHorizontal curve

def chapter01HorizontalSectionDivisor
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    (σ : Chapter01HorizontalSection X) : Chapter01Divisor X.carrier :=
  Finsupp.single σ.curve 1

theorem chapter01_horizontal_section_intersects_special_fiber_once
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    {s : B.carrier}
    (F : Chapter01SpecialFiberData X s)
    (σ : Chapter01HorizontalSection X) :
    F.intersectionContext.pairing F.fiberDivisor
        (chapter01HorizontalSectionDivisor σ) = 1 := by
  sorry

theorem chapter01_principal_fiber_has_trivial_associated_line_bundle
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    {s : B.carrier}
    (F : Chapter01SpecialFiberData X s) :
    chapter04LineBundleIsomorphic F.associatedLineBundle
      (chapter04TrivialLineBundle X.carrier) :=
  F.associatedLineBundle_trivial

/-! ### The quotient convention for projective bundles -/

abbrev Chapter01QuasiCoherentModule (Z : Scheme.{u}) := Chapter02QuasiCoherentModule Z

abbrev Chapter01ProjectiveBundleData (Z : Scheme.{u})
    (E : Chapter01QuasiCoherentModule Z) := Chapter02ProjectiveBundleData Z E

noncomputable def chapter01ProjectiveBundle
    (Z : Scheme.{u}) (E : Chapter01QuasiCoherentModule Z) : Scheme.{u} :=
  (chapter02ProjectiveBundleData Z E).scheme

noncomputable def chapter01ProjectiveBundleProjection
    (Z : Scheme.{u}) (E : Chapter01QuasiCoherentModule Z) :
    chapter01ProjectiveBundle Z E ⟶ Z :=
  (chapter02ProjectiveBundleData Z E).projection

theorem chapter01_projective_bundle_classifies_invertible_quotients
    (Z : Scheme.{u}) (E : Chapter01QuasiCoherentModule Z)
    {T : Scheme.{u}} (f : T ⟶ Z) :
    {u : T ⟶ chapter01ProjectiveBundle Z E //
        u ≫ chapter01ProjectiveBundleProjection Z E = f} ≃
      Chapter02InvertibleQuotientClass
        ((Scheme.Modules.pullback f).obj E.carrier) := by
  exact (chapter02ProjectiveBundleData Z E).universalProperty f

/- LOCAL_DEPENDENCY_GUESS: the pinned module-sheaf API does not expose the
dual of an arbitrary finite locally free module sheaf as a bundled object. -/
structure Chapter01DualModuleData
    (Z : Scheme.{u}) (N : Chapter01QuasiCoherentModule Z) where
  dual : Chapter01QuasiCoherentModule Z
  dual_is_dual : Prop

structure Chapter01NormalDirectionsData
    (Z : Scheme.{u}) (N : Chapter01QuasiCoherentModule Z)
    (D : Chapter01DualModuleData Z N) where
  projectivization : Chapter01ProjectiveBundleData Z D.dual

abbrev chapter01ProjectivizedNormalDirections
    (Z : Scheme.{u}) (N : Chapter01QuasiCoherentModule Z)
    (D : Chapter01DualModuleData Z N) : Scheme.{u} :=
  (D.projectivization).scheme

theorem chapter01_normal_directions_use_the_dual_bundle
    (Z : Scheme.{u}) (N : Chapter01QuasiCoherentModule Z)
    (D : Chapter01DualModuleData Z N)
    (P : Chapter01NormalDirectionsData Z N D) :
    chapter01ProjectivizedNormalDirections Z N D = P.projectivization.scheme := by
  rfl

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter01
