import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Flat.TorsionFree
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter02.Section02EffectiveCartierDivisors

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter02

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry nonZeroDivisors

universe u v

/-!
### 2.3 Pullback, restriction, and flatness
-/

/- LOCAL_DEPENDENCY_GUESS: the functorial map on the chosen total quotient
   sheaves.  It is partial because a morphism need not preserve the regular
   elements that must be inverted.  When defined, the map is a ring hom, and
   the restriction and unit-compatibility fields are the data needed to glue
   a pulled-back Cartier divisor. -/
class Chapter02MeromorphicPullbackMap {X Y : Scheme.{u}}
    [KX : Chapter02MeromorphicSheaf X] [KY : Chapter02MeromorphicSheaf Y]
    (g : Y ⟶ X) where
  map : ∀ (U : X.Opens) (V : Y.Opens), V ≤ g ⁻¹ᵁ U →
    Option (Chapter02MeromorphicSection X U →+* Chapter02MeromorphicSection Y V)
  map_source_restrict : ∀ (U U' : X.Opens) (V : Y.Opens)
    (hUU' : U' ≤ U) (hV' : V ≤ g ⁻¹ᵁ U') (hV : V ≤ g ⁻¹ᵁ U)
    (φ' : Chapter02MeromorphicSection X U' →+*
      Chapter02MeromorphicSection Y V)
    (φ : Chapter02MeromorphicSection X U →+*
      Chapter02MeromorphicSection Y V),
    map U' V hV' = some φ' → map U V hV = some φ →
    ∀ s : Chapter02MeromorphicSection X U,
      φ' (chapter02MeromorphicRestriction X hUU' s) = φ s
  map_target_restrict : ∀ (U : X.Opens) (V W : Y.Opens)
    (hV : V ≤ g ⁻¹ᵁ U) (hW : W ≤ V) (hW' : W ≤ g ⁻¹ᵁ U)
    (φ : Chapter02MeromorphicSection X U →+* Chapter02MeromorphicSection Y V)
    (φ' : Chapter02MeromorphicSection X U →+* Chapter02MeromorphicSection Y W),
    map U V hV = some φ → map U W hW' = some φ' →
    ∀ s : Chapter02MeromorphicSection X U,
      chapter02MeromorphicRestriction Y hW (φ s) = φ' s
  map_source_intersection : ∀ (U U' : X.Opens) (V : Y.Opens)
    (hV : V ≤ g ⁻¹ᵁ (U ⊓ U')) (hVU : V ≤ g ⁻¹ᵁ U)
    (hVU' : V ≤ g ⁻¹ᵁ U')
    (φ : Chapter02MeromorphicSection X U →+*
      Chapter02MeromorphicSection Y V)
    (φ' : Chapter02MeromorphicSection X U' →+*
      Chapter02MeromorphicSection Y V)
    (φij : Chapter02MeromorphicSection X (U ⊓ U') →+*
      Chapter02MeromorphicSection Y V),
    map U V hVU = some φ → map U' V hVU' = some φ' →
    map (U ⊓ U') V hV = some φij →
    (∀ s : Chapter02MeromorphicSection X U,
      φij (chapter02MeromorphicRestriction X inf_le_left s) = φ s) ∧
    (∀ s : Chapter02MeromorphicSection X U',
      φij (chapter02MeromorphicRestriction X inf_le_right s) = φ' s)
  map_structure : ∀ (U : X.Opens) (V : Y.Opens) (hV : V ≤ g ⁻¹ᵁ U)
    (φ : Chapter02MeromorphicSection X U →+*
      Chapter02MeromorphicSection Y V),
    map U V hV = some φ →
    ∀ f : Γ(X, U),
      φ (chapter02RegularSectionMap X U f) =
        chapter02RegularSectionMap Y V
          (chapter02StructureSheafPullbackMap g U V hV f)
  map_none_iff : ∀ (U : X.Opens) (V : Y.Opens) (hV : V ≤ g ⁻¹ᵁ U),
    map U V hV = none ↔
      ∃ f : Γ(X, U), f ∈ nonZeroDivisors (Γ(X, U)) ∧
        chapter02StructureSheafPullbackMap g U V hV f ∉
          nonZeroDivisors (Γ(Y, V))

/- Flatness on affine charts gives the ring-level regular-element statement,
   but the Cartier pullback API also needs maps on arbitrary opens.  This
   interface records that missing sheaf-level bridge explicitly. -/
class Chapter02FlatMeromorphicPullbackInterface {X Y : Scheme.{u}}
    [KX : Chapter02MeromorphicSheaf X] [KY : Chapter02MeromorphicSheaf Y]
    (g : Y ⟶ X) [Flat g] [M : Chapter02MeromorphicPullbackMap g] where
  map_exists : ∀ (U : X.Opens) (V : Y.Opens) (hV : V ≤ g ⁻¹ᵁ U),
    ∃ φ : Chapter02MeromorphicSection X U →+*
      Chapter02MeromorphicSection Y V,
      M.map U V hV = some φ
  preserves_regular : ∀ (U : X.Opens) (V : Y.Opens)
    (hV : V ≤ g ⁻¹ᵁ U)
    (φ : Chapter02MeromorphicSection X U →+*
      Chapter02MeromorphicSection Y V),
    M.map U V hV = some φ →
    ∀ f : Γ(X, U), f ∈ nonZeroDivisors (Γ(X, U)) →
      chapter02StructureSheafPullbackMap g U V hV f ∈
        nonZeroDivisors (Γ(Y, V))

private theorem chapter02_flat_ring_hom_preserves_regular_aux
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] (φ : R →+* S) (r : R)
    (hr : r ∈ nonZeroDivisors R) (hcompat : algebraMap R S = φ) :
    φ r ∈ nonZeroDivisors S := by
  rw [chapter02_regular_element_iff_injective_multiplication S (φ r)]
  have hsmul : IsSMulRegular S r :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors hr
  intro x y hxy
  apply hsmul
  simpa [Algebra.smul_def, hcompat] using hxy

theorem chapter02_flat_ring_hom_preserves_regular
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : φ.Flat) (r : R)
    (hr : r ∈ nonZeroDivisors R) : φ r ∈ nonZeroDivisors S := by
  exact @chapter02_flat_ring_hom_preserves_regular_aux R S _ _ φ.toAlgebra hφ φ r hr
    (RingHom.algebraMap_toAlgebra φ)

def chapter02MeromorphicSectionIsAdmissible {X Y : Scheme.{u}}
    [KX : Chapter02MeromorphicSheaf X] [KY : Chapter02MeromorphicSheaf Y]
    (g : Y ⟶ X) [M : Chapter02MeromorphicPullbackMap g]
    (U : X.Opens) (V : Y.Opens) (hV : V ≤ g ⁻¹ᵁ U)
    (s : Chapter02MeromorphicSection X U) : Prop :=
    ∃ φ : Chapter02MeromorphicSection X U →+*
        Chapter02MeromorphicSection Y V,
      M.map U V hV = some φ ∧
      IsUnit (φ s) ∧
      ∀ (W : Y.Opens) (hW : W ≤ V) (hW' : W ≤ g ⁻¹ᵁ U),
        ∃ φW : Chapter02MeromorphicSection X U →+*
            Chapter02MeromorphicSection Y W,
          M.map U W hW' = some φW ∧
            ∀ t : Chapter02MeromorphicSection X U,
              chapter02MeromorphicRestriction Y hW (φ t) = φW t

def chapter02PullbackSourceIntersectionCompatible {X Y : Scheme.{u}}
    [KX : Chapter02MeromorphicSheaf X] [KY : Chapter02MeromorphicSheaf Y]
    (g : Y ⟶ X) [M : Chapter02MeromorphicPullbackMap g]
    (D : Chapter02CartierDivisor X) : Prop :=
  ∀ (i j : D.index) (V : Y.Opens)
    (hVi : V ≤ g ⁻¹ᵁ D.openSet i)
    (hVj : V ≤ g ⁻¹ᵁ D.openSet j)
    (hVij : V ≤ g ⁻¹ᵁ (D.openSet i ⊓ D.openSet j)),
    ∃ (φi : Chapter02MeromorphicSection X (D.openSet i) →+*
        Chapter02MeromorphicSection Y V)
      (φj : Chapter02MeromorphicSection X (D.openSet j) →+*
        Chapter02MeromorphicSection Y V)
      (φij : Chapter02MeromorphicSection X (D.openSet i ⊓ D.openSet j) →+*
        Chapter02MeromorphicSection Y V),
      M.map (D.openSet i) V hVi = some φi ∧
        M.map (D.openSet j) V hVj = some φj ∧
        M.map (D.openSet i ⊓ D.openSet j) V hVij = some φij ∧
        (∀ s : Chapter02MeromorphicSection X (D.openSet i),
          φij (chapter02MeromorphicRestriction X inf_le_left s) = φi s) ∧
        (∀ s : Chapter02MeromorphicSection X (D.openSet j),
          φij (chapter02MeromorphicRestriction X inf_le_right s) = φj s)

def chapter02PullbackEquationAdmissible {X Y : Scheme.{u}}
    [KX : Chapter02MeromorphicSheaf X] [KY : Chapter02MeromorphicSheaf Y]
    (g : Y ⟶ X) [M : Chapter02MeromorphicPullbackMap g]
    (D : Chapter02CartierDivisor X) : Prop :=
  (∀ (i : D.index) (V : Y.Opens) (hV : V ≤ g ⁻¹ᵁ D.openSet i),
    chapter02MeromorphicSectionIsAdmissible g (D.openSet i) V hV (D.equation i)) ∧
    chapter02PullbackSourceIntersectionCompatible g D

def chapter02EffectivePullbackEquationRegular {X Y : Scheme.{u}}
    [KX : Chapter02MeromorphicSheaf X] [KY : Chapter02MeromorphicSheaf Y]
    (g : Y ⟶ X) [M : Chapter02MeromorphicPullbackMap g]
    (D : Chapter02EffectiveCartierDivisor X) : Prop :=
  ∀ (i : D.divisor.index) (V : Y.Opens)
    (hV : V ≤ g ⁻¹ᵁ D.divisor.openSet i) (y : Y), y ∈ V →
    ∃ (W : Y.Opens) (_hyW : y ∈ W) (hWV : W ≤ V)
      (φ : Chapter02MeromorphicSection X (D.divisor.openSet i) →+*
        Chapter02MeromorphicSection Y W),
      M.map (D.divisor.openSet i) W (hWV.trans hV) = some φ ∧
        chapter02MeromorphicSectionIsRegular Y W
          (φ (D.divisor.equation i))

def chapter02CartierPullbackRepresents {X Y : Scheme.{u}}
    [KX : Chapter02MeromorphicSheaf X] [KY : Chapter02MeromorphicSheaf Y]
    (g : Y ⟶ X) [M : Chapter02MeromorphicPullbackMap g]
    (D : Chapter02CartierDivisor X) (E : Chapter02CartierDivisor Y) : Prop :=
  ∀ (j : E.index),
    ∃ (i : D.index) (h : E.openSet j ≤ g ⁻¹ᵁ D.openSet i)
      (φ : Chapter02MeromorphicSection X (D.openSet i) →+*
        Chapter02MeromorphicSection Y (E.openSet j)),
      M.map (D.openSet i) (E.openSet j) h = some φ ∧
      (E.equation j : Chapter02MeromorphicSection Y (E.openSet j)) =
        φ (D.equation i : Chapter02MeromorphicSection X (D.openSet i))

structure Chapter02CartierPullbackData {X Y : Scheme.{u}}
    [KX : Chapter02MeromorphicSheaf X] [KY : Chapter02MeromorphicSheaf Y]
    (g : Y ⟶ X) [M : Chapter02MeromorphicPullbackMap g]
    (D : Chapter02CartierDivisor.{u, v} X) where
  divisor : Chapter02CartierDivisor.{u, v} Y
  represents : chapter02CartierPullbackRepresents g D divisor
  equations_are_admissible : chapter02PullbackEquationAdmissible g D

theorem chapter02_cartier_pullback_exists_iff {X Y : Scheme.{u}}
    [KX : Chapter02MeromorphicSheaf X] [KY : Chapter02MeromorphicSheaf Y]
    (g : Y ⟶ X) [M : Chapter02MeromorphicPullbackMap g]
    (D : Chapter02CartierDivisor X) :
    Nonempty (Chapter02CartierPullbackData g D) ↔
      chapter02PullbackEquationAdmissible g D := by
  sorry

theorem chapter02_pullback_equations_admissible_of_flat {X Y : Scheme.{u}}
    [KX : Chapter02MeromorphicSheaf X] [KY : Chapter02MeromorphicSheaf Y]
    (g : Y ⟶ X) [Flat g] [M : Chapter02MeromorphicPullbackMap g]
    [F : Chapter02FlatMeromorphicPullbackInterface g]
    (D : Chapter02CartierDivisor X) :
    chapter02PullbackEquationAdmissible g D := by
  sorry

theorem chapter02_cartier_pullback_exists_of_flat {X Y : Scheme.{u}}
    [KX : Chapter02MeromorphicSheaf X] [KY : Chapter02MeromorphicSheaf Y]
    (g : Y ⟶ X) [Flat g] [M : Chapter02MeromorphicPullbackMap g]
    [F : Chapter02FlatMeromorphicPullbackInterface g]
    (D : Chapter02CartierDivisor X) :
    Nonempty (Chapter02CartierPullbackData g D) := by
  apply (chapter02_cartier_pullback_exists_iff g D).2
  exact chapter02_pullback_equations_admissible_of_flat g D

theorem chapter02_cartier_restriction_to_open_exists {X : Scheme.{u}}
    [KX : Chapter02MeromorphicSheaf X] {U : X.Opens}
    [KU : Chapter02MeromorphicSheaf U] [M : Chapter02MeromorphicPullbackMap U.ι]
    [F : Chapter02FlatMeromorphicPullbackInterface U.ι]
    (D : Chapter02CartierDivisor X) :
    Nonempty (Chapter02CartierPullbackData U.ι D) := by
  exact chapter02_cartier_pullback_exists_of_flat U.ι D

def Chapter02MapFactorsThroughSupport {X Y : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X]
    (g : Y ⟶ X) (D : Chapter02EffectiveCartierDivisor X) : Prop :=
  ∃ h : Y ⟶ D.subscheme, h ≫ D.inclusion = g

theorem chapter02_pullback_map_none_of_factors_through_support {X Y : Scheme.{u}}
    [KX : Chapter02MeromorphicSheaf X] [KY : Chapter02MeromorphicSheaf Y]
    (g : Y ⟶ X) [M : Chapter02MeromorphicPullbackMap g] [Nonempty Y]
    (D : Chapter02EffectiveCartierDivisor X)
    (h : Chapter02MapFactorsThroughSupport g D) :
    ∃ (i : D.divisor.index) (V : Y.Opens)
      (hV : V ≤ g ⁻¹ᵁ D.divisor.openSet i)
      (f : Γ(X, D.divisor.openSet i)),
      f ∈ nonZeroDivisors (Γ(X, D.divisor.openSet i)) ∧
        chapter02StructureSheafPullbackMap g (D.divisor.openSet i) V hV f = 0 ∧
          M.map (D.divisor.openSet i) V hV = none := by
  sorry

theorem chapter02_pullback_can_fail_on_support {X Y : Scheme.{u}}
    [KX : Chapter02MeromorphicSheaf X] [KY : Chapter02MeromorphicSheaf Y]
    (g : Y ⟶ X) [M : Chapter02MeromorphicPullbackMap g] [Nonempty Y]
    (D : Chapter02EffectiveCartierDivisor X)
    (h : Chapter02MapFactorsThroughSupport g D) :
    ¬ chapter02PullbackEquationAdmissible g D.divisor := by
  sorry

def chapter02EffectiveCartierPullbackIdeal {X Y : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X]
    (g : Y ⟶ X) (D : Chapter02EffectiveCartierDivisor X) :
    Y.IdealSheafData :=
  D.ideal.comap g

def chapter02EffectiveCartierPullbackSubschemeIso {X Y : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X]
    (g : Y ⟶ X) (D : Chapter02EffectiveCartierDivisor X) :
    (chapter02EffectiveCartierPullbackIdeal g D).subscheme ≅
      pullback g D.inclusion :=
  D.ideal.comapIso g

theorem chapter02_effective_pullback_ideal_is_effective {X Y : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X]
    (g : Y ⟶ X) [Flat g] (D : Chapter02EffectiveCartierDivisor X) :
    Chapter02IsEffectiveCartierIdeal (chapter02EffectiveCartierPullbackIdeal g D) := by
  sorry

theorem chapter02_effective_pullback_equations_regular_of_flat {X Y : Scheme.{u}}
    [KX : Chapter02MeromorphicSheaf X] [KY : Chapter02MeromorphicSheaf Y]
    (g : Y ⟶ X) [Flat g] [M : Chapter02MeromorphicPullbackMap g]
    [F : Chapter02FlatMeromorphicPullbackInterface g]
    (D : Chapter02EffectiveCartierDivisor X) :
    chapter02EffectivePullbackEquationRegular g D := by
  sorry

theorem chapter02_effective_pullback_exact_sequence {X Y : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X]
    (g : Y ⟶ X) [Flat g] (D : Chapter02EffectiveCartierDivisor X) :
    Nonempty (Chapter02CartierExactSequence
      (chapter02EffectiveCartierPullbackIdeal g D)) := by
  exact chapter02_effective_cartier_exact_sequence_of_ideal _
    (chapter02_effective_pullback_ideal_is_effective g D)

theorem chapter02_effective_pullback_is_base_change {X Y : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X]
    (g : Y ⟶ X) (D : Chapter02EffectiveCartierDivisor X) :
    (chapter02EffectiveCartierPullbackSubschemeIso g D).inv ≫
        (chapter02EffectiveCartierPullbackIdeal g D).subschemeι =
      pullback.fst g D.inclusion := by
  exact D.ideal.comapIso_inv_subschemeι g

theorem chapter02_effective_pullback_is_closed_immersion {X Y : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X]
    (g : Y ⟶ X) (D : Chapter02EffectiveCartierDivisor X) :
    IsClosedImmersion (pullback.fst g D.inclusion) := by
  infer_instance

structure Chapter02RelativeEffectiveCartierDivisor {X S : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X] (f : X ⟶ S) where
  divisor : Chapter02EffectiveCartierDivisor.{u, v} X
  flat_over_base : Flat (divisor.inclusion ≫ f)

def chapter02RelativeFiberIdeal {X S : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X]
    {f : X ⟶ S} (D : Chapter02RelativeEffectiveCartierDivisor f) (s : S) :
    (f.fiber s).IdealSheafData :=
  D.divisor.ideal.comap (f.fiberι s)

def chapter02RelativeFiberSubschemeIso {X S : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X]
    {f : X ⟶ S} (D : Chapter02RelativeEffectiveCartierDivisor f) (s : S) :
    (chapter02RelativeFiberIdeal D s).subscheme ≅
      pullback (f.fiberι s) D.divisor.inclusion :=
  D.divisor.ideal.comapIso (f.fiberι s)

theorem chapter02_relative_fiber_is_effective_cartier {X S : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X]
    {f : X ⟶ S} (D : Chapter02RelativeEffectiveCartierDivisor f) (s : S) :
    Chapter02IsEffectiveCartierIdeal (chapter02RelativeFiberIdeal D s) := by
  sorry

theorem chapter02_relative_fiber_exact_sequence {X S : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X]
    {f : X ⟶ S} (D : Chapter02RelativeEffectiveCartierDivisor f) (s : S) :
    Nonempty (Chapter02CartierExactSequence (chapter02RelativeFiberIdeal D s)) := by
  exact chapter02_effective_cartier_exact_sequence_of_ideal _
    (chapter02_relative_fiber_is_effective_cartier D s)

/- The parameter-divisor warning is recorded by the elementary family
   `k[t] -> k[t]/(t)`: the parameter is regular upstairs and zero downstairs. -/

abbrev Chapter02BaseParameterRing (k : Type u) [CommRing k] := Polynomial k

abbrev Chapter02BaseSpecialFiberRing (k : Type u) [CommRing k] :=
  Chapter02BaseParameterRing k ⧸
    Ideal.span ({Polynomial.X} : Set (Chapter02BaseParameterRing k))

def chapter02BaseParameter (k : Type u) [CommRing k] : Chapter02BaseParameterRing k :=
  Polynomial.X

def chapter02BaseParameterSpecialization (k : Type u) [CommRing k] :
    Chapter02BaseParameterRing k →+* Chapter02BaseSpecialFiberRing k :=
  Ideal.Quotient.mk _

theorem chapter02_base_parameter_is_regular (k : Type u) [Nontrivial k] [CommRing k] :
    chapter02BaseParameter k ∈ nonZeroDivisors (Chapter02BaseParameterRing k) := by
  exact Polynomial.monic_X.mem_nonZeroDivisors

theorem chapter02_base_parameter_restricts_to_zero (k : Type u) [CommRing k] :
    chapter02BaseParameterSpecialization k (chapter02BaseParameter k) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.2
  exact Ideal.subset_span (by simp [chapter02BaseParameter])

theorem chapter02_base_parameter_is_not_regular_on_special_fiber
    (k : Type u) [Field k] :
    chapter02BaseParameterSpecialization k (chapter02BaseParameter k) ∉
      nonZeroDivisors (Chapter02BaseSpecialFiberRing k) := by
  have hnontrivial : Nontrivial (Chapter02BaseSpecialFiberRing k) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (Ideal.span_singleton_ne_top Polynomial.not_isUnit_X)
  rw [chapter02_base_parameter_restricts_to_zero]
  exact @zero_notMem_nonZeroDivisors _ _ hnontrivial

theorem chapter02_base_parameter_fiber_warning (k : Type u) [Field k] :
    chapter02BaseParameter k ∈ nonZeroDivisors (Chapter02BaseParameterRing k) ∧
      chapter02BaseParameterSpecialization k (chapter02BaseParameter k) = 0 ∧
      chapter02BaseParameterSpecialization k (chapter02BaseParameter k) ∉
        nonZeroDivisors (Chapter02BaseSpecialFiberRing k) := by
  exact ⟨chapter02_base_parameter_is_regular k,
    chapter02_base_parameter_restricts_to_zero k,
    chapter02_base_parameter_is_not_regular_on_special_fiber k⟩

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter02
