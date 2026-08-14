import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03.Section02FromCartierToWeil

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open scoped AlgebraicGeometry BigOperators

noncomputable section

universe u

/-! ## 3.3. Normal curves and regular models -/

/-- On a noetherian integral one-dimensional scheme, normality and regularity agree. -/
theorem chapter03_normal_iff_regular_integral_noetherian_curve
    {X : Scheme.{u}} [Chapter03IntegralNoetherianCurve X] :
    Chapter03Normal X ↔ Chapter03Regular X := by
  sorry

/-- A normal integral curve has the Cartier--Weil divisor dictionary. -/
noncomputable def chapter03_normal_integral_curve_cartierWeilEquiv
    {X : Scheme.{u}} [Chapter03IntegralNoetherianCurve X]
    [Chapter03Normal X] [Chapter03CartierDivisorTheory X] :
    Chapter03CartierDivisor X ≃ Chapter03WeilDivisor X := by
  letI : Chapter03Regular X :=
    (chapter03_normal_iff_regular_integral_noetherian_curve (X := X)).mp inferInstance
  exact chapter03CartierWeilEquiv

/-- A smooth morphism from a curve over a field has regular total space. -/
theorem chapter03_smooth_curve_is_regular
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] :
    Chapter03Regular X := by
  sorry

/-- Smoothness is a sufficient, but stronger, hypothesis for the divisor dictionary. -/
theorem chapter03_smooth_curve_cartierWeilEquiv
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f]
    [Chapter03IntegralNoetherianCurve X]
    [Chapter03CartierDivisorTheory X] :
    Nonempty (Chapter03CartierDivisor X ≃ Chapter03WeilDivisor X) := by
  letI : Chapter03Regular X := chapter03_smooth_curve_is_regular f
  letI : Chapter03Normal X :=
    (chapter03_normal_iff_regular_integral_noetherian_curve (X := X)).mpr inferInstance
  exact ⟨chapter03CartierWeilEquiv⟩

/-- Regularity of a relative total space is enough for all codimension-one cycles to be Cartier. -/
theorem chapter03_regular_relative_totalSpace_all_prime_divisors_cartier
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsIntegral X] [IsNoetherian X] [Chapter03Normal X] [Chapter03Regular X]
    [Chapter03CartierDivisorTheory X] :
    Function.Surjective (chapter03CartierDivisorToWeil X) := by
  exact chapter03_regular_noetherian_integral_cartier_to_weil_surjective (X := X)

/-- The scheme underlying a prime divisor and its canonical closed immersion. -/
noncomputable def chapter03PrimeDivisorClosure
    {X : Scheme.{u}} (P : Chapter03PrimeDivisor X) : Scheme :=
  P.closedSubscheme.subscheme

noncomputable def chapter03PrimeDivisorClosureMap
    {X : Scheme.{u}} (P : Chapter03PrimeDivisor X) :
    chapter03PrimeDivisorClosure P ⟶ X :=
  P.closedSubscheme.subschemeι

theorem chapter03_primeDivisorClosureMap_isClosedImmersion
    {X : Scheme.{u}} (P : Chapter03PrimeDivisor X) :
    IsClosedImmersion (chapter03PrimeDivisorClosureMap P) := by
  exact chapter03_primeDivisor_isClosedImmersion P

/-- A prime divisor is horizontal when its generic point maps to the generic point of the base. -/
def chapter03HorizontalPrime
    {X S : Scheme.{u}} [IsIntegral S] (f : X ⟶ S)
    (P : Chapter03PrimeDivisor X) : Prop :=
  f.base P.genericPoint = genericPoint S

/-- A prime divisor is vertical when its support lies in one closed fiber. -/
def chapter03VerticalPrime
    {X S : Scheme.{u}} [IsIntegral S] (f : X ⟶ S)
    (P : Chapter03PrimeDivisor X) : Prop :=
  ∃ s : S, s ≠ genericPoint S ∧ P.support ⊆ (f.base ⁻¹' ({s} : Set S))

/-- Every prime divisor on the relative surface is horizontal or vertical. -/
theorem chapter03_primeDivisor_horizontal_or_vertical
    {X S : Scheme.{u}} {f : X ⟶ S}
    [IsIntegral X] [IsNoetherian X] [Chapter03Normal X]
    [Chapter03DedekindBase S] [Chapter03RelativeCurveModel f]
    (P : Chapter03PrimeDivisor X) :
    chapter03HorizontalPrime f P ∨ chapter03VerticalPrime f P := by
  sorry

/-- The quasi-finiteness package used for horizontal closures. -/
def chapter03HorizontalPrimeQuasiFinite
    {X S : Scheme.{u}} {f : X ⟶ S}
    (P : Chapter03PrimeDivisor X) : Prop :=
  Chapter03QuasiFiniteMorphism
    (chapter03PrimeDivisorClosureMap P ≫ f)

/-- A horizontal closure is proper over the Dedekind base. -/
theorem chapter03_horizontal_prime_closure_isProper
    {X S : Scheme.{u}} {f : X ⟶ S}
    [IsIntegral X] [IsNoetherian X] [Chapter03Normal X]
    [Chapter03DedekindBase S] [Chapter03RelativeCurveModel f]
    (P : Chapter03PrimeDivisor X)
    (hP : chapter03HorizontalPrime f P) :
    IsProper (chapter03PrimeDivisorClosureMap P ≫ f) := by
  sorry

/-- A horizontal closure is quasi-finite over the base. -/
theorem chapter03_horizontal_prime_closure_isQuasiFinite
    {X S : Scheme.{u}} {f : X ⟶ S}
    [IsIntegral X] [IsNoetherian X] [Chapter03Normal X]
    [Chapter03DedekindBase S] [Chapter03RelativeCurveModel f]
    (P : Chapter03PrimeDivisor X)
    (hP : chapter03HorizontalPrime f P) :
    chapter03HorizontalPrimeQuasiFinite (f := f) P := by
  sorry

/-- Proper and quasi-finite morphisms are finite in the form used here. -/
theorem chapter03_proper_quasiFinite_isFinite
    {Y S : Scheme.{u}} (g : Y ⟶ S) (hproper : IsProper g)
    (hquasi : Chapter03QuasiFiniteMorphism g) : IsFinite g := by
  sorry

/-- The horizontal closure is finite over the Dedekind base. -/
theorem chapter03_horizontal_prime_closure_isFinite
    {X S : Scheme.{u}} {f : X ⟶ S}
    [IsIntegral X] [IsNoetherian X] [Chapter03Normal X]
    [Chapter03DedekindBase S] [Chapter03RelativeCurveModel f]
    (P : Chapter03PrimeDivisor X)
    (hP : chapter03HorizontalPrime f P) :
    IsFinite (chapter03PrimeDivisorClosureMap P ≫ f) := by
  apply chapter03_proper_quasiFinite_isFinite
  · exact chapter03_horizontal_prime_closure_isProper P hP
  · exact chapter03_horizontal_prime_closure_isQuasiFinite P hP

/-- Local coordinate algebras of a morphism are torsion-free over the base. -/
def chapter03CoordinateTorsionFreeOverBase
    {Y S : Scheme.{u}} (g : Y ⟶ S) : Prop :=
  ∀ (U : S.affineOpens) (V : Y.affineOpens)
    (h : V ≤ g ⁻¹ᵁ U),
    letI := (g.appLE U V h).hom.toAlgebra
    Module.IsTorsionFree (Γ(S, U)) (Γ(Y, V))

/-- The integral coordinate algebra of a horizontal closure is torsion-free over the base. -/
theorem chapter03_horizontal_prime_coordinate_algebra_torsionFree
    {X S : Scheme.{u}} {f : X ⟶ S}
    [IsIntegral X] [IsNoetherian X] [Chapter03Normal X]
    [Chapter03DedekindBase S] [Chapter03RelativeCurveModel f]
    (P : Chapter03PrimeDivisor X)
    (hP : chapter03HorizontalPrime f P) :
    chapter03CoordinateTorsionFreeOverBase
      (chapter03PrimeDivisorClosureMap P ≫ f) := by
  sorry

/-- Torsion-free finite algebras over a Dedekind base are flat. -/
theorem chapter03_torsionFree_finite_over_dedekind_isFlat
    {Y S : Scheme.{u}} [Chapter03DedekindBase S] (g : Y ⟶ S)
    (hfinite : IsFinite g) (htorsionFree : chapter03CoordinateTorsionFreeOverBase g) :
    Flat g := by
  sorry

/-- A horizontal closure is finite and flat over the base. -/
theorem chapter03_horizontal_prime_closure_isFlat
    {X S : Scheme.{u}} {f : X ⟶ S}
    [IsIntegral X] [IsNoetherian X] [Chapter03Normal X]
    [Chapter03DedekindBase S] [Chapter03RelativeCurveModel f]
    (P : Chapter03PrimeDivisor X)
    (hP : chapter03HorizontalPrime f P) :
    Flat (chapter03PrimeDivisorClosureMap P ≫ f) := by
  apply chapter03_torsionFree_finite_over_dedekind_isFlat
  · exact chapter03_horizontal_prime_closure_isFinite P hP
  · exact chapter03_horizontal_prime_coordinate_algebra_torsionFree P hP

/-- The rank of a finite-flat horizontal closure at a base point. -/
def chapter03HorizontalPrimeRank
    {X S : Scheme.{u}} {f : X ⟶ S}
    [IsIntegral X] [IsNoetherian X] [Chapter03Normal X]
    [Chapter03DedekindBase S] [Chapter03RelativeCurveModel f]
    (P : Chapter03PrimeDivisor X) (hP : chapter03HorizontalPrime f P) (s : S) : ℕ := by
  letI := chapter03_horizontal_prime_closure_isFinite P hP
  letI := chapter03_horizontal_prime_closure_isFlat P hP
  exact Scheme.Hom.finrank (chapter03PrimeDivisorClosureMap P ≫ f) s

/-- The degree of a horizontal prime is its generic-fiber rank. -/
def chapter03HorizontalPrimeDegree
    {X S : Scheme.{u}} {f : X ⟶ S}
    [IsIntegral X] [IsNoetherian X] [Chapter03Normal X]
    [Chapter03DedekindBase S] [Chapter03RelativeCurveModel f]
    (P : Chapter03PrimeDivisor X) (hP : chapter03HorizontalPrime f P) : ℕ :=
  chapter03HorizontalPrimeRank P hP (genericPoint S)

theorem chapter03_horizontal_prime_rank_at_genericPoint
    {X S : Scheme.{u}} {f : X ⟶ S}
    [IsIntegral X] [IsNoetherian X] [Chapter03Normal X]
    [Chapter03DedekindBase S] [Chapter03RelativeCurveModel f]
    (P : Chapter03PrimeDivisor X) (hP : chapter03HorizontalPrime f P) :
    chapter03HorizontalPrimeRank P hP (genericPoint S) =
      chapter03HorizontalPrimeDegree P hP := by
  rfl

theorem chapter03_horizontal_prime_rank_isLocallyConstant
    {X S : Scheme.{u}} {f : X ⟶ S}
    [IsIntegral X] [IsNoetherian X] [Chapter03Normal X]
    [Chapter03DedekindBase S] [Chapter03RelativeCurveModel f]
    (P : Chapter03PrimeDivisor X)
    (hP : chapter03HorizontalPrime f P) :
    IsLocallyConstant
      (Scheme.Hom.finrank (chapter03PrimeDivisorClosureMap P ≫ f)) := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the pinned tree has finite-flat fiber ranks but no
  intersection product for a horizontal closure and a fiber.  Keep that
  numerical compatibility as an explicit interface rather than identifying
  it definitionally with the rank. -/
class Chapter03HorizontalFiberIntersectionTheory
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsIntegral X] [IsNoetherian X] [Chapter03Normal X]
    [Chapter03DedekindBase S] [Chapter03RelativeCurveModel f] where
  fiberIntersection : Chapter03PrimeDivisor X → ℕ
  horizontal_eq_degree :
    ∀ (P : Chapter03PrimeDivisor X)
      (hP : chapter03HorizontalPrime f P),
      fiberIntersection P = chapter03HorizontalPrimeDegree P hP

def chapter03HorizontalFiberIntersectionNumber
    {X S : Scheme.{u}} {f : X ⟶ S}
    [IsIntegral X] [IsNoetherian X] [Chapter03Normal X]
    [Chapter03DedekindBase S] [Chapter03RelativeCurveModel f]
    [Chapter03HorizontalFiberIntersectionTheory f]
    (P : Chapter03PrimeDivisor X) : ℕ :=
  Chapter03HorizontalFiberIntersectionTheory.fiberIntersection (f := f) P

theorem chapter03_horizontal_degree_eq_fiberIntersection
    {X S : Scheme.{u}} {f : X ⟶ S}
    [IsIntegral X] [IsNoetherian X] [Chapter03Normal X]
    [Chapter03DedekindBase S] [Chapter03RelativeCurveModel f]
    [Chapter03HorizontalFiberIntersectionTheory f]
    (P : Chapter03PrimeDivisor X) (hP : chapter03HorizontalPrime f P) :
    chapter03HorizontalFiberIntersectionNumber (f := f) P =
      chapter03HorizontalPrimeDegree P hP := by
  exact Chapter03HorizontalFiberIntersectionTheory.horizontal_eq_degree (f := f) P hP

/--
The component-intersection pairing for vertical primes is deliberately a
separate interface: it is not supplied by the divisor dictionary alone.
-/
class Chapter03VerticalComponentPairing
    {X S : Scheme.{u}} (f : X ⟶ S) where
  pairing : Chapter03PrimeDivisor X → Chapter03PrimeDivisor X → ℤ
  pairing_vanishes_off_common_fibers :
    ∀ P Q, ¬ (∃ s : S,
      P.support ⊆ (f.base ⁻¹' ({s} : Set S)) ∧
      Q.support ⊆ (f.base ⁻¹' ({s} : Set S))) → pairing P Q = 0

def chapter03VerticalComponentIntersectionNumber
    {X S : Scheme.{u}} {f : X ⟶ S}
    [Chapter03VerticalComponentPairing f]
    (P Q : Chapter03PrimeDivisor X) : ℤ :=
  Chapter03VerticalComponentPairing.pairing (f := f) P Q

/-- A vertical component is a divisor on the total space, not on its own fiber. -/
def chapter03VerticalComponentOnTotalSpace
    {X S : Scheme.{u}} [IsIntegral S] (f : X ⟶ S) (P : Chapter03PrimeDivisor X) : Prop :=
  chapter03VerticalPrime f P

/-- The warning that vertical degree needs component-pairing data. -/
theorem chapter03_vertical_intersection_requires_pairing
    {X S : Scheme.{u}} (f : X ⟶ S) (P Q : Chapter03PrimeDivisor X)
    [Chapter03VerticalComponentPairing f] :
    chapter03VerticalComponentIntersectionNumber (f := f) P Q =
      Chapter03VerticalComponentPairing.pairing (f := f) P Q := by
  rfl

/-- The base-change map attached to a field extension. -/
def chapter03SpecBaseChangeMap
    {k K : Type u} [Field k] [Field K] [Algebra k K] :
    Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k K))

def chapter03PurelyInseparableBaseChangedCurveMap
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) :
    pullback f (chapter03SpecBaseChangeMap (k := k) (K := K)) ⟶
      Spec (CommRingCat.of K) :=
  pullback.snd f (chapter03SpecBaseChangeMap (k := k) (K := K))

/--
Regularity of a curve need not survive as smoothness after a purely
inseparable extension.  This predicate records the exact failure profile
used by the warning in the source text.
-/
def Chapter03RegularCurvePurelyInseparableSmoothnessFailure
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) : Prop :=
  Chapter03Regular X ∧ IsPurelyInseparable k K ∧
    ¬ Smooth (chapter03PurelyInseparableBaseChangedCurveMap (k := k) (K := K) f)

theorem chapter03_regular_divisor_theory_uses_regular_not_smooth
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (h : Chapter03RegularCurvePurelyInseparableSmoothnessFailure (k := k) (K := K) f) :
    Chapter03Regular X :=
  h.1

theorem chapter03_normal_surface_need_not_be_locallyFactorial
    {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X] [Chapter03Normal X]
    [Chapter03CartierDivisorTheory X]
    (h : ¬ Chapter03LocallyFactorial X) :
    ¬ Function.Surjective (chapter03CartierDivisorToWeil X) := by
  intro hs
  exact h ((chapter03_cartier_to_weil_surjective_iff_locallyFactorial (X := X)).1 hs)

theorem chapter03_normal_nonCartier_prime_exists
    {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X] [Chapter03Normal X]
    [Chapter03CartierDivisorTheory X]
    (h : ¬ Chapter03LocallyFactorial X) :
    ∃ P : Chapter03PrimeDivisor X,
      ¬ ∃ D : Chapter03CartierDivisor X,
        chapter03CartierDivisorToWeil X D = chapter03PrimeDivisorCycle P 1 := by
  sorry

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03
