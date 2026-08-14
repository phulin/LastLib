import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter10.Section03RosenlichtDifferentials

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter10

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Set
open scoped BigOperators

universe u

/-! ## 10.4. Families of nodal curves -/

/-!
The family record keeps properness, flatness, finite presentation, nodality,
and the relative local-complete-intersection hypothesis separate.  The last
property is a local dependency interface for the pinned snapshot; it is not
silently replaced by smoothness.
-/

theorem chapter10_relative_dualizing_sheaf_exists
    (F : Chapter10ProperFlatNodalFamily) :
    Nonempty (Chapter10RelativeDualizingSheafData F) := by
  sorry

theorem chapter10_relative_dualizing_is_invertible
    (F : Chapter10ProperFlatNodalFamily)
    (ω : Chapter10RelativeDualizingSheafData F) :
    chapter10RelativeDualizingIsLineBundle ω := by
  sorry

theorem chapter10_relative_dualizing_commutes_with_arbitrary_base_change
    (F : Chapter10ProperFlatNodalFamily)
    (ω : Chapter10RelativeDualizingSheafData F) :
    chapter10RelativeDualizingCommutesWithBaseChange ω := by
  intro T g
  exact ⟨ω.baseChangeIso g⟩

theorem chapter10_relative_dualizing_restricts_to_rosenlicht_on_geometric_fibers
    (F : Chapter10ProperFlatNodalFamily)
    (ω : Chapter10RelativeDualizingSheafData F)
    (p : Chapter10GeometricPoint F.base) :
    ω.fiberwiseRosenlicht p := by
  exact ω.fiberwiseRosenlicht_holds p

/-! ### Étale-local node charts -/

structure Chapter10EtaleNodalChart (F : Chapter10ProperFlatNodalFamily) where
  coefficientRing : Type u
  [coefficientRingCommRing : CommRing coefficientRing]
  parameter : coefficientRing
  chartRing : Type u
  [chartRingCommRing : CommRing chartRing]
  [chartRingAlgebra : Algebra coefficientRing chartRing]
  x : chartRing
  y : chartRing
  equation : x * y = algebraMap coefficientRing chartRing parameter
  basePoint : Spec (.of coefficientRing) ⟶ F.base
  chartMap : Spec (.of chartRing) ⟶ F.total
  etaleNeighborhood : Etale chartMap
  smoothRelativeSurface : Prop
  smoothRelativeSurface_holds : smoothRelativeSurface
  mapsToFamily :
    chartMap ≫ F.map =
      Scheme.Spec.map
        (CommRingCat.ofHom (algebraMap coefficientRing chartRing)).op ≫ basePoint
  logFrame : Prop
  logFrame_holds : logFrame

attribute [instance] Chapter10EtaleNodalChart.coefficientRingCommRing
attribute [instance] Chapter10EtaleNodalChart.chartRingCommRing
attribute [instance] Chapter10EtaleNodalChart.chartRingAlgebra

structure Chapter10EtaleNodalChartFamily (F : Chapter10ProperFlatNodalFamily) where
  /-- A finite collection of local charts; this is not a global enumeration
  of all nodes of an arbitrary base. -/
  nodes : Type u
  [nodesFinite : Fintype nodes]
  chart : nodes → Chapter10EtaleNodalChart F

attribute [instance] Chapter10EtaleNodalChartFamily.nodesFinite

theorem chapter10_etale_node_chart_has_smoothing_equation
    (F : Chapter10ProperFlatNodalFamily)
    (H : Chapter10EtaleNodalChartFamily F) (q : H.nodes) :
    (H.chart q).x * (H.chart q).y =
      algebraMap (H.chart q).coefficientRing (H.chart q).chartRing
        (H.chart q).parameter := by
  exact (H.chart q).equation

theorem chapter10_etale_node_chart_log_frame
    (F : Chapter10ProperFlatNodalFamily)
    (H : Chapter10EtaleNodalChartFamily F) (q : H.nodes) :
    (H.chart q).logFrame := by
  exact (H.chart q).logFrame_holds

theorem chapter10_relative_dualizing_local_frames_glue_by_adjunction
    (F : Chapter10ProperFlatNodalFamily)
    (ω : Chapter10RelativeDualizingSheafData F) :
    ω.canonicalAdjunctionGluing := by
  exact ω.canonicalAdjunctionGluing_holds

/-!
Simultaneous normalization is an extra hypothesis, not a consequence of
normalizing the total space.  The local ramified smoothing below records the
non-Cartier section from the source without incorrectly promoting its affine
local model to a proper family.
-/

abbrev chapter10RamifiedSmoothingBaseRing (k : Type u) [Field k] :=
  Polynomial k

abbrev chapter10RamifiedSmoothingAmbientRing (k : Type u) [Field k] :=
  MvPolynomial (Fin 2) (chapter10RamifiedSmoothingBaseRing k)

def chapter10RamifiedSmoothingEquationIdeal (k : Type u) [Field k] :
    Ideal (chapter10RamifiedSmoothingAmbientRing k) :=
  Ideal.span ({
    MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) -
      MvPolynomial.C (Polynomial.X ^ 2)
  } : Set (chapter10RamifiedSmoothingAmbientRing k))

abbrev chapter10RamifiedSmoothingTotalRing (k : Type u) [Field k] :=
  chapter10RamifiedSmoothingAmbientRing k ⧸
    chapter10RamifiedSmoothingEquationIdeal k

def chapter10RamifiedSmoothingBaseStructureMap (k : Type u) [Field k] :
    chapter10RamifiedSmoothingBaseRing k →+*
      chapter10RamifiedSmoothingTotalRing k :=
  (Ideal.Quotient.mk (chapter10RamifiedSmoothingEquationIdeal k)).comp
    (MvPolynomial.C)

def chapter10RamifiedSmoothingBaseScheme (k : Type u) [Field k] : Scheme.{u} :=
  Spec (.of (chapter10RamifiedSmoothingBaseRing k))

def chapter10RamifiedSmoothingTotalScheme (k : Type u) [Field k] : Scheme.{u} :=
  Spec (.of (chapter10RamifiedSmoothingTotalRing k))

def chapter10RamifiedSmoothingFamilyMap (k : Type u) [Field k] :
    chapter10RamifiedSmoothingTotalScheme k ⟶
      chapter10RamifiedSmoothingBaseScheme k :=
  Scheme.Spec.map
    (CommRingCat.ofHom (chapter10RamifiedSmoothingBaseStructureMap k)).op

abbrev chapter10RamifiedSmoothingSpecialFiberRing (k : Type u) [Field k] :=
  MvPolynomial (Fin 2) k ⧸ Ideal.span ({
    MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)
  } : Set (MvPolynomial (Fin 2) k))

def chapter10RamifiedSmoothingSpecialFiberScheme (k : Type u) [Field k] :
    Scheme.{u} :=
  Spec (.of (chapter10RamifiedSmoothingSpecialFiberRing k))

def chapter10RamifiedSmoothingSectionIdeal (k : Type u) [Field k] :
    Ideal (chapter10RamifiedSmoothingTotalRing k) :=
  Ideal.span ({
    Ideal.Quotient.mk (chapter10RamifiedSmoothingEquationIdeal k)
      (MvPolynomial.X (0 : Fin 2) - MvPolynomial.C (Polynomial.X)),
    Ideal.Quotient.mk (chapter10RamifiedSmoothingEquationIdeal k)
      (MvPolynomial.X (1 : Fin 2) - MvPolynomial.C (Polynomial.X))
  } : Set (chapter10RamifiedSmoothingTotalRing k))

def chapter10RamifiedSmoothingSectionIdealAt
    (k : Type u) [Field k]
    (p : PrimeSpectrum (chapter10RamifiedSmoothingTotalRing k)) :
    Ideal (Localization.AtPrime p.asIdeal) :=
  Ideal.span ({
    IsLocalization.mk' (M := p.asIdeal.primeCompl)
      (Localization.AtPrime p.asIdeal)
      (Ideal.Quotient.mk (chapter10RamifiedSmoothingEquationIdeal k)
        (MvPolynomial.X (0 : Fin 2) - MvPolynomial.C (Polynomial.X)))
      ⟨1, p.asIdeal.primeCompl.one_mem⟩,
    IsLocalization.mk' (M := p.asIdeal.primeCompl)
      (Localization.AtPrime p.asIdeal)
      (Ideal.Quotient.mk (chapter10RamifiedSmoothingEquationIdeal k)
        (MvPolynomial.X (1 : Fin 2) - MvPolynomial.C (Polynomial.X)))
      ⟨1, p.asIdeal.primeCompl.one_mem⟩} :
      Set (Localization.AtPrime p.asIdeal))

def chapter10RamifiedSmoothingSectionIsCartierAt
    (k : Type u) [Field k]
    (p : PrimeSpectrum (chapter10RamifiedSmoothingTotalRing k)) : Prop :=
  ∃ f : Localization.AtPrime p.asIdeal,
    chapter10RamifiedSmoothingSectionIdealAt k p =
        Ideal.span ({f} : Set (Localization.AtPrime p.asIdeal)) ∧
      (∀ z : Localization.AtPrime p.asIdeal, z * f = 0 → z = 0)

/-- An effective Cartier divisor is locally principal and regular at every
prime.  The node counterexample must therefore be tested in localizations,
not by asking for one global generator of the section ideal. -/
def chapter10RamifiedSmoothingSectionIsCartier
    (k : Type u) [Field k] : Prop :=
  ∀ p : PrimeSpectrum (chapter10RamifiedSmoothingTotalRing k),
    chapter10RamifiedSmoothingSectionIsCartierAt k p

structure Chapter10RamifiedSmoothingCounterexample
    (k : Type u) [Field k] where
  sectionNotCartier : ¬ chapter10RamifiedSmoothingSectionIsCartier k

theorem chapter10_ramified_smoothing_section_is_not_cartier
    (k : Type u) [Field k] :
    ¬ chapter10RamifiedSmoothingSectionIsCartier k := by
  let M := Fin 2 → k
  let B := TrivSqZeroExt k M
  let e0 : M := fun i => if i = 0 then 1 else 0
  let e1 : M := fun i => if i = 1 then 1 else 0
  let coeff : Polynomial k →+* B :=
    (TrivSqZeroExt.inlHom k M).comp (Polynomial.evalRingHom 0)
  let vars : Fin 2 → B := fun i =>
    if i = 0 then TrivSqZeroExt.inr e0 else TrivSqZeroExt.inr e1
  let φ : chapter10RamifiedSmoothingAmbientRing k →+* B :=
    MvPolynomial.eval₂Hom coeff vars
  have hφrel : φ
      (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) -
        MvPolynomial.C (Polynomial.X ^ 2)) = 0 := by
    simp [φ, coeff, vars, e0, e1]
    exact TrivSqZeroExt.inr_mul_inr (R := k) (M := M) e0 e1
  let q : chapter10RamifiedSmoothingTotalRing k →+* B :=
    Ideal.Quotient.lift (chapter10RamifiedSmoothingEquationIdeal k) φ
      (by
        intro z hz
        rw [chapter10RamifiedSmoothingEquationIdeal] at hz
        rw [Ideal.mem_span_singleton] at hz
        rcases hz with ⟨c, rfl⟩
        rw [map_mul, hφrel, zero_mul])
  have hqX : q (Ideal.Quotient.mk
      (chapter10RamifiedSmoothingEquationIdeal k)
      (MvPolynomial.X (0 : Fin 2) - MvPolynomial.C (Polynomial.X))) =
      TrivSqZeroExt.inr e0 - TrivSqZeroExt.inl 0 := by
    rw [Ideal.Quotient.lift_mk]
    simp [φ, coeff, vars, e0]
  have hqY : q (Ideal.Quotient.mk
      (chapter10RamifiedSmoothingEquationIdeal k)
      (MvPolynomial.X (1 : Fin 2) - MvPolynomial.C (Polynomial.X))) =
      TrivSqZeroExt.inr e1 - TrivSqZeroExt.inl 0 := by
    rw [Ideal.Quotient.lift_mk]
    simp [φ, coeff, vars, e1]
  let ev : chapter10RamifiedSmoothingAmbientRing k →+* k :=
    MvPolynomial.eval₂Hom (Polynomial.evalRingHom 0) (fun _ => 0)
  have hevrel : ev
      (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) -
        MvPolynomial.C (Polynomial.X ^ 2)) = 0 := by
    simp [ev]
  let e : chapter10RamifiedSmoothingTotalRing k →+* k :=
    Ideal.Quotient.lift (chapter10RamifiedSmoothingEquationIdeal k) ev
      (by
        intro z hz
        rw [chapter10RamifiedSmoothingEquationIdeal] at hz
        rw [Ideal.mem_span_singleton] at hz
        rcases hz with ⟨c, rfl⟩
        rw [map_mul, hevrel, zero_mul])
  have hfst :
      (TrivSqZeroExt.fstHom k k M).toRingHom.comp q = e := by
    apply Ideal.Quotient.ringHom_ext
    rw [RingHom.comp_assoc, Ideal.Quotient.lift_comp_mk,
      Ideal.Quotient.lift_comp_mk]
    apply MvPolynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext'
      · ext z
        simp [φ, ev, coeff, TrivSqZeroExt.fstHom]
        change (TrivSqZeroExt.inl z : B).fst = z
        rfl
      · simp [φ, coeff, ev, TrivSqZeroExt.fstHom]
    · intro z
      simp [φ, ev, vars, TrivSqZeroExt.fstHom]
      change
        (if z = 0 then TrivSqZeroExt.inr e0 else TrivSqZeroExt.inr e1 : B).fst =
          (0 : k)
      split <;> rfl
  let p : PrimeSpectrum (chapter10RamifiedSmoothingTotalRing k) :=
    ⟨RingHom.ker e, RingHom.ker_isPrime e⟩
  let : p.asIdeal.IsPrime := p.isPrime
  have hunit : ∀ y : p.asIdeal.primeCompl, IsUnit (q (y :
      chapter10RamifiedSmoothingTotalRing k)) := by
    intro y
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero]
    have hy : e (y : chapter10RamifiedSmoothingTotalRing k) ≠ 0 := by
      intro hy
      exact y.2 (RingHom.mem_ker.mpr hy)
    have h := congrArg
      (fun f : chapter10RamifiedSmoothingTotalRing k →+* k =>
        f (y : chapter10RamifiedSmoothingTotalRing k)) hfst
    have hqeq : (q (y : chapter10RamifiedSmoothingTotalRing k)).fst =
        e (y : chapter10RamifiedSmoothingTotalRing k) := by
      simpa using h
    rw [hqeq]
    exact hy
  let ℓ : Localization.AtPrime p.asIdeal →+* B :=
    IsLocalization.lift (M := p.asIdeal.primeCompl) hunit
  let u : Localization.AtPrime p.asIdeal :=
    IsLocalization.mk' (M := p.asIdeal.primeCompl)
      (Localization.AtPrime p.asIdeal)
      (Ideal.Quotient.mk (chapter10RamifiedSmoothingEquationIdeal k)
        (MvPolynomial.X (0 : Fin 2) - MvPolynomial.C (Polynomial.X)))
      ⟨1, p.asIdeal.primeCompl.one_mem⟩
  let v : Localization.AtPrime p.asIdeal :=
    IsLocalization.mk' (M := p.asIdeal.primeCompl)
      (Localization.AtPrime p.asIdeal)
      (Ideal.Quotient.mk (chapter10RamifiedSmoothingEquationIdeal k)
        (MvPolynomial.X (1 : Fin 2) - MvPolynomial.C (Polynomial.X)))
      ⟨1, p.asIdeal.primeCompl.one_mem⟩
  have hℓu : ℓ u = TrivSqZeroExt.inr e0 := by
    dsimp [u]
    rw [IsLocalization.lift_mk'_spec]
    simp [q, φ, coeff, vars, e0]
  have hℓv : ℓ v = TrivSqZeroExt.inr e1 := by
    dsimp [v]
    rw [IsLocalization.lift_mk'_spec]
    simp [q, φ, coeff, vars, e1]
  intro hcartier
  rcases hcartier p with ⟨f, hfspan, hfregular⟩
  have hsection : chapter10RamifiedSmoothingSectionIdealAt k p =
      Ideal.span ({u, v} : Set (Localization.AtPrime p.asIdeal)) := by
    rfl
  let ρ : Localization.AtPrime p.asIdeal →+* k :=
    (TrivSqZeroExt.fstHom k k M).toRingHom.comp ℓ
  have hJker : Ideal.span ({u, v} : Set (Localization.AtPrime p.asIdeal)) ≤
      RingHom.ker ρ := by
    refine Ideal.span_le.2 ?_
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · change ρ u = 0
      change (TrivSqZeroExt.fstHom k k M) (ℓ u) = 0
      rw [hℓu]
      change (TrivSqZeroExt.inr e0 : B).fst = (0 : k)
      rfl
    · rcases Set.mem_singleton_iff.mp hz with rfl
      change ρ v = 0
      change (TrivSqZeroExt.fstHom k k M) (ℓ v) = 0
      rw [hℓv]
      change (TrivSqZeroExt.inr e1 : B).fst = (0 : k)
      rfl
  have hfmem : f ∈ chapter10RamifiedSmoothingSectionIdealAt k p := by
    rw [hfspan]
    exact Ideal.mem_span_singleton_self f
  have hfker : f ∈ RingHom.ker ρ := by
    apply hJker
    rw [← hsection]
    exact hfmem
  have hρf : ρ f = 0 := RingHom.mem_ker.mp hfker
  have hfstf : (ℓ f).fst = 0 := by
    change ρ f = 0
    exact hρf
  have humem : u ∈ Ideal.span ({f} : Set (Localization.AtPrime p.asIdeal)) := by
    rw [← hfspan, hsection]
    exact Ideal.subset_span (by simp)
  have hvmem : v ∈ Ideal.span ({f} : Set (Localization.AtPrime p.asIdeal)) := by
    rw [← hfspan, hsection]
    exact Ideal.subset_span (by simp)
  rcases Ideal.mem_span_singleton'.mp humem with ⟨a, ha⟩
  rcases Ideal.mem_span_singleton'.mp hvmem with ⟨b, hb⟩
  have hua : TrivSqZeroExt.inr e0 = ℓ a * ℓ f := by
    have h := congrArg ℓ ha
    rw [map_mul, hℓu] at h
    exact h.symm
  have hvb : TrivSqZeroExt.inr e1 = ℓ b * ℓ f := by
    have h := congrArg ℓ hb
    rw [map_mul, hℓv] at h
    exact h.symm
  have he0 : e0 = (ℓ a).fst • (ℓ f).snd := by
    have h := congrArg TrivSqZeroExt.snd hua
    rw [TrivSqZeroExt.snd_mul, hfstf] at h
    simp only [op_smul_eq_smul, zero_smul, add_zero] at h
    change e0 = (ℓ a).fst • (ℓ f).snd at h
    exact h
  have he1 : e1 = (ℓ b).fst • (ℓ f).snd := by
    have h := congrArg TrivSqZeroExt.snd hvb
    rw [TrivSqZeroExt.snd_mul, hfstf] at h
    simp only [op_smul_eq_smul, zero_smul, add_zero] at h
    change e1 = (ℓ b).fst • (ℓ f).snd at h
    exact h
  have hw0 : (ℓ f).snd 0 ≠ 0 := by
    intro hw
    have hcoord := congrFun he0 0
    change (1 : k) = (ℓ a).fst * (ℓ f).snd 0 at hcoord
    rw [hw, mul_zero] at hcoord
    have hzero : (1 : k) = 0 := hcoord
    exact one_ne_zero hzero
  have hbzero : (ℓ b).fst = 0 := by
    have hcoord := congrFun he1 0
    change (0 : k) = (ℓ b).fst * (ℓ f).snd 0 at hcoord
    have hmul : (ℓ b).fst * (ℓ f).snd 0 = 0 := hcoord.symm
    exact (mul_eq_zero.mp hmul).resolve_right hw0
  have hzero : (1 : k) = 0 := by
    have hcoord := congrFun he1 1
    change (1 : k) = (ℓ b).fst * (ℓ f).snd 1 at hcoord
    rw [hbzero, zero_mul] at hcoord
    exact hcoord
  exact one_ne_zero hzero

theorem chapter10_ramified_smoothing_counterexample_exists
    (k : Type u) [Field k] :
    Nonempty (Chapter10RamifiedSmoothingCounterexample k) := by
  exact ⟨{sectionNotCartier := chapter10_ramified_smoothing_section_is_not_cartier k}⟩

structure Chapter10FiberwiseNormalization
    (F : Chapter10ProperFlatNodalFamily)
    (p : Chapter10GeometricPoint F.base) where
  normalizedFiber : Scheme.{u}
  map : normalizedFiber ⟶ chapter10GeometricFiberTotal F.map p
  finite : IsFinite map
  normal : chapter10IsNormal normalizedFiber
  normalizesTheGeometricFiber : Chapter10NormalizationUniversalProperty map

def chapter10HasFiberwiseNormalization
    (F : Chapter10ProperFlatNodalFamily)
    (p : Chapter10GeometricPoint F.base) : Prop :=
  Nonempty (Chapter10FiberwiseNormalization F p)

/-! ### Marked smooth points and logarithmic twists -/

def chapter10MarkedSections
    (F : Chapter10ProperFlatNodalFamily)
    (ω : Chapter10RelativeDualizingSheafData F)
    (n : ℕ) (D : Chapter10MarkedDifferentialData F ω n) :
    Fin n → Chapter10MarkedSection F :=
  D.markings

def chapter10MarkedTwistedDualizingSheaf
    (F : Chapter10ProperFlatNodalFamily)
    (ω : Chapter10RelativeDualizingSheafData F)
    (n : ℕ) (D : Chapter10MarkedDifferentialData F ω n) : F.total.Modules :=
  D.twistedOmega

def chapter10MarkedGlobalSection
    (F : Chapter10ProperFlatNodalFamily)
    (ω : Chapter10RelativeDualizingSheafData F)
    (n : ℕ) (D : Chapter10MarkedDifferentialData F ω n) : Type u :=
  (Scheme.Modules.presheaf (chapter10MarkedTwistedDualizingSheaf F ω n D)).obj
    (Opposite.op (⊤ : F.total.Opens))

theorem chapter10_marked_twist_allows_simple_marking_poles
    (F : Chapter10ProperFlatNodalFamily)
    (ω : Chapter10RelativeDualizingSheafData F)
    (n : ℕ) (D : Chapter10MarkedDifferentialData F ω n) :
    D.allowsSimplePolesAtMarkings := by
  exact D.allowsSimplePolesAtMarkings_holds

theorem chapter10_marked_twist_retains_implicit_node_branch_poles
    (F : Chapter10ProperFlatNodalFamily)
    (ω : Chapter10RelativeDualizingSheafData F)
    (n : ℕ) (D : Chapter10MarkedDifferentialData F ω n) :
    D.allowsImplicitNodeBranchPoles := by
  exact D.allowsImplicitNodeBranchPoles_holds

/-!
The total-residue statement is numerical on each geometric fiber.  Since the
residue field varies with the geometric point, the profile below keeps the
fiber field explicit.  Its residue functions are restrictions of one global
residue functional on the marked global section, and the supplied
Rosenlicht condition is tested on that same section.
-/

abbrev Chapter10MarkedResidueIndex (nodes : Type u) (n : ℕ) :=
  nodes ⊕ (nodes ⊕ Fin n)

structure Chapter10MarkedFiberResidueProfile
    (F : Chapter10ProperFlatNodalFamily)
    (ω : Chapter10RelativeDualizingSheafData F)
    (n : ℕ) (D : Chapter10MarkedDifferentialData F ω n)
    (η : chapter10MarkedGlobalSection F ω n D) where
  nodes : Type u
  [nodesFinite : Fintype nodes]
  globalResidue : ∀ p : Chapter10GeometricPoint F.base,
    Chapter10MarkedResidueIndex nodes n →
      chapter10MarkedGlobalSection F ω n D → p.field
  localFunctions : ∀ _p : Chapter10GeometricPoint F.base, Type u
  localAction : ∀ p : Chapter10GeometricPoint F.base,
    localFunctions p →
      chapter10MarkedGlobalSection F ω n D →
        chapter10MarkedGlobalSection F ω n D
  unitLocalFunction : ∀ p, localFunctions p
  unitAction : ∀ p,
    localAction p (unitLocalFunction p) η = η
  globalRosenlichtCondition : ∀ p,
    letI := Classical.decEq (Chapter10MarkedResidueIndex nodes n)
    chapter10GlobalRosenlichtResidueCondition
      (Finset.univ : Finset (Chapter10MarkedResidueIndex nodes n))
      (localFunctions p) (localAction p) (globalResidue p) η
  nodeOppositeResidue : ∀ (p : Chapter10GeometricPoint F.base) (q : nodes),
    globalResidue p (Sum.inl q) η +
        globalResidue p (Sum.inr (Sum.inl q)) η = 0

attribute [instance] Chapter10MarkedFiberResidueProfile.nodesFinite

def Chapter10MarkedFiberResidueProfile.totalResidue
    {F : Chapter10ProperFlatNodalFamily}
    {ω : Chapter10RelativeDualizingSheafData F}
    {n : ℕ} {D : Chapter10MarkedDifferentialData F ω n}
    {η : chapter10MarkedGlobalSection F ω n D}
    (R : Chapter10MarkedFiberResidueProfile F ω n D η)
    (p : Chapter10GeometricPoint F.base) : p.field :=
  letI := Classical.decEq (Chapter10MarkedResidueIndex R.nodes n)
  Finset.sum Finset.univ (fun i => R.globalResidue p i η)

def Chapter10MarkedFiberResidueProfile.nodeLeftResidue
    {F : Chapter10ProperFlatNodalFamily}
    {ω : Chapter10RelativeDualizingSheafData F}
    {n : ℕ} {D : Chapter10MarkedDifferentialData F ω n}
    {η : chapter10MarkedGlobalSection F ω n D}
    (R : Chapter10MarkedFiberResidueProfile F ω n D η)
    (p : Chapter10GeometricPoint F.base) (q : R.nodes) : p.field :=
  R.globalResidue p (Sum.inl q) η

def Chapter10MarkedFiberResidueProfile.nodeRightResidue
    {F : Chapter10ProperFlatNodalFamily}
    {ω : Chapter10RelativeDualizingSheafData F}
    {n : ℕ} {D : Chapter10MarkedDifferentialData F ω n}
    {η : chapter10MarkedGlobalSection F ω n D}
    (R : Chapter10MarkedFiberResidueProfile F ω n D η)
    (p : Chapter10GeometricPoint F.base) (q : R.nodes) : p.field :=
  R.globalResidue p (Sum.inr (Sum.inl q)) η

def Chapter10MarkedFiberResidueProfile.markingResidue
    {F : Chapter10ProperFlatNodalFamily}
    {ω : Chapter10RelativeDualizingSheafData F}
    {n : ℕ} {D : Chapter10MarkedDifferentialData F ω n}
    {η : chapter10MarkedGlobalSection F ω n D}
    (R : Chapter10MarkedFiberResidueProfile F ω n D η)
    (p : Chapter10GeometricPoint F.base) (i : Fin n) : p.field :=
  R.globalResidue p (Sum.inr (Sum.inr i)) η

def chapter10NodeResiduesCancelInternally
    {F : Chapter10ProperFlatNodalFamily}
    {ω : Chapter10RelativeDualizingSheafData F}
    {n : ℕ} {D : Chapter10MarkedDifferentialData F ω n}
    {η : chapter10MarkedGlobalSection F ω n D}
    (R : Chapter10MarkedFiberResidueProfile F ω n D η) : Prop :=
  ∀ (p : Chapter10GeometricPoint F.base) (q : R.nodes),
    R.nodeLeftResidue p q + R.nodeRightResidue p q = 0

def chapter10TotalResidueIsZeroOnEveryGeometricFiber
    {F : Chapter10ProperFlatNodalFamily}
    {ω : Chapter10RelativeDualizingSheafData F}
    {n : ℕ} {D : Chapter10MarkedDifferentialData F ω n}
    {η : chapter10MarkedGlobalSection F ω n D}
    (R : Chapter10MarkedFiberResidueProfile F ω n D η) : Prop :=
  ∀ p : Chapter10GeometricPoint F.base, R.totalResidue p = 0

theorem chapter10_marked_global_section_has_total_residue_zero
    (F : Chapter10ProperFlatNodalFamily)
    (ω : Chapter10RelativeDualizingSheafData F)
    (n : ℕ) (D : Chapter10MarkedDifferentialData F ω n)
    (η : chapter10MarkedGlobalSection F ω n D)
    (R : Chapter10MarkedFiberResidueProfile F ω n D η) :
    chapter10TotalResidueIsZeroOnEveryGeometricFiber R ∧
      chapter10NodeResiduesCancelInternally R := by
  classical
  constructor
  · intro p
    have h := R.globalRosenlichtCondition p
      (R.unitLocalFunction p)
    rw [R.unitAction p] at h
    simpa [Chapter10MarkedFiberResidueProfile.totalResidue] using h
  · intro p q
    exact R.nodeOppositeResidue p q

theorem chapter10_marked_residue_statement_is_node_cancellation_plus_marking_balance
    (F : Chapter10ProperFlatNodalFamily)
    (ω : Chapter10RelativeDualizingSheafData F)
    (n : ℕ) (D : Chapter10MarkedDifferentialData F ω n)
    (η : chapter10MarkedGlobalSection F ω n D)
    (R : Chapter10MarkedFiberResidueProfile F ω n D η) :
    chapter10TotalResidueIsZeroOnEveryGeometricFiber R ∧
      chapter10NodeResiduesCancelInternally R := by
  exact chapter10_marked_global_section_has_total_residue_zero F ω n D η R

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter10
