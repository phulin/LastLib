import Mathlib.LinearAlgebra.Quotient.Defs
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08.Dependencies

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09

noncomputable section

universe u v

/-! ### 8.1 The local residue -/

variable (k : Type u) [Field k]
variable (C : Chapter08SmoothIntegralCurve k)
variable (x : Chapter08ClosedPoint C.carrier)

theorem chapter08_closed_point_is_effective_cartier
    (C : Chapter08SmoothIntegralCurve k)
    (x : Chapter08ClosedPoint C.carrier) :
    ∃ D : Chapter09EffectiveCartierDivisor C.carrier,
      D.ideal =
          Scheme.IdealSheafData.vanishingIdeal
            (⟨{x.1}, x.2⟩ : TopologicalSpace.Closeds C.carrier) ∧
        (D.ideal.support : Set C.carrier) = {x.1} := by
  sorry

/- The image of the Kähler differentials of the local ring is the subspace of
rational differentials regular at the point.  Multiplying that image by the
inverse of a local equation of `nx` gives the local pole-bound subspace.  Using
the whole local differential module, rather than `D t` for a uniformizer,
also covers inseparable residue-field extensions. -/
noncomputable def chapter08LocalDifferentialMap
    (x : Chapter08ClosedPoint C.carrier) :
    Ω[(C.carrier.presheaf.stalk x.1)⁄k] →ₗ[C.carrier.presheaf.stalk x.1]
      Ω[C.carrier.functionField⁄k] :=
  letI : Algebra k (C.carrier.presheaf.stalk x.1) :=
    chapter08StalkAlgebra C x
  letI : IsScalarTower k (C.carrier.presheaf.stalk x.1) C.carrier.functionField :=
    by sorry
  KaehlerDifferential.map k k
    (C.carrier.presheaf.stalk x.1) C.carrier.functionField

def chapter08DifferentialRegularAt
    (η : Chapter08RationalDifferentials k C.carrier) : Prop :=
  ∃ ξ : Ω[(C.carrier.presheaf.stalk x.1)⁄k],
    chapter08LocalDifferentialMap k C x ξ = η

def chapter08DifferentialWithPoleBound
    (_T : Chapter08PointThickening k C x n)
    (η : Chapter08RationalDifferentials k C.carrier) : Prop :=
  ∃ (t : C.carrier.functionField)
    (ξ : Ω[(C.carrier.presheaf.stalk x.1)⁄k]),
    Chapter08UniformizerAt C x t ∧
      η = (t ^ n)⁻¹ • chapter08LocalDifferentialMap k C x ξ

structure Chapter08PrincipalParts
    (T : Chapter08PointThickening k C x n) where
  poleDifferentials : Submodule k (Chapter08RationalDifferentials k C.carrier)
  regularDifferentials : Submodule k (Chapter08RationalDifferentials k C.carrier)
  regular_le_pole : regularDifferentials ≤ poleDifferentials
  regularDifferentials_characterization :
    ∀ η, η ∈ regularDifferentials ↔ chapter08DifferentialRegularAt k C x η
  poleDifferentials_characterization :
    ∀ η, η ∈ poleDifferentials ↔ chapter08DifferentialWithPoleBound k C x T η

abbrev Chapter08PrincipalParts.quotient
    {T : Chapter08PointThickening k C x n}
    (P : Chapter08PrincipalParts k C x T) : Type u :=
  ((P.poleDifferentials : Type u) ⧸
    (P.regularDifferentials.comap P.poleDifferentials.subtype))

structure Chapter08PointAdjunction
    (T : Chapter08PointThickening k C x n)
    [Chapter08ThickeningSectionsAlgebra T] where
  principalParts : Chapter08PrincipalParts k C x T
  adjunctionIso :
    principalParts.quotient ≃ₗ[k]
      Chapter08ThickeningDual T

abbrev Chapter08PointAdjunction.poleDifferentials
    {T : Chapter08PointThickening k C x n}
    [Chapter08ThickeningSectionsAlgebra T]
    (A : Chapter08PointAdjunction k C x T) :=
  A.principalParts.poleDifferentials

abbrev Chapter08PointAdjunction.regularDifferentials
    {T : Chapter08PointThickening k C x n}
    [Chapter08ThickeningSectionsAlgebra T]
    (A : Chapter08PointAdjunction k C x T) :=
  A.principalParts.regularDifferentials

theorem chapter08_point_adjunction_regular_le_pole
    {T : Chapter08PointThickening k C x n}
    [Chapter08ThickeningSectionsAlgebra T]
    (A : Chapter08PointAdjunction k C x T) :
    A.regularDifferentials ≤ A.poleDifferentials :=
  A.principalParts.regular_le_pole

abbrev Chapter08PoleQuotient
    [Chapter08ThickeningSectionsAlgebra T]
    (A : Chapter08PointAdjunction k C x T) : Type u :=
  A.principalParts.quotient

def chapter08_point_adjunction_iso
    [Chapter08ThickeningSectionsAlgebra T]
    (A : Chapter08PointAdjunction k C x T) :
    Chapter08PoleQuotient k C x A ≃ₗ[k] Chapter08ThickeningDual T :=
  A.adjunctionIso

theorem chapter08_point_thickening_exists
    (n : ℕ) (hn : 0 < n) :
    Nonempty (Chapter08PointThickening k C x n) := by
  sorry

theorem chapter08_point_cartier_exact_sequence
    (T : Chapter08PointThickening k C x n) :
    Nonempty (Chapter08CartierExactSequence T) := by
  exact LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.chapter10_cartier_exact_sequence_exists
    T.divisor

theorem chapter08_finite_cartier_adjunction
    (T : Chapter08PointThickening k C x n)
    [Chapter08ThickeningSectionsAlgebra T] :
    Nonempty (Chapter08PointAdjunction k C x T) := by
  sorry

/- The quotient map of successive thickenings induces the restriction of a
functional in the opposite direction. -/
def chapter08_dual_of_quotient
    {A B : Type v} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (q : A →ₐ[k] B) : (B →ₗ[k] k) →ₗ[k] (A →ₗ[k] k) :=
  { toFun := fun φ => φ.comp q.toLinearMap
    map_add' := by
      intro φ ψ
      ext a
      simp
    map_smul' := by
      intro r φ
      ext a
      simp }

def chapter08_thickening_evaluation_at_one
    (T : Chapter08PointThickening k C x n)
    [Chapter08ThickeningSectionsAlgebra T] :
    Chapter08ThickeningDual T →ₗ[k] k :=
  { toFun := fun φ => φ 1
    map_add' := by
      intro φ ψ
      simp
    map_smul' := by
      intro a φ
      simp }

@[simp] theorem chapter08_thickening_evaluation_at_one_apply
    (T : Chapter08PointThickening k C x n)
    [Chapter08ThickeningSectionsAlgebra T]
    (φ : Chapter08ThickeningDual T) :
    chapter08_thickening_evaluation_at_one k C x T φ = φ 1 :=
  rfl

@[simp] theorem chapter08_dual_of_quotient_apply
    {A B : Type v} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (q : A →ₐ[k] B) (φ : B →ₗ[k] k) (a : A) :
    chapter08_dual_of_quotient k q φ a = φ (q a) :=
  rfl

def chapter08_point_adjunction_stage_residue
    (T : Chapter08PointThickening k C x n)
    [Chapter08ThickeningSectionsAlgebra T]
    (A : Chapter08PointAdjunction k C x T)
    (η : Chapter08RationalDifferentials k C.carrier)
    (hη : η ∈ A.poleDifferentials) : k :=
  chapter08_thickening_evaluation_at_one k C x T
    (A.adjunctionIso
      (Submodule.mkQ (A.regularDifferentials.comap A.poleDifferentials.subtype)
        ⟨η, hη⟩))

structure Chapter08ThickeningTransition
    (Tn : Chapter08PointThickening k C x n)
    (Tnext : Chapter08PointThickening k C x (n + 1))
    [Chapter08ThickeningSectionsAlgebra Tn]
    [Chapter08ThickeningSectionsAlgebra Tnext] where
  thickeningMap :
    Chapter08ThickeningScheme Tn ⟶ Chapter08ThickeningScheme Tnext
  thickeningMap_over_curve :
    thickeningMap ≫ Tnext.divisor.ideal.subschemeι = Tn.divisor.ideal.subschemeι
  quotientMap : Chapter08ThickeningSections Tnext →ₐ[k] Chapter08ThickeningSections Tn
  quotientMap_eq_thickeningMap_appTop :
    quotientMap.toRingHom = thickeningMap.appTop.hom
  dualRestriction : Chapter08ThickeningDual Tn →ₗ[k] Chapter08ThickeningDual Tnext
  dualRestriction_eq :
    dualRestriction = chapter08_dual_of_quotient k quotientMap
  quotientMap_surjective : Function.Surjective quotientMap
  evaluation_compatibility :
    (chapter08_thickening_evaluation_at_one k C x Tnext).comp dualRestriction =
      chapter08_thickening_evaluation_at_one k C x Tn

theorem chapter08_successive_thickening_quotient
    (Tn : Chapter08PointThickening k C x n)
    (Tnext : Chapter08PointThickening k C x (n + 1))
    [Chapter08ThickeningSectionsAlgebra Tn]
    [Chapter08ThickeningSectionsAlgebra Tnext] :
    Nonempty (Chapter08ThickeningTransition k C x Tn Tnext) := by
  sorry

/- The pinned tree does not yet expose the directed system of finite Cartier
duals as a reusable module-valued colimit.  Record its stages and transition
maps explicitly so that the residue functional is not detached from the
finite Cartier thickenings. -/
structure Chapter08LocalResidueStages
    (x : Chapter08ClosedPoint C.carrier) where
  pointThickening : ∀ n : ℕ, 0 < n → Chapter08PointThickening k C x n
  adjunction :
    ∀ (n : ℕ) (hn : 0 < n),
      Chapter08PointAdjunction k C x (pointThickening n hn)
  transition :
    ∀ (n : ℕ) (hn : 0 < n),
      Chapter08ThickeningTransition k C x
        (pointThickening n hn)
        (pointThickening (n + 1) (Nat.zero_lt_succ n))
  residue : Chapter08RationalDifferentials k C.carrier →ₗ[k] k
  poleNested :
    ∀ (n : ℕ) (hn : 0 < n),
      (adjunction n hn).poleDifferentials ≤
        (adjunction (n + 1) (Nat.zero_lt_succ n)).poleDifferentials
  stage_compatibility :
    ∀ (n : ℕ) (hn : 0 < n)
      (η : Chapter08RationalDifferentials k C.carrier)
      (hη : η ∈ (adjunction n hn).poleDifferentials),
      chapter08_point_adjunction_stage_residue k C x
          (pointThickening n hn) (adjunction n hn) η hη =
        chapter08_point_adjunction_stage_residue k C x
          (pointThickening (n + 1) (Nat.zero_lt_succ n))
          (adjunction (n + 1) (Nat.zero_lt_succ n)) η
          ((poleNested n hn) hη)
  dual_stage_compatibility :
    ∀ (n : ℕ) (hn : 0 < n)
      (η : Chapter08RationalDifferentials k C.carrier)
      (hη : η ∈ (adjunction n hn).poleDifferentials),
      (adjunction (n + 1) (Nat.zero_lt_succ n)).adjunctionIso
          (Submodule.mkQ
            ((adjunction (n + 1) (Nat.zero_lt_succ n)).regularDifferentials.comap
              (adjunction (n + 1) (Nat.zero_lt_succ n)).poleDifferentials.subtype)
            ⟨η, (poleNested n hn) hη⟩) =
        (transition n hn).dualRestriction
          ((adjunction n hn).adjunctionIso
            (Submodule.mkQ
              ((adjunction n hn).regularDifferentials.comap
                (adjunction n hn).poleDifferentials.subtype)
              ⟨η, hη⟩))
  residue_agrees_with_stage :
    ∀ (n : ℕ) (hn : 0 < n)
      (η : Chapter08RationalDifferentials k C.carrier)
      (hη : η ∈ (adjunction n hn).poleDifferentials),
      residue η =
        chapter08_point_adjunction_stage_residue k C x
          (pointThickening n hn) (adjunction n hn) η hη
  pole_exhaustive :
    ∀ η : Chapter08RationalDifferentials k C.carrier,
      ∃ (n : ℕ) (hn : 0 < n), η ∈ (adjunction n hn).poleDifferentials

structure Chapter08LocalResidueSystem
    (x : Chapter08ClosedPoint C.carrier) where
  stages : Chapter08LocalResidueStages k C x
  regularDifferentials : Submodule k (Chapter08RationalDifferentials k C.carrier)
  regularDifferentials_eq_stage :
    ∀ (n : ℕ) (hn : 0 < n),
      (stages.adjunction n hn).regularDifferentials = regularDifferentials
  residue_kills_regular :
    ∀ {η : Chapter08RationalDifferentials k C.carrier},
      η ∈ regularDifferentials → stages.residue η = 0
  residue_kills_exact :
    ∀ b : C.carrier.functionField,
      stages.residue (KaehlerDifferential.D k C.carrier.functionField b) = 0
  unit_log_differential_regular :
    ∀ f : C.carrier.functionField,
      Chapter08UnitAt C x f →
        f⁻¹ • KaehlerDifferential.D k C.carrier.functionField f ∈ regularDifferentials

def chapter08ResidueAt
    (R : Chapter08LocalResidueSystem k C x) :
    Chapter08RationalDifferentials k C.carrier →ₗ[k] k :=
  R.stages.residue

@[simp] theorem chapter08ResidueAt_apply
    (R : Chapter08LocalResidueSystem k C x)
    (η : Chapter08RationalDifferentials k C.carrier) :
    chapter08ResidueAt k C x R η = R.stages.residue η :=
  rfl

theorem chapter08_local_residue_exists
    :
    Nonempty (Chapter08LocalResidueSystem k C x) := by
  sorry

structure Chapter08LaurentExpansion
    (E : Type v) [Field E] [Algebra k E]
    [FiniteDimensional k E] [Algebra.IsSeparable k E]
    (η : Chapter08RationalDifferentials k C.carrier) where
  coefficientFieldIdentification : E ≃+* C.carrier.residueField x.1
  coefficientFieldMap : k →+* C.carrier.residueField x.1
  coefficientFieldMap_eq_canonical :
    coefficientFieldMap = chapter08ResidueFieldMap C x
  coefficientFieldIdentification_overBase :
    ∀ a : k,
      coefficientFieldIdentification (algebraMap k E a) =
        coefficientFieldMap a
  parameter : C.carrier.functionField
  series : LaurentSeries E
  parameter_is_uniformizer : Chapter08UniformizerAt C x parameter
  completionMap : C.carrier.functionField →+* LaurentSeries E
  completionMap_overBase :
    ∀ a : k,
      completionMap (algebraMap k C.carrier.functionField a) =
        algebraMap k (LaurentSeries E) a
  completionMap_parameter :
    completionMap parameter = HahnSeries.single (1 : ℤ) (1 : E)
  differentialMap :
    Ω[C.carrier.functionField⁄k] →ₗ[k] Ω[LaurentSeries E⁄k]
  differentialMap_semilinear :
    ∀ (a : C.carrier.functionField)
      (ξ : Ω[C.carrier.functionField⁄k]),
      differentialMap (a • ξ) =
        completionMap a • differentialMap ξ
  differentialMap_on_D :
    ∀ f : C.carrier.functionField,
      differentialMap (KaehlerDifferential.D k C.carrier.functionField f) =
        KaehlerDifferential.D k (LaurentSeries E) (completionMap f)
  differentialMap_expansion :
    differentialMap η =
      series • KaehlerDifferential.D k (LaurentSeries E) (completionMap parameter)

def Chapter08LaurentExpansion.residueCoefficient
    {E : Type v} [Field E] [Algebra k E]
    [FiniteDimensional k E] [Algebra.IsSeparable k E]
    {η : Chapter08RationalDifferentials k C.carrier}
    (e : Chapter08LaurentExpansion k C x E η) : E :=
  e.series.coeff (-1)

/- The finite-adjunction construction supplies a residue system.  We keep one
chosen representative behind the book-facing definition below; canonicality
comes from the construction of that system, not from treating an arbitrary
choice of principal-parts isomorphisms as unique. -/
structure Chapter08CanonicalLocalResidueSystem
    (x : Chapter08ClosedPoint C.carrier) where
  system : Chapter08LocalResidueSystem k C x
  normalization :
      ∀ {E : Type v} [Field E] [Algebra k E]
      [FiniteDimensional k E] [Algebra.IsSeparable k E]
      {η : Chapter08RationalDifferentials k C.carrier},
      (e : Chapter08LaurentExpansion k C x E η) →
        system.stages.residue η = Algebra.trace k E e.residueCoefficient

theorem chapter08_canonical_local_residue_exists
    :
    Nonempty (Chapter08CanonicalLocalResidueSystem k C x) := by
  sorry

/- The residue is the one obtained from the compatible finite Cartier
thickenings.  The construction theorem above supplies this canonical choice;
later global statements must not quantify over an arbitrary linear functional
with the same interface. -/
noncomputable def chapter08CanonicalLocalResidueSystem
    :
    Chapter08LocalResidueSystem k C x :=
  (Classical.choice (chapter08_canonical_local_residue_exists.{u, u} k C x)).system

noncomputable def chapter08CanonicalResidueMap
    :
    Chapter08RationalDifferentials k C.carrier →ₗ[k] k :=
  chapter08ResidueAt k C x (chapter08CanonicalLocalResidueSystem k C x)

noncomputable def chapter08CanonicalResidueAt
    (η : Chapter08RationalDifferentials k C.carrier) : k :=
  chapter08CanonicalResidueMap k C x η

@[simp] theorem chapter08CanonicalResidueMap_apply
    (η : Chapter08RationalDifferentials k C.carrier) :
    chapter08CanonicalResidueMap k C x η = chapter08CanonicalResidueAt k C x η :=
  rfl

@[simp] theorem chapter08CanonicalResidueAt_apply
    (η : Chapter08RationalDifferentials k C.carrier) :
    chapter08CanonicalResidueAt k C x η =
      (chapter08CanonicalLocalResidueSystem k C x).stages.residue η :=
  rfl

theorem chapter08_canonical_residue_kills_regular
    {η : Chapter08RationalDifferentials k C.carrier}
    (hη : η ∈
      (chapter08CanonicalLocalResidueSystem k C x).regularDifferentials) :
    chapter08CanonicalResidueAt k C x η = 0 := by
  exact (chapter08CanonicalLocalResidueSystem k C x).residue_kills_regular hη

theorem chapter08_canonical_residue_of_exact_differential
    (b : C.carrier.functionField) :
    chapter08CanonicalResidueAt k C x
        (KaehlerDifferential.D k C.carrier.functionField b) = 0 := by
  exact (chapter08CanonicalLocalResidueSystem k C x).residue_kills_exact b

theorem chapter08_residue_kills_regular
    (R : Chapter08LocalResidueSystem k C x)
    {η : Chapter08RationalDifferentials k C.carrier}
    (hη : η ∈ R.regularDifferentials) :
    chapter08ResidueAt k C x R η = 0 := by
  exact R.residue_kills_regular hη

theorem chapter08_residue_of_exact_differential
    (R : Chapter08LocalResidueSystem k C x)
    (b : C.carrier.functionField) :
    chapter08ResidueAt k C x R (KaehlerDifferential.D k C.carrier.functionField b) = 0 := by
  exact R.residue_kills_exact b

/- The residue is defined intrinsically by the compatible finite Cartier
  thickenings.  For a closed point of the smooth curve in this chapter, the
  residue field is finite separable over `k`; this trace-free interface is
  retained as preparatory language for later finite-map situations, where a
  residue-field extension need not be separable. -/
def chapter08IntrinsicResidue
    (η : Chapter08RationalDifferentials k C.carrier) : k :=
  chapter08CanonicalResidueAt k C x η

def chapter08ResidueFieldTracePairing
    {E : Type v} [Field E] [Algebra k E] [FiniteDimensional k E]
    (a : E) : E →ₗ[k] k :=
  { toFun := fun b => Algebra.trace k E (a * b)
    map_add' := by
      intro b₁ b₂
      simp [mul_add]
    map_smul' := by
      intro m x
      simpa [Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm] using
        (Algebra.trace k E).map_smul m (a * x) }

theorem chapter08_residue_field_trace_pairing_apply
    {E : Type v} [Field E] [Algebra k E] [FiniteDimensional k E] (a b : E) :
    chapter08ResidueFieldTracePairing k a b = Algebra.trace k E (a * b) := by
  rfl

theorem chapter08_residue_separable_expansion
    {E : Type v} [Field E] [Algebra k E] [FiniteDimensional k E]
    [Algebra.IsSeparable k E]
    {η : Chapter08RationalDifferentials k C.carrier}
    (e : Chapter08LaurentExpansion k C x E η) :
    chapter08CanonicalResidueAt k C x η =
      Algebra.trace k E e.residueCoefficient := by
  sorry

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08
