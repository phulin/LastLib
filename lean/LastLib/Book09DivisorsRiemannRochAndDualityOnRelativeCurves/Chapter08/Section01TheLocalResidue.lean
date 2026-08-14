import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08.Dependencies

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

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
      (D.ideal.support : Set C.carrier) = {x.1} := by
  sorry

structure Chapter08PointAdjunction
    [Algebra k C.carrier.functionField]
    (T : Chapter08PointThickening k C x n)
    [Chapter08ThickeningSectionsAlgebra T] where
  poleDifferentials : Submodule k (Chapter08RationalDifferentials k C.carrier)
  regularDifferentials : Submodule k (Chapter08RationalDifferentials k C.carrier)
  regular_le_pole : regularDifferentials ≤ poleDifferentials
  adjunctionIso :
    Submodule.Quotient (regularDifferentials.comap poleDifferentials.subtype) ≃ₗ[k]
      Chapter08ThickeningDual T

abbrev Chapter08PoleQuotient
    [Algebra k C.carrier.functionField]
    (A : Chapter08PointAdjunction k C x T) :=
  Submodule.Quotient (A.regularDifferentials.comap A.poleDifferentials.subtype)

def chapter08_point_adjunction_iso
    [Algebra k C.carrier.functionField]
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
  sorry

theorem chapter08_finite_cartier_adjunction
    [Algebra k C.carrier.functionField]
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
    chapter08_thickening_evaluation_at_one T φ = φ 1 :=
  rfl

@[simp] theorem chapter08_dual_of_quotient_apply
    {A B : Type v} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (q : A →ₐ[k] B) (φ : B →ₗ[k] k) (a : A) :
    chapter08_dual_of_quotient q φ a = φ (q a) :=
  rfl

structure Chapter08ThickeningTransition
    [Algebra k C.carrier.functionField]
    (Tn : Chapter08PointThickening k C x n)
    (Tnext : Chapter08PointThickening k C x (n + 1))
    [Chapter08ThickeningSectionsAlgebra Tn]
    [Chapter08ThickeningSectionsAlgebra Tnext] where
  quotientMap : Chapter08ThickeningSections Tnext →ₐ[k] Chapter08ThickeningSections Tn
  dualRestriction : Chapter08ThickeningDual Tn →ₗ[k] Chapter08ThickeningDual Tnext
  dualRestriction_eq :
    dualRestriction = chapter08_dual_of_quotient quotientMap
  evaluation_compatibility :
    (chapter08_thickening_evaluation_at_one Tnext).comp dualRestriction =
      chapter08_thickening_evaluation_at_one Tn

theorem chapter08_successive_thickening_quotient
    (Tn : Chapter08PointThickening k C x n)
    (Tnext : Chapter08PointThickening k C x (n + 1))
    [Chapter08ThickeningSectionsAlgebra Tn]
    [Chapter08ThickeningSectionsAlgebra Tnext] :
    Nonempty (Chapter08ThickeningTransition k C x Tn Tnext) := by
  sorry

/- Local dependency guess: the pinned tree does not yet expose the directed
system of finite Cartier duals as a reusable module-valued colimit, so the
stage-compatibility predicates remain bundled here for the fixup pass. -/
structure Chapter08LocalResidueSystem
    [Algebra k C.carrier.functionField] where
  regularDifferentials : Submodule k (Chapter08RationalDifferentials k C.carrier)
  residue : Chapter08RationalDifferentials k C.carrier →ₗ[k] k
  evaluationAtOne : Prop
  restrictionCompatibility : Prop
  directLimitDescription : Prop

def chapter08ResidueAt
    [Algebra k C.carrier.functionField]
    (R : Chapter08LocalResidueSystem k C x) :
    Chapter08RationalDifferentials k C.carrier →ₗ[k] k :=
  R.residue

@[simp] theorem chapter08ResidueAt_apply
    [Algebra k C.carrier.functionField]
    (R : Chapter08LocalResidueSystem k C x)
    (η : Chapter08RationalDifferentials k C.carrier) :
    chapter08ResidueAt k C x R η = R.residue η :=
  rfl

theorem chapter08_local_residue_exists
    [Algebra k C.carrier.functionField] :
    Nonempty (Chapter08LocalResidueSystem k C x) := by
  sorry

theorem chapter08_residue_kills_regular
    [Algebra k C.carrier.functionField]
    (R : Chapter08LocalResidueSystem k C x)
    {η : Chapter08RationalDifferentials k C.carrier}
    (hη : η ∈ R.regularDifferentials) :
    chapter08ResidueAt k C x R η = 0 := by
  sorry

theorem chapter08_residue_of_exact_differential
    [Algebra k C.carrier.functionField]
    (R : Chapter08LocalResidueSystem k C x)
    (b : C.carrier.functionField) :
    chapter08ResidueAt k C x R (KaehlerDifferential.D k C.carrier.functionField b) = 0 := by
  sorry

/- The same map is used when the residue field extension is inseparable; no
field-trace hypothesis occurs in its definition. -/
def chapter08InseparableResidue
    [Algebra k C.carrier.functionField]
    (R : Chapter08LocalResidueSystem k C x) :=
  chapter08ResidueAt k C x R

structure Chapter08LaurentExpansion
    [Algebra k C.carrier.functionField]
    (E : Type v) [Field E] [Algebra k E]
    (η : Chapter08RationalDifferentials k C.carrier) where
  coefficientFieldIdentification : E ≃+* C.carrier.residueField x.1
  parameter : C.carrier.functionField
  series : LaurentSeries E
  parameter_is_uniformizer : Prop
  expansion : Prop

def Chapter08LaurentExpansion.residueCoefficient
    [Algebra k C.carrier.functionField]
    {E : Type v} [Field E] [Algebra k E]
    {η : Chapter08RationalDifferentials k C.carrier}
    (e : Chapter08LaurentExpansion k C x E η) : E :=
  e.series.coeff (-1)

def chapter08ResidueFieldTracePairing
    {E : Type v} [Field E] [Algebra k E]
    (a : E) : E →ₗ[k] k :=
  { toFun := fun b => Algebra.trace k E (a * b)
    map_add' := by
      intro b₁ b₂
      simp [mul_add]
    map_smul' := by
      intro r b
      simp [Algebra.smul_def, mul_comm, mul_left_comm, mul_assoc] }

theorem chapter08_residue_field_trace_pairing_apply
    {E : Type v} [Field E] [Algebra k E] (a b : E) :
    chapter08ResidueFieldTracePairing k a b = Algebra.trace k E (a * b) := by
  rfl

theorem chapter08_residue_separable_expansion
    [Algebra k C.carrier.functionField]
    (R : Chapter08LocalResidueSystem k C x)
    {E : Type v} [Field E] [Algebra k E] [FiniteDimensional k E]
    [Algebra.IsSeparable k E]
    {η : Chapter08RationalDifferentials k C.carrier}
    (e : Chapter08LaurentExpansion k C x E η) :
    chapter08ResidueAt k C x R η =
      Algebra.trace k E e.residueCoefficient := by
  sorry

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08
