import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08.Section01TheLocalResidue

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u v

/-! ### 8.2 Independence of parameter -/

variable (k : Type u) [Field k]
variable (C : Chapter08SmoothIntegralCurve k)
variable (x : Chapter08ClosedPoint C.carrier)

def chapter08LogDifferential
    {F : Type v} [Field F] [Algebra k F] (a : F) : Ω[F⁄k] :=
  a⁻¹ • KaehlerDifferential.D k F a

structure Chapter08LocalParameter
    where
  oldParameter : C.carrier.functionField
  newParameter : C.carrier.functionField
  unitFactor : C.carrier.functionField
  parameter_change : newParameter = oldParameter * unitFactor
  oldParameter_is_uniformizer : Chapter08UniformizerAt C x oldParameter
  newParameter_is_uniformizer : Chapter08UniformizerAt C x newParameter
  oldParameter_ne_zero : oldParameter ≠ 0
  newParameter_ne_zero : newParameter ≠ 0
  unitFactor_isUnit : IsUnit unitFactor
  unitFactor_isUnit_at : Chapter08UnitAt C x unitFactor

theorem chapter08_local_parameter_exists_of_uniformizers
    {t u : C.carrier.functionField}
    (ht : Chapter08UniformizerAt C x t)
    (hu : Chapter08UniformizerAt C x u) :
    Nonempty (Chapter08LocalParameter k C x) := by
  rcases ht with ⟨st, ht, hst, hstreg⟩
  rcases hu with ⟨su, hu, hsu, hsureg⟩
  have hsu_mem : su ∈ Ideal.span ({st} : Set (C.carrier.presheaf.stalk x.1)) := by
    have hsu_max : su ∈ IsLocalRing.maximalIdeal (C.carrier.presheaf.stalk x.1) := by
      rw [← hsu]
      exact Ideal.mem_span_singleton_self _
    rw [hst]
    exact hsu_max
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp hsu_mem
  have hst_mem : st ∈ Ideal.span ({su} : Set (C.carrier.presheaf.stalk x.1)) := by
    have hst_max : st ∈ IsLocalRing.maximalIdeal (C.carrier.presheaf.stalk x.1) := by
      rw [← hst]
      exact Ideal.mem_span_singleton_self _
    rw [hsu]
    exact hst_max
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hst_mem
  have hqmulr : q * r = 1 := by
    have h : (r * q) * st = 1 * st := by
      calc
        (r * q) * st = r * (q * st) := by ring
        _ = r * su := by rw [hq]
        _ = st := hr
        _ = 1 * st := by simp
    simpa [mul_comm] using hstreg.right h
  have hq_unit : IsUnit q := by
    refine isUnit_iff_exists.mpr ⟨r, hqmulr, ?_⟩
    simpa [mul_comm] using hqmulr
  have hq_field : IsUnit (algebraMap (C.carrier.presheaf.stalk x.1)
      C.carrier.functionField q) :=
    IsUnit.map (algebraMap (C.carrier.presheaf.stalk x.1) C.carrier.functionField) hq_unit
  have ht0 : t ≠ 0 := by
    rw [← ht]
    intro hzero
    apply IsRegular.ne_zero hstreg
    apply (IsFractionRing.injective (C.carrier.presheaf.stalk x.1)
      C.carrier.functionField)
    simpa using hzero
  have hu0 : u ≠ 0 := by
    rw [← hu]
    intro hzero
    apply IsRegular.ne_zero hsureg
    apply (IsFractionRing.injective (C.carrier.presheaf.stalk x.1)
      C.carrier.functionField)
    simpa using hzero
  refine ⟨{
    oldParameter := t
    newParameter := u
    unitFactor := algebraMap (C.carrier.presheaf.stalk x.1) C.carrier.functionField q
    parameter_change := ?_
    oldParameter_is_uniformizer := ⟨st, ht, hst, hstreg⟩
    newParameter_is_uniformizer := ⟨su, hu, hsu, hsureg⟩
    oldParameter_ne_zero := ht0
    newParameter_ne_zero := hu0
    unitFactor_isUnit := hq_field
    unitFactor_isUnit_at := ⟨q, hq_unit, rfl⟩
  }⟩
  calc
    u = algebraMap (C.carrier.presheaf.stalk x.1) C.carrier.functionField su := hu.symm
    _ = algebraMap (C.carrier.presheaf.stalk x.1) C.carrier.functionField (q * st) :=
      congrArg _ hq.symm
    _ = algebraMap (C.carrier.presheaf.stalk x.1) C.carrier.functionField q *
        algebraMap (C.carrier.presheaf.stalk x.1) C.carrier.functionField st := by
      rw [map_mul]
    _ = t * algebraMap (C.carrier.presheaf.stalk x.1) C.carrier.functionField q := by
      rw [ht]
      ring

theorem chapter08_log_differential_product
    {F : Type v} [Field F] [Algebra k F]
    {t v u : F} (hu : u = t * v) (ht : t ≠ 0) (hv : v ≠ 0) :
    chapter08LogDifferential k u =
      chapter08LogDifferential k t + chapter08LogDifferential k v := by
  subst u
  simp only [chapter08LogDifferential]
  rw [Derivation.leibniz]
  simp only [smul_add, smul_smul]
  have h₁ : (t * v)⁻¹ * t = v⁻¹ := by
    field_simp [ht, hv]
  have h₂ : (t * v)⁻¹ * v = t⁻¹ := by
    field_simp [ht, hv]
  rw [h₁, h₂]
  exact add_comm _ _

theorem chapter08_parameter_unit_log_differential_regular
    (R : Chapter08LocalResidueSystem k C x)
    (p : Chapter08LocalParameter k C x) :
    chapter08LogDifferential k p.unitFactor ∈ R.regularDifferentials := by
  exact R.unit_log_differential_regular p.unitFactor p.unitFactor_isUnit_at

theorem chapter08_residue_log_differential_parameter_change
    (R : Chapter08LocalResidueSystem k C x)
    (p : Chapter08LocalParameter k C x) :
    chapter08ResidueAt k C x R (chapter08LogDifferential k p.oldParameter) =
      chapter08ResidueAt k C x R
        (chapter08LogDifferential k p.newParameter) := by
  have hv : p.unitFactor ≠ 0 := p.unitFactor_isUnit.ne_zero
  have hlog : chapter08LogDifferential k p.newParameter =
      chapter08LogDifferential k p.oldParameter +
        chapter08LogDifferential k p.unitFactor :=
    chapter08_log_differential_product k p.parameter_change
      p.oldParameter_ne_zero hv
  rw [hlog, map_add]
  have hzero : chapter08ResidueAt k C x R
      (chapter08LogDifferential k p.unitFactor) = 0 :=
    chapter08_residue_kills_regular k C x R
      (R.unit_log_differential_regular p.unitFactor p.unitFactor_isUnit_at)
  rw [hzero, add_zero]

theorem chapter08_residue_parameter_change_regular_correction
    (R : Chapter08LocalResidueSystem k C x)
    {t v : C.carrier.functionField}
    (ht : t ≠ 0) (hv : v ≠ 0)
    (hregular : chapter08LogDifferential k v ∈ R.regularDifferentials) :
    chapter08ResidueAt k C x R (chapter08LogDifferential k (t * v)) =
      chapter08ResidueAt k C x R (chapter08LogDifferential k t) := by
  have hlog : chapter08LogDifferential k (t * v) =
      chapter08LogDifferential k t + chapter08LogDifferential k v :=
    chapter08_log_differential_product k (t := t) (v := v) (u := t * v)
      rfl ht hv
  rw [hlog, map_add]
  have hzero : chapter08ResidueAt k C x R
      (chapter08LogDifferential k v) = 0 :=
    chapter08_residue_kills_regular k C x R hregular
  rw [hzero, add_zero]

theorem chapter08_laurent_derivative_termwise
    {E : Type v} [Field E] (b : LaurentSeries E) (m : ℤ) :
    (LaurentSeries.derivative E b).coeff m =
      Ring.choose (m + 1) 1 • b.coeff (m + 1) := by
  rfl

theorem chapter08_laurent_derivative_minus_one_coefficient
    {E : Type v} [Field E] (b : LaurentSeries E) :
    (LaurentSeries.derivative E b).coeff (-1) = 0 := by
  rw [chapter08_laurent_derivative_termwise]
  norm_num

structure Chapter08CoordinateResidue
    (E : Type v) [Field E] [Algebra k E]
    [FiniteDimensional k E] [Algebra.IsSeparable k E]
    (η : Chapter08RationalDifferentials k C.carrier) where
  expansion : Chapter08LaurentExpansion k C x E η

def chapter08_coordinate_residue
    {E : Type v} [Field E] [Algebra k E]
    [FiniteDimensional k E] [Algebra.IsSeparable k E]
    {η : Chapter08RationalDifferentials k C.carrier}
    (c : Chapter08CoordinateResidue k C x E η) : k :=
  Algebra.trace k E c.expansion.residueCoefficient

theorem chapter08_coordinate_residue_parameter_independent
    {E : Type v} [Field E] [Algebra k E] [FiniteDimensional k E]
    [Algebra.IsSeparable k E]
    {η : Chapter08RationalDifferentials k C.carrier}
    (c₁ c₂ : Chapter08CoordinateResidue k C x E η)
    :
    chapter08_coordinate_residue k C x c₁ =
      chapter08_coordinate_residue k C x c₂ := by
  exact (chapter08_residue_separable_expansion k C x c₁.expansion).symm.trans
    (chapter08_residue_separable_expansion k C x c₂.expansion)

theorem chapter08_residue_is_parameter_independent
    {E : Type v} [Field E] [Algebra k E] [FiniteDimensional k E]
    [Algebra.IsSeparable k E]
    {η : Chapter08RationalDifferentials k C.carrier}
    (c : Chapter08CoordinateResidue k C x E η) :
    chapter08_coordinate_residue k C x c =
      chapter08CanonicalResidueAt k C x η := by
  exact (chapter08_residue_separable_expansion k C x c.expansion).symm

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08
