import LastLib.Book04AdelesAndIdeles.Chapter08.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter08

noncomputable section

open scoped BigOperators nonZeroDivisors RestrictedProduct WithZero
open Filter IsDedekindDomain

/-! ## 8.1 From local valuations to a fractional ideal -/

def chapter08FiniteIdeleComponent {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K)
    (v : HeightOneSpectrum (Chapter08Integers K)) : v.adicCompletion K :=
  (x.1 v)

theorem chapter08_finite_idele_component_ne_zero
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K)
    (v : HeightOneSpectrum (Chapter08Integers K)) :
    chapter08FiniteIdeleComponent x v ≠ 0 := by
  sorry

/- The additive valuation exponent of a finite local component.  The zero case is only a harmless
totalization; all uses coming from finite ideles have nonzero local components. -/
def chapter08LocalOrder {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (Chapter08Integers K))
    (x : v.adicCompletion K) : ℤ :=
  if hx : (Valued.v x : ℤᵐ⁰) = 0 then
    0
  else
    (WithZero.unzero hx).toAdd

def chapter08FiniteIdeleOrder {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K)
    (v : HeightOneSpectrum (Chapter08Integers K)) : ℤ :=
  chapter08LocalOrder v (chapter08FiniteIdeleComponent x v)

theorem chapter08_local_order_eq_zero_iff_valued_eq_one
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (Chapter08Integers K))
    (x : v.adicCompletion K) (hx : x ≠ 0) :
    chapter08LocalOrder v x = 0 ↔ (Valued.v x : ℤᵐ⁰) = 1 := by
  sorry

theorem chapter08_finite_idele_order_eventually_eq_zero
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K) :
    ∀ᶠ v : HeightOneSpectrum (Chapter08Integers K) in Filter.cofinite,
      chapter08FiniteIdeleOrder x v = 0 := by
  sorry

def chapter08FiniteIdeleOrderFinsupp {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K) : Chapter08FiniteDivisors K :=
  Finsupp.mk (chapter08_finite_idele_order_eventually_eq_zero x).toFinset
    (chapter08FiniteIdeleOrder x)
    (fun _ => (chapter08_finite_idele_order_eventually_eq_zero x).mem_toFinset)

@[simp]
theorem chapter08FiniteIdeleOrderFinsupp_apply {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K)
    (v : HeightOneSpectrum (Chapter08Integers K)) :
    chapter08FiniteIdeleOrderFinsupp x v = chapter08FiniteIdeleOrder x v := by
  rfl

theorem chapter08_finite_idele_order_mul
    {K : Type*} [Field K] [NumberField K]
    (x y : Chapter08FiniteIdeles K)
    (v : HeightOneSpectrum (Chapter08Integers K)) :
    chapter08FiniteIdeleOrder (x * y) v =
      chapter08FiniteIdeleOrder x v + chapter08FiniteIdeleOrder y v := by
  sorry

theorem chapter08_finite_idele_order_inv
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K)
    (v : HeightOneSpectrum (Chapter08Integers K)) :
    chapter08FiniteIdeleOrder x⁻¹ v = -chapter08FiniteIdeleOrder x v := by
  sorry

theorem chapter08_finite_idele_order_eq_zero_iff_local_unit
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K)
    (v : HeightOneSpectrum (Chapter08Integers K)) :
    chapter08FiniteIdeleOrder x v = 0 ↔
      (Valued.v (chapter08FiniteIdeleComponent x v) : ℤᵐ⁰) = 1 := by
  exact chapter08_local_order_eq_zero_iff_valued_eq_one v _
    (chapter08_finite_idele_component_ne_zero x v)

/-! The divisor-to-ideal construction is the finite Euler product of prime ideals. -/

noncomputable def chapter08FiniteIdeleFractionalIdeal
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K) : Chapter08FractionalIdeal K :=
  (chapter08FiniteIdeleOrderFinsupp x).prod
    (fun v n => (v.asIdeal : Chapter08FractionalIdeal K) ^ n)

theorem chapter08_finite_idele_fractionalIdeal_ne_zero
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K) :
    chapter08FiniteIdeleFractionalIdeal x ≠ 0 := by
  sorry

noncomputable def chapter08FiniteIdeleIdeal
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K) : Chapter08IdealGroup K :=
  Units.mk0 (chapter08FiniteIdeleFractionalIdeal x)
    (chapter08_finite_idele_fractionalIdeal_ne_zero x)

noncomputable def chapter08FiniteIdeleIdealMap
    (K : Type*) [Field K] [NumberField K] :
    Chapter08FiniteIdeles K →* Chapter08IdealGroup K where
  toFun := chapter08FiniteIdeleIdeal
  map_one' := by
    sorry
  map_mul' := by
    intro x y
    sorry

theorem chapter08FiniteIdeleIdealMap_apply
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K) :
    chapter08FiniteIdeleIdealMap K x = chapter08FiniteIdeleIdeal x :=
  rfl

theorem chapter08_finite_idele_ideal_count
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K)
    (v : HeightOneSpectrum (Chapter08Integers K)) :
    FractionalIdeal.count K v
        (chapter08FiniteIdeleIdealMap K x : Chapter08FractionalIdeal K) =
      chapter08FiniteIdeleOrder x v := by
  sorry

def chapter08FiniteIntegralUnits {K : Type*} [Field K] [NumberField K] :
    Subgroup (Chapter08FiniteIdeles K) where
  carrier := {x | ∀ v, chapter08FiniteIdeleOrder x v = 0}
  one_mem' := by
    intro v
    sorry
  mul_mem' := by
    intro x y hx hy v
    rw [chapter08_finite_idele_order_mul, hx v, hy v, add_zero]
  inv_mem' := by
    intro x hx v
    rw [chapter08_finite_idele_order_inv, hx v, neg_zero]

theorem chapter08_mem_finiteIntegralUnits_iff
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K) :
    x ∈ chapter08FiniteIntegralUnits ↔
      ∀ v, chapter08FiniteIdeleOrder x v = 0 :=
  Iff.rfl

theorem chapter08_finite_integral_unit_iff_local_valued_eq_one
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K) :
    x ∈ chapter08FiniteIntegralUnits ↔
      ∀ v, (Valued.v (chapter08FiniteIdeleComponent x v) : ℤᵐ⁰) = 1 := by
  sorry

theorem chapter08_finite_idele_ideal_kernel
    {K : Type*} [Field K] [NumberField K] :
    MonoidHom.ker (chapter08FiniteIdeleIdealMap K) = chapter08FiniteIntegralUnits := by
  sorry

theorem chapter08_finite_idele_ideal_surjective
    (K : Type*) [Field K] [NumberField K] :
    Function.Surjective (chapter08FiniteIdeleIdealMap K) := by
  sorry

theorem chapter08_finite_idele_ideal_short_exact
    (K : Type*) [Field K] [NumberField K] :
    chapter08IsShortExact (chapter08FiniteIntegralUnits (K := K)).subtype
      (chapter08FiniteIdeleIdealMap K) := by
  refine ⟨?_, ?_, chapter08_finite_idele_ideal_surjective K⟩
  exact (chapter08FiniteIntegralUnits (K := K)).subtype_injective
  sorry

/-! The sign convention is the book's convention: the exponent is `+ ord_v`. -/

def chapter08IdealNorm {K : Type*} [Field K] [NumberField K]
    (I : Chapter08IdealGroup K) : ℚ :=
  FractionalIdeal.absNorm (I : Chapter08FractionalIdeal K)

def chapter08FiniteIdeleNorm {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K) : ℚ :=
  ∏ᶠ v : HeightOneSpectrum (Chapter08Integers K),
    (Ideal.absNorm v.asIdeal : ℚ) ^ (-chapter08FiniteIdeleOrder x v)

theorem chapter08_finite_idele_norm_product_formula
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K) :
    chapter08FiniteIdeleNorm x =
      (chapter08IdealNorm (chapter08FiniteIdeleIdealMap K x))⁻¹ := by
  sorry

def chapter08FiniteDegreeContribution {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K) : ℝ :=
  Real.log (chapter08IdealNorm (chapter08FiniteIdeleIdealMap K x) : ℝ)

theorem chapter08_finite_degree_contribution_eq_log_norm
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K) :
    chapter08FiniteDegreeContribution x =
      Real.log (chapter08IdealNorm (chapter08FiniteIdeleIdealMap K x) : ℝ) :=
  rfl

/-! Surjectivity is realized by local uniformizers at a finite set of places. -/

theorem chapter08_finite_idele_order_finsupp_surjective
    (K : Type*) [Field K] [NumberField K] :
    Function.Surjective (chapter08FiniteIdeleOrderFinsupp (K := K)) := by
  sorry

theorem chapter08_finite_idele_ideal_realizes_divisor
    (K : Type*) [Field K] [NumberField K]
    (d : Chapter08FiniteDivisors K) :
    ∃ x : Chapter08FiniteIdeles K,
      chapter08FiniteIdeleOrderFinsupp x = d := by
  exact chapter08_finite_idele_order_finsupp_surjective K d

def chapter08FinitePrincipalIdele {K : Type*} [Field K] [NumberField K]
    (a : Kˣ) : Chapter08FiniteIdeles K :=
  IsDedekindDomain.FiniteAdeleRing.unitEmbedding (Chapter08Integers K) K a

def chapter08FinitePrincipalIdeleHom (K : Type*) [Field K] [NumberField K] :
    Kˣ →* Chapter08FiniteIdeles K :=
  IsDedekindDomain.FiniteAdeleRing.unitEmbedding (Chapter08Integers K) K

theorem chapter08FinitePrincipalIdeleHom_apply
    {K : Type*} [Field K] [NumberField K] (a : Kˣ) :
    chapter08FinitePrincipalIdeleHom K a = chapter08FinitePrincipalIdele a :=
  rfl

theorem chapter08_finite_idele_ideal_principal
    {K : Type*} [Field K] [NumberField K]
    (a : Kˣ) :
    chapter08FiniteIdeleIdealMap K (chapter08FinitePrincipalIdele a) =
      toPrincipalIdeal (Chapter08Integers K) K a := by
  sorry

/-! The opposite convention used in some references is obtained by inversion. -/

def chapter08OppositeFiniteIdeleIdealMap
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K) : Chapter08IdealGroup K :=
  (chapter08FiniteIdeleIdealMap K x)⁻¹

theorem chapter08_opposite_finite_idele_ideal_count
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K)
    (v : HeightOneSpectrum (Chapter08Integers K)) :
    FractionalIdeal.count K v
        (chapter08OppositeFiniteIdeleIdealMap x : Chapter08FractionalIdeal K) =
      -chapter08FiniteIdeleOrder x v := by
  sorry

theorem chapter08_finite_idele_realization_need_not_be_global_principal
    (K : Type*) [Field K] [NumberField K]
    {I : Chapter08IdealGroup K}
    (hI : ClassGroup.mk K I ≠ 1) :
    ∀ a : Kˣ, chapter08FiniteIdeleIdealMap K
      (chapter08FinitePrincipalIdele a) ≠ I := by
  sorry

/-! Topological assertions are stated with the source's graph topology and discrete target. -/

theorem chapter08_finite_idele_ideal_continuous
    (K : Type*) [Field K] [NumberField K] :
    letI : TopologicalSpace (Chapter08FiniteIdeles K) :=
      chapter08FiniteIdeleGraphTopology K
    letI : TopologicalSpace (Chapter08IdealGroup K) := ⊥
    Continuous (chapter08FiniteIdeleIdealMap K) := by
  sorry

theorem chapter08_finite_idele_ideal_isOpenMap
    (K : Type*) [Field K] [NumberField K] :
    letI : TopologicalSpace (Chapter08FiniteIdeles K) :=
      chapter08FiniteIdeleGraphTopology K
    letI : TopologicalSpace (Chapter08IdealGroup K) := ⊥
    IsOpenMap (chapter08FiniteIdeleIdealMap K) := by
  sorry

theorem chapter08_ideal_group_has_discrete_topology
    (K : Type*) [Field K] [NumberField K] :
    @DiscreteTopology (Chapter08IdealGroup K) ⊥ := by
  exact discreteTopology_bot _

end

end LastLib.Book04AdelesAndIdeles.Chapter08
