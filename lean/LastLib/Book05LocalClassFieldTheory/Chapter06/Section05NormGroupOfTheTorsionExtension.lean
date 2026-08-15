import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import LastLib.Book05LocalClassFieldTheory.Chapter06.Section04GaloisActionOnTorsion

namespace LastLib.Book05LocalClassFieldTheory.Chapter06

noncomputable section

open scoped BigOperators Interval

/-!
### 6.5. The norm group of the torsion extension
-/

theorem chapter06_finite_residue_norm_surjective
    (k l : Type*) [Field k] [Field l] [Algebra k l] [Finite l] :
    Function.Surjective (Algebra.norm k (S := l)) := by
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11_finite_residue_norm_surjective
    k l

theorem chapter06_finite_residue_trace_surjective
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l] [Algebra.IsSeparable k l] :
    Function.Surjective (Algebra.trace k l) := by
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11_unramified_residue_trace_surjective
    k l

/-- The image of a subgroup of extension units under the multiplicative norm. -/
def chapter06NormImageOfUnitSubgroup
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (U : Subgroup Lˣ) : Subgroup Kˣ :=
  Subgroup.map
    (LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05NormMap K L) U

/-- The filtration subgroup `N(U_L⁰) U_Kᵐ`. -/
def chapter06NormFiltrationSubgroup
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (baseUnits : ℕ → Subgroup Kˣ) (extensionUnits : ℕ → Subgroup Lˣ)
    (m : ℕ) : Subgroup Kˣ :=
  chapter06NormImageOfUnitSubgroup (extensionUnits 0) ⊔ baseUnits m

/-- The lower ramification displacement of an automorphism. -/
def chapter06RamificationDisplacement
    {L : Type*} [Field L]
    (vL : AddValuation L (WithTop ℤ)) (πL : L)
    (σ : L ≃+* L) : WithTop ℤ :=
  vL (σ πL - πL)

/-- The Herbrand integral in the convention used by the source. -/
noncomputable def chapter06HerbrandPhi
    {G : Type*} [CommGroup G] [Fintype G]
    (lower : ℝ → Subgroup G) (u : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..u,
    (Nat.card ((lower 0 : Type _) ⧸
      ((lower 0 ⊓ lower t).comap (lower 0).subtype)) : ℝ)⁻¹

/-- The inverse function used to define upper numbering. -/
noncomputable def chapter06HerbrandPsi
    {G : Type*} [CommGroup G] [Fintype G]
    (lower : ℝ → Subgroup G) : ℝ → ℝ :=
  Function.invFun (chapter06HerbrandPhi lower)

/-- The upper-numbered group attached to lower-numbered groups. -/
def chapter06UpperRamificationGroup
    {G : Type*} [CommGroup G] [Fintype G]
    (lower : ℝ → Subgroup G) (upper : ℝ → ℝ → Subgroup G)
    (s : ℝ) : Subgroup G :=
  upper s (chapter06HerbrandPsi lower s)

/-- The precise Herbrand/Hasse--Arf package used in Lemma 6.4. -/
structure Chapter06HerbrandData
    (G : Type*) [CommGroup G] [Fintype G] where
  lower : ℝ → Subgroup G
  lower_mono : ∀ s t, s ≤ t → lower t ≤ lower s
  lower_at_nonintegral : ∀ t, lower t = lower (Int.ceil t)
  phi : ℝ → ℝ
  phi_eq_integral : ∀ u, phi u = chapter06HerbrandPhi lower u
  psi : ℝ → ℝ
  phi_psi : Function.LeftInverse phi psi
  psi_phi : Function.LeftInverse psi phi
  upper : ℝ → Subgroup G
  upper_eq : ∀ s, upper s = lower (psi s)
  upper_breaks : Set ℝ
  upper_break_integer : ∀ s, s ∈ upper_breaks → ∃ z : ℤ, s = z

/-- The norm-filtration equality in Lemma 6.4. -/
theorem chapter06_norm_filtration_index_formula
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))] [Chapter06FiniteAbelianExtension K L]
    (baseUnits : ℕ → Subgroup Kˣ)
    (extensionUnits : ℕ → Subgroup Lˣ)
    (R : Chapter06HerbrandData (Gal(L / K)))
    (m : ℕ)
    (hzero : chapter06NormFiltrationSubgroup baseUnits extensionUnits m ≤
      baseUnits 0) :
    Nat.card (baseUnits 0 ⧸
      (chapter06NormFiltrationSubgroup baseUnits extensionUnits m).comap
        (baseUnits 0).subtype) =
      Nat.card ((R.upper 0 : Type _) ⧸
        ((R.upper 0 ⊓ R.upper m).comap (R.upper 0).subtype)) := by
  sorry

/-- The usable, source-facing form of the preceding index identity. -/
theorem chapter06_norm_filtration_index_formula_source_form
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))] [Chapter06FiniteAbelianExtension K L]
    (baseUnits : ℕ → Subgroup Kˣ)
    (extensionUnits : ℕ → Subgroup Lˣ)
    (R : Chapter06HerbrandData (Gal(L / K)))
    (m : ℕ)
    (hzero : chapter06NormFiltrationSubgroup baseUnits extensionUnits m ≤
      baseUnits 0) :
    Nat.card (baseUnits 0 ⧸
      (chapter06NormFiltrationSubgroup baseUnits extensionUnits m).comap
        (baseUnits 0).subtype) =
      Nat.card ((R.upper 0 : Type _) ⧸
        ((R.upper 0 ⊓ R.upper m).comap (R.upper 0).subtype)) := by
  sorry

/-- At a positive lower break the ramification quotient has additive residue
coordinates; at zero it has multiplicative residue coordinates. -/
def chapter06RamificationLayer
    {G : Type*} [CommGroup G] (ramification : ℕ → Subgroup G) (b : ℕ) : Type _ := by
  letI : ((ramification b ⊓ ramification (b + 1)).comap
      (ramification b).subtype).Normal := by infer_instance
  exact (ramification b : Type _) ⧸
    ((ramification b ⊓ ramification (b + 1)).comap (ramification b).subtype)

instance chapter06RamificationLayer.commGroup
    {G : Type*} [CommGroup G] (ramification : ℕ → Subgroup G) (b : ℕ) :
    CommGroup (chapter06RamificationLayer ramification b) := by
  unfold chapter06RamificationLayer
  letI : ((ramification b ⊓ ramification (b + 1)).comap
      (ramification b).subtype).Normal := by infer_instance
  infer_instance

structure Chapter06AdditiveLayerMap
    (α l : Type*) [Mul α] [Add l] where
  toFun : α → l
  map_mul' : ∀ x y, toFun (x * y) = toFun x + toFun y

instance chapter06AdditiveLayerMap.coeFun
    {α l : Type*} [Mul α] [Add l] : CoeFun (Chapter06AdditiveLayerMap α l)
      (fun _ => α → l) :=
  ⟨Chapter06AdditiveLayerMap.toFun⟩

structure Chapter06RamificationLayerCoordinates
    (G : Type*) [CommGroup G] [Fintype G] (l : Type*) [Field l] where
  ramification : ℕ → Subgroup G
  tame : chapter06RamificationLayer ramification 0 →* lˣ
  tame_injective : Function.Injective tame
  positive : ∀ b : ℕ,
    Chapter06AdditiveLayerMap (chapter06RamificationLayer ramification b) l
  positive_injective : ∀ b, Function.Injective (positive b)

theorem chapter06_ramification_layer_coordinates_exist
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))] [Chapter06FiniteAbelianExtension K L]
    (vL : AddValuation L (WithTop ℤ)) (πL : L)
    (l : Type*) [Field l] [Finite l] :
    Nonempty (Chapter06RamificationLayerCoordinates (Gal(L / K)) l) := by
  sorry

/-- The additive polynomial associated to a finite additive subgroup. -/
def chapter06AdditiveLayerPolynomial
    {l : Type*} [Field l] (C : AddSubgroup l) [Fintype C] : Polynomial l :=
  ∏ c : C, (Polynomial.X + Polynomial.C (c : l))

theorem chapter06_additive_layer_polynomial_additive
    {l : Type*} [Field l] (C : AddSubgroup l) [Fintype C] :
    ∀ x y : l,
      (chapter06AdditiveLayerPolynomial C).eval (x + y) =
        (chapter06AdditiveLayerPolynomial C).eval x +
          (chapter06AdditiveLayerPolynomial C).eval y := by
  sorry

theorem chapter06_additive_layer_polynomial_kernel
    {l : Type*} [Field l] (C : AddSubgroup l) [Fintype C] (x : l) :
    (chapter06AdditiveLayerPolynomial C).eval x = 0 ↔ x ∈ C := by
  sorry

theorem chapter06_additive_layer_polynomial_image_index
    {l : Type*} [Field l] [Finite l] (C : AddSubgroup l) [Fintype C] :
    Nat.card l / Nat.card (Set.range (chapter06AdditiveLayerPolynomial C).eval) =
      Nat.card C := by
  sorry

/-- The tame residue layer is, up to nonzero scalars, a power map. -/
def chapter06TameResiduePowerMap
    {l : Type*} [Field l] (d : ℕ) : lˣ →* lˣ where
  toFun u := u ^ d
  map_one' := by simp
  map_mul' u v := by simp [mul_pow]

theorem chapter06_tame_residue_layer_image_index
    {l : Type*} [Field l] [Fintype l] (d : ℕ) :
    Nat.card (lˣ ⧸ Subgroup.map (chapter06TameResiduePowerMap d) ⊤) =
      Nat.gcd d (Fintype.card l - 1) := by
  sorry

theorem chapter06_frobenius_layer_normalization
    {k l : Type*} [Field k] [Field l] [Algebra k l]
    [Fintype k] [Fintype l] (lambda : lˣ)
    (hlambda : lambda ^ ((Fintype.card l - 1) / (Fintype.card k - 1)) = 1) :
    ∃ μ : lˣ, lambda = μ ^ (Fintype.card k - 1) := by
  sorry

theorem chapter06_abelian_upper_breaks_are_integral
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))] [Chapter06FiniteAbelianExtension K L]
    (R : Chapter06HerbrandData (Gal(L / K))) :
    ∀ s, s ∈ R.upper_breaks → ∃ z : ℤ, s = z := by
  exact R.upper_break_integer

theorem chapter06_deep_units_are_norms
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))] [Chapter06FiniteAbelianExtension K L]
    (baseUnits : ℕ → Subgroup Kˣ)
    (extensionUnits : ℕ → Subgroup Lˣ)
    (R : Chapter06HerbrandData (Gal(L / K))) (m : ℕ)
    (htrivial : R.upper m = ⊥) :
    baseUnits m ≤ chapter06NormImageOfUnitSubgroup (extensionUnits 0) := by
  sorry

theorem chapter06_torsion_norm_of_primitive_point_regular_case
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (n : ℕ) (hn : 0 < n)
    (ω : Chapter06PrimitiveTorsionPoint D n hn)
    [FiniteDimensional K (chapter06TorsionField D n ω.point)]
    (hdegree : Even
      (chapter06ResidueCardinality D ^ (n - 1) *
        (chapter06ResidueCardinality D - 1))) :
    Algebra.norm K (chapter06PrimitivePointInField D n hn ω) =
      (chapter06UniformizerUnit D : K) := by
  sorry

/-- At level one with even residue cardinality, the primitive division
polynomial has odd degree, so the primitive point has norm `-π`. -/
theorem chapter06_torsion_norm_of_primitive_point_exceptional_case
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (ω : Chapter06PrimitiveTorsionPoint D 1 (by decide))
    [FiniteDimensional K (chapter06TorsionField D 1 ω.point)]
    (hq_even : Even (chapter06ResidueCardinality D)) :
    Algebra.norm K (chapter06PrimitivePointInField D 1 (by decide) ω) =
        -(chapter06UniformizerUnit D : K) ∧
      Algebra.norm K
          (-chapter06PrimitivePointInField D 1 (by decide) ω) =
        (chapter06UniformizerUnit D : K) := by
  sorry

theorem chapter06_torsion_uniformizer_norm_witness
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (n : ℕ) (hn : 0 < n)
    (ω : Chapter06PrimitiveTorsionPoint D n hn)
    [FiniteDimensional K (chapter06TorsionField D n ω.point)] :
    ∃ y : chapter06TorsionField D n ω.point,
      Algebra.norm K y = (chapter06UniformizerUnit D : K) := by
  sorry

theorem chapter06_lemma_6_4
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))] [Chapter06FiniteAbelianExtension K L]
    (baseUnits : ℕ → Subgroup Kˣ)
    (extensionUnits : ℕ → Subgroup Lˣ)
    (R : Chapter06HerbrandData (Gal(L / K)))
    (m : ℕ)
    (hzero : chapter06NormFiltrationSubgroup baseUnits extensionUnits m ≤
      baseUnits 0) :
    Nat.card (baseUnits 0 ⧸
      (chapter06NormFiltrationSubgroup baseUnits extensionUnits m).comap
        (baseUnits 0).subtype) =
        Nat.card ((R.upper 0 : Type _) ⧸
          ((R.upper 0 ⊓ R.upper m).comap (R.upper 0).subtype)) ∧
      (∀ s, s ∈ R.upper_breaks → ∃ z : ℤ, s = z) ∧
      (∀ j : ℕ, R.upper j = ⊥ →
        baseUnits j ≤ chapter06NormImageOfUnitSubgroup (extensionUnits 0)) := by
  refine ⟨chapter06_norm_filtration_index_formula baseUnits extensionUnits R m hzero,
    chapter06_abelian_upper_breaks_are_integral R, ?_⟩
  intro j hj
  exact chapter06_deep_units_are_norms baseUnits extensionUnits R j hj

/-- The lower breaks predicted by the explicit torsion calculation. -/
def chapter06TorsionLowerBreak
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (r : ℕ) : ℕ :=
  chapter06ResidueCardinality D ^ r - 1

theorem chapter06_torsion_difference_valuation
    {K : Type*} [Field K] [UniformSpace (AlgebraicClosure K)]
    (D : Chapter06LocalFieldData K)
    [UniformSpace (Chapter06ValuationRing D)]
    (n : ℕ) (hn : 0 < n)
    (f : Chapter06UnivariateSeries (Chapter06ValuationRing D))
    (hf : chapter06LubinTateCondition D f)
    (M : Chapter06FormalModuleData D f)
    (A : Chapter06TorsionAction D f n hn M)
    (ω : Chapter06PrimitiveTorsionPoint D n hn)
    [FiniteDimensional K (chapter06TorsionField D n ω.point)]
    (V : Chapter06ValuedFiniteExtension D
      (chapter06TorsionField D n ω.point))
    (r : ℕ) (hr : 1 ≤ r) (hrn : r < n)
    (a : Chapter06ValuationRing D)
    (ha : a - 1 ∈
      (IsLocalRing.maximalIdeal (Chapter06ValuationRing D)) ^ r)
    (ha_next : a - 1 ∉
      (IsLocalRing.maximalIdeal (Chapter06ValuationRing D)) ^ (r + 1)) :
    V.valuation
        (((⟨(A.action a (chapter06PrimitivePointAsTorsion D n hn ω)).1,
          by sorry⟩ :
          chapter06TorsionField D n ω.point) :
          chapter06TorsionField D n ω.point) -
          chapter06PrimitivePointInField D n hn ω) =
      chapter06ResidueCardinality D ^ r := by
  sorry

/- The interval profile is the exact finite calculation needed to turn the
   lower breaks `q^j - 1` into the upper labels `j`.  It is stated as a
   reusable ramification interface rather than assuming the resulting value
   of the Herbrand function. -/
structure Chapter06TorsionHerbrandIntervalData
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    [Chapter06FiniteAbelianExtension K L]
    (D : Chapter06LocalFieldData K)
    (R : Chapter06HerbrandData (Gal(L / K))) (r : ℕ) where
  positive : 0 < r
  interval_index : ∀ j : ℕ, 1 ≤ j → j ≤ r →
    ∀ t : ℝ,
      (chapter06TorsionLowerBreak D (j - 1) : ℝ) ≤ t →
      t < chapter06TorsionLowerBreak D j →
      Nat.card ((R.lower 0 : Type _) ⧸
        ((R.lower 0 ⊓ R.lower t).comap (R.lower 0).subtype)) =
        chapter06ResidueCardinality D ^ (j - 1) *
          (chapter06ResidueCardinality D - 1)

theorem chapter06_torsion_herbrand_break
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))] [Chapter06FiniteAbelianExtension K L]
    (D : Chapter06LocalFieldData K)
    (R : Chapter06HerbrandData (Gal(L / K))) (r : ℕ)
    (I : Chapter06TorsionHerbrandIntervalData D R r) :
    R.phi (chapter06TorsionLowerBreak D r) = r := by
  sorry

/- The exact identification `G^r = {σ_a : a ∈ U^r/U^n}` is recorded as a
ramification-profile interface so that the later norm argument consumes the
computed upper groups rather than assuming the desired norm equality. -/
structure Chapter06TorsionRamificationProfile
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))] [Chapter06FiniteAbelianExtension K L] where
  base : Chapter06LocalFieldData K
  level : ℕ
  herbrand : Chapter06HerbrandData (Gal(L / K))
  upper_principal : ∀ r, r ≤ level →
    Nonempty
      (((Chapter06UnitFiltration base r : Type _) ⧸
          (Chapter06UnitFiltration base level).comap
            (Chapter06UnitFiltration base r).subtype) ≃*
        herbrand.upper r)
  terminal : herbrand.upper level = ⊥

theorem chapter06_torsion_deep_units_are_norms
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (n : ℕ) (hn : 0 < n)
    (ω : Chapter06PrimitiveTorsionPoint D n hn)
    [FiniteDimensional K (chapter06TorsionField D n ω.point)]
    [IsGalois K (chapter06TorsionField D n ω.point)]
    [Fintype (Gal(chapter06TorsionField D n ω.point / K))]
    [Chapter06FiniteAbelianExtension K (chapter06TorsionField D n ω.point)] :
    Chapter06UnitFiltration D n ≤
      chapter06NormSubgroup K (chapter06TorsionField D n ω.point) := by
  sorry

theorem chapter06_torsion_uniformizer_is_norm
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (n : ℕ) (hn : 0 < n)
    (ω : Chapter06PrimitiveTorsionPoint D n hn)
    [FiniteDimensional K (chapter06TorsionField D n ω.point)] :
    chapter06UniformizerUnit D ∈
      chapter06NormSubgroup K (chapter06TorsionField D n ω.point) := by
  sorry

theorem chapter06_torsion_norm_index_eq_degree
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (n : ℕ) (hn : 0 < n)
    (ω : Chapter06PrimitiveTorsionPoint D n hn)
    [FiniteDimensional K (chapter06TorsionField D n ω.point)]
    [IsGalois K (chapter06TorsionField D n ω.point)]
    [Fintype (Gal(chapter06TorsionField D n ω.point / K))]
    [CommGroup (Gal(chapter06TorsionField D n ω.point / K))]
    [Finite (Kˣ ⧸ chapter06NormSubgroup K
      (chapter06TorsionField D n ω.point))] :
    Nat.card (Kˣ ⧸ chapter06NormSubgroup K
      (chapter06TorsionField D n ω.point)) =
      Module.finrank K (chapter06TorsionField D n ω.point) := by
  sorry

theorem chapter06_torsion_precision_index_eq_degree
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (n : ℕ) (hn : 0 < n)
    (ω : Chapter06PrimitiveTorsionPoint D n hn)
    [FiniteDimensional K (chapter06TorsionField D n ω.point)] :
    Nat.card (Kˣ ⧸ chapter06PrecisionSubgroup D 1 n) =
      Module.finrank K (chapter06TorsionField D n ω.point) := by
  sorry

theorem chapter06_torsion_norm_group
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (n : ℕ) (hn : 0 < n)
    (ω : Chapter06PrimitiveTorsionPoint D n hn)
    [FiniteDimensional K (chapter06TorsionField D n ω.point)]
    [IsGalois K (chapter06TorsionField D n ω.point)]
    [Fintype (Gal(chapter06TorsionField D n ω.point / K))]
    [CommGroup (Gal(chapter06TorsionField D n ω.point / K))]
    [Finite (Kˣ ⧸ chapter06NormSubgroup K
      (chapter06TorsionField D n ω.point))]
    (hdeep : Chapter06UnitFiltration D n ≤
      chapter06NormSubgroup K (chapter06TorsionField D n ω.point))
    (hπ : chapter06UniformizerUnit D ∈
      chapter06NormSubgroup K (chapter06TorsionField D n ω.point)) :
    chapter06NormSubgroup K (chapter06TorsionField D n ω.point) =
      chapter06PrecisionSubgroup D 1 n := by
  sorry

theorem chapter06_torsion_norm_group_exact
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (n : ℕ) (hn : 0 < n)
    (ω : Chapter06PrimitiveTorsionPoint D n hn)
    [FiniteDimensional K (chapter06TorsionField D n ω.point)]
    [IsGalois K (chapter06TorsionField D n ω.point)]
    [Fintype (Gal(chapter06TorsionField D n ω.point / K))]
    [CommGroup (Gal(chapter06TorsionField D n ω.point / K))]
    [Finite (Kˣ ⧸ chapter06NormSubgroup K
      (chapter06TorsionField D n ω.point))]
    [Chapter06FiniteAbelianExtension K
      (chapter06TorsionField D n ω.point)] :
    chapter06NormSubgroup K (chapter06TorsionField D n ω.point) =
      chapter06PrecisionSubgroup D 1 n := by
  exact chapter06_torsion_norm_group D n hn ω
    (chapter06_torsion_deep_units_are_norms D n hn ω)
    (chapter06_torsion_uniformizer_is_norm D n hn ω)

end

end LastLib.Book05LocalClassFieldTheory.Chapter06
