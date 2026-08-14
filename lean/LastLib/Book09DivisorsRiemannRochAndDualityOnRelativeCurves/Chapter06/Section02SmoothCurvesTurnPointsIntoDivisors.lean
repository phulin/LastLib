import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter06.Section01TheCorrectRelativeNotion

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter06

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11
open RelativeScheme

universe u

/-! ## 6.2. Smooth curves turn points into divisors -/

abbrev Chapter06SmoothRelativeCurve {S : Scheme.{u}}
    (C : RelativeScheme S) : Prop :=
  SmoothOfRelativeDimension 1 C.structuralMap

instance chapter11SmoothQuasiProjectiveCurve_to_chapter06SmoothRelativeCurve
    {S : Scheme.{u}} {C : RelativeScheme S}
    [Chapter11SmoothQuasiProjectiveCurve C] :
    Chapter06SmoothRelativeCurve C :=
  Chapter11SmoothQuasiProjectiveCurve.smooth (C := C)

private theorem chapter06_locally_regular_principal_is_effective_cartier
    {X : Scheme.{u}} (I : Chapter06ClosedSubscheme X)
    (hI : Chapter10LocallyRegularPrincipal I) : I.IsEffectiveCartier := by
  intro U x
  rcases hI x.1 with ⟨W, hxW, a, hWa, ha⟩
  obtain ⟨f, g, hfg, hxf⟩ :=
    exists_basicOpen_le_affine_inter W.2 U.2 x.1 ⟨hxW, x.2⟩
  let V : X.affineOpens := X.affineBasicOpen f
  have hVW : V ≤ W := X.affineBasicOpen_le f
  have hVW' : V.1 ≤ W.1 := hVW
  have hVU : V ≤ U := by
    change X.basicOpen f ≤ U.1
    rw [hfg]
    exact X.basicOpen_le g
  let φ := (X.presheaf.map (homOfLE hVW').op).hom
  have hideal : I.ideal V = Ideal.span ({φ a} : Set Γ(X, V)) := by
    have hmap := I.map_ideal' (U := V) (V := W) (homOfLE hVW').op
    rw [← hmap, hWa]
    rw [Ideal.map_span]
    simp [φ]
  have hregular : IsRegular (φ a) := by
    let _ : Algebra Γ(X, W) Γ(X, V) :=
      (X.presheaf.map (homOfLE hVW').op).hom.toAlgebra
    let _ : IsLocalization.Away f Γ(X, V) :=
      W.2.isLocalization_of_eq_basicOpen f (homOfLE hVW') rfl
    change IsRegular (algebraMap Γ(X, W) Γ(X, V) a)
    apply (isRegular_iff_eq_zero_of_mul).2
    have hsmul : IsSMulRegular Γ(X, V) (algebraMap Γ(X, W) Γ(X, V) a) :=
      IsSMulRegular.of_isLocalization (R := Γ(X, W)) (S := Γ(X, V))
        (p := Submonoid.powers f) ha.isSMulRegular
    constructor
    · intro b hb
      exact hsmul (by simpa [Algebra.smul_def] using hb)
    · intro b hb
      exact hsmul (by simpa [Algebra.smul_def, mul_comm] using hb)
  refine ⟨V, φ a, hxf, hVU, hideal, ?_⟩
  exact isRegular_iff_mem_nonZeroDivisors.mp hregular

theorem chapter06_smooth_curve_finite_flat_family_is_cartier
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    [Chapter06SmoothRelativeCurve C]
    (Z : Chapter06FiniteFlatClosedFamily C T d) :
    ∃ D : Chapter06RelativeEffectiveDivisor C T d,
      D.divisor.ideal = Z.ideal := by
  rcases chapter10_smooth_curve_family_is_cartier C.structuralMap T.structuralMap d
      (chapter06FiniteFlatClosedFamilyAsChapter10Family C T d Z) with ⟨D, hD⟩
  refine ⟨⟨{ ideal := D.divisor.ideal,
              isEffectiveCartier :=
                chapter06_locally_regular_principal_is_effective_cartier
                  D.divisor.ideal D.divisor.locallyRegularPrincipal }, ?_⟩, hD⟩
  exact ⟨D.finiteLocallyFree.finite, D.finiteLocallyFree.flat,
    D.finiteLocallyFree.locallyOfFinitePresentation, D.finiteLocallyFree.rank⟩

noncomputable def chapter06FiniteFlatFamilyToRelativeDivisor
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    [Chapter06SmoothRelativeCurve C]
    (Z : Chapter06FiniteFlatClosedFamily C T d) :
    Chapter06RelativeEffectiveDivisor C T d :=
  Classical.choose (chapter06_smooth_curve_finite_flat_family_is_cartier C T d Z)

theorem chapter06FiniteFlatFamilyToRelativeDivisor_ideal
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    [Chapter06SmoothRelativeCurve C]
    (Z : Chapter06FiniteFlatClosedFamily C T d) :
    (chapter06FiniteFlatFamilyToRelativeDivisor C T d Z).divisor.ideal = Z.ideal :=
  Classical.choose_spec (chapter06_smooth_curve_finite_flat_family_is_cartier C T d Z)

def chapter06RelativeDivisorToFiniteFlatFamily
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    (D : Chapter06RelativeEffectiveDivisor C T d) :
    Chapter06FiniteFlatClosedFamily C T d :=
  { ideal := D.divisor.ideal
    finite_flat_rank := D.finite_flat_rank }

theorem chapter06RelativeDivisorToFiniteFlatFamily_ideal
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    (D : Chapter06RelativeEffectiveDivisor C T d) :
    (chapter06RelativeDivisorToFiniteFlatFamily C T d D).ideal = D.divisor.ideal :=
  rfl

theorem chapter06_relative_divisor_to_family_is_cartier
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    (D : Chapter06RelativeEffectiveDivisor C T d) :
    chapter06IsEffectiveCartierFamily
      (chapter06RelativeDivisorToFiniteFlatFamily C T d D) := by
  exact D.divisor.isEffectiveCartier

noncomputable def chapter06_length_d_family_divisor_equiv
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    [Chapter06SmoothRelativeCurve C] :
    Chapter06FiniteFlatClosedFamily C T d ≃
      Chapter06RelativeEffectiveDivisor C T d where
  toFun := chapter06FiniteFlatFamilyToRelativeDivisor C T d
  invFun := chapter06RelativeDivisorToFiniteFlatFamily C T d
  left_inv := by
    intro Z
    apply chapter06FiniteFlatClosedFamily_ext
    exact chapter06FiniteFlatFamilyToRelativeDivisor_ideal C T d Z
  right_inv := by
    intro D
    apply chapter06_relative_effective_divisor_ext
    exact (chapter06FiniteFlatFamilyToRelativeDivisor_ideal C T d
      (chapter06RelativeDivisorToFiniteFlatFamily C T d D)).trans
      (chapter06RelativeDivisorToFiniteFlatFamily_ideal C T d D)

theorem chapter06_smooth_curve_length_and_divisor_functors_agree
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    [Chapter06SmoothRelativeCurve C] :
    Nonempty (Chapter06FiniteFlatClosedFamily C T d ≃
      Chapter06RelativeEffectiveDivisor C T d) :=
  ⟨chapter06_length_d_family_divisor_equiv C T d⟩

theorem chapter06_smooth_curve_length_family_is_effective_cartier
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    [Chapter06SmoothRelativeCurve C]
    (Z : Chapter06FiniteFlatClosedFamily C T d) :
    ∃ D : Chapter06RelativeEffectiveDivisor C T d,
      D.divisor.ideal = Z.ideal ∧
        chapter06IsEffectiveCartierFamily Z := by
  rcases chapter06_smooth_curve_finite_flat_family_is_cartier C T d Z with ⟨D, hD⟩
  refine ⟨D, hD, ?_⟩
  simpa [chapter06IsEffectiveCartierFamily, hD] using D.divisor.isEffectiveCartier

/-!
The node model is written with the affine coordinate ring used by Book 8;
its localization/completion is the usual local ring `k[[x,y]]/(xy)`.  The
profile records both the finite-flat length-one quotient and failure of local
principality of its ideal.
-/

abbrev Chapter06NodeRing (k : Type u) [Field k] := chapter10NodeRing k

abbrev Chapter06NodeIdeal (k : Type u) [Field k] := chapter10NodeIdeal k

abbrev Chapter06NodePointLengthOneProfile (k : Type u) [Field k] :=
  Chapter10NodePointLengthOneProfile k

theorem chapter06_node_point_has_length_one
    (k : Type u) [Field k] :
    Chapter06NodePointLengthOneProfile k :=
  chapter10_node_point_has_length_one k

theorem chapter06_node_point_ideal_is_not_principal
    (k : Type u) [Field k] :
    ¬ ∃ a : Chapter06NodeRing k,
      Chapter06NodeIdeal k = Ideal.span ({a} : Set (Chapter06NodeRing k)) :=
  chapter10_node_ideal_is_not_principal k

/-!
Global nonprincipality is a useful affine warning, but Cartierness is a local
condition.  Localize at the complement of the node ideal so that the next
statement records the actual stalk obstruction rather than only its global
shadow.
-/
def chapter06NodePointComplement (k : Type u) [Field k] :
    Submonoid (Chapter06NodeRing k) where
  carrier := {a | a ∉ Chapter06NodeIdeal k}
  one_mem' := by
    intro h
    apply chapter10_node_ideal_is_not_principal k
    refine ⟨1, ?_⟩
    rw [Ideal.span_singleton_one]
    exact (Ideal.eq_top_iff_one (chapter10NodeIdeal k)).2 h
  mul_mem' := by sorry

abbrev Chapter06NodePointLocalRing (k : Type u) [Field k] :=
  Localization (chapter06NodePointComplement k)

def chapter06NodePointLocalIdeal (k : Type u) [Field k] :
    Ideal (Chapter06NodePointLocalRing k) :=
  Ideal.map (algebraMap (Chapter06NodeRing k) (Chapter06NodePointLocalRing k))
    (Chapter06NodeIdeal k)

def Chapter06NodePointCartierObstruction (k : Type u) [Field k] : Prop :=
  ¬ ∃ a : Chapter06NodePointLocalRing k,
    chapter06NodePointLocalIdeal k = Ideal.span ({a} : Set (Chapter06NodePointLocalRing k))

theorem chapter06_node_point_local_ideal_is_not_principal
    (k : Type u) [Field k] :
    Chapter06NodePointCartierObstruction k := by
  sorry

theorem chapter06_node_point_is_length_one_but_not_cartier
    (k : Type u) [Field k] :
    Chapter06NodePointLengthOneProfile k ∧
      Chapter06NodePointCartierObstruction k :=
  ⟨chapter06_node_point_has_length_one k,
    chapter06_node_point_local_ideal_is_not_principal k⟩

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter06
