import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter02.Section02GeneratorsRelationsAndSymmetricAlgebra

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter02

universe u v

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped BigOperators TensorProduct
open Polynomial

/-! ## 2.3. Localization, powers, and integral closure -/

/-- The extension of an ideal along a ring map. -/
def chapter02LocalizedIdeal
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) : Ideal S :=
  Ideal.map (algebraMap R S) I

/-- The Rees algebra of the extended ideal. -/
abbrev chapter02LocalizedReesAlgebra
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) : Subalgebra S (Polynomial S) :=
  reesAlgebra (chapter02LocalizedIdeal I)

/-- The image of the localization denominators in the Rees algebra. -/
def chapter02ReesLocalizationSubmonoid
    {R : Type u} [CommRing R] (I : Ideal R) (W : Submonoid R) :
    Submonoid (Chapter02ReesAlgebra R I) :=
  W.map (algebraMap R (Chapter02ReesAlgebra R I)).toMonoidHom

structure Chapter02ReesLocalizationData
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (W : Submonoid R) where
  equivalence :
    Localization (chapter02ReesLocalizationSubmonoid I W)
        ≃+*
      chapter02LocalizedReesAlgebra (S := S) I
  /-- The equivalence is the coefficientwise localization map, rather than an unrelated
      isomorphism of rings. -/
  equivalence_on_rees :
    ∀ p : Chapter02ReesAlgebra R I,
      ((equivalence
          (algebraMap (Chapter02ReesAlgebra R I)
            (Localization (chapter02ReesLocalizationSubmonoid I W)) p) :
        chapter02LocalizedReesAlgebra (S := S) I) : Polynomial S) =
        p.1.map (algebraMap R S)

/- LOCAL_DEPENDENCY_GUESS: localization of the Rees algebra commutes with extension of the ideal; the coefficientwise map of powers is the proof route. -/
theorem chapter02_rees_localization_exists
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (W : Submonoid R) [IsLocalization W S] :
    Nonempty (Chapter02ReesLocalizationData (S := S) I W) := by
  sorry

noncomputable def chapter02ReesLocalizationDataOf
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (W : Submonoid R) [IsLocalization W S] :
    Chapter02ReesLocalizationData (S := S) I W :=
  Classical.choice (chapter02_rees_localization_exists I W)

theorem chapter02_localized_ideal_pow
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (n : ℕ) :
    Ideal.map (algebraMap R S) (I ^ n) =
      chapter02LocalizedIdeal (S := S) I ^ n := by
  exact Ideal.map_pow (algebraMap R S) I n

theorem chapter02_localized_ideal_mul
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I J : Ideal R) :
    Ideal.map (algebraMap R S) (I * J) =
      chapter02LocalizedIdeal (S := S) I * chapter02LocalizedIdeal (S := S) J := by
  exact Ideal.map_mul (algebraMap R S) I J

noncomputable def chapter02LocalizedReesProj
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) : Scheme.{u} :=
  chapter02ReesProj (chapter02LocalizedIdeal (S := S) I)

/-- The canonical affine base map of the Rees relative Proj. -/
noncomputable def chapter02ReesProjToSpec
    {R : Type u} [CommRing R] (I : Ideal R) :
    chapter02ReesProj I ⟶ AlgebraicGeometry.Spec (CommRingCat.of R) := by
  let G := chapter02ReesGradingData I
  letI := G.graded
  exact AlgebraicGeometry.Proj.toSpecZero G.component ≫
    AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom G.degreeZeroEquiv.toRingHom)

/-- The base change of the Rees relative Proj along a coefficient-ring map. -/
noncomputable def chapter02ReesProjBaseChange
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) : Scheme.{u} :=
  pullback (chapter02ReesProjToSpec I)
    (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R S)))

structure Chapter02BlowupLocalityData
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (W : Submonoid R) [IsLocalization W S] where
  reesAlgebra : Chapter02ReesLocalizationData (S := S) I W
  projectiveIso :
    chapter02ReesProjBaseChange (S := S) I ≅ chapter02LocalizedReesProj (S := S) I
  projectiveIso_over :
    projectiveIso.hom ≫
        chapter02ReesProjToSpec (R := S) (chapter02LocalizedIdeal (S := S) I) =
      pullback.snd (chapter02ReesProjToSpec I)
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R S)))

/- LOCAL_DEPENDENCY_GUESS: localization of the Rees algebra and relative Proj commute for this
  affine localization. -/
theorem chapter02_blowup_is_local_on_target
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (W : Submonoid R) [IsLocalization W S] :
    Nonempty (Chapter02BlowupLocalityData (S := S) I W) := by
  sorry

/-! ### Flat base change and its limits -/

/- The degreewise comparison records the canonical tensor-to-extension map on pure tensors. -/
def Chapter02PowerBaseChangeComparison
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (n : ℕ) : Prop :=
  ∃ e : S ⊗[R] (I ^ n : Submodule R R) ≃ₗ[S]
      (chapter02LocalizedIdeal (S := S) I ^ n : Submodule S S),
    ∀ (s : S) (r : (I ^ n : Submodule R R)),
      ((e (s ⊗ₜ[R] r) : (chapter02LocalizedIdeal (S := S) I ^ n :
        Submodule S S)) : S) = s * algebraMap R S (r : R)

def Chapter02AllPowersBaseChangeComparison
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) : Prop :=
  ∀ n : ℕ, Chapter02PowerBaseChangeComparison (S := S) I n

/- Without flatness the canonical degreewise tensor comparisons can fail because tensoring creates
   torsion. -/
def Chapter02ArbitraryBaseChangeMayHavePowerTorsion
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) : Prop :=
  ¬ Chapter02AllPowersBaseChangeComparison (S := S) I

/- LOCAL_DEPENDENCY_GUESS: flatness makes every degreewise tensor comparison an isomorphism. -/
theorem chapter02_flat_base_change_has_power_comparisons
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) [Module.Flat R S] :
    Chapter02AllPowersBaseChangeComparison (S := S) I := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the degreewise flat Rees comparison induces the corresponding relative
Proj base-change isomorphism. -/
theorem chapter02_rees_proj_flat_base_change
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) [Module.Flat R S] :
    Nonempty (chapter02ReesProjBaseChange (S := S) I ≅
      chapter02LocalizedReesProj (S := S) I) := by
  sorry

/-- The integral-closure ideal detected by the degree-`n` homogeneous elements. -/
def chapter02IntegralClosurePower
    {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) : Ideal R where
  carrier := {r : R |
    Polynomial.monomial n r ∈
      integralClosure (Chapter02ReesAlgebra R I) (Polynomial R)}
  zero_mem' := by
    simp
  add_mem' := by
    intro r s hr hs
    change Polynomial.monomial n (r + s) ∈
      integralClosure (Chapter02ReesAlgebra R I) (Polynomial R)
    change Polynomial.monomial n r ∈
      integralClosure (Chapter02ReesAlgebra R I) (Polynomial R) at hr
    change Polynomial.monomial n s ∈
      integralClosure (Chapter02ReesAlgebra R I) (Polynomial R) at hs
    simpa using
      (integralClosure (Chapter02ReesAlgebra R I) (Polynomial R)).add_mem hr hs
  smul_mem' := by
    intro a r hr
    change Polynomial.monomial n (a * r) ∈
      integralClosure (Chapter02ReesAlgebra R I) (Polynomial R)
    change Polynomial.monomial n r ∈
      integralClosure (Chapter02ReesAlgebra R I) (Polynomial R) at hr
    have ha : Polynomial.C a ∈
        integralClosure (Chapter02ReesAlgebra R I) (Polynomial R) := by
      have h :=
        (integralClosure (Chapter02ReesAlgebra R I) (Polynomial R)).algebraMap_mem
          (algebraMap R (Chapter02ReesAlgebra R I) a)
      simpa using
        h
    simpa [Polynomial.C_mul_monomial] using
      (integralClosure (Chapter02ReesAlgebra R I) (Polynomial R)).mul_mem ha hr

abbrev chapter02IntegralClosureIdeal
    {R : Type u} [CommRing R] (I : Ideal R) : Ideal R :=
  chapter02IntegralClosurePower I 1

abbrev chapter02IdealIntegralClosure
    {R : Type u} [CommRing R] (J : Ideal R) : Ideal R :=
  chapter02IntegralClosureIdeal J

theorem chapter02_integral_closure_power_mem_iff
    {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) (r : R) :
    r ∈ chapter02IntegralClosurePower I n ↔
      Polynomial.monomial n r ∈
        integralClosure (Chapter02ReesAlgebra R I) (Polynomial R) := by
  rfl

/- LOCAL_DEPENDENCY_GUESS: over a normal domain, the degree-`n` integral-closure piece agrees
with the ordinary integral closure of the ideal power `I^n`. -/
theorem chapter02_normal_domain_integral_closure_power_eq
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (I : Ideal R) {n : ℕ} (hn : 0 < n) :
    chapter02IntegralClosurePower I n =
      chapter02IdealIntegralClosure (I ^ n) := by
  sorry

private theorem chapter02_integral_closure_power_mul_mem
    {R : Type u} [CommRing R] (I : Ideal R) (m n : ℕ) {r s : R}
    (hr : r ∈ chapter02IntegralClosurePower I m)
    (hs : s ∈ chapter02IntegralClosurePower I n) :
    r * s ∈ chapter02IntegralClosurePower I (m + n) := by
  change Polynomial.monomial m r ∈
    integralClosure (Chapter02ReesAlgebra R I) (Polynomial R) at hr
  change Polynomial.monomial n s ∈
    integralClosure (Chapter02ReesAlgebra R I) (Polynomial R) at hs
  change Polynomial.monomial (m + n) (r * s) ∈
    integralClosure (Chapter02ReesAlgebra R I) (Polynomial R)
  simpa [Polynomial.monomial_mul_monomial] using
    (integralClosure (Chapter02ReesAlgebra R I) (Polynomial R)).mul_mem hr hs

def chapter02NormalizedReesAlgebra
    {R : Type u} [CommRing R] (I : Ideal R) : Subalgebra R (Polynomial R) where
  carrier := {p | ∀ n, p.coeff n ∈ chapter02IntegralClosurePower I n}
  zero_mem' := by
    intro n
    exact (chapter02IntegralClosurePower I n).zero_mem
  add_mem' := by
    intro p q hp hq n
    exact (chapter02IntegralClosurePower I n).add_mem (hp n) (hq n)
  mul_mem' := by
    intro p q hp hq n
    rw [Polynomial.coeff_mul]
    apply Ideal.sum_mem
    rintro ⟨j, k⟩ hjk
    rw [← Finset.mem_antidiagonal.mp hjk]
    exact chapter02_integral_closure_power_mul_mem I j k (hp j) (hq k)
  one_mem' := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp [chapter02IntegralClosurePower]
    · simp [Polynomial.coeff_one, hn]
  algebraMap_mem' := by
    intro r n
    by_cases hn : n = 0
    · subst n
      change Polynomial.monomial 0
          (((algebraMap R (Polynomial R)) r).coeff 0) ∈
        integralClosure (Chapter02ReesAlgebra R I) (Polynomial R)
      have h :=
        (integralClosure (Chapter02ReesAlgebra R I) (Polynomial R)).algebraMap_mem
          (algebraMap R (Chapter02ReesAlgebra R I) r)
      simpa using h
    · simp [Polynomial.coeff_C, hn, chapter02IntegralClosurePower]

theorem chapter02_rees_le_normalized_rees
    {R : Type u} [CommRing R] (I : Ideal R) :
    Chapter02ReesAlgebra R I ≤ chapter02NormalizedReesAlgebra I := by
  intro p hp
  change ∀ n, p.1.coeff n ∈ chapter02IntegralClosurePower I n
  intro n
  change Polynomial.monomial n (p.1.coeff n) ∈
    integralClosure (Chapter02ReesAlgebra R I) (Polynomial R)
  have hmon : Polynomial.monomial n (p.1.coeff n) ∈
      Chapter02ReesAlgebra R I := by
    exact (chapter02_rees_monomial_mem_iff I n (p.1.coeff n)).2 (hp n)
  have h :=
    (integralClosure (Chapter02ReesAlgebra R I) (Polynomial R)).algebraMap_mem
      (⟨Polynomial.monomial n (p.1.coeff n), hmon⟩ : Chapter02ReesAlgebra R I)
  simpa using h

theorem chapter02_normalized_rees_monomial_mem_iff
    {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) (r : R) :
    Polynomial.monomial n r ∈ chapter02NormalizedReesAlgebra I ↔
      r ∈ chapter02IntegralClosurePower I n := by
  change (∀ j, (Polynomial.monomial n r).coeff j ∈
      chapter02IntegralClosurePower I j) ↔
    r ∈ chapter02IntegralClosurePower I n
  constructor
  · intro h
    simpa using h n
  · intro hr j
    by_cases hj : j = n
    · subst j
      simpa using hr
    · simp [Polynomial.coeff_monomial, Ne.symm hj]

def chapter02NormalizedReesHomogeneous
    {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ)
    (p : chapter02NormalizedReesAlgebra I) : Prop :=
  ∀ j, j ≠ n → p.1.coeff j = 0

structure Chapter02NormalizedReesGradingData
    {R : Type u} [CommRing R] (I : Ideal R) where
  component : ℕ → Submodule R (chapter02NormalizedReesAlgebra I)
  graded : GradedAlgebra component
  component_spec :
    ∀ n (p : chapter02NormalizedReesAlgebra I),
      p ∈ component n ↔ chapter02NormalizedReesHomogeneous I n p
  degreeZeroEquiv : R ≃+* component 0
  degreeZeroEquiv_algebraMap :
    ∀ r, algebraMap R (chapter02NormalizedReesAlgebra I) r =
      (degreeZeroEquiv r : chapter02NormalizedReesAlgebra I)

/- LOCAL_DEPENDENCY_GUESS: the homogeneous pieces of the integral closure form the normalized Rees algebra grading. -/
theorem chapter02_normalized_rees_grading_exists
    {R : Type u} [CommRing R] (I : Ideal R) :
    Nonempty (Chapter02NormalizedReesGradingData I) := by
  classical
  let component : ℕ → Submodule R (chapter02NormalizedReesAlgebra I) := fun n =>
    { carrier := {p | chapter02NormalizedReesHomogeneous I n p}
      zero_mem' := by
        intro j hj
        simp
      add_mem' := by
        intro p q hp hq j hj
        simp only [chapter02NormalizedReesHomogeneous] at hp hq ⊢
        simpa [map_add] using congrArg₂ (· + ·) (hp j hj) (hq j hj)
      smul_mem' := by
        intro r p hp j hj
        simp only [chapter02NormalizedReesHomogeneous] at hp ⊢
        simpa [smul_eq_mul] using congrArg (r * ·) (hp j hj) }
  have hgm : SetLike.GradedMonoid component := by
    refine { one_mem := ?_, mul_mem := ?_ }
    · change chapter02NormalizedReesHomogeneous I 0 1
      intro j hj
      simp [Polynomial.coeff_one, hj]
    · intro m n p q hp hq
      change chapter02NormalizedReesHomogeneous I (m + n) (p * q)
      have hp' : p.1 = Polynomial.monomial m (p.1.coeff m) := by
        ext j
        by_cases hj : j = m
        · subst j
          simp
        · simpa [Polynomial.coeff_monomial, hj, Ne.symm hj] using hp j hj
      have hq' : q.1 = Polynomial.monomial n (q.1.coeff n) := by
        ext j
        by_cases hj : j = n
        · subst j
          simp
        · simpa [Polynomial.coeff_monomial, hj, Ne.symm hj] using hq j hj
      intro j hj
      change (p.1 * q.1).coeff j = 0
      rw [hp', hq', Polynomial.monomial_mul_monomial]
      simp [Polynomial.coeff_monomial, Ne.symm hj]
  have hcoe_coeff (x : DirectSum ℕ (fun n => component n)) (n : ℕ) :
      (DirectSum.coeAddMonoidHom component x : chapter02NormalizedReesAlgebra I).1.coeff n =
        (x n : chapter02NormalizedReesAlgebra I).1.coeff n := by
    induction x using DFinsupp.induction with
    | h0 => simp
    | ha i b x hxi hb ih =>
        rw [map_add]
        change
          ((DirectSum.coeAddMonoidHom component (DFinsupp.single i b)).1 +
              (DirectSum.coeAddMonoidHom component x).1).coeff n =
            (((DFinsupp.single i b + x : DirectSum ℕ (fun n => component n)) n : component n) :
              chapter02NormalizedReesAlgebra I).1.coeff n
        rw [Polynomial.coeff_add]
        have hsingle :
            DirectSum.coeAddMonoidHom component (DFinsupp.single i b) =
              (b : chapter02NormalizedReesAlgebra I) := by
          exact DirectSum.coeAddMonoidHom_of component i b
        rw [hsingle]
        by_cases hin : i = n
        · subst n
          rw [DFinsupp.add_apply, DFinsupp.single_eq_same, hxi, add_zero]
          simp [ih, hxi]
        · have hbi := b.2 n (Ne.symm hin)
          rw [DFinsupp.add_apply, DFinsupp.single_eq_of_ne (Ne.symm hin), zero_add]
          simp [hbi, ih]
  have hspan : iSup component = ⊤ := by
    apply le_antisymm le_top
    intro p hp
    have hp_eq : p = ∑ n ∈ p.1.support,
        (⟨Polynomial.monomial n (p.1.coeff n),
            (chapter02_normalized_rees_monomial_mem_iff I n (p.1.coeff n)).2 (p.2 n)⟩ :
          chapter02NormalizedReesAlgebra I) := by
      apply Subtype.ext
      simp only [AddSubmonoidClass.coe_finsetSum]
      exact p.1.as_sum_support
    rw [hp_eq]
    apply Submodule.sum_mem
    intro n hn
    let hncomp : component n :=
      ⟨⟨Polynomial.monomial n (p.1.coeff n),
        (chapter02_normalized_rees_monomial_mem_iff I n (p.1.coeff n)).2 (p.2 n)⟩, by
        intro j hj
        simp [Polynomial.coeff_monomial, Ne.symm hj]⟩
    exact Submodule.mem_iSup_of_mem n hncomp.property
  have hinternal : DirectSum.IsInternal component :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top component).2
      ⟨by
        rw [iSupIndep_iff_dfinsupp_lsum_injective]
        intro x y hxy
        apply DirectSum.ext
        intro n
        have hcoeff := congrArg
          (fun z : chapter02NormalizedReesAlgebra I => z.1.coeff n) hxy
        apply Subtype.ext
        apply Subtype.ext
        ext j
        by_cases hj : j = n
        · subst j
          exact (hcoe_coeff x n).symm.trans (hcoeff.trans (hcoe_coeff y n))
        · exact ((x n).2 j hj).trans ((y n).2 j hj).symm
      , hspan⟩
  let graded : GradedAlgebra component :=
    @DirectSum.IsInternal.gradedAlgebra R _ (chapter02NormalizedReesAlgebra I) _ _ ℕ _ _
      component hgm hinternal
  let e0 : R →+* component 0 :=
    { toFun := fun r =>
        ⟨⟨Polynomial.C r, (chapter02NormalizedReesAlgebra I).algebraMap_mem r⟩, by
          intro j hj
          simp [Polynomial.coeff_C, hj]⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        simp
      map_mul' := by
        intro r s
        apply Subtype.ext
        apply Subtype.ext
        simp
      map_zero' := by
        apply Subtype.ext
        apply Subtype.ext
        simp
      map_add' := by
        intro r s
        apply Subtype.ext
        apply Subtype.ext
        simp }
  have he0bij : Function.Bijective e0 := by
    constructor
    · intro r s hrs
      have hcoeff := congrArg (fun z : component 0 => z.1.1.coeff 0) hrs
      simpa [e0, Polynomial.coeff_C] using hcoeff
    · intro p
      refine ⟨p.1.1.coeff 0, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      ext j
      by_cases hj : j = 0
      · subst j
        simp [e0]
      · have hpj := p.2 j hj
        simpa [e0, Polynomial.coeff_C, hj, Ne.symm hj] using hpj.symm
  let e : R ≃+* component 0 := RingEquiv.ofBijective e0 he0bij
  let data : Chapter02NormalizedReesGradingData I :=
    { component := component
      graded := graded
      component_spec := by
        intro n p
        rfl
      degreeZeroEquiv := e
      degreeZeroEquiv_algebraMap := by
        intro r
        apply Subtype.ext
        simp [e, e0, component] }
  exact ⟨data⟩

noncomputable def chapter02NormalizedReesGradingData
    {R : Type u} [CommRing R] (I : Ideal R) :
    Chapter02NormalizedReesGradingData I :=
  Classical.choice (chapter02_normalized_rees_grading_exists I)

noncomputable def chapter02NormalizedBlowupScheme
    {R : Type u} [CommRing R] (I : Ideal R) : Scheme.{u} := by
  let G := chapter02NormalizedReesGradingData I
  letI := G.graded
  exact AlgebraicGeometry.«Proj» G.component

/-- The canonical affine base map of the normalized Rees Proj. -/
noncomputable def chapter02NormalizedReesProjToSpec
    {R : Type u} [CommRing R] (I : Ideal R) :
    chapter02NormalizedBlowupScheme I ⟶
      AlgebraicGeometry.Spec (CommRingCat.of R) := by
  let G := chapter02NormalizedReesGradingData I
  letI := G.graded
  exact AlgebraicGeometry.Proj.toSpecZero G.component ≫
    AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom G.degreeZeroEquiv.toRingHom)

theorem chapter02_normalized_rees_degree_n_is_integral_closure
    {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) (r : R) :
    Polynomial.monomial n r ∈ chapter02NormalizedReesAlgebra I ↔
      r ∈ chapter02IntegralClosurePower I n := by
  exact chapter02_normalized_rees_monomial_mem_iff I n r

/-- A normal domain is supplied to the integral-closure statements by these canonical classes. -/
def Chapter02NormalDomain (R : Type u) [CommRing R] : Prop :=
  IsDomain R ∧ IsIntegrallyClosed R

def Chapter02ReesIsNormal
    {R : Type u} [CommRing R] (I : Ideal R) : Prop :=
  IsDomain (Chapter02ReesAlgebra R I) ∧
    IsIntegrallyClosed (Chapter02ReesAlgebra R I)

/-- This predicate records the source's warning that normality need not pass to a Rees algebra. -/
def Chapter02ReesNormalityCanFail
    (R : Type u) [CommRing R] : Prop :=
  ∃ I : Ideal R, ¬ Chapter02ReesIsNormal I

/- A concrete non-normal example uses a non-integrally-closed monomial ideal.  The square of the
homogeneous maximal ideal is deliberately not used here: its powers are integrally closed, so its
Rees algebra is normal even though it is a different graded algebra from the Rees algebra of the
maximal ideal. -/
def chapter02BivariateNonNormalIdeal {k : Type u} [CommRing k] :
    Ideal (Chapter02BivariatePolynomial k) :=
  Ideal.span ({chapter02BivariateX ^ 2, chapter02BivariateY ^ 3} :
    Set (Chapter02BivariatePolynomial k))

theorem chapter02_bivariate_non_normal_rees
    {k : Type u} [Field k] :
    ¬ Chapter02ReesIsNormal (chapter02BivariateNonNormalIdeal (k := k)) := by
  sorry

theorem chapter02_rees_normality_can_fail_over_a_field
    {k : Type u} [Field k] :
    Chapter02ReesNormalityCanFail (Chapter02BivariatePolynomial k) := by
  exact ⟨chapter02BivariateNonNormalIdeal (k := k), chapter02_bivariate_non_normal_rees⟩

def chapter02ReesToNormalizedRees
    {R : Type u} [CommRing R] (I : Ideal R) :
    Chapter02ReesAlgebra R I →+* chapter02NormalizedReesAlgebra I :=
  (Subalgebra.inclusion (chapter02_rees_le_normalized_rees I)).toRingHom

@[instance_reducible]
noncomputable def chapter02ReesAlgebraOnNormalizedRees
    {R : Type u} [CommRing R] (I : Ideal R) :
    Algebra (Chapter02ReesAlgebra R I) (chapter02NormalizedReesAlgebra I) :=
  (chapter02ReesToNormalizedRees I).toAlgebra

def Chapter02NormalizedReesIsIntegralClosure
    {R : Type u} [CommRing R] (I : Ideal R) : Prop :=
  letI := chapter02ReesAlgebraOnNormalizedRees I
  IsIntegralClosure (chapter02NormalizedReesAlgebra I)
    (Chapter02ReesAlgebra R I) (Polynomial R)

/- LOCAL_DEPENDENCY_GUESS: in a normal domain, the coefficientwise normalized Rees subalgebra is
the integral closure of the ordinary Rees algebra inside `R[T]`. -/
theorem chapter02_normalized_rees_is_integral_closure
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (I : Ideal R) :
    Chapter02NormalizedReesIsIntegralClosure I := by
  sorry

def Chapter02NormalizationFiniteOverRees
    {R : Type u} [CommRing R] (I : Ideal R) : Prop :=
  letI := chapter02ReesAlgebraOnNormalizedRees I
  Module.Finite (Chapter02ReesAlgebra R I) (chapter02NormalizedReesAlgebra I)

/- LOCAL_DEPENDENCY_GUESS: excellence plus finite type and surface hypotheses make the normalization finite over the Rees algebra. -/
theorem chapter02_normalization_finite_over_rees
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (hR : Chapter02ExcellentFiniteTypeSurface R) (I : Ideal R) (hI : I.FG) :
    Chapter02NormalizationFiniteOverRees I := by
  sorry

structure Chapter02NormalizedBlowupProperties
    {R : Type u} [CommRing R] (I : Ideal R) where
  projective :
    Chapter02AffineProjectivePresentation R (chapter02NormalizedBlowupScheme I)
      (chapter02NormalizedReesProjToSpec I)
  birational :
    Scheme.BirationalOver (chapter02NormalizedReesProjToSpec I) (𝟙 _)

/- LOCAL_DEPENDENCY_GUESS: the normalized Rees Proj is projective and birational over the affine surface; the pinned scheme API has no projective-morphism predicate. -/
theorem chapter02_normalized_blowup_projective_birational
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (hR : Chapter02ExcellentFiniteTypeSurface R) (I : Ideal R) (hI : I.FG)
    (hI0 : I ≠ ⊥) :
    Nonempty (Chapter02NormalizedBlowupProperties I) := by
  sorry

def Chapter02SameIntegralClosures
    {R : Type u} [CommRing R] (I J : Ideal R) : Prop :=
  ∀ n, 0 < n → chapter02IntegralClosurePower I n =
    chapter02IntegralClosurePower J n

theorem chapter02_same_integral_closures_same_normalized_blowup
    {R : Type u} [CommRing R] (I J : Ideal R)
    (hIJ : Chapter02SameIntegralClosures I J) :
    Nonempty (chapter02NormalizedBlowupScheme I ≅ chapter02NormalizedBlowupScheme J) := by
  sorry

/-! ### Regular points and the limits of ordinary blowups -/

structure Chapter02RegularSurfaceBlowupComparison
    (D : Chapter02RegularSurfaceClosedPoint) where
  normalizedBlowup : Scheme.{u}
  normalizedBlowupIsNormalization :
    Chapter02SchemeNormalization D.ordinaryBlowup normalizedBlowup

theorem chapter02_ordinary_blowup_regular_at_regular_closed_point
    (D : Chapter02RegularSurfaceClosedPoint)
    (hD : Chapter02OrdinaryBlowupAtPoint D.scheme D.ordinaryBlowup D.point) :
    Chapter02RegularSurface D.ordinaryBlowup := by
  sorry

theorem chapter02_normalization_adds_nothing_at_regular_closed_point
    (D : Chapter02RegularSurfaceClosedPoint)
    (C : Chapter02RegularSurfaceBlowupComparison D)
    (hD : Chapter02OrdinaryBlowupAtPoint D.scheme D.ordinaryBlowup D.point)
    (hC : Chapter02SchemeNormalization D.ordinaryBlowup C.normalizedBlowup) :
    Nonempty (C.normalizedBlowup ≅ D.ordinaryBlowup) := by
  sorry

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter02
