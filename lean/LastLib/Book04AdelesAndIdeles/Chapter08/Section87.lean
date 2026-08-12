import LastLib.Book04AdelesAndIdeles.Chapter08.Section82

namespace LastLib.Book04AdelesAndIdeles.Chapter08

noncomputable section

open scoped BigOperators nonZeroDivisors RestrictedProduct
open IsDedekindDomain

/-! ## 8.7 Divisor sequence in one view -/

def chapter08GlobalUnitEmbedding (K : Type*) [Field K] [NumberField K] :
    (Chapter08Integers K)ˣ →* Kˣ :=
  Units.map (algebraMap (Chapter08Integers K) K)

def chapter08PrincipalIdealGroup (K : Type*) [Field K] [NumberField K] :=
  (toPrincipalIdeal (Chapter08Integers K) K).range

def chapter08PrincipalIdealMap (K : Type*) [Field K] [NumberField K] :
    Kˣ →* chapter08PrincipalIdealGroup K where
  toFun := fun a => ⟨toPrincipalIdeal (Chapter08Integers K) K a,
    MonoidHom.mem_range.mpr ⟨a, rfl⟩⟩
  map_one' := by
    sorry
  map_mul' := by
    intro x y
    sorry

def chapter08GlobalUnitToPrincipalIdeal (K : Type*) [Field K] [NumberField K] :
    (Chapter08Integers K)ˣ →* chapter08PrincipalIdealGroup K :=
  (chapter08PrincipalIdealMap K).comp (chapter08GlobalUnitEmbedding K)

theorem chapter08_global_unit_kernel_principal_ideal
    (K : Type*) [Field K] [NumberField K] :
    MonoidHom.ker (chapter08PrincipalIdealMap K) =
      MonoidHom.range (chapter08GlobalUnitEmbedding K) := by
  sorry

theorem chapter08_global_divisor_short_exact
    (K : Type*) [Field K] [NumberField K] :
    chapter08IsShortExact (chapter08GlobalUnitEmbedding K)
      (chapter08PrincipalIdealMap K) := by
  sorry

theorem chapter08_divisor_diagram_commutes
    {K : Type*} [Field K] [NumberField K]
    (u : (Chapter08Integers K)ˣ) :
    chapter08FiniteIdeleIdealMap K
        (chapter08FinitePrincipalIdele (chapter08GlobalUnitEmbedding K u)) =
      toPrincipalIdeal (Chapter08Integers K) K (chapter08GlobalUnitEmbedding K u) := by
  exact chapter08_finite_idele_ideal_principal _

theorem chapter08_finite_divisor_square_commutes
    (K : Type*) [Field K] [NumberField K] :
    (chapter08FiniteIdeleIdealMap K).comp (chapter08FinitePrincipalIdeleHom K) =
      toPrincipalIdeal (Chapter08Integers K) K := by
  sorry

theorem chapter08_divisor_quotient_is_class_group
    (K : Type*) [Field K] [NumberField K] :
    Nonempty
      ((Chapter08IdealGroup K ⧸
        (toPrincipalIdeal (Chapter08Integers K) K).range) ≃*
        Chapter08OrdinaryClassGroup K) := by
  exact ⟨(ClassGroup.equiv K).symm⟩

/-! Finite divisors are the finitely supported valuation vectors. -/

def chapter08PrincipalDivisor {K : Type*} [Field K] [NumberField K]
    (a : Kˣ) : Chapter08FiniteDivisors K :=
  chapter08FiniteIdeleOrderFinsupp (chapter08FinitePrincipalIdele a)

@[simp]
theorem chapter08PrincipalDivisor_apply
    {K : Type*} [Field K] [NumberField K]
    (a : Kˣ) (v : HeightOneSpectrum (Chapter08Integers K)) :
    chapter08PrincipalDivisor a v =
      FractionalIdeal.count K v
        (toPrincipalIdeal (Chapter08Integers K) K a : Chapter08FractionalIdeal K) := by
  rw [chapter08PrincipalDivisor, chapter08FiniteIdeleOrderFinsupp_apply,
    ← chapter08_finite_idele_ideal_count (x := chapter08FinitePrincipalIdele a) v,
    chapter08_finite_idele_ideal_principal]

def chapter08PrincipalDivisorHom (K : Type*) [Field K] [NumberField K] :
    Kˣ →* Multiplicative (Chapter08FiniteDivisors K) where
  toFun := fun a => Multiplicative.ofAdd (chapter08PrincipalDivisor a)
  map_one' := by
    sorry
  map_mul' := by
    intro x y
    sorry

abbrev Chapter08DivisorClassGroup (K : Type*) [Field K] [NumberField K] :=
  Multiplicative (Chapter08FiniteDivisors K) ⧸
    MonoidHom.range (chapter08PrincipalDivisorHom K)

noncomputable def chapter08DivisorToIdeal
    {K : Type*} [Field K] [NumberField K]
    (d : Chapter08FiniteDivisors K) : Chapter08IdealGroup K :=
  Units.mk0
    (d.prod (fun v n => (v.asIdeal : Chapter08FractionalIdeal K) ^ n)) (by
      sorry)

def chapter08DivisorToIdealHom (K : Type*) [Field K] [NumberField K] :
    Multiplicative (Chapter08FiniteDivisors K) →* Chapter08IdealGroup K where
  toFun := fun d => chapter08DivisorToIdeal (Multiplicative.toAdd d)
  map_one' := by
    sorry
  map_mul' := by
    intro x y
    sorry

theorem chapter08_divisor_to_ideal_principal
    {K : Type*} [Field K] [NumberField K]
    (a : Kˣ) :
    chapter08DivisorToIdealHom K (chapter08PrincipalDivisorHom K a) =
      toPrincipalIdeal (Chapter08Integers K) K a := by
  sorry

def chapter08DivisorClassMap (K : Type*) [Field K] [NumberField K] :
    Chapter08DivisorClassGroup K →* Chapter08OrdinaryClassGroup K :=
  QuotientGroup.lift (MonoidHom.range (chapter08PrincipalDivisorHom K))
    ((ClassGroup.mk K).comp (chapter08DivisorToIdealHom K)) (by
      intro x hx
      sorry)

theorem chapter08_divisor_class_map_surjective
    (K : Type*) [Field K] [NumberField K] :
    Function.Surjective (chapter08DivisorClassMap K) := by
  sorry

theorem chapter08_divisor_class_map_kernel
    (K : Type*) [Field K] [NumberField K] :
    MonoidHom.ker (chapter08DivisorClassMap K) = ⊥ := by
  sorry

noncomputable def chapter08DivisorClassGroupEquivClassGroup
    (K : Type*) [Field K] [NumberField K] :
    Chapter08DivisorClassGroup K ≃* Chapter08OrdinaryClassGroup K :=
  MulEquiv.ofBijective (chapter08DivisorClassMap K)
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (chapter08_divisor_class_map_kernel K),
      chapter08_divisor_class_map_surjective K⟩

/-! Adding archimedean real coefficients records the degree balance that the ideal map alone omits. -/

def chapter08ArchimedeanDivisorCoefficient
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08InfiniteIdeles K)
    (w : NumberField.InfinitePlace K) : ℝ :=
  -Real.log (‖x.1 w‖ ^ w.mult)

def chapter08ExtendedDivisorDegree
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08Ideles K) : ℝ :=
  Real.log (chapter08IdealNorm (chapter08FiniteIdeleIdealMap K x.2) : ℝ) +
    ∑ w : NumberField.InfinitePlace K,
      chapter08ArchimedeanDivisorCoefficient x.1 w

/- Local dependency guess for the later fixup pass: the earlier product-formula API identifies the
normalization of the finite ideal norm with the weighted archimedean norm used here. -/

theorem chapter08_extended_divisor_degree_principal_zero
    {K : Type*} [Field K] [NumberField K]
    (a : Kˣ) :
    chapter08ExtendedDivisorDegree (chapter08PrincipalIdeleHom K a) = 0 := by
  sorry

theorem chapter08_extended_divisor_degree_has_finite_log_term
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08Ideles K) :
    chapter08ExtendedDivisorDegree x =
      chapter08FiniteDegreeContribution x.2 +
        ∑ w : NumberField.InfinitePlace K,
          chapter08ArchimedeanDivisorCoefficient x.1 w := by
  rfl

end

end LastLib.Book04AdelesAndIdeles.Chapter08
