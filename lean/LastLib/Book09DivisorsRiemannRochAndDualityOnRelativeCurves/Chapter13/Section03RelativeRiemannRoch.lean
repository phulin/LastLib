import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter13.Section02SemicontinuityAndBaseChange

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter13

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10
open scoped AlgebraicGeometry

noncomputable section

universe u

/-! ## 13.3. Relative Riemann--Roch -/

/-! ### Connected reduced fibers and degree -/

/-- The geometric connectedness, reducedness, and arithmetic-genus profile used by RR. -/
structure Chapter13GeometricGenusData (C : Chapter13RelativeCurve) where
  geometrically_connected : GeometricallyConnected C.f
  geometrically_reduced : GeometricallyReduced C.f
  genus : ℕ
  arithmetic_genus : C.S → ℕ
  arithmetic_genus_eq : ∀ s, arithmetic_genus s = genus

/-- The fiberwise degree interface for line bundles. -/
structure Chapter13FiberDegreeTheory (C : Chapter13RelativeCurve) where
  degree : ∀ s : C.S, Chapter04LineBundle (C.f.fiber s) → ℤ
  degree_tensor_additive :
    ∀ (s : C.S) (L M : Chapter04LineBundle (C.f.fiber s)),
      degree s (chapter04LineBundleTensor L M) = degree s L + degree s M
  degree_trivial : ∀ s, degree s (chapter04TrivialLineBundle (C.f.fiber s)) = 0

/-- Relative degree of a line bundle on the total space. -/
def chapter13RelativeDegree {C : Chapter13RelativeCurve}
    (deg : Chapter13FiberDegreeTheory C) (L : Chapter04LineBundle C.X)
    (s : C.S) : ℤ :=
  deg.degree s (chapter13FiberLineBundle L s)

/-- A line bundle whose relative degree is the integer `d`. -/
def chapter13LineBundleOfRelativeDegree {C : Chapter13RelativeCurve}
    (deg : Chapter13FiberDegreeTheory C) (L : Chapter04LineBundle C.X)
    (d : ℤ) : Prop :=
  ∀ s : C.S, chapter13RelativeDegree deg L s = d

/-- Local constancy of the relative degree function. -/
def chapter13RelativeDegreeLocallyConstant
    {C : Chapter13RelativeCurve} (deg : Chapter13FiberDegreeTheory C)
    (L : Chapter04LineBundle C.X) : Prop :=
  Chapter13LocallyConstant (chapter13RelativeDegree deg L)

theorem chapter13_relative_degree_locally_constant_of_fixed_degree
    {C : Chapter13RelativeCurve} (deg : Chapter13FiberDegreeTheory C)
    (L : Chapter04LineBundle C.X) (d : ℤ)
    (hd : chapter13LineBundleOfRelativeDegree deg L d) :
    chapter13RelativeDegreeLocallyConstant deg L := by
  sorry

/- The genus profile is likewise locally constant under the displayed
constant-genus hypothesis. -/
def chapter13ArithmeticGenusLocallyConstant
    {C : Chapter13RelativeCurve} (G : Chapter13GeometricGenusData C) : Prop :=
  Chapter13LocallyConstant G.arithmetic_genus

theorem chapter13_arithmetic_genus_locally_constant
    {C : Chapter13RelativeCurve} (G : Chapter13GeometricGenusData C) :
    chapter13ArithmeticGenusLocallyConstant G := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the preceding divisor chapters are expected to
identify the degree function with the degree of a Cartier divisor and to prove
its local constancy in flat projective families.  The RR statements use only
the displayed fiberwise degree interface. -/

/-- Cohomology data for a line bundle, using the actual scheme-theoretic fibers. -/
structure Chapter13LineBundleCohomologyData
    (C : Chapter13RelativeCurve) (L : Chapter04LineBundle C.X) where
  fiber : Chapter13FiberCohomologyProfile C L.sheaf

/-- Euler characteristic of a line bundle on a fiber. -/
def chapter13LineFiberEulerCharacteristic
    {C : Chapter13RelativeCurve} {L : Chapter04LineBundle C.X}
    (H : Chapter13LineBundleCohomologyData C L) (s : C.S) : ℤ :=
  (Module.finrank (C.S.residueField s) (H.fiber.h0 s).module : ℤ) -
    (Module.finrank (C.S.residueField s) (H.fiber.h1 s).module : ℤ)

/-- The line-bundle relative Riemann--Roch identity (13.6). -/
theorem chapter13_relative_line_bundle_riemann_roch
    {C : Chapter13RelativeCurve} (G : Chapter13GeometricGenusData C)
    (deg : Chapter13FiberDegreeTheory C) (L : Chapter04LineBundle C.X)
    (H : Chapter13LineBundleCohomologyData C L) (d : ℤ)
    (hd : chapter13LineBundleOfRelativeDegree deg L d) :
    ∀ s : C.S,
      chapter13LineFiberEulerCharacteristic H s = d + 1 - (G.genus : ℤ) := by
  sorry

/-- Degree of a vector bundle, defined as the degree of its determinant. -/
def chapter13VectorBundleDegree {C : Chapter13RelativeCurve}
    (deg : Chapter13FiberDegreeTheory C) (E : Chapter13VectorBundle C.X)
    (s : C.S) : ℤ :=
  deg.degree s (chapter13FiberVectorBundle E s).determinant

/-- Euler characteristic of a vector bundle on a fiber. -/
def chapter13VectorFiberEulerCharacteristic
    {C : Chapter13RelativeCurve} {E : Chapter13VectorBundle C.X}
    (D : Chapter13RelativeCohomologyData C E) (s : C.S) : ℤ :=
  chapter13FiberEulerCharacteristic D.fiber s

/- The determinant-degree notation is intentionally a definition rather than a
second degree operation, so (13.7) is phrased exactly through `det E`. -/

/-! ### The line-bundle reduction -/

/- LOCAL_DEPENDENCY_GUESS: the earlier Chapter 10 effective-Cartier-divisor
object is canonical, but its inverse line bundle is exposed through a class
and is not reconciled with the Chapter 4 line-bundle object. -/

/-- An effective divisor package with `𝒪(D)` and `𝒪(-D)`. -/
structure Chapter13EffectiveDivisorData (C : Chapter13RelativeCurve) where
  divisor : Chapter10EffectiveCartierDivisor C.X
  OofD : Chapter04LineBundle C.X
  OofMinusD : Chapter04LineBundle C.X
  inverse_line_bundle :
    chapter04LineBundleIsomorphic
      (chapter04LineBundleTensor OofD OofMinusD)
      (chapter04TrivialLineBundle C.X)
  degree : C.S → ℤ

/-- The twist `E(D)` used in the generation and incidence argument. -/
def chapter13TwistModule {C : Chapter13RelativeCurve}
    (E : Chapter13VectorBundle C.X) (D : Chapter13EffectiveDivisorData C) : C.X.Modules :=
  chapter04Tensor E.sheaf D.OofD.sheaf

/-- Relative global generation of the twisted vector bundle. -/
def chapter13TwistGloballyGenerated {C : Chapter13RelativeCurve}
    (E : Chapter13VectorBundle C.X) (D : Chapter13EffectiveDivisorData C) : Prop :=
  chapter04SheafSurjective (chapter04EvaluationMap C.f (chapter13TwistModule E D))

/-- Vanishing of a global section at a point, stated on its stalk germ. -/
def chapter13SectionVanishesAt {X : Scheme.{u}} {M : X.Modules}
    (σ : Γ(M, ⊤)) (x : X) : Prop :=
  TopCat.Presheaf.germ M.presheaf ⊤ x (Set.mem_univ x) σ = 0

/-- A global section of `E(D)` which is nonzero at every point. -/
structure Chapter13EverywhereNonvanishingSection
    {C : Chapter13RelativeCurve} (E : Chapter13VectorBundle C.X)
    (D : Chapter13EffectiveDivisorData C) where
  sectionData : Γ(chapter13TwistModule E D, ⊤)
  nonvanishing : ∀ x : C.X, ¬ chapter13SectionVanishesAt sectionData x

/-- The incidence profile used to justify an everywhere-nonvanishing section. -/
structure Chapter13IncidenceProfile
    {C : Chapter13RelativeCurve} (E : Chapter13VectorBundle C.X)
    (D : Chapter13EffectiveDivisorData C) where
  incidence : Set (Γ(chapter13TwistModule E D, ⊤) × C.X)
  incidenceFiberCodimension : C.X → ℕ
  incidence_fiber_codimension : ∀ x : C.X, incidenceFiberCodimension x = E.rank
  image_is_proper :
    Set.range (fun p : incidence => p.1) ≠ Set.univ

/-- The incidence argument produces a section avoiding all point-zero loci. -/
theorem chapter13_incidence_nonvanishing_section
    {C : Chapter13RelativeCurve} (E : Chapter13VectorBundle C.X)
    (D : Chapter13EffectiveDivisorData C)
    (hgenerated : chapter13TwistGloballyGenerated E D)
    (hrank : 1 < E.rank) :
    Nonempty (Chapter13EverywhereNonvanishingSection E D) := by
  sorry

/-! ### The exact reduction step -/

/-- A short exact sequence of vector-bundle module sheaves. -/
structure Chapter13ShortExactVectorBundle
    {C : Chapter13RelativeCurve}
    (A B Q : Chapter13VectorBundle C.X) where
  injection : A.sheaf ⟶ B.sheaf
  projection : B.sheaf ⟶ Q.sheaf
  comp_zero : injection ≫ projection = 0
  exact : (ShortComplex.mk injection projection comp_zero).Exact

/-- The line-sub-bundle reduction produced by a nonvanishing section. -/
structure Chapter13LineSubbundleReduction
    {C : Chapter13RelativeCurve} (E : Chapter13VectorBundle C.X)
    (D : Chapter13EffectiveDivisorData C) where
  quotient : Chapter13VectorBundle C.X
  injection : D.OofMinusD.sheaf ⟶ E.sheaf
  projection : E.sheaf ⟶ quotient.sheaf
  comp_zero : injection ≫ projection = 0
  exact : (ShortComplex.mk injection projection comp_zero).Exact
  determinant_relation :
    chapter04LineBundleIsomorphic quotient.determinant
      (chapter04LineBundleTensor E.determinant D.OofD)

/-- A nowhere-vanishing section gives a subbundle and a vector-bundle quotient. -/
theorem chapter13_nonvanishing_section_gives_subbundle
    {C : Chapter13RelativeCurve} (E : Chapter13VectorBundle C.X)
    (D : Chapter13EffectiveDivisorData C)
    (σ : Chapter13EverywhereNonvanishingSection E D) :
    Nonempty (Chapter13LineSubbundleReduction E D) := by
  sorry

/-- The induction step in the source proof of vector-bundle RR. -/
theorem chapter13_vector_bundle_reduction_step
    {C : Chapter13RelativeCurve} (E : Chapter13VectorBundle C.X)
    (D : Chapter13EffectiveDivisorData C)
    (σ : Chapter13EverywhereNonvanishingSection E D) :
    Nonempty (Chapter13LineSubbundleReduction E D) := by
  exact chapter13_nonvanishing_section_gives_subbundle E D σ

/-! ### Additivity and the vector-bundle formula -/

/-- A short exact sequence of arbitrary module sheaves on the total space. -/
structure Chapter13ShortExactSheaf
    {C : Chapter13RelativeCurve}
    (A B Q : C.X.Modules) where
  injection : A ⟶ B
  projection : B ⟶ Q
  comp_zero : injection ≫ projection = 0
  exact : (ShortComplex.mk injection projection comp_zero).Exact

/-- Fiberwise additivity of Euler characteristic for a short exact sequence. -/
theorem chapter13_euler_characteristic_additive
    {C : Chapter13RelativeCurve}
    {A B Q : C.X.Modules}
    (S : Chapter13ShortExactSheaf A B Q)
    (HA : Chapter13FiberCohomologyProfile C A)
    (HB : Chapter13FiberCohomologyProfile C B)
    (HQ : Chapter13FiberCohomologyProfile C Q) :
    ∀ s : C.S,
      ((Module.finrank (C.S.residueField s) (HB.h0 s).module : ℤ) -
          (Module.finrank (C.S.residueField s) (HB.h1 s).module : ℤ)) =
        ((Module.finrank (C.S.residueField s) (HA.h0 s).module : ℤ) -
          (Module.finrank (C.S.residueField s) (HA.h1 s).module : ℤ)) +
          ((Module.finrank (C.S.residueField s) (HQ.h0 s).module : ℤ) -
            (Module.finrank (C.S.residueField s) (HQ.h1 s).module : ℤ)) := by
  sorry

/-! ### Relative Riemann--Roch for vector bundles -/

/-- The vector-bundle formula (13.7). -/
theorem chapter13_relative_vector_bundle_riemann_roch
    {C : Chapter13RelativeCurve} (G : Chapter13GeometricGenusData C)
    (deg : Chapter13FiberDegreeTheory C) (E : Chapter13VectorBundle C.X)
    (D : Chapter13RelativeCohomologyData C E) :
    ∀ s : C.S,
      chapter13VectorFiberEulerCharacteristic D s =
        chapter13VectorBundleDegree deg E s +
          (E.rank : ℤ) * (1 - (G.genus : ℤ)) := by
  sorry

/-- The virtual rank of the finite-free two-term model equals the RR number. -/
theorem chapter13_two_term_virtual_rank_is_riemann_roch_number
    {C : Chapter13RelativeCurve} (G : Chapter13GeometricGenusData C)
    (deg : Chapter13FiberDegreeTheory C) (E : Chapter13VectorBundle C.X)
    (D : Chapter13RelativeCohomologyData C E)
    (T : Chapter13TwoTermEulerCharacteristicData C E D) (s : C.S) :
    chapter13TwoTermVirtualRank (Classical.choice (T.local_model s)).model =
      chapter13VectorBundleDegree deg E s +
        (E.rank : ℤ) * (1 - (G.genus : ℤ)) := by
  sorry

/- The separate dimensions may jump even when their difference is constant. -/
def chapter13H0H1JumpsCanCancel
    {C : Chapter13RelativeCurve} {E : Chapter13VectorBundle C.X}
    (D : Chapter13RelativeCohomologyData C E) : Prop :=
  ¬ Chapter13LocallyConstant (fun s => chapter13H0Dimension D.fiber s) ∧
    ¬ Chapter13LocallyConstant (fun s => chapter13H1Dimension D.fiber s) ∧
      Chapter13LocallyConstant (fun s => chapter13FiberEulerCharacteristic D.fiber s)

end
end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter13
