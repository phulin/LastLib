import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter07.Section01FromDimensionsToAPolynomial

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter07

noncomputable section

universe u

open CategoryTheory
open AlgebraicGeometry
open Polynomial

/-! ## 7.2. The polynomial of a projective scheme -/

def chapter07ProjectiveSpaceHilbertPolynomial (r : ℕ) : Polynomial ℚ :=
  chapter07BinomialPolynomial r 0

@[simp] theorem chapter07_projectiveSpaceHilbertPolynomial_eval
    (r n : ℕ) :
    (chapter07ProjectiveSpaceHilbertPolynomial r).eval (n : ℚ) =
      (Nat.choose (n + r) r : ℚ) := by
  simpa [chapter07ProjectiveSpaceHilbertPolynomial] using
    chapter07_binomialPolynomial_eval r 0 n (Nat.zero_le n)

def chapter07HypersurfaceHilbertPolynomial (r e : ℕ) : Polynomial ℚ :=
  chapter07ProjectiveSpaceHilbertPolynomial r - chapter07BinomialPolynomial r e

def chapter07PlaneCurveHilbertPolynomial (e : ℕ) : Polynomial ℚ :=
  Polynomial.C (e : ℚ) * Polynomial.X + Polynomial.C 1 -
    Polynomial.C (((e : ℚ) - 1) * ((e : ℚ) - 2) / 2)

structure Chapter07ClosedSubschemeOfProjectiveSpace
    (k : Type u) [Field k] where
  r : ℕ
  Z : Scheme.{u}
  inclusion : Z ⟶ chapter07ProjectiveSpace k r
  closedImmersion : IsClosedImmersion inclusion
  structureMap : Z ⟶ chapter07BaseScheme k
  overBase :
    inclusion ≫ chapter07ProjectiveSpaceToBase k r = structureMap

/-!
The cohomological additivity input is stated separately from exactness.  It
is the reusable bridge supplied by the long exact cohomology sequence, and it
keeps this chapter independent of a particular cohomology implementation.
-/
theorem chapter07_hilbert_polynomial_additive_of_short_exact
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    {A B D : Chapter07HilbertSetup k C}
    (hseq : Chapter07ShortExactSequence A.F B.F D.F)
    (hEuler : ∀ n : ℕ,
      chapter07EulerCharacteristic B n =
        chapter07EulerCharacteristic A n + chapter07EulerCharacteristic D n) :
    chapter07HilbertPolynomial B =
      chapter07HilbertPolynomial A + chapter07HilbertPolynomial D := by
  apply chapter07_polynomial_eq_of_eventually_equal
  rcases chapter07_hilbert_polynomial_matches_euler_eventually A with
    ⟨NA, hNA⟩
  rcases chapter07_hilbert_polynomial_matches_euler_eventually B with
    ⟨NB, hNB⟩
  rcases chapter07_hilbert_polynomial_matches_euler_eventually D with
    ⟨ND, hND⟩
  refine ⟨max NA (max NB ND), fun n hn => ?_⟩
  have hA := hNA n (le_trans (Nat.le_max_left _ _) hn)
  have hB := hNB n (le_trans
    (le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn)
  have hD := hND n (le_trans
    (le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn)
  calc
    (chapter07HilbertPolynomial B).eval (n : ℚ) =
        (chapter07EulerCharacteristic B n : ℚ) := hB
    _ = ((chapter07EulerCharacteristic A n +
        chapter07EulerCharacteristic D n : ℤ) : ℚ) := by
          exact_mod_cast hEuler n
    _ = (chapter07HilbertPolynomial A + chapter07HilbertPolynomial D).eval
        (n : ℚ) := by
          rw [Polynomial.eval_add, hA, hD]
          norm_num

theorem chapter07_hilbert_polynomial_subtractive_of_short_exact
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    {A B D : Chapter07HilbertSetup k C}
    (hseq : Chapter07ShortExactSequence A.F B.F D.F)
    (hEuler : ∀ n : ℕ,
      chapter07EulerCharacteristic B n =
        chapter07EulerCharacteristic A n + chapter07EulerCharacteristic D n) :
    chapter07HilbertPolynomial D =
      chapter07HilbertPolynomial B - chapter07HilbertPolynomial A := by
  have h := chapter07_hilbert_polynomial_additive_of_short_exact hseq hEuler
  rw [h]
  ring

/-!
This record packages the ideal sequence
`0 → 𝓘_Z → 𝓞_{ℙ^r} → 𝓞_Z → 0` together with the two standard inputs needed
to identify its terms.  The `ambientPolynomial` field is the projective-space
calculation, not the closed-subscheme conclusion proved below.
-/
structure Chapter07ClosedSubschemeHilbertData
    (k : Type u) [Field k]
    (C : Chapter07PolarizedScheme k) where
  subscheme : Chapter07ClosedSubschemeOfProjectiveSpace k
  ambientIdentification : C.X ≅ chapter07ProjectiveSpace k subscheme.r
  ambientIdentification_overBase :
    ambientIdentification.hom ≫ chapter07ProjectiveSpaceToBase k subscheme.r =
      C.structureMap
  ambientPolarization :
    C.L.sheaf ≅
      (Scheme.Modules.pullback ambientIdentification.hom).obj
        (chapter07ProjectiveSpaceTautologicalLineBundle k subscheme.r).sheaf
  ambient : Chapter07HilbertSetup k C
  ambientStructureSheaf :
    ambient.F.sheaf ≅ SheafOfModules.unit C.X.ringCatSheaf
  ideal : Chapter07HilbertSetup k C
  structureSheaf : Chapter07HilbertSetup k C
  idealSequence : Chapter07ShortExactSequence ideal.F ambient.F structureSheaf.F
  idealInjection_mono : Mono idealSequence.injection
  closedStructureSheaf : Chapter07CoherentSheaf subscheme.Z
  closedStructureSheaf_isStructureSheaf :
    closedStructureSheaf.sheaf ≅ SheafOfModules.unit subscheme.Z.ringCatSheaf
  structureSheafPushforward :
    structureSheaf.F.sheaf ≅
      (Scheme.Modules.pushforward
        (subscheme.inclusion ≫ ambientIdentification.inv)).obj closedStructureSheaf.sheaf
  ambientPolynomial :
    chapter07HilbertPolynomial ambient =
      chapter07ProjectiveSpaceHilbertPolynomial subscheme.r
  euler_additive : ∀ n : ℕ,
      chapter07EulerCharacteristic ambient n =
      chapter07EulerCharacteristic ideal n +
        chapter07EulerCharacteristic structureSheaf n

theorem chapter07_closed_subscheme_hilbert_polynomial
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (D : Chapter07ClosedSubschemeHilbertData k C) :
    chapter07HilbertPolynomial D.structureSheaf =
      chapter07ProjectiveSpaceHilbertPolynomial D.subscheme.r -
        chapter07HilbertPolynomial D.ideal := by
  have h := chapter07_hilbert_polynomial_subtractive_of_short_exact
    D.idealSequence D.euler_additive
  simpa [D.ambientPolynomial] using h

theorem chapter07_closed_subscheme_hilbert_function_eventually
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (D : Chapter07ClosedSubschemeHilbertData k C) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      chapter07HilbertFunction D.structureSheaf n =
        Nat.choose (n + D.subscheme.r) D.subscheme.r -
          chapter07HilbertFunction D.ideal n := by
  rcases chapter07_hilbert_polynomial_matches_function_eventually D.ideal with
    ⟨NI, hNI⟩
  rcases chapter07_hilbert_polynomial_matches_function_eventually D.structureSheaf with
    ⟨NS, hNS⟩
  refine ⟨max NI NS, fun n hn => ?_⟩
  have hNI' := hNI n (le_trans (Nat.le_max_left _ _) hn)
  have hNS' := hNS n (le_trans (Nat.le_max_right _ _) hn)
  have hrat :
      (chapter07HilbertFunction D.structureSheaf n : ℚ) =
        (Nat.choose (n + D.subscheme.r) D.subscheme.r : ℚ) -
          (chapter07HilbertFunction D.ideal n : ℚ) := by
    calc
      (chapter07HilbertFunction D.structureSheaf n : ℚ) =
          (chapter07HilbertPolynomial D.structureSheaf).eval (n : ℚ) := hNS'.symm
      _ = (chapter07ProjectiveSpaceHilbertPolynomial D.subscheme.r -
          chapter07HilbertPolynomial D.ideal).eval (n : ℚ) := by
            rw [chapter07_closed_subscheme_hilbert_polynomial D]
      _ = (chapter07ProjectiveSpaceHilbertPolynomial D.subscheme.r).eval (n : ℚ) -
          (chapter07HilbertPolynomial D.ideal).eval (n : ℚ) := by simp
      _ = (Nat.choose (n + D.subscheme.r) D.subscheme.r : ℚ) -
          (chapter07HilbertFunction D.ideal n : ℚ) := by
            rw [chapter07_projectiveSpaceHilbertPolynomial_eval, hNI']
  have hrat' :
      (Nat.choose (n + D.subscheme.r) D.subscheme.r : ℚ) =
        (chapter07HilbertFunction D.ideal n : ℚ) +
          (chapter07HilbertFunction D.structureSheaf n : ℚ) := by
    rw [hrat]
    ring
  have hnat :
      Nat.choose (n + D.subscheme.r) D.subscheme.r =
        chapter07HilbertFunction D.ideal n +
          chapter07HilbertFunction D.structureSheaf n := by
    exact_mod_cast hrat'
  exact (Nat.sub_eq_of_eq_add hnat).symm

structure Chapter07HypersurfaceHilbertData
    (k : Type u) [Field k]
    (C : Chapter07PolarizedScheme k) where
  closedSubscheme : Chapter07ClosedSubschemeHilbertData k C
  degree : ℕ
  degreePositive : 0 < degree
  ideal_euler_characteristic_shift : ∀ n : ℕ,
    chapter07EulerCharacteristicAtInteger closedSubscheme.ideal (n : ℤ) =
      chapter07EulerCharacteristicAtInteger closedSubscheme.ambient
        ((n : ℤ) - (degree : ℤ))

theorem chapter07_hypersurface_hilbert_polynomial
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (D : Chapter07HypersurfaceHilbertData k C) :
    chapter07HilbertPolynomial D.closedSubscheme.structureSheaf =
      chapter07HypersurfaceHilbertPolynomial D.closedSubscheme.subscheme.r D.degree := by
  have hIdeal :
      chapter07HilbertPolynomial D.closedSubscheme.ideal =
        chapter07BinomialPolynomial D.closedSubscheme.subscheme.r D.degree := by
    apply chapter07_polynomial_eq_of_eventually_equal
    refine ⟨D.degree, fun n hn => ?_⟩
    have hcast :
        (((n : ℤ) - (D.degree : ℤ) : ℤ) : ℚ) =
          ((n - D.degree : ℕ) : ℚ) := by
      rw [Nat.cast_sub hn]
      push_cast
    calc
      (chapter07HilbertPolynomial D.closedSubscheme.ideal).eval (n : ℚ) =
          chapter07EulerCharacteristicAtInteger D.closedSubscheme.ideal (n : ℤ) :=
        chapter07_hilbert_polynomial_matches_euler_at_all_integers
          D.closedSubscheme.ideal (n : ℤ)
      _ = chapter07EulerCharacteristicAtInteger D.closedSubscheme.ambient
          ((n : ℤ) - (D.degree : ℤ)) := D.ideal_euler_characteristic_shift n
      _ = (chapter07HilbertPolynomial D.closedSubscheme.ambient).eval
          (((n : ℤ) - (D.degree : ℤ) : ℤ) : ℚ) := by
            symm
            exact chapter07_hilbert_polynomial_matches_euler_at_all_integers
              D.closedSubscheme.ambient ((n : ℤ) - (D.degree : ℤ))
      _ = (chapter07ProjectiveSpaceHilbertPolynomial
          D.closedSubscheme.subscheme.r).eval ((n - D.degree : ℕ) : ℚ) := by
            rw [D.closedSubscheme.ambientPolynomial, hcast]
      _ = (Nat.choose (n - D.degree + D.closedSubscheme.subscheme.r)
          D.closedSubscheme.subscheme.r : ℚ) :=
        chapter07_projectiveSpaceHilbertPolynomial_eval
          D.closedSubscheme.subscheme.r (n - D.degree)
      _ = (Nat.choose (n + D.closedSubscheme.subscheme.r - D.degree)
          D.closedSubscheme.subscheme.r : ℚ) := by
            congr 2
            omega
      _ = (chapter07BinomialPolynomial D.closedSubscheme.subscheme.r D.degree).eval
          (n : ℚ) :=
        (chapter07_binomialPolynomial_eval
          D.closedSubscheme.subscheme.r D.degree n hn).symm
  rw [chapter07_closed_subscheme_hilbert_polynomial D.closedSubscheme, hIdeal]
  rfl

theorem chapter07_hypersurface_hilbert_polynomial_eval
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (D : Chapter07HypersurfaceHilbertData k C) (n : ℕ)
    (hn : D.degree ≤ n) :
    (chapter07HilbertPolynomial D.closedSubscheme.structureSheaf).eval (n : ℚ) =
      (Nat.choose (n + D.closedSubscheme.subscheme.r)
        D.closedSubscheme.subscheme.r : ℚ) -
        (Nat.choose (n + D.closedSubscheme.subscheme.r - D.degree)
          D.closedSubscheme.subscheme.r : ℚ) := by
  rw [chapter07_hypersurface_hilbert_polynomial D]
  simp only [chapter07HypersurfaceHilbertPolynomial, Polynomial.eval_sub]
  rw [chapter07_projectiveSpaceHilbertPolynomial_eval,
    chapter07_binomialPolynomial_eval _ _ _ hn]

/-!
No smoothness field occurs in the hypersurface data: the formula is
scheme-theoretic and applies equally to singular and nonreduced hypersurfaces.
-/
theorem chapter07_plane_curve_hilbert_polynomial
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (D : Chapter07HypersurfaceHilbertData k C)
    (hplane : D.closedSubscheme.subscheme.r = 2) :
    chapter07HilbertPolynomial D.closedSubscheme.structureSheaf =
      chapter07PlaneCurveHilbertPolynomial D.degree := by
  rw [chapter07_hypersurface_hilbert_polynomial D]
  rw [hplane]
  simp [chapter07HypersurfaceHilbertPolynomial,
    chapter07ProjectiveSpaceHilbertPolynomial, chapter07BinomialPolynomial,
    Finset.prod_range_succ]
  push_cast
  ring

theorem chapter07_plane_curve_hilbert_polynomial_eval
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (D : Chapter07HypersurfaceHilbertData k C)
    (hplane : D.closedSubscheme.subscheme.r = 2) (n : ℕ) :
    (chapter07HilbertPolynomial D.closedSubscheme.structureSheaf).eval (n : ℚ) =
      (D.degree : ℚ) * n + 1 -
        (((D.degree : ℚ) - 1) * ((D.degree : ℚ) - 2) / 2) := by
  rw [chapter07_plane_curve_hilbert_polynomial D hplane]
  simp [chapter07PlaneCurveHilbertPolynomial]
  ring

/-! A zero-dimensional coherent sheaf is represented by its total length. -/
structure Chapter07ZeroDimensionalHilbertData
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k} where
  setup : Chapter07HilbertSetup k C
  length : ℕ
  supportDimension : Chapter07SupportDimensionCertificate setup.F
  supportDimension_zero : supportDimension.dimension = 0
  eulerCharacteristic_eq_length : ∀ n : ℕ,
    chapter07EulerCharacteristic setup n = (length : ℤ)

theorem chapter07_zero_dimensional_hilbert_polynomial
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (D : Chapter07ZeroDimensionalHilbertData (k := k) (C := C)) :
    chapter07HilbertPolynomial D.setup = Polynomial.C (D.length : ℚ) := by
  have h := chapter07_hilbert_polynomial_unique D.setup
    (show Chapter07PolynomialMatchesEventually
        (Polynomial.C (D.length : ℚ))
        (chapter07EulerCharacteristic D.setup) from by
      refine ⟨0, fun n _ => ?_⟩
      simp [D.eulerCharacteristic_eq_length n])
  exact h.symm

structure Chapter07DoubledPointHilbertData
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k} where
  doubled : Chapter07ZeroDimensionalHilbertData (k := k) (C := C)
  reducedSupport : Chapter07ZeroDimensionalHilbertData (k := k) (C := C)
  thickeningSequence :
    Chapter07ShortExactSequence reducedSupport.setup.F doubled.setup.F
      reducedSupport.setup.F
  doubledLength : doubled.length = 2
  reducedLength : reducedSupport.length = 1

theorem chapter07_doubled_point_hilbert_polynomials
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (D : Chapter07DoubledPointHilbertData (k := k) (C := C)) :
    chapter07HilbertPolynomial D.doubled.setup = Polynomial.C 2 ∧
      chapter07HilbertPolynomial D.reducedSupport.setup = Polynomial.C 1 := by
  constructor
  · rw [chapter07_zero_dimensional_hilbert_polynomial D.doubled, D.doubledLength]
  · rw [chapter07_zero_dimensional_hilbert_polynomial D.reducedSupport,
      D.reducedLength]

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter07
