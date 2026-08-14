import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter09.Dependencies

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter09

noncomputable section

open CategoryTheory
open AlgebraicGeometry

universe u

/-! ## 9.3 Determinants, sections, and forms -/

abbrev Chapter09Section
    {X : Scheme.{u}} {r : ℕ} (E : Chapter09VectorBundle X r) :=
  E.carrier.val.sections

abbrev Chapter09PullbackSectionData
    {S T : Scheme.{u}} (p : T ⟶ S) (M : S.Modules) :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.Chapter02PullbackSectionData p M

noncomputable def chapter09PullbackSectionData
    {S T : Scheme.{u}} (p : T ⟶ S) (M : S.Modules) :
    Chapter09PullbackSectionData p M :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.chapter02PullbackSectionData p M

noncomputable def chapter09TensorModule
    {X : Scheme.{u}} (M N : X.Modules) : X.Modules :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.chapter02Tensor M N

noncomputable def chapter09TensorPower
    {X : Scheme.{u}} (M : X.Modules) (n : ℕ) : X.Modules :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.chapter02TensorPower M n

noncomputable def chapter09LineBundleTensorPower
    {X : Scheme.{u}} (L : Chapter09LineBundle X) (n : ℕ) : Chapter09LineBundle X where
  carrier := chapter09TensorPower L.carrier n
  locallyFree := by sorry

/-! ### Closed subschemes and regular sections -/

abbrev Chapter09ClosedSubscheme (X : Scheme.{u}) := X.IdealSheafData

noncomputable def chapter09ClosedSubschemeScheme
    {X : Scheme.{u}} (Z : Chapter09ClosedSubscheme X) : Scheme.{u} :=
  Z.subscheme

noncomputable def chapter09ClosedSubschemeInclusion
    {X : Scheme.{u}} (Z : Chapter09ClosedSubscheme X) :
    chapter09ClosedSubschemeScheme Z ⟶ X :=
  Z.subschemeι

theorem chapter09_closedSubscheme_inclusion_isClosedImmersion
    {X : Scheme.{u}} (Z : Chapter09ClosedSubscheme X) :
    IsClosedImmersion (chapter09ClosedSubschemeInclusion Z) := by
  infer_instance

/- LOCAL_DEPENDENCY_GUESS: the dual-evaluation map and its sheaf-theoretic regularity test. -/
noncomputable def chapter09SectionAsMap
    {X : Scheme.{u}} (L : Chapter09LineBundle X) (s : Chapter09Section L) :
    SheafOfModules.unit X.ringCatSheaf ⟶ L.carrier := by
  sorry

def chapter09RegularSection
    {X : Scheme.{u}} (L : Chapter09LineBundle X) (s : Chapter09Section L) : Prop :=
  Mono (chapter09SectionAsMap L s)

/-! ### Missing finite-locally-free operations -/

/- LOCAL_DEPENDENCY_GUESS: pinned Mathlib has the presheaf tensor carrier but no complete sheaf
internal-Hom/symmetric/exterior-power package for finite locally free module sheaves. -/
noncomputable def chapter09DualModule
    {X : Scheme.{u}} (M : X.Modules) : X.Modules := by
  sorry

noncomputable def chapter09SymmetricPowerModule
    {X : Scheme.{u}} (n : ℕ) (M : X.Modules) : X.Modules := by
  sorry

noncomputable def chapter09ExteriorPowerModule
    {X : Scheme.{u}} (n : ℕ) (M : X.Modules) : X.Modules := by
  sorry

noncomputable def chapter09InternalHomModule
    {X : Scheme.{u}} (M N : X.Modules) : X.Modules := by
  sorry

noncomputable def chapter09TensorSwap
    {X : Scheme.{u}} (M N : X.Modules) :
    chapter09TensorModule M N ⟶ chapter09TensorModule N M := by
  sorry

noncomputable def chapter09BilinearFormAdjoint
    {X : Scheme.{u}} {r : ℕ} (E : Chapter09VectorBundle X r)
    (L : Chapter09LineBundle X)
    (b : chapter09TensorModule E.carrier E.carrier ⟶ L.carrier) :
    E.carrier ⟶ chapter09TensorModule (chapter09DualModule E.carrier) L.carrier := by
  sorry

/-! ### Operations on finite locally free sheaves -/

/- LOCAL_DEPENDENCY_GUESS: the determinant is the top exterior power of a finite locally free
sheaf; the pinned sheaf API does not provide this as a bundled module-sheaf operation. -/
noncomputable def chapter09DeterminantModule
    {X : Scheme.{u}} {r : ℕ} (M : X.Modules) : X.Modules :=
  chapter09ExteriorPowerModule r M

theorem chapter09_determinant_commutes_with_pullback
    {X Y : Scheme.{u}} (f : Y ⟶ X) {r : ℕ} (M : X.Modules) :
    Chapter09PullbackModule f (chapter09DeterminantModule M) ≅
      chapter09DeterminantModule (Chapter09PullbackModule f M) := by
  sorry

theorem chapter09_tensor_commutes_with_pullback
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M N : X.Modules) :
    Chapter09PullbackModule f (chapter09TensorModule M N) ≅
      chapter09TensorModule (Chapter09PullbackModule f M) (Chapter09PullbackModule f N) := by
  sorry

theorem chapter09_dual_commutes_with_pullback
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules) :
    Chapter09PullbackModule f (chapter09DualModule M) ≅
      chapter09DualModule (Chapter09PullbackModule f M) := by
  sorry

theorem chapter09_symmetric_power_commutes_with_pullback
    {X Y : Scheme.{u}} (f : Y ⟶ X) (n : ℕ) (M : X.Modules) :
    Chapter09PullbackModule f (chapter09SymmetricPowerModule n M) ≅
      chapter09SymmetricPowerModule n (Chapter09PullbackModule f M) := by
  sorry

theorem chapter09_exterior_power_commutes_with_pullback
    {X Y : Scheme.{u}} (f : Y ⟶ X) (n : ℕ) (M : X.Modules) :
    Chapter09PullbackModule f (chapter09ExteriorPowerModule n M) ≅
      chapter09ExteriorPowerModule n (Chapter09PullbackModule f M) := by
  sorry

theorem chapter09_internal_hom_commutes_with_pullback
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M N : X.Modules) :
    Chapter09PullbackModule f (chapter09InternalHomModule M N) ≅
      chapter09InternalHomModule (Chapter09PullbackModule f M)
        (Chapter09PullbackModule f N) := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the operation-specific overlap comparison maps are not packaged by
pinned Mathlib, so their descent compatibility is exposed as named predicates. -/
def chapter09TensorDescentCompatible
    {S T : Scheme.{u}} {p : T ⟶ S} {r s : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (E : Chapter09ModuleDescentDatum p s) : Prop := by
  sorry

def chapter09DualDescentCompatible
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (D : Chapter09ModuleDescentDatum p r) : Prop := by
  sorry

def chapter09SymmetricPowerDescentCompatible
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (n : ℕ) (D : Chapter09ModuleDescentDatum p r) : Prop := by
  sorry

def chapter09ExteriorPowerDescentCompatible
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (n : ℕ) (D : Chapter09ModuleDescentDatum p r) : Prop := by
  sorry

def chapter09InternalHomDescentCompatible
    {S T : Scheme.{u}} {p : T ⟶ S} {r s : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (E : Chapter09ModuleDescentDatum p s) : Prop := by
  sorry

theorem chapter09_tensor_preserves_descent
    {S T : Scheme.{u}} {p : T ⟶ S} {r s : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (E : Chapter09ModuleDescentDatum p s) :
    chapter09TensorDescentCompatible D E := by
  sorry

theorem chapter09_dual_preserves_descent
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (D : Chapter09ModuleDescentDatum p r) :
    chapter09DualDescentCompatible D := by
  sorry

theorem chapter09_symmetric_power_preserves_descent
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (n : ℕ) (D : Chapter09ModuleDescentDatum p r) :
    chapter09SymmetricPowerDescentCompatible n D := by
  sorry

theorem chapter09_exterior_power_preserves_descent
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (n : ℕ) (D : Chapter09ModuleDescentDatum p r) :
    chapter09ExteriorPowerDescentCompatible n D := by
  sorry

theorem chapter09_internal_hom_preserves_descent
    {S T : Scheme.{u}} {p : T ⟶ S} {r s : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (E : Chapter09ModuleDescentDatum p s) :
    chapter09InternalHomDescentCompatible D E := by
  sorry

/-! ### Bilinear forms -/

structure Chapter09BilinearForm
    {X : Scheme.{u}} {r : ℕ}
    (E : Chapter09VectorBundle X r) (L : Chapter09LineBundle X) where
  map : chapter09TensorModule E.carrier E.carrier ⟶ L.carrier

def chapter09BilinearFormIsSymmetric
    {X : Scheme.{u}} {r : ℕ}
    {E : Chapter09VectorBundle X r} {L : Chapter09LineBundle X}
    (b : Chapter09BilinearForm E L) : Prop :=
  b.map = chapter09TensorSwap E.carrier E.carrier ≫ b.map

def chapter09BilinearFormIsAlternating
    {X : Scheme.{u}} {r : ℕ}
    {E : Chapter09VectorBundle X r} {L : Chapter09LineBundle X}
    (b : Chapter09BilinearForm E L) : Prop :=
  b.map = -(chapter09TensorSwap E.carrier E.carrier ≫ b.map)

def chapter09BilinearFormIsPerfect
    {X : Scheme.{u}} {r : ℕ}
    {E : Chapter09VectorBundle X r} {L : Chapter09LineBundle X}
    (b : Chapter09BilinearForm E L) : Prop :=
  IsIso (chapter09BilinearFormAdjoint E L b.map)

/- LOCAL_DEPENDENCY_GUESS: compatibility of a bilinear form with two descent data. -/
def chapter09BilinearFormCompatibleWithDescent
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (L : Chapter09LineBundleDescentDatum p)
    (b : Chapter09BilinearForm D.upstairs L.upstairs) : Prop := by
  sorry

def chapter09BilinearFormComparisonCompatible
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (L : Chapter09LineBundleDescentDatum p)
    (b : Chapter09BilinearForm D.upstairs L.upstairs)
    (E : Chapter09VectorBundle S r) (K : Chapter09LineBundle S)
    (b₀ : Chapter09BilinearForm E K)
    (eE : (chapter09PullbackVectorBundle p E).carrier ≅ D.upstairs.carrier)
    (eK : (chapter09PullbackLineBundle p K).carrier ≅ L.upstairs.carrier) : Prop := by
  sorry

structure Chapter09BilinearFormDescentResult
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (L : Chapter09LineBundleDescentDatum p)
    (b : Chapter09BilinearForm D.upstairs L.upstairs) where
  downstairsVectorBundle : Chapter09VectorBundle S r
  downstairsLineBundle : Chapter09LineBundle S
  downstairsForm :
    Chapter09BilinearForm downstairsVectorBundle downstairsLineBundle
  comparisonVector :
    (chapter09PullbackVectorBundle p downstairsVectorBundle).carrier ≅ D.upstairs.carrier
  comparisonLine :
    (chapter09PullbackLineBundle p downstairsLineBundle).carrier ≅ L.upstairs.carrier
  compatible : chapter09BilinearFormComparisonCompatible D L b
    downstairsVectorBundle downstairsLineBundle downstairsForm comparisonVector comparisonLine

theorem chapter09_bilinear_form_effective_descent
    {S T : Scheme.{u}} {p : T ⟶ S} (hp : Chapter09FpqcCover p) {r : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (L : Chapter09LineBundleDescentDatum p)
    (b : Chapter09BilinearForm D.upstairs L.upstairs)
    (hb : chapter09BilinearFormCompatibleWithDescent D L b) :
    Nonempty (Chapter09BilinearFormDescentResult D L b) := by
  sorry

theorem chapter09_symmetric_bilinear_form_descends
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (L : Chapter09LineBundleDescentDatum p)
    (b : Chapter09BilinearForm D.upstairs L.upstairs)
    (R : Chapter09BilinearFormDescentResult D L b)
    (hb : chapter09BilinearFormIsSymmetric b) :
    chapter09BilinearFormIsSymmetric R.downstairsForm := by
  sorry

theorem chapter09_alternating_bilinear_form_descends
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (L : Chapter09LineBundleDescentDatum p)
    (b : Chapter09BilinearForm D.upstairs L.upstairs)
    (R : Chapter09BilinearFormDescentResult D L b)
    (hb : chapter09BilinearFormIsAlternating b) :
    chapter09BilinearFormIsAlternating R.downstairsForm := by
  sorry

theorem chapter09_perfect_bilinear_form_descends
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (L : Chapter09LineBundleDescentDatum p)
    (b : Chapter09BilinearForm D.upstairs L.upstairs)
    (R : Chapter09BilinearFormDescentResult D L b)
    (hb : chapter09BilinearFormIsPerfect b) :
    chapter09BilinearFormIsPerfect R.downstairsForm := by
  sorry

/-! ### Sections -/

noncomputable def chapter09PullbackSection
    {S T : Scheme.{u}} (p : T ⟶ S) {r : ℕ}
    (E : Chapter09VectorBundle S r) (s : Chapter09Section E) :
    Chapter09Section (chapter09PullbackVectorBundle p E) :=
  (chapter09PullbackSectionData p E.carrier).map s

def chapter09SectionCompatibleWithDescent
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (D : Chapter09ModuleDescentDatum p r) (s : Chapter09Section D.upstairs) : Prop :=
  SheafOfModules.sectionsMap D.overlapIso.hom
      ((chapter09PullbackSectionData (chapter09DoubleFirst p) D.upstairs.carrier).map s) =
    (chapter09PullbackSectionData (chapter09DoubleSecond p) D.upstairs.carrier).map s

theorem chapter09_section_descends_iff_overlap_compatibility
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (D : Chapter09ModuleDescentDatum p r) (s : Chapter09Section D.upstairs) :
    chapter09SectionCompatibleWithDescent D s ↔
      SheafOfModules.sectionsMap D.overlapIso.hom
          ((chapter09PullbackSectionData (chapter09DoubleFirst p)
            D.upstairs.carrier).map s) =
        (chapter09PullbackSectionData (chapter09DoubleSecond p)
          D.upstairs.carrier).map s := by
  rfl

def chapter09SectionMatchesDescentComparison
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (R : Chapter09VectorBundleDescentResult D)
    (s : Chapter09Section D.upstairs)
    (s₀ : Chapter09Section R.downstairs) : Prop :=
  SheafOfModules.sectionsMap R.comparison.hom
      ((chapter09PullbackSectionData p R.downstairs.carrier).map s₀) = s

theorem chapter09_section_effective_descent
    {S T : Scheme.{u}} {p : T ⟶ S} (hp : Chapter09FpqcCover p) {r : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (R : Chapter09VectorBundleDescentResult D)
    (s : Chapter09Section D.upstairs)
    (hs : chapter09SectionCompatibleWithDescent D s) :
    ∃ s₀ : Chapter09Section R.downstairs,
      chapter09SectionMatchesDescentComparison D R s s₀ := by
  sorry

/-! ### Zero schemes and regular sections -/

/- LOCAL_DEPENDENCY_GUESS: the dual of a finite locally free sheaf and its evaluation map. -/
structure Chapter09ZeroScheme
    {X : Scheme.{u}} {r : ℕ}
    (E : Chapter09VectorBundle X r) (s : Chapter09Section E) where
  idealSheaf : Chapter09ClosedSubscheme X
  dualMap : chapter09DualModule E.carrier ⟶ SheafOfModules.unit X.ringCatSheaf
  isDefinedByDualMap : Prop

theorem chapter09_zero_scheme_exists
    {X : Scheme.{u}} {r : ℕ}
    (E : Chapter09VectorBundle X r) (s : Chapter09Section E) :
    Nonempty (Chapter09ZeroScheme E s) := by
  sorry

noncomputable def chapter09ZeroScheme
    {X : Scheme.{u}} {r : ℕ}
    (E : Chapter09VectorBundle X r) (s : Chapter09Section E) :
    Chapter09ZeroScheme E s :=
  Classical.choice (chapter09_zero_scheme_exists E s)

noncomputable def chapter09ZeroSubscheme
    {X : Scheme.{u}} {r : ℕ}
    (E : Chapter09VectorBundle X r) (s : Chapter09Section E) : Scheme.{u} :=
  (chapter09ZeroScheme E s).idealSheaf.subscheme

noncomputable def chapter09ZeroSubschemeInclusion
    {X : Scheme.{u}} {r : ℕ}
    (E : Chapter09VectorBundle X r) (s : Chapter09Section E) :
    chapter09ZeroSubscheme E s ⟶ X :=
  (chapter09ZeroScheme E s).idealSheaf.subschemeι

theorem chapter09_zero_subscheme_isClosed
    {X : Scheme.{u}} {r : ℕ}
    (E : Chapter09VectorBundle X r) (s : Chapter09Section E) :
    IsClosedImmersion (chapter09ZeroSubschemeInclusion E s) := by
  infer_instance

def chapter09ZeroSchemeCompatibleWithDescent
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (s : Chapter09Section D.upstairs)
    (Z : Chapter09ZeroScheme D.upstairs s) : Prop := by
  sorry

def chapter09ZeroSchemeMatchesDescent
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (R : Chapter09VectorBundleDescentResult D)
    (s : Chapter09Section D.upstairs)
    (s₀ : Chapter09Section R.downstairs)
    (Z : Chapter09ZeroScheme D.upstairs s)
    (Z₀ : Chapter09ZeroScheme R.downstairs s₀) : Prop := by
  sorry

theorem chapter09_zero_scheme_effective_descent
    {S T : Scheme.{u}} {p : T ⟶ S} (hp : Chapter09FpqcCover p) {r : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (R : Chapter09VectorBundleDescentResult D)
    (s : Chapter09Section D.upstairs)
    (hs : chapter09SectionCompatibleWithDescent D s)
    (Z : Chapter09ZeroScheme D.upstairs s)
    (hZ : chapter09ZeroSchemeCompatibleWithDescent D s Z) :
    ∃ s₀ : Chapter09Section R.downstairs,
      ∃ Z₀ : Chapter09ZeroScheme R.downstairs s₀,
        chapter09SectionMatchesDescentComparison D R s s₀ ∧
          chapter09ZeroSchemeMatchesDescent D R s s₀ Z Z₀ := by
  sorry

theorem chapter09_regular_section_reflected_by_fpqc
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter09FpqcCover p)
    (L : Chapter09LineBundle S) (s : Chapter09Section L) :
    chapter09RegularSection L s ↔
      chapter09RegularSection (chapter09PullbackLineBundle p L)
        (chapter09PullbackSection p L s) := by
  sorry

/-! ### Effective Cartier divisors -/

structure Chapter09EffectiveCartierDivisor (X : Scheme.{u}) where
  lineBundle : Chapter09LineBundle X
  section : Chapter09Section lineBundle
  regular : chapter09RegularSection lineBundle section
  zeroScheme : Chapter09ZeroScheme lineBundle section

structure Chapter09EffectiveCartierDivisorDescentDatum
    {S T : Scheme.{u}} (p : T ⟶ S) where
  lineBundleDatum : Chapter09LineBundleDescentDatum p
  upstairsDivisor : Chapter09EffectiveCartierDivisor T
  line_carrier_agrees : upstairsDivisor.lineBundle.carrier = lineBundleDatum.upstairs.carrier
  section_compatible : Prop
  zero_scheme_compatible : Prop

def chapter09EffectiveCartierDivisorMatches
    {S T : Scheme.{u}} {p : T ⟶ S}
    (D : Chapter09LineBundleDescentDatum p)
    (R : Chapter09VectorBundleDescentResult D)
    (d : Chapter09EffectiveCartierDivisor T)
    (d₀ : Chapter09EffectiveCartierDivisor S) : Prop := by
  sorry

theorem chapter09_effective_cartier_divisor_effective_descent
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter09FpqcCover p)
    (D : Chapter09EffectiveCartierDivisorDescentDatum p)
    (R : Chapter09VectorBundleDescentResult D.lineBundleDatum) :
    ∃ d₀ : Chapter09EffectiveCartierDivisor S,
      chapter09EffectiveCartierDivisorMatches D.lineBundleDatum R D.upstairsDivisor d₀ := by
  sorry

end
end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter09
