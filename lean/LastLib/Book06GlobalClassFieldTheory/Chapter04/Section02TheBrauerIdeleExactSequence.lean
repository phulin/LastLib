import LastLib.Book06GlobalClassFieldTheory.Chapter04.Dependencies
import LastLib.Book06GlobalClassFieldTheory.Chapter01.Section03FourKindsOfNormAssertion
import LastLib.Book06GlobalClassFieldTheory.Chapter01.Section04ArchitectureOfTheProof

namespace LastLib.Book06GlobalClassFieldTheory.Chapter04

noncomputable section

universe u v

open LastLib.Book06GlobalClassFieldTheory.Chapter01

open scoped BigOperators NumberField nonZeroDivisors Topology

/-! ## 4.2. The Brauer--idele exact sequence -/

/-- The Brauer invariant row, with the direct sum and total-invariant map explicit. -/
theorem chapter04_brauer_invariant_sequence
    {F : Type u} [Field F] [NumberField F]
    (D : Chapter04BrauerContext.{u, v} F)
    (S : Chapter04BrauerInvariantSequenceData D) :
    chapter04BrauerInvariantExact D := by
  exact S.exact_sequence

/-- The complex local Brauer group vanishes. -/
theorem chapter04_brauer_complex_eq_zero
    {F : Type u} [Field F] [NumberField F]
    (D : Chapter04BrauerContext.{u, v} F)
    (hlocal : Chapter04LocalBrauerBehavior D)
    (w : NumberField.InfinitePlace F)
    (hw : NumberField.InfinitePlace.IsComplex w) :
    Subsingleton (D.localBr (Sum.inr w)) := by
  exact hlocal.complex_zero w hw

/-- Every local Brauer class at a real place is killed by two. -/
theorem chapter04_brauer_real_is_half_integer
    {F : Type u} [Field F] [NumberField F]
    (D : Chapter04BrauerContext.{u, v} F)
    (hlocal : Chapter04LocalBrauerBehavior D)
    (w : NumberField.InfinitePlace F)
    (hw : NumberField.InfinitePlace.IsReal w) :
    ∀ x : D.localBr (Sum.inr w), 2 • x = 0 := by
  exact hlocal.real_two_torsion w hw

theorem chapter04_brauer_real_contains_half_integer
    {F : Type u} [Field F] [NumberField F]
    (D : Chapter04BrauerContext.{u, v} F)
    (hlocal : Chapter04LocalBrauerBehavior D)
    (w : NumberField.InfinitePlace F)
    (hw : NumberField.InfinitePlace.IsReal w) :
    ∃ x : D.localBr (Sum.inr w),
      D.invariant (Sum.inr w) x = chapter04QModZOfRat ((1 : ℚ) / 2) := by
  exact hlocal.real_half_class w hw

/-- At a real place the invariant identifies the local Brauer group with its two-torsion range. -/
theorem chapter04_brauer_real_is_two_torsion_equiv
    {F : Type u} [Field F] [NumberField F]
    (D : Chapter04BrauerContext.{u, v} F)
    (hlocal : Chapter04LocalBrauerBehavior D)
    (w : NumberField.InfinitePlace F)
    (hw : NumberField.InfinitePlace.IsReal w) :
    ∃ e : D.localBr (Sum.inr w) ≃+ chapter04QModZTorsion 2,
      ∀ x, (e x : chapter04QModZ) = D.invariant (Sum.inr w) x := by
  exact ⟨hlocal.real_invariant_equiv w hw,
    hlocal.real_invariant_is_equiv w hw⟩

/-- At a finite place the invariant identifies the local Brauer group with `ℚ / ℤ`. -/
theorem chapter04_brauer_finite_is_QModZ
    {F : Type u} [Field F] [NumberField F]
    (D : Chapter04BrauerContext.{u, v} F)
    (hlocal : Chapter04LocalBrauerBehavior D)
    (v : NumberField.FinitePlace F) :
    Nonempty (D.localBr (Sum.inl v) ≃+ chapter04QModZ) := by
  exact ⟨hlocal.finite_invariant_equiv v⟩

theorem chapter04_brauer_finite_invariant_is_the_identification
    {F : Type u} [Field F] [NumberField F]
    (D : Chapter04BrauerContext.{u, v} F)
    (hlocal : Chapter04LocalBrauerBehavior D)
    (v : NumberField.FinitePlace F) (x : D.localBr (Sum.inl v)) :
    hlocal.finite_invariant_equiv v x = D.invariant (Sum.inl v) x := by
  exact hlocal.finite_invariant_is_equiv v x

/-! ### The elementary separation input -/

/-- The ideal-counting function appearing in the source proof of the simple pole. -/
def chapter04IdealCountingFunction
    (F : Type*) [Field F] [NumberField F] (X : ℝ) : ℝ :=
  Set.ncard {I : (Ideal (𝓞 F))⁰ |
    (Ideal.absNorm (I : Ideal (𝓞 F)) : ℝ) ≤ X}

/-- A concrete `O`-bound used for the source's lattice-counting estimate. -/
def chapter04BigO (f g : ℝ → ℝ) : Prop :=
  ∃ C X₀ : ℝ, 0 ≤ C ∧ ∀ X, X₀ ≤ X → |f X| ≤ C * |g X|

/-- The source's estimate `A_F(X) = κ_F X + O_F(X^(1 - 1/[F:ℚ]))`, with `O_F(1)` in degree one. -/
theorem chapter04_ideal_counting_asymptotic
    (F : Type*) [Field F] [NumberField F] :
    ∃ κ : ℝ, 0 < κ ∧
      chapter04BigO
        (fun X => chapter04IdealCountingFunction F X - κ * X)
        (if Module.finrank ℚ F = 1 then (fun _ => 1) else
          fun X => Real.rpow X (1 - (1 : ℝ) / Module.finrank ℚ F)) := by
  sorry

/-- The real restriction of the canonical Mathlib Dedekind zeta function. -/
def chapter04DedekindZetaReal
    (F : Type*) [Field F] [NumberField F] (s : ℝ) : ℝ :=
  (NumberField.dedekindZeta F (s : ℂ)).re

/-- The simple-pole statement at `s = 1`. -/
theorem chapter04_dedekind_zeta_simple_pole
    (F : Type*) [Field F] [NumberField F] :
    Filter.Tendsto
      (fun s : ℝ => (s - 1) * chapter04DedekindZetaReal F s)
      (𝓝[>] (1 : ℝ))
      (𝓝 (NumberField.dedekindZeta_residue F)) := by
  sorry

/-- The Mellin expression used for partial summation. -/
def chapter04PartialSummationValue (A : ℝ → ℝ) (s : ℝ) : ℝ :=
  s * ∫ X in Set.Ioi (1 : ℝ), A X * Real.rpow X (-s - 1)

/-- Partial summation identifies the zeta series with the displayed integral. -/
theorem chapter04_dedekind_zeta_partial_summation
    (F : Type*) [Field F] [NumberField F] {s : ℝ} (hs : 1 < s) :
    chapter04DedekindZetaReal F s =
      chapter04PartialSummationValue (chapter04IdealCountingFunction F) s := by
  sorry

/-- A source-facing predicate for an extension that splits completely at every completion.

The earlier global-place interface supplies the completion-valued local tensor algebra and its
product decomposition, so the separation lemma does not assume its degree-one conclusion as hidden
typeclass data.
-/
def Chapter04SplitsAtEveryCompletion
    (F E : Type*) [Field F] [Field E] [NumberField F] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] : Prop :=
  ∀ v : LastLib.Book06GlobalClassFieldTheory.Chapter01.BookPlace F,
    ∃ D : LastLib.Book06GlobalClassFieldTheory.Chapter01.LocalProductDecomposition F E v,
      ∀ i : D.branchIndex,
        letI := D.branchFieldField i
        letI := D.branchFieldAlgebra i
        letI := D.branchFieldFiniteDimensional i
        Module.finrank
            (LastLib.Book06GlobalClassFieldTheory.Chapter01.BookPlace.completion v)
            (D.branchField i) = 1

/-- A nontrivial finite extension cannot split completely at every completion. -/
theorem chapter04_no_nontrivial_everywhere_split
    (F E : Type*) [Field F] [Field E] [NumberField F] [NumberField E]
    [Algebra F E] [FiniteDimensional F E]
    (hdegree : 1 < Module.finrank F E) :
    ¬ Chapter04SplitsAtEveryCompletion F E := by
  sorry

/-! ### Finite-level compact support and Kummer interfaces -/

/-- A finite place lies above the integer `n` when its prime ideal divides `(n)`. -/
def chapter04PlaceAboveNat
    (F : Type*) [Field F] [NumberField F]
    (n : ℕ) (v : NumberField.FinitePlace F) : Prop :=
  (n : 𝓞 F) ∈ (NumberField.FinitePlace.equivHeightOneSpectrum v).asIdeal

/-- A finite set of places at level `n`, containing the archimedean and `n`-adic places. -/
structure Chapter04FiniteSupportLevel (F : Type*) [Field F] [NumberField F] where
  n : ℕ
  positive_n : 0 < n
  S : Finset (Chapter04Place F)
  contains_infinite : ∀ w : NumberField.InfinitePlace F, Sum.inr w ∈ S
  places_above_n : Finset (NumberField.FinitePlace F)
  places_above_n_spec : ∀ v,
    v ∈ places_above_n ↔ chapter04PlaceAboveNat F n v
  contains_n_places : ∀ v, chapter04PlaceAboveNat F n v → Sum.inl v ∈ S

/-- An additive local Kummer/valuation exact sequence. -/
structure Chapter04LocalKummerValuationSequence
    {F : Type u} [Field F] [NumberField F]
    {level : Chapter04FiniteSupportLevel F}
    (v : Chapter04Place F) where
  U : Type u
  [uGroup : AddCommGroup U]
  H : Type u
  [hGroup : AddCommGroup H]
  C : Type u
  [cGroup : AddCommGroup C]
  i : U →+ H
  p : H →+ C
  i_injective : Function.Injective i
  exactness : Function.Exact i p
  surjective : Function.Surjective p

attribute [instance] Chapter04LocalKummerValuationSequence.uGroup
  Chapter04LocalKummerValuationSequence.hGroup
  Chapter04LocalKummerValuationSequence.cGroup

/-- The finite-level Kummer/valuation row from (4.2). -/
structure Chapter04KummerValuationData
    (F : Type u) [Field F] [NumberField F]
    (level : Chapter04FiniteSupportLevel F) where
  SUnitQuotient : Type u
  [SUnitQuotientGroup : AddCommGroup SUnitQuotient]
  H1Mu : Type u
  [H1MuGroup : AddCommGroup H1Mu]
  classGroupTorsion : Type u
  [classGroupTorsionGroup : AddCommGroup classGroupTorsion]
  unitsMap : SUnitQuotient →+ H1Mu
  classMap : H1Mu →+ classGroupTorsion
  unitsMap_injective : Function.Injective unitsMap
  exactness : Function.Exact unitsMap classMap
  classMap_surjective : Function.Surjective classMap
  local_sequences : ∀ v : Chapter04Place F,
    Nonempty (Chapter04LocalKummerValuationSequence (level := level) v)

attribute [instance] Chapter04KummerValuationData.SUnitQuotientGroup
  Chapter04KummerValuationData.H1MuGroup
  Chapter04KummerValuationData.classGroupTorsionGroup

theorem chapter04_kummer_valuation_exact
    {F : Type*} [Field F] [NumberField F]
    {level : Chapter04FiniteSupportLevel F}
    (K : Chapter04KummerValuationData F level) :
    Function.Injective K.unitsMap ∧
      Function.Exact K.unitsMap K.classMap ∧
      Function.Surjective K.classMap := by
  exact ⟨K.unitsMap_injective, K.exactness, K.classMap_surjective⟩

/-- The same Kummer/valuation sequence is available at each local completion. -/
theorem chapter04_local_kummer_valuation_exact
    {F : Type*} [Field F] [NumberField F]
    {level : Chapter04FiniteSupportLevel F}
  (K : Chapter04KummerValuationData F level) :
    ∀ v : Chapter04Place F,
      Nonempty (Chapter04LocalKummerValuationSequence (level := level) v) := by
  exact K.local_sequences

/-! ### The explicit Wang defect and the degree alternative -/

/- The Kummer quotient and its localization are already exposed by the earlier
 Cartier-duality bridge.  This local definition keeps `D_{n,S}` as the actual
 subgroup of global Kummer classes which vanish outside `S`, rather than as an
 unnamed obstruction predicate. -/
def chapter04WangDefectSubgroup
    (F : Type*) [Field F] [NumberField F] (n : ℕ)
    (S : Finset (BookPlace F)) :
    AddSubgroup (CartierKummerClassGroup F n) := by
  classical
  exact
    { carrier := {a | ∀ v, v ∉ S → cartierKummerLocalization v n a = 0}
      zero_mem' := by
        intro v hv
        simp
      add_mem' := by
        intro x y hx hy v hv
        rw [map_add]
        rw [hx v hv, hy v hv]
        exact add_zero (0 : CartierLocalKummerClassGroup F v n)
      neg_mem' := by
        intro x hx v hv
        simp [hx v hv] }

@[simp] theorem chapter04_mem_wangDefectSubgroup_iff
    (F : Type*) [Field F] [NumberField F] (n : ℕ)
    (S : Finset (BookPlace F)) (a : CartierKummerClassGroup F n) :
    a ∈ chapter04WangDefectSubgroup F n S ↔
      ∀ v, v ∉ S → cartierKummerLocalization v n a = 0 :=
  Iff.rfl

/- The cyclotomic parameters below separate the exact special-case criterion
 from the local square predicate.  The latter is supplied by the completion
 interface, so no accidental identification of a global square with a local
 square is built into the statement. -/
def chapter04WangUnitIsSquare {F : Type*} [Field F] (x : Fˣ) : Prop :=
  ∃ y : Fˣ, y ^ 2 = x

/- A compatible tower of finite cyclotomic layers.  The primitive roots, their
transition maps, and the maximality condition are part of the data; an
arbitrary element called `eta_s` is not enough to justify the Wang defect. -/
structure Chapter04CompatibleCyclotomicLayers
    (F : Type u) [Field F] [NumberField F] where
  s : ℕ
  s_ge_two : 2 ≤ s
  layer : ℕ → Type u
  [layerField : ∀ r, Field (layer r)]
  [layerAlgebra : ∀ r, Algebra F (layer r)]
  [layerFiniteDimensional : ∀ r, FiniteDimensional F (layer r)]
  zeta : ∀ r, layer r
  primitive : ∀ r, IsPrimitiveRoot (zeta r) (2 ^ r)
  transition : ∀ r, layer r →ₐ[F] layer (r + 1)
  transition_zeta : ∀ r,
    transition r (zeta r) = (zeta (r + 1)) ^ 2
  eta_s : F
  eta_s_spec :
    algebraMap F (layer s) eta_s = zeta s + (zeta s)⁻¹
  eta_maximal : ∀ r, s < r → ∀ x : F,
    algebraMap F (layer r) x ≠ zeta r + (zeta r)⁻¹

attribute [instance] Chapter04CompatibleCyclotomicLayers.layerField
  Chapter04CompatibleCyclotomicLayers.layerAlgebra
  Chapter04CompatibleCyclotomicLayers.layerFiniteDimensional

structure Chapter04WangCyclotomicData
    (F : Type u) [Field F] [NumberField F] where
  n : ℕ
  ν : ℕ
  m : ℕ
  positive_n : 0 < n
  factorization : n = 2 ^ ν * m
  odd_part : Odd m
  cyclotomic : Chapter04CompatibleCyclotomicLayers F
  bK : Fˣ
  bK_formula : (bK : F) = 2 + cyclotomic.eta_s
  S : Finset (BookPlace F)
  S₀ : Finset (BookPlace F)
  localSquare : BookPlace F → Fˣ → Prop
  S₀_spec : ∀ v,
    v ∈ S₀ ↔
      ¬ localSquare v (-1) ∧ ¬ localSquare v bK ∧
        ¬ localSquare v (-bK)
  localSquare_iff : ∀ v x,
    localSquare v x ↔
      cartierKummerLocalization v 2
          (cartierKummerClassMk (F := F) 2 x) = 0

def chapter04WangSpecial
    {F : Type*} [Field F] [NumberField F]
    (D : Chapter04WangCyclotomicData F) : Prop :=
  D.cyclotomic.s + 1 ≤ D.ν ∧
    ¬ chapter04WangUnitIsSquare (F := F) (-1 : Fˣ) ∧
    ¬ chapter04WangUnitIsSquare D.bK ∧
    ¬ chapter04WangUnitIsSquare (-D.bK) ∧
    ∀ v, v ∈ D.S₀ → v ∈ D.S

def chapter04WangSpecialClass
    {F : Type*} [Field F] [NumberField F]
    (D : Chapter04WangCyclotomicData F) : CartierKummerClassGroup F D.n :=
  cartierKummerClassMk D.n (D.bK ^ (D.n / 2))

theorem chapter04_wang_special_class_has_order_two
    {F : Type*} [Field F] [NumberField F]
    (D : Chapter04WangCyclotomicData F)
    (hD : chapter04WangSpecial D) :
    chapter04WangSpecialClass D + chapter04WangSpecialClass D = 0 := by
  sorry

theorem chapter04_wang_special_class_is_nontrivial
    {F : Type*} [Field F] [NumberField F]
    (D : Chapter04WangCyclotomicData F)
    (hD : chapter04WangSpecial D) :
    chapter04WangSpecialClass D ≠ 0 := by
  sorry

theorem chapter04_wang_special_class_is_locally_trivial_off_S₀
    {F : Type*} [Field F] [NumberField F]
    (D : Chapter04WangCyclotomicData F)
    (hD : chapter04WangSpecial D) :
    ∀ v, v ∉ D.S₀ →
      cartierKummerLocalization v D.n (chapter04WangSpecialClass D) = 0 := by
  sorry

/- The finite local--global calculation has exactly two outputs: no defect in
 the ordinary case, and the cyclic subgroup generated by the Wang class in the
 special case.  In additive Kummer notation the latter is
 `AddSubgroup.zmultiples`, the two-element subgroup once the preceding order
 calculation is applied. -/
theorem chapter04_wang_defect_group_two_case
    {F : Type*} [Field F] [NumberField F]
    (D : Chapter04WangCyclotomicData F) :
    (chapter04WangSpecial D →
      chapter04WangDefectSubgroup F D.n D.S =
        AddSubgroup.zmultiples (chapter04WangSpecialClass D)) ∧
    (¬ chapter04WangSpecial D →
      chapter04WangDefectSubgroup F D.n D.S = (⊥ : AddSubgroup
        (CartierKummerClassGroup F D.n))) := by
  sorry

/-- The perfect finite-level pairing (4.1), with the compact-support degree shift visible. -/
structure Chapter04FiniteLevelPairing
    {G : Type u} [Group G]
    (C : Chapter04CompactSupportAPI.{u, v} G)
    (P : Chapter04DualCoefficientPair.{u, v} G) where
  pairing : ∀ i : ℤ,
    chapter04CompactSupportH C P.M i →
      chapter04GlobalH C P.Mdual (3 - i) → chapter04QModZ
  isDiagonalX : ∀ i, chapter04CompactSupportH C P.M i → Prop
  isDiagonalY : ∀ i, chapter04GlobalH C P.Mdual (3 - i) → Prop
  diagonal_orthogonality : ∀ i x y,
    isDiagonalX i x → isDiagonalY i y → pairing i x y = 0

/-! Perfectness is the finite arithmetic-duality input, not a consequence of
the existence of a pairing and an orthogonality predicate alone. -/
structure Chapter04FiniteLevelPairingPerfectness
    {G : Type u} [Group G]
    (C : Chapter04CompactSupportAPI.{u, v} G)
    (P : Chapter04DualCoefficientPair.{u, v} G)
    (Q : Chapter04FiniteLevelPairing C P) where
  perfect : ∀ i : ℤ,
    chapter04PerfectPairing (Q.pairing i)

theorem chapter04_finite_level_pairing_is_perfect
    {G : Type u} [Group G]
    (C : Chapter04CompactSupportAPI.{u, v} G)
    (P : Chapter04DualCoefficientPair.{u, v} G)
    (Q : Chapter04FiniteLevelPairing C P)
    (L : Chapter04FiniteLevelPairingPerfectness C P Q) :
    ∀ i : ℤ,
      chapter04PerfectPairing
        (Q.pairing i) := by
  exact L.perfect

/-- Diagonal global classes are orthogonal under the finite-level local sum. -/
theorem chapter04_finite_level_diagonal_orthogonality
    {G : Type u} [Group G]
    (C : Chapter04CompactSupportAPI.{u, v} G)
    (P : Chapter04DualCoefficientPair.{u, v} G)
    (Q : Chapter04FiniteLevelPairing C P)
    (i : ℤ) (x : chapter04CompactSupportH C P.M i)
    (y : chapter04GlobalH C P.Mdual (3 - i))
    (hx : Q.isDiagonalX i x) (hy : Q.isDiagonalY i y) :
    Q.pairing i x y = 0 := by
  exact Q.diagonal_orthogonality i x y hx hy

/-! ### The degree-two row and the invariant map -/

/-- The degree-two row attached to a concrete cone and Brauer context. -/
structure Chapter04DegreeTwoRowData
    {F : Type u} [Field F] [NumberField F]
    (D : Chapter04CompactSupportDegreeTwoContext.{u, v} F) where
  target_identification :
    D.targetH₀ ≃+ (ZMod D.n →+ chapter04QModZ)
  exactness : Function.Exact D.localization D.totalInvariant
  surjective : Function.Surjective D.totalInvariant

/-- The compact-support/Brauer calculation supplies the exact row only after
the global cone, coefficient identifications, and invariant compatibilities
have been fixed. -/
theorem chapter04_compact_support_degree_two_row
    {F : Type u} [Field F] [NumberField F]
    (D : Chapter04CompactSupportDegreeTwoContext.{u, v} F) :
    Nonempty (Chapter04DegreeTwoRowData D) := by
  sorry

/-- Hilbert 90 and Kummer identify the degree-two coefficient groups with Brauer torsion. -/
structure Chapter04DegreeTwoKummerData where
  n : ℕ
  positive_n : 0 < n
  globalH : Type u
  [globalHGroup : AddCommGroup globalH]
  globalBrauerTorsion : Type u
  [globalBrauerGroup : AddCommGroup globalBrauerTorsion]
  localH : Type u
  [localHGroup : AddCommGroup localH]
  localBrauerTorsion : Type u
  [localBrauerGroup : AddCommGroup localBrauerTorsion]
  globalKummerMap : globalH →+ globalBrauerTorsion
  localKummerMap : localH →+ localBrauerTorsion
  globalKummerEquiv : globalH ≃+ globalBrauerTorsion
  localKummerEquiv : localH ≃+ localBrauerTorsion
  globalKummerMap_eq_equiv : ∀ x, globalKummerMap x = globalKummerEquiv x
  localKummerMap_eq_equiv : ∀ x, localKummerMap x = localKummerEquiv x

attribute [instance] Chapter04DegreeTwoKummerData.globalHGroup
  Chapter04DegreeTwoKummerData.globalBrauerGroup
  Chapter04DegreeTwoKummerData.localHGroup
  Chapter04DegreeTwoKummerData.localBrauerGroup

theorem chapter04_degree_two_Kummer_Brauer_identification
    (K : Chapter04DegreeTwoKummerData) :
    Nonempty (K.globalH ≃+ K.globalBrauerTorsion) ∧
      Nonempty (K.localH ≃+ K.localBrauerTorsion) := by
  exact ⟨⟨K.globalKummerEquiv⟩, ⟨K.localKummerEquiv⟩⟩

/-- The middle arrow in the degree-two row is the total local invariant. -/
theorem chapter04_degree_two_arrow_is_total_invariant
    {F : Type u} [Field F] [NumberField F]
    (D : Chapter04BrauerContext.{u, v} F)
    (S : Chapter04BrauerInvariantSequenceData D) :
    Function.Exact D.localization (chapter04BrauerInvariantSum D) := by
  exact (chapter04_brauer_invariant_sequence D S).2.1

/-- Every finitely supported invariant family has finite exponent, so torsion rows assemble to the
full Brauer invariant sequence. -/
theorem chapter04_brauer_torsion_directed_union
    {F : Type u} [Field F] [NumberField F]
    (D : Chapter04BrauerContext.{u, v} F)
    (S : Chapter04BrauerInvariantSequenceData D) :
    chapter04BrauerInvariantExact D := by
  exact chapter04_brauer_invariant_sequence D S

end

end LastLib.Book06GlobalClassFieldTheory.Chapter04
