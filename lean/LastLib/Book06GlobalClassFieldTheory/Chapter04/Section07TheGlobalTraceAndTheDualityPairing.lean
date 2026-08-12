import LastLib.Book06GlobalClassFieldTheory.Chapter04.Dependencies

namespace LastLib.Book06GlobalClassFieldTheory.Chapter04

noncomputable section

universe u v

open scoped Classical

open scoped BigOperators

/-! ## 4.7. The global trace and the duality pairing -/

/-! The global/local cochain and trace objects are intentionally packaged as a dependency boundary.
The `compactH` component of `Chapter04CompactSupportAPI` is the cohomology of the shifted cone in
(4.13); the fields below expose exactly the finite-support and trace compatibilities needed by the
chapter without inventing a second cochain-complex implementation. -/

/-- Localized cup products have finite support. -/
structure Chapter04GlobalLocalizedPairingData (I : Type u) where
  X : Type v
  [xGroup : AddCommGroup X]
  Y : Type v
  [yGroup : AddCommGroup Y]
  Xlocal : I → Type v
  [xlocalGroup : ∀ i, AddCommGroup (Xlocal i)]
  Ylocal : I → Type v
  [ylocalGroup : ∀ i, AddCommGroup (Ylocal i)]
  localPairing : ∀ i, Xlocal i → Ylocal i → chapter04QModZ
  localizeX : X →+ (∀ i, Xlocal i)
  localizeY : Y →+ (∀ i, Ylocal i)
  finite_support : ∀ x y,
    Set.Finite {i | localPairing i ((localizeX x) i) ((localizeY y) i) ≠ 0}
  diagonal_sum_zero : ∀ x y,
    (finite_support x y).toFinset.sum
      (fun i => localPairing i ((localizeX x) i) ((localizeY y) i)) = 0

attribute [instance] Chapter04GlobalLocalizedPairingData.xGroup
  Chapter04GlobalLocalizedPairingData.yGroup
  Chapter04GlobalLocalizedPairingData.xlocalGroup
  Chapter04GlobalLocalizedPairingData.ylocalGroup

theorem chapter04_global_localized_cup_has_finite_support
    {I : Type*} (D : Chapter04GlobalLocalizedPairingData I)
    (x : D.X) (y : D.Y) :
    Set.Finite {i | D.localPairing i ((D.localizeX x) i) ((D.localizeY y) i) ≠ 0} := by
  exact D.finite_support x y

/-- Global reciprocity makes the sum of diagonal local numerical pairings zero (4.12). -/
theorem chapter04_global_diagonal_cup_orthogonality
    {I : Type*} (D : Chapter04GlobalLocalizedPairingData I)
    (x : D.X) (y : D.Y) :
    (D.finite_support x y).toFinset.sum
      (fun i => D.localPairing i ((D.localizeX x) i) ((D.localizeY y) i)) = 0 := by
  exact D.diagonal_sum_zero x y

/-! ### The compact-support cone and its trace -/

/-- A presentation of the compact-support cone shifted by `[-1]`. -/
structure Chapter04CompactSupportConePresentation where
  globalCochains : ℤ → Type u
  [globalGroup : ∀ r, AddCommGroup (globalCochains r)]
  localCochains : ℤ → Type u
  [localGroup : ∀ r, AddCommGroup (localCochains r)]
  localization : ∀ r, globalCochains r →+ localCochains r
  compactSupportCochains : ℤ → Type u
  [compactGroup : ∀ r, AddCommGroup (compactSupportCochains r)]
  conePresentation : ∀ r,
    compactSupportCochains r ≃+
      (globalCochains r × localCochains (r - 1))

attribute [instance] Chapter04CompactSupportConePresentation.globalGroup
  Chapter04CompactSupportConePresentation.localGroup
  Chapter04CompactSupportConePresentation.compactGroup

/-! The displayed cone differential and its cohomology are supplied by the earlier
Galois-cohomology complex API; `conePresentation` fixes the source-order `[-1]` degree shift. -/

/-- The degree-three compact-support trace is supplied by the compact-support API. -/
def chapter04CompactSupportTrace
    {G : Type u} [Group G]
    (C : Chapter04CompactSupportAPI.{u, v} G)
    (M : Chapter04GModule.{u, v} G) :
    chapter04CompactSupportH C M 3 →+ chapter04QModZ :=
  C.trace M

/- The degree-three target is the `n`-torsion subgroup when `M = μₙ`; the trace construction is
independent of the choice of cone representative because the global invariant row is exact. -/
theorem chapter04_compact_support_trace_has_finite_coefficient_range
    {G : Type u} [Group G]
    (C : Chapter04CompactSupportAPI.{u, v} G)
    (P : Chapter04DualCoefficientPair.{u, v} G)
    (z : chapter04CompactSupportH C P.μn 3) :
    chapter04CompactSupportTrace C P.μn z ∈ chapter04QModZTorsion P.n := by
  sorry

/-! ### The global compact-support pairing -/

/-- The trace-and-cup pairing with the global degree shift `3-r`. -/
structure Chapter04GlobalCompactPairingData
    {G : Type u} [Group G]
    (C : Chapter04CompactSupportAPI.{u, v} G)
    (P : Chapter04DualCoefficientPair.{u, v} G) where
  pairing : ∀ r : ℤ,
    chapter04CompactSupportH C P.M r →
      chapter04GlobalH C P.Mdual (3 - r) → chapter04QModZ
  trace_realization : Prop

theorem chapter04_global_compact_support_pairing_is_perfect
    {G : Type u} [Group G]
    (C : Chapter04CompactSupportAPI.{u, v} G)
    (P : Chapter04DualCoefficientPair.{u, v} G)
    (Q : Chapter04GlobalCompactPairingData C P) :
    ∀ r : ℤ, chapter04PerfectPairing (Q.pairing r) := by
  sorry

/-! Perfectness here is deliberately a separate theorem from the trace construction.  For arbitrary
finite coefficients it is the further global duality theorem mentioned in the source; the special
`Aₙ`--`μₙ` calculation is supplied by the finite-level arithmetic interface. -/

/-- Global restriction/corestriction adjunction under the compact-support pairing (4.16). -/
structure Chapter04GlobalPairingAdjunctionData where
  X₀ : Type u
  [x₀Group : AddCommGroup X₀]
  Y₀ : Type u
  [y₀Group : AddCommGroup Y₀]
  X₁ : Type u
  [x₁Group : AddCommGroup X₁]
  Y₁ : Type u
  [y₁Group : AddCommGroup Y₁]
  pairing₀ : X₀ → Y₀ → chapter04QModZ
  pairing₁ : X₁ → Y₁ → chapter04QModZ
  restriction : X₀ →+ X₁
  corestriction : Y₁ →+ Y₀
  trace_preserved : ∀ x y,
    pairing₁ (restriction x) y = pairing₀ x (corestriction y)

attribute [instance] Chapter04GlobalPairingAdjunctionData.x₀Group
  Chapter04GlobalPairingAdjunctionData.y₀Group
  Chapter04GlobalPairingAdjunctionData.x₁Group
  Chapter04GlobalPairingAdjunctionData.y₁Group

theorem chapter04_global_restriction_corestriction_adjoint
    (D : Chapter04GlobalPairingAdjunctionData) (x : D.X₀) (y : D.Y₁) :
    D.pairing₁ (D.restriction x) y = D.pairing₀ x (D.corestriction y) := by
  exact D.trace_preserved x y

/-! ### The global trace sum over branches -/

structure Chapter04GlobalTraceBranchData (I : Type u) [Fintype I] where
  base : Type u
  [baseGroup : AddCommGroup base]
  branch : I → Type u
  [branchGroup : ∀ i, AddCommGroup (branch i)]
  baseInvariant : base →+ chapter04QModZ
  branchInvariant : ∀ i, branch i →+ chapter04QModZ
  branchCorestriction : ∀ i, branch i →+ base
  trace_compatibility : ∀ z : ∀ i, branch i,
    baseInvariant (∑ i, branchCorestriction i (z i)) =
      ∑ i, branchInvariant i (z i)

attribute [instance] Chapter04GlobalTraceBranchData.baseGroup
  Chapter04GlobalTraceBranchData.branchGroup

theorem chapter04_global_trace_branch_sum_formula
    {I : Type*} [Fintype I]
    (D : Chapter04GlobalTraceBranchData I) (z : ∀ i, D.branch i) :
    D.baseInvariant (∑ i, D.branchCorestriction i (z i)) =
      ∑ i, D.branchInvariant i (z i) := by
  exact D.trace_compatibility z

end

end LastLib.Book06GlobalClassFieldTheory.Chapter04
