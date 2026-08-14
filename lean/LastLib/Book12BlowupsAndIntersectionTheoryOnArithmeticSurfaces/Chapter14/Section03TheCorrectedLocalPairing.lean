import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter14.Section02IntegralDataAndRationalCorrections

/-!
# Book 12, Chapter 14, §14.3: the corrected local pairing
-/

noncomputable section

open scoped BigOperators

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter14

/-! ## One-sided and fully corrected pairings -/

def chapter14CorrectedLocalPairing
    {r : ℕ} {F : Chapter14FiberMatrix r}
    (I : Chapter14LocalIntersectionData F)
    (D G : Chapter14HorizontalDivisor F)
  (hgeneric : I.genericDisjoint D G)
  (v : Chapter14RationalVerticalDivisor F) : ℚ :=
  I.rawIntersection D G hgeneric +
    chapter14VerticalAgainstHorizontal v G.componentIntersections

def chapter14FullyCorrectedLocalPairing
    {r : ℕ} {F : Chapter14FiberMatrix r}
    (I : Chapter14LocalIntersectionData F)
    (D G : Chapter14HorizontalDivisor F)
  (hgeneric : I.genericDisjoint D G)
  (v w : Chapter14RationalVerticalDivisor F) : ℚ :=
  I.rawIntersection D G hgeneric +
    chapter14VerticalAgainstHorizontal v G.componentIntersections +
    chapter14VerticalAgainstHorizontal w D.componentIntersections +
    chapter14VerticalIntersection F v w

noncomputable def chapter14CorrectedLocalPairingUsingCorrections
    {r : ℕ} (F : Chapter14FiberMatrix r)
    (I : Chapter14LocalIntersectionData F)
    (hconnected : F.connected)
    (D G : Chapter14HorizontalDivisor F)
    (hgeneric : I.genericDisjoint D G) : ℚ :=
  chapter14CorrectedLocalPairing I D G hgeneric
    (chapter14VerticalCorrection F hconnected D).coefficients

theorem chapter14_equation_14_3
    {r : ℕ} {F : Chapter14FiberMatrix r}
    (I : Chapter14LocalIntersectionData F)
    (D G : Chapter14HorizontalDivisor F)
    (hgeneric : I.genericDisjoint D G)
    (v : Chapter14RationalVerticalDivisor F) :
    chapter14CorrectedLocalPairing I D G hgeneric v =
      I.rawIntersection D G hgeneric +
        chapter14VerticalAgainstHorizontal v G.componentIntersections := by
  rfl

theorem chapter14_corrected_pairing_independent_of_fiber_representative
    {r : ℕ} {F : Chapter14FiberMatrix r}
    (I : Chapter14LocalIntersectionData F)
    (D G : Chapter14HorizontalDivisor F)
    (hgeneric : I.genericDisjoint D G)
    {v v' : Chapter14RationalVerticalDivisor F}
    (hclass : chapter14RationallyEquivalentModuloFiber F v v') :
    chapter14CorrectedLocalPairing I D G hgeneric v =
      chapter14CorrectedLocalPairing I D G hgeneric v' := by
  sorry

theorem chapter14_balanced_divisor_intersects_vertical_zero
    {r : ℕ} {F : Chapter14FiberMatrix r}
    (D : Chapter14HorizontalDivisor F)
    (v w : Chapter14RationalVerticalDivisor F)
    (hv : chapter14Balanced F
      (fun i => (D.componentIntersections i : ℚ)) v) :
    chapter14VerticalAgainstHorizontal w D.componentIntersections +
        chapter14VerticalIntersection F w v = 0 := by
  sorry

theorem chapter14_corrected_local_pairing_eq_raw_sub_vertical
    {r : ℕ} {F : Chapter14FiberMatrix r}
    (I : Chapter14LocalIntersectionData F)
    (D G : Chapter14HorizontalDivisor F)
    (hgeneric : I.genericDisjoint D G)
    (v w : Chapter14RationalVerticalDivisor F)
    (hv : chapter14Balanced F
      (fun i => (D.componentIntersections i : ℚ)) v)
    (hw : chapter14Balanced F
      (fun i => (G.componentIntersections i : ℚ)) w) :
    chapter14CorrectedLocalPairing I D G hgeneric v =
      I.rawIntersection D G hgeneric - chapter14VerticalIntersection F v w := by
  sorry

theorem chapter14_equation_14_4
    {r : ℕ} {F : Chapter14FiberMatrix r}
    (I : Chapter14LocalIntersectionData F)
    (D G : Chapter14HorizontalDivisor F)
    (hgeneric : I.genericDisjoint D G)
    (v w : Chapter14RationalVerticalDivisor F)
    (hv : chapter14Balanced F
      (fun i => (D.componentIntersections i : ℚ)) v)
    (hw : chapter14Balanced F
      (fun i => (G.componentIntersections i : ℚ)) w) :
    chapter14CorrectedLocalPairing I D G hgeneric v =
      I.rawIntersection D G hgeneric - chapter14VerticalIntersection F v w := by
  exact chapter14_corrected_local_pairing_eq_raw_sub_vertical
    I D G hgeneric v w hv hw

theorem chapter14_fully_corrected_pairing_eq_one_sided_pairing
    {r : ℕ} {F : Chapter14FiberMatrix r}
    (I : Chapter14LocalIntersectionData F)
    (D G : Chapter14HorizontalDivisor F)
    (hgeneric : I.genericDisjoint D G)
    (v w : Chapter14RationalVerticalDivisor F)
    (hv : chapter14Balanced F
      (fun i => (D.componentIntersections i : ℚ)) v)
    (hw : chapter14Balanced F
      (fun i => (G.componentIntersections i : ℚ)) w) :
    chapter14FullyCorrectedLocalPairing I D G hgeneric v w =
      chapter14CorrectedLocalPairing I D G hgeneric v := by
  sorry

theorem chapter14_corrected_local_pairing_symmetric
    {r : ℕ} {F : Chapter14FiberMatrix r}
    (I : Chapter14LocalIntersectionData F)
    (D G : Chapter14HorizontalDivisor F)
    (hgeneric : I.genericDisjoint D G)
    (v w : Chapter14RationalVerticalDivisor F)
    (hv : chapter14Balanced F
      (fun i => (D.componentIntersections i : ℚ)) v)
    (hw : chapter14Balanced F
      (fun i => (G.componentIntersections i : ℚ)) w)
    (hgeneric' : I.genericDisjoint G D) :
    chapter14CorrectedLocalPairing I D G hgeneric v =
      chapter14CorrectedLocalPairing I G D hgeneric' w := by
  sorry

theorem chapter14_fully_corrected_pairing_is_symmetric
    {r : ℕ} {F : Chapter14FiberMatrix r}
    (I : Chapter14LocalIntersectionData F)
    (D G : Chapter14HorizontalDivisor F)
    (hgeneric : I.genericDisjoint D G)
    (v w : Chapter14RationalVerticalDivisor F)
    (hv : chapter14Balanced F
      (fun i => (D.componentIntersections i : ℚ)) v)
    (hw : chapter14Balanced F
      (fun i => (G.componentIntersections i : ℚ)) w)
    (hgeneric' : I.genericDisjoint G D) :
    chapter14FullyCorrectedLocalPairing I D G hgeneric v w =
      chapter14FullyCorrectedLocalPairing I G D hgeneric' w v := by
  sorry

theorem chapter14_corrected_pairing_independent_of_both_corrections
    {r : ℕ} {F : Chapter14FiberMatrix r}
    (I : Chapter14LocalIntersectionData F)
    (D G : Chapter14HorizontalDivisor F)
    (hgeneric : I.genericDisjoint D G)
    {v v' w w' : Chapter14RationalVerticalDivisor F}
    (hv : chapter14Balanced F
      (fun i => (D.componentIntersections i : ℚ)) v)
    (hv' : chapter14Balanced F
      (fun i => (D.componentIntersections i : ℚ)) v')
    (hw : chapter14Balanced F
      (fun i => (G.componentIntersections i : ℚ)) w)
    (hw' : chapter14Balanced F
      (fun i => (G.componentIntersections i : ℚ)) w') :
    chapter14FullyCorrectedLocalPairing I D G hgeneric v w =
      chapter14FullyCorrectedLocalPairing I D G hgeneric v' w' := by
  sorry

/-! ## Component energy and bilinear component pairing -/

def chapter14ComponentEnergy {r : ℕ} (F : Chapter14FiberMatrix r)
    (v : Chapter14RationalVerticalDivisor F) : ℚ :=
  -chapter14VerticalIntersection F v v

def chapter14ComponentEnergyOfDivisor
    {r : ℕ} (F : Chapter14FiberMatrix r)
    (hconnected : F.connected)
    (D : Chapter14HorizontalDivisor F) : ℚ :=
  chapter14ComponentEnergy F
    (chapter14VerticalCorrection F hconnected D).coefficients

theorem chapter14_equation_14_5
    {r : ℕ} {F : Chapter14FiberMatrix r}
    (v : Chapter14RationalVerticalDivisor F) :
    chapter14ComponentEnergy F v =
      -chapter14VerticalIntersection F v v := by
  rfl

theorem chapter14_component_energy_nonnegative
    {r : ℕ} (F : Chapter14FiberMatrix r)
    (v : Chapter14RationalVerticalDivisor F) :
    0 ≤ chapter14ComponentEnergy F v := by
  sorry

theorem chapter14_component_energy_of_horizontal_divisor_nonnegative
    {r : ℕ} (F : Chapter14FiberMatrix r)
    (hconnected : F.connected)
    (D : Chapter14HorizontalDivisor F) :
    0 ≤ chapter14ComponentEnergyOfDivisor F hconnected D := by
  exact chapter14_component_energy_nonnegative F _

def chapter14ComponentBilinearPairing
    {r : ℕ} (F : Chapter14FiberMatrix r)
    (d e : Chapter14RationalVector r)
    (v w : Chapter14RationalVector r) : ℚ :=
  -chapter14VerticalIntersection F v w

theorem chapter14_equation_14_6
    {r : ℕ} {F : Chapter14FiberMatrix r}
    (d e : Chapter14RationalVector r)
    (v w : Chapter14RationalVector r) :
    chapter14ComponentBilinearPairing F d e v w =
      -chapter14VerticalIntersection F v w := by
  rfl

theorem chapter14_component_bilinear_pairing_independent_of_corrections
    {r : ℕ} {F : Chapter14FiberMatrix r}
    {d e : Chapter14RationalVector r}
    {v v' w w' : Chapter14RationalVector r}
    (hv : chapter14MatrixVec (chapter14FiberRationalMatrix F) v = -d)
    (hv' : chapter14MatrixVec (chapter14FiberRationalMatrix F) v' = -d)
    (hw : chapter14MatrixVec (chapter14FiberRationalMatrix F) w = -e)
    (hw' : chapter14MatrixVec (chapter14FiberRationalMatrix F) w' = -e) :
    chapter14ComponentBilinearPairing F d e v w =
      chapter14ComponentBilinearPairing F d e v' w' := by
  sorry

theorem chapter14_component_bilinear_pairing_symmetric
    {r : ℕ} (F : Chapter14FiberMatrix r)
    (d e : Chapter14RationalVector r)
    (v w : Chapter14RationalVector r) :
    chapter14ComponentBilinearPairing F d e v w =
      chapter14ComponentBilinearPairing F e d w v := by
  sorry

theorem chapter14_component_energy_is_diagonal_component_pairing
    {r : ℕ} {F : Chapter14FiberMatrix r}
    (d : Chapter14RationalVector r)
    (v : Chapter14RationalVector r)
    (hv : chapter14MatrixVec (chapter14FiberRationalMatrix F) v = -d) :
    chapter14ComponentBilinearPairing F d d v v =
      chapter14ComponentEnergy F v := by
  rfl

/-!
The raw self-intersection is intentionally not a field of the raw-pair API:
it is available only when the generic-disjointness hypothesis supplies a
proper pair.  The component energy above remains defined for every
degree-zero divisor.
-/
def chapter14RawSelfIntersectionDefined
    {r : ℕ} {F : Chapter14FiberMatrix r}
    (I : Chapter14LocalIntersectionData F)
    (D : Chapter14HorizontalDivisor F) : Prop :=
  I.genericDisjoint D D

theorem chapter14_raw_self_intersection_available_of_proper_generic_pair
    {r : ℕ} {F : Chapter14FiberMatrix r}
    (I : Chapter14LocalIntersectionData F)
    (D : Chapter14HorizontalDivisor F)
    (h : chapter14RawSelfIntersectionDefined I D) :
    ∃ q : ℚ, q = I.rawIntersection D D h := by
  exact ⟨I.rawIntersection D D h, rfl⟩

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter14
