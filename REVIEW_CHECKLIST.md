# Textbook Review Checklist

This is the common sign-off standard for every manuscript in `books/`. A book may be reported
`READY` only after a fresh-context author or reviewer has checked every applicable item below.
The reviewer records the result in the review ledger at the end of this file. Root commits the
book only after the report is `READY` with no unresolved coverage gap.

## 1. Scope and structure

- [ ] The manuscript matches the current description in `BOOKS.md`, not an older title or scope.
- [ ] Every direct prerequisite in `BOOK_DEPENDENCIES.md` has been inspected.
- [ ] The book is one logically continuous mathematical narrative rather than a collection of notes.
- [ ] The linked table of contents is at the top and agrees exactly with the final headings.
- [ ] Every chapter and section has substantive motivation and a clear role in the overall theory.
- [ ] Complicated arguments receive proportionally deeper explanation and are not compressed at the decisive step.
- [ ] The conclusion states the mathematical package established by the book.
- [ ] There are no appendices, exercises, optional-results sections, reader tasks, planning notes, or bibliographic filler.

## 2. Mathematical correctness

- [ ] Definitions are well-typed and use consistent variance, normalization, and sign conventions.
- [ ] Every theorem states all necessary hypotheses, including characteristic, finiteness, flatness,
      separability, perfectness, coefficient, and local/global assumptions where relevant.
- [ ] Every result central to the catalog description is proved at the required depth.
- [ ] Proof strategies are explained before difficult proofs, decisive steps are explicit, and consequences are interpreted.
- [ ] Examples and counterexamples respect the stated hypotheses and calculations have been checked.
- [ ] Edge cases, exceptional primes, scalar or reducible cases, and normalization changes are handled or explicitly excluded.
- [ ] No circular argument uses a later theorem, the desired conclusion, faithfulness, component coverage,
      or a numerical equality before it has been established.
- [ ] All equation labels, internal references, diagrams, and theorem references resolve correctly.

## 3. Dependency closure

- [ ] Each substantial imported result is ordinary assumed background or is actually proved in a prior numbered book.
- [ ] For every prior-book citation, the cited result exists and its hypotheses imply the form used here.
- [ ] No theorem is lost in a gap between books: if no prior source proves the needed statement, this book proves it.
- [ ] Later books are used only for orientation, never as proof dependencies.
- [ ] External class-field-theory or Chebotarev inputs are used only where the dependency graph permits them.
- [ ] The prose never mentions Lean, Mathlib, proof assistants, code APIs, theorem identifiers, or implementation details.

## 4. Exposition

- [ ] The intended graduate reader can follow the notation and the transition from intuition to formal statement.
- [ ] New constructions are motivated by the problem they solve.
- [ ] Dense theorem-proof cataloguing has been replaced by explanatory connective prose.
- [ ] Notation is introduced before use and remains stable across chapters.
- [ ] Cross-book recollections are sufficient to make the present narrative readable without duplicating whole prior books.
- [ ] The treatment is complete enough for later formalization and is near the soft target of roughly 100 typeset pages,
      while mathematical completeness takes priority over raw length.

## 5. Format and repository hygiene

- [ ] Inline mathematics uses `$...$`; display mathematics uses `$$...$$`.
- [ ] Math delimiters, braces, environments, and code fences are balanced.
- [ ] ASCII diagrams are used where a diagram is needed; no unavailable image is referenced.
- [ ] The manuscript contains no prohibited implementation vocabulary or accidental tool output.
- [ ] Only the assigned book file was edited by the author or reviewer.
- [ ] `git diff --check -- <book-file>` passes.
- [ ] The final report includes path, word count, line count, chapter count, section count, coverage gaps,
      and an unambiguous `READY` or `NOT READY` verdict.

## All-books review ledger

A checked box means that the current, renumbered manuscript received a fresh-context `READY`
report under this project and was committed. An unchecked box may have an older draft, but still
requires the current full-book pass. Root updates this list when each reviewed book is committed.

- [x] 001. Valuations, DVRs, and Completions
- [x] 002. Finite Extensions of Local Fields
- [x] 003. Ramification Theory
- [x] 004. Adeles and Ideles
- [x] 005. Local Class Field Theory
- [x] 006. Global Class Field Theory
- [x] 007. Analytic Foundations for Odlyzko–Poitou Bounds
- [x] 008. Ample Line Bundles, Hilbert Polynomials, and Symmetric Powers
- [x] 009. Divisors, Riemann–Roch, and Duality on Relative Curves
- [x] 010. Normalization and Regular Models of Arithmetic Curves
- [x] 011. Blowups and Intersection Theory on Arithmetic Surfaces
- [x] 012. Semistable Curves, Dual Graphs, and Component Groups
- [x] 013. Faithfully Flat Descent in Algebraic Geometry
- [x] 014. Moduli Stacks for Modular and PEL Problems
- [x] 015. Coherent Cohomology in Proper Families
- [x] 016. Arithmetic Spectral Sequences and Derived Cohomology
- [x] 017. Cotangent Complexes, Perfect Complexes, and Determinant Lines
- [x] 018. Formal Schemes, GAGA, and Algebraization
- [x] 019. Finite Étale Covers and Fundamental Groups
- [x] 020. Étale Sheaves and Cohomology on Curves
- [x] 021. Derived Étale and ℓ-adic Cohomology
- [x] 022. Proper and Smooth Base Change
- [x] 023. Étale Duality and Trace Maps in Low Dimension
- [x] 024. Nearby Cycles and Monodromy in Dimensions One and Two
- [x] 025. Lefschetz Trace Formulas for Curves and Surfaces
- [x] 026. Weights, Hard Lefschetz, and Weil Bounds in Low Dimension
- [x] 027. Betti, de Rham, and Étale Comparison for Curves
- [x] 028. fppf Cohomology and Kummer Theory
- [x] 029. Continuous Cohomology of Profinite Groups
- [x] 030. Local Galois Cohomology
- [x] 031. Tate Local Duality
- [x] 032. Global Galois Cohomology and Selmer Groups
- [x] 033. Poitou–Tate Duality
- [x] 034. Rigid Analytic Curves and Formal Models
- [x] 035. Rigid Uniformization of Abelian Varieties
- [x] 036. Relative Picard Schemes and Jacobians
- [x] 037. Jacobians and (H^1) of Curves
- [x] 038. Abelian Schemes, Isogenies, and Polarizations
- [x] 039. Néron Models and Component Groups
- [x] 040. Semistable Abelian Varieties and Monodromy
- [x] 041. Integral Correspondences on Curves and Jacobians
- [x] 042. Descent and Weak Mordell–Weil for Abelian Varieties
- [x] 043. Heights and the Mordell–Weil Theorem
- [x] 044. Finite Locally Free Schemes and Algebras
- [x] 045. Affine Group Schemes and Hopf Algebras
- [x] 046. Finite Flat Commutative Group Schemes
- [x] 047. Cartier Duality
- [x] 048. Finite-Flat Galois Representations
- [x] 049. Elliptic Curves over DVRs
- [x] 050. Tate Curves and Multiplicative Reduction
- [x] 051. Torsion and Tate Modules of Elliptic Curves
- [x] 052. Algebraic de Rham Cohomology and Gauss–Manin Connections
- [x] 053. Divided Powers and Crystalline Sites
- [x] 054. Crystalline Cohomology of Curves and Abelian Schemes
- [x] 055. Syntomic Cohomology and Integral Period Maps
- [x] 056. Finite-Flat Group Schemes of Small Height
- [x] 057. Dieudonné Theory and Raynaud Full Faithfulness
- [x] 058. Fontaine–Laffaille Modules and Torsion Representations
- [x] 059. Integral Fontaine–Laffaille Equivalence and Base Change
- [x] 060. p-divisible Groups and Serre–Tate Theory
- [x] 061. Ramification and Discriminants of Finite-Flat Representations
- [x] 062. Artinian and Complete Local Coefficient Rings
- [x] 063. Pseudocompact Trace Algebras and Carayol Descent
- [x] 064. Deformation Functors of Representations
- [x] 065. Representability of Deformation Problems
- [x] 066. Local Deformation Conditions Away from (\ell)
- [x] 067. Finite-Flat Deformation Conditions at (\ell)
- [x] 068. Global Deformation Problems
- [x] 069. Complete Local Algebra for Deformation Theory
- [x] 070. Depth, Complete Intersections, and Fitting Ideals
- [x] 071. Numerical Criteria for (R=T)
- [x] 072. Taylor–Wiles Primes
- [x] 073. Taylor–Wiles Systems
- [x] 074. Patching Modules and Rings
- [x] 075. The Abstract (R=T) Argument
- [x] 076. Smooth Representations of (p)-adic Groups
- [x] 077. Representations of (GL_2(K))
- [x] 078. Parabolic Induction, Jacquet Modules, and Whittaker Models for GL₂
- [x] 079. Dihedral Supercuspidals, Types, and Newvectors for GL₂
- [x] 080. Weil–Deligne Representations and Local Constants
- [x] 081. Local Langlands in the Principal, Special, and Dihedral Cases
- [x] 082. Representations of Quaternion Division Algebras
- [x] 083. Characters and Dihedral Types on Quaternion Division Algebras
- [x] 084. Local Jacquet–Langlands
- [x] 085. Local Jacquet–Langlands for Special and Dihedral Packets
- [x] 086. Cyclic Base Change: Local Theory
- [x] 087. Quaternion Algebras over Number Fields
- [x] 088. Orders in Quaternion Algebras
- [x] 089. Automorphic Forms on Definite Quaternion Algebras
- [x] 090. Hecke Operators on Quaternionic Forms
- [x] 091. Hecke Algebras and Congruences
- [x] 092. Automorphic Representations of (GL_2)
- [x] 093. Automorphic Representations of (D^\times)
- [x] 094. Global Jacquet–Langlands
- [x] 095. Hecke Characters and Automorphic Induction from (GL_1)
- [x] 096. Cyclic Base Change for (GL_2)
- [x] 097. Solvable Base Change and Descent
- [x] 098. Schwartz–Bruhat Analysis and Tate’s Thesis
- [x] 099. Archimedean GL₂ and Discrete Series
- [x] 100. Hilbert-Space Spectral and Trace-Class Theory
- [x] 101. Sobolev Theory and Elliptic Regularity on Arithmetic Quotients
- [x] 102. Reduction Theory and the Cuspidal Spectrum of GL₂
- [x] 103. Global Constant Terms and Eisenstein Contributions for GL₂
- [x] 104. Global Whittaker Models and Rankin–Selberg Theory
- [x] 105. Analytic Theory of Automorphic Rankin–Selberg L-functions
- [x] 106. Strong Multiplicity One and Global Newforms for GL₂
- [x] 107. Algebraicity and Integral Structures of Weight-Two Packets
- [x] 108. Cuspidal Trace-Formula Kernels for Rank Two
- [x] 109. The Cuspidal Spectral Side of the GL₂ Trace Formula
- [x] 110. The Geometric Side of the GL₂ Trace Formula
- [x] 111. Orbital Integrals for GL₂ and Quaternion Algebras
- [x] 112. Transfer of Test Functions and the Rank-Two Fundamental Lemma
- [x] 113. Twisted Conjugacy and Geometric Trace Distributions
- [x] 114. Twisted Cuspidal Trace Kernels and Spectral Expansion
- [x] 115. Twisted Orbital Matching and the Cyclic Fundamental Lemma
- [x] 116. Generalized Elliptic Curves and Level Structures
- [x] 117. Compactified Modular Stacks and Coarse Modular Curves
- [x] 118. Deligne–Rapoport Integral Models of Modular Curves
- [x] 119. Integral Modular Forms and q-Expansion
- [x] 120. Modular and Shimura Curves
- [x] 121. Modular Jacobians, Néron Models, and Hecke Correspondences
- [x] 122. Hecke Correspondences on Curves and Jacobians
- [x] 123. Reductive Groups, Inner Forms, and Corestriction in Rank Two
- [x] 124. CM Abelian Varieties, Types, and Reflex Norms
- [x] 125. Complex Multiplication, Reciprocity, and Reduction
- [x] 126. Shimura Data and Canonical Models in the FLT Cases
- [x] 127. Quaternionic PEL Functors and Representability
- [x] 128. Uniformization, Components, and Hecke Descent for Shimura Curves
- [x] 129. Unitary Shimura Surfaces and the Modèles Étranges Construction
- [ ] 130. Good Integral Models of Shimura Curves and Surfaces
- [ ] 131. Semistable Models and Monodromy of Shimura Varieties
- [x] 132. Automorphic Decomposition of Shimura-Curve H¹
- [x] 133. Automorphic Decomposition of Unitary-Surface H²
- [x] 134. Galois Representations from Weight-Two Shimura Cohomology
- [x] 135. Galois Representations Attached to Weight-Two Automorphic Forms
- [x] 136. Local–Global Compatibility for Weight-Two Galois Representations
- [x] 137. Compatible Coefficient Systems and Purity
- [x] 138. Canonical Galois Lattices and Finite-Flat Quotients
- [x] 139. Modular Curves (X_0(N)) and (X_1(N))
- [x] 140. Jacobians of Modular Curves
- [x] 141. The Eisenstein Ideal
- [x] 142. Eisenstein Series, Congruences, and the Eisenstein Ideal
- [x] 143. Cuspidal Divisors and Specialization on Modular Jacobians
- [x] 144. Mazur–Raynaud Admissible Group Schemes
- [x] 145. Completed Hecke Pieces and Eisenstein p-divisible Groups
- [x] 146. Eisenstein Descent and the Mordell–Weil Group of the Eisenstein Quotient
- [x] 147. Eisenstein Cotangent Lattices and Formal Immersion
- [x] 148. Rational Isogenies of Prime Degree
- [x] 149. Genus-Two Curves, Jacobians, and Abel–Jacobi Geometry
- [x] 150. Mumford Representations and Exact Genus-Two Jacobian Arithmetic
- [x] 151. Explicit Two-Descent on Genus-Two Jacobians
- [x] 152. Mordell–Weil Sieves for Hyperelliptic Curves
- [x] 153. Semistable Isogeny Characters and Frey Residual Representations
- [ ] 154. The Frey Curve and Fermat’s Last Theorem
- [x] 155. Minimal Modularity Lifting
- [x] 156. Nonminimal Modularity Lifting
- [x] 157. Integral Local Types and Type Lattices
- [x] 158. Ihara Theory and Saturated Degeneracy Maps on Shimura Curves
- [x] 159. Integral Level Change and Jacquet–Langlands Comparison
- [x] 160. Deep-Level Quaternionic Modules and Diamond Actions
- [x] 161. Hecke-Valued Galois Representations and Nonminimal Reciprocity
- [x] 162. Dickson Classification and Adequate Residual Image
- [x] 163. The Minimal Totally-Real Deformation–Hecke Problem
- [x] 164. Minimal Patching and R=T over Totally Real Fields
- [ ] 165. One-Prime Type Complexes and Component Support
- [x] 166. One-Prime Nonminimal Patching and R=T
- [x] 167. Hilbert Irreducibility and Arithmetic Approximation
- [x] 168. Moret–Bailly’s Theorem
- [x] 169. Moduli Constructions for Potential Modularity
- [x] 170. Potential Modularity of Two-Dimensional Representations
- [x] 171. Galois and Solvable Refinements of Arithmetic Approximation
- [x] 172. Hilbert–Blumenthal Moduli and Two-Prime Level Covers
- [x] 173. Local Geometry of Hilbert–Blumenthal Moduli
- [ ] 174. Auxiliary Dihedral Data and Residual Potential Modularity
- [x] 175. Compatible Systems of Galois Representations
- [x] 176. Brauer Induction and Descent of Automorphy
- [ ] 177. Changing the Prime
- [x] 178. Discriminants of Galois Representations
- [x] 179. Odlyzko Bounds and Fontaine’s Argument
- [ ] 180. Hardly Ramified (3)-adic Representations
- [x] 181. Schoof's Finite-Flat Category over ℤ[1/2]
- [ ] 182. Local Conditions for Hardly-Ramified Minimal Deformations
- [ ] 183. Supported Galois Cohomology and Selmer Calculations
- [ ] 184. Relation Obstructions and Poitou–Tate Corrections
- [ ] 185. Finite Image and the Balanced Minimal-Lift Argument
- [ ] 186. Potential Automorphy and Galois Refinement of a Chosen Lift
- [x] 187. Brauer Induction for Automorphy Families
- [x] 188. Brauer Characters and Effectivity of Compatible Families
- [x] 189. Compatible Systems over the Base Field
- [ ] 190. The Fixed-Three Integral Local Theory
- [x] 191. Quintic Cyclotomic Units and Kummer Arithmetic
- [x] 192. Cyclotomic Descent for Quintic Fermat-Type Equations
- [x] 193. The Chebotarev Density Theorem
- [ ] 194. Frey-Special Modularity Admissibility and the Minimal Lift
