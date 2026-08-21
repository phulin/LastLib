# Fresh chronological review: Books 065--128

## Method and status key

This ledger records a fresh, chronological, result-by-result audit against
`AUTHORING.md`, the earlier books, and the local Mathlib checkout. A book is
marked **PASS** only after every line from the title through EOF has been read
without tool-output elision and every substantive result has an available
proof or prerequisite. **FAIL** means that the full read is complete but at
least one operative gap remains. **PENDING** means that no full-read
attestation is made yet. Repairs and dependency defects are recorded with
locations and evidence below.

## Per-book ledger

- **065 -- Cotangent Complexes, Perfect Complexes, and Determinant Lines: FAIL.** **Full-read-to-EOF attestation:** I personally read lines 1--1950, in chronological order, through EOF, in untruncated spans. The definitions, forward complete-intersection calculation, perfect-complex material, determinant construction, and applications are internally ordered. The converse quotient-rigidity/lci argument has an operative gap; see Cross-book finding 1.
- **066 -- Representability of Deformation Problems: PASS.** **Full-read-to-EOF attestation:** I personally read lines 1--2755, in chronological order, through EOF, in untruncated spans. The Schlessinger construction proves finite-stage versality before passing to the limit; framed and unframed representability keep their distinct gluing hypotheses; complete-ring reconstruction proves compatibility of representatives/conjugators; and coefficient change distinguishes same-residue restriction from residual-field enlargement. Relation bounds are asserted only with complete, functorial, additive, torsor-compatible, effective obstruction data (Sections 8.4, 20.6, 21.4, and 21.6), rather than from an arbitrary obstruction receptacle.
- **067 -- Local Deformation Conditions Away from ell: PASS.** **Full-read-to-EOF attestation:** I personally read lines 1--2085, in chronological order, through EOF, in untruncated spans. Prime-to-ell inertia rigidity is proved by averaging; the tame relation has an explicit tangent complex and complete small-extension defect; fixed-type and special smoothness use solved torsors/normal forms; and the top-degree formula is proved by Hochschild--Serre rather than assumed. Scalar Frobenius, characteristic two, modular inertia, nonunique lines, and open nonzero-monodromy loci are all excluded from generic conclusions where required. The malformed Section 13.1 summary table was repaired in commit `65b29c6`.
- **068 -- Finite-Flat Deformation Conditions at ell: PASS.** **Full-read-to-EOF attestation:** I personally read lines 1--3500, in chronological order, through EOF, in untruncated spans. General coefficient change and Schlessinger gluing are proved by saturated closure and represented quotients, without assuming model uniqueness; dual tangent spaces are defined by Tate orthogonality rather than an unproved geometric annihilator theorem. In the unramified odd low-weight range, the deep classification inputs are genuinely supplied earlier by Book 54 (anti-equivalence, exactness, Raynaud rigidity, coefficient actions/base change, admissible annihilators, and height-two structure), and this book proves the covariant coefficient chart, tangent complex, determinant equation, and explicit small-extension lift. Outside that range the relation ideal is correctly retained.
- **069 -- Global Deformation Problems: PASS.** **Full-read-to-EOF attestation:** I personally read lines 1--2823, in chronological order, through EOF, in untruncated spans. The global functor and its completed-pushout representing ring have the correct variance; strict equivalence, determinant coefficients, and partial framing retain their distinct gauge modules and global/local invariant corrections. Local tangent subspaces are not promoted to obstruction theories: the Selmer-complex presentation and dual-Selmer relation bound are stated only under six explicit cohomological-control, perfect-duality, completeness, and effectiveness hypotheses. Poitou--Tate signs, Tate twists, modified real cohomology, exceptional determinant characteristics, and the limits of the balanced conclusion are all exposed rather than suppressed.
- **070 -- Depth, Complete Intersections, and Fitting Ideals: PASS.** **Full-read-to-EOF attestation:** I personally read lines 1--2962, in chronological order, through EOF, in untruncated spans. Regular sequences, Koszul homology, Ext-depth, localization/completion, minimal resolutions, Auslander--Buchsbaum, Cohen--Macaulay and complete-intersection criteria, Fitting ideals, congruence/cotangent modules, and miracle flatness are developed in dependency order with their finiteness, locality, flatness, and finite-projective-dimension boundaries explicit. Section 9.2's proof of the Auslander--Buchsbaum--Serre converse previously tried to choose a regular minimal generator by prime avoidance over an arbitrary residue field; it now first makes the standard faithfully flat generic residue-field extension, where the finite-union argument is valid, and records descent of regularity.
- **071 -- Numerical Criteria for R Equals T: FAIL.** **Full-read-to-EOF attestation:** I personally read lines 1--3241, in chronological order, through EOF, in untruncated spans. The definitions, branch-idempotent interpretation, fundamental Fitting-ideal inclusion, complete-intersection forward Jacobian formula, conormal comparison, target-relation-lattice kernel elimination, module saturation distinctions, base-change caveats, and examples are internally ordered. The converse relation--determinant step is not actually proved at the required level, so the Lenstra complete-intersection characterization and all source-unrestricted $R=T$ corollaries remain unsupported; see Cross-book finding 3. Two malformed strict-inequality displays in Sections 11.5 and 16.6 were repaired locally.
- **072 -- Smooth Representations of p-adic Groups: PASS.** **Full-read-to-EOF attestation:** I personally read lines 1--2046, in chronological order, through EOF, in untruncated spans. Van Dantzig's theorem and Haar/modular conventions precede smoothness; compact and ordinary induction retain their different support and adjunction hypotheses; Mackey sums versus products, admissibility, contragredient biduality, Hecke reconstruction, and type-generated categories all state the needed compactness, characteristic-zero, finiteness, or categorical-boundary assumptions. Distribution characters are constructed from finite-rank integrated operators before any character-function claim. The $\operatorname{GL}_2$ and quaternionic laboratories prove only their elementary lattice/conjugacy facts and explicitly defer quadratic embedding, orbital convergence, matching functions, transfer sign, and classification. The previously damaged display relation in this book was already repaired and context-checked in commit `cbd2ee3`.
- **073 -- Parabolic Induction, Jacquet Modules, and Whittaker Models for GL2: PENDING.** No full-read-to-EOF attestation yet.
- **074 -- Dihedral Supercuspidals, Types, and Newvectors for GL2: PENDING.** No full-read-to-EOF attestation yet.
- **075 -- Weil--Deligne Representations and Local Constants: PENDING.** No full-read-to-EOF attestation yet.
- **076 -- Local Langlands in the Principal, Special, and Dihedral Cases: PENDING.** No full-read-to-EOF attestation yet.
- **077 -- Quaternion Algebras over Number Fields: PENDING (read-only).** No full-read-to-EOF attestation yet. This manuscript was designated pre-existing dirty and will not be edited or staged in this audit.
- **078 -- Characters and Dihedral Types on Quaternion Division Algebras: PENDING.** No full-read-to-EOF attestation yet.
- **079 -- Representations of Quaternion Division Algebras: PENDING.** No full-read-to-EOF attestation yet.
- **080 -- Local Jacquet--Langlands for Special and Dihedral Packets: PENDING.** No full-read-to-EOF attestation yet.
- **081 -- Cyclic Base Change: Local Theory: PENDING.** No full-read-to-EOF attestation yet.
- **082 -- Orders in Quaternion Algebras: PENDING.** No full-read-to-EOF attestation yet.
- **083 -- Automorphic Forms on Definite Quaternion Algebras: PENDING.** No full-read-to-EOF attestation yet.
- **084 -- Hecke Operators on Quaternionic Forms: PENDING.** No full-read-to-EOF attestation yet.
- **085 -- Hecke Algebras and Congruences: PENDING.** No full-read-to-EOF attestation yet; the standing-hypothesis audit will distinguish object data and theorem hypotheses from concealed prerequisites.
- **086 -- Schwartz--Bruhat Analysis and Tate's Thesis: PENDING.** No full-read-to-EOF attestation yet.
- **087 -- Archimedean GL2 and Discrete Series: PENDING.** No full-read-to-EOF attestation yet.
- **088 -- Hilbert-Space, Spectral, and Trace-Class Theory: PENDING.** No full-read-to-EOF attestation yet.
- **089 -- Sobolev Theory and Elliptic Regularity on Arithmetic Quotients: PENDING.** No full-read-to-EOF attestation yet.
- **090 -- Reduction Theory and the Cuspidal Spectrum of GL2: PENDING.** No full-read-to-EOF attestation yet.
- **091 -- Global Constant Terms and Eisenstein Contributions for GL2: PENDING.** No full-read-to-EOF attestation yet.
- **092 -- Global Whittaker Models and Rankin--Selberg Theory: PENDING.** No full-read-to-EOF attestation yet.
- **093 -- Analytic Theory of Automorphic Rankin--Selberg L-functions: PENDING.** No full-read-to-EOF attestation yet.
- **094 -- Strong Multiplicity One and Global Newforms for GL2: PENDING.** No full-read-to-EOF attestation yet.
- **095 -- Automorphic Representations of GL2: PENDING.** No full-read-to-EOF attestation yet.
- **096 -- Automorphic Representations of Quaternion Algebras: PENDING.** No full-read-to-EOF attestation yet.
- **097 -- Algebraicity and Integral Structures of Weight-Two Packets: PENDING.** No full-read-to-EOF attestation yet.
- **098 -- Hecke Characters and Automorphic Induction: PENDING.** No full-read-to-EOF attestation yet.
- **099 -- Cuspidal Trace-Formula Kernels for Rank Two: PENDING.** No full-read-to-EOF attestation yet.
- **100 -- Cuspidal Spectral Side of the GL2 Trace Formula: PENDING.** No full-read-to-EOF attestation yet.
- **101 -- Geometric Side of the GL2 Trace Formula: PENDING.** No full-read-to-EOF attestation yet.
- **102 -- Orbital Integrals for GL2 and Quaternion Algebras: PENDING.** No full-read-to-EOF attestation yet.
- **103 -- Transfer of Test Functions and the Rank-Two Fundamental Lemma: PENDING.** No full-read-to-EOF attestation yet. A malformed display relation was repaired in commit `cbd2ee3`; final verdict awaits the full read.
- **104 -- Global Jacquet--Langlands: PENDING.** No full-read-to-EOF attestation yet.
- **105 -- Twisted Conjugacy and Geometric Trace Distributions: PENDING.** No full-read-to-EOF attestation yet.
- **106 -- Twisted Cuspidal Trace Kernels and Spectral Expansion: PENDING.** No full-read-to-EOF attestation yet.
- **107 -- Twisted Orbital Matching and the Cyclic Fundamental Lemma: PENDING.** No full-read-to-EOF attestation yet.
- **108 -- Cyclic Base Change for GL2: PENDING.** No full-read-to-EOF attestation yet.
- **109 -- Solvable Base Change and Descent: PENDING.** No full-read-to-EOF attestation yet.
- **110 -- Generalized Elliptic Curves and Level Structures: PENDING.** No full-read-to-EOF attestation yet.
- **111 -- Compactified Modular Stacks and Coarse Modular Curves: PENDING.** No full-read-to-EOF attestation yet.
- **112 -- Deligne--Rapoport Integral Models of Modular Curves: PENDING.** No full-read-to-EOF attestation yet.
- **113 -- Integral Modular Forms and q-Expansion: PENDING.** No full-read-to-EOF attestation yet.
- **114 -- Modular Jacobians, Neron Models, and Hecke Correspondences: PENDING.** No full-read-to-EOF attestation yet.
- **115 -- Reductive Groups, Inner Forms, and Corestriction in Rank Two: PENDING.** No full-read-to-EOF attestation yet.
- **116 -- CM Abelian Varieties, Types, and Reflex Norms: PENDING.** No full-read-to-EOF attestation yet.
- **117 -- Complex Multiplication, Reciprocity, and Reduction: PENDING.** No full-read-to-EOF attestation yet.
- **118 -- Shimura Data and Canonical Models in the FLT Cases: PENDING.** No full-read-to-EOF attestation yet; a targeted check has already confirmed Cross-book finding 2.
- **119 -- Quaternionic PEL Functors and Representability: PENDING.** No full-read-to-EOF attestation yet.
- **120 -- Uniformization, Components, and Hecke Descent for Shimura Curves: PENDING.** No full-read-to-EOF attestation yet; hypotheses from Section 5.1 onward and the use of strong approximation require final classification.
- **121 -- Good Integral Models of Quaternionic Shimura Curves: PENDING.** No full-read-to-EOF attestation yet; completeness will be assessed on substance, not word count.
- **122 -- Semistable Models and Monodromy of Quaternionic Shimura Curves: PENDING.** No full-read-to-EOF attestation yet.
- **123 -- Modular and Shimura Curves: PENDING.** No full-read-to-EOF attestation yet.
- **124 -- Hecke Correspondences on Curves and Jacobians: PENDING.** No full-read-to-EOF attestation yet.
- **125 -- Automorphic Decomposition of Shimura-Curve H1: PENDING.** No full-read-to-EOF attestation yet.
- **126 -- Galois Representations from Weight-Two Shimura Cohomology: PENDING.** No full-read-to-EOF attestation yet.
- **127 -- Galois Representations from Automorphic Forms: PENDING.** No full-read-to-EOF attestation yet; completeness will be assessed on substance, not word count.
- **128 -- Local--Global Compatibility for Weight-Two Galois Representations: PENDING.** No full-read-to-EOF attestation yet.

## Confirmed cross-book findings

### 1. Cotangent-amplitude converse is not established

- **Source / consumer:** Book 065, Section 7.2, especially lines 866--920; consumed immediately by the lci converse at lines 928--942 and by any later argument that infers a regular sequence from cotangent amplitude.
- **Needed result:** for a quotient $B=P/I$ of a noetherian local ring, perfection of $L_{B/P}$ with amplitude $[-1,-1]$ implies that $I$ is generated by a regular sequence (the deep complete-intersection/cotangent criterion).
- **Gap:** lines 896--903 introduce a filtration spectral sequence and then assert that its derived-symmetric-power layers have “no further differential or extension.” Freeness of $I/I^2$ and the identification $L_{B/P}\simeq(I/I^2)[1]$ do not by themselves prove spectral-sequence degeneration or identify the entire Tor algebra. Lines 913--920 therefore cannot yet compare the Koszul and minimal resolutions as claimed.
- **Availability check:** searches in the local checkout find only the naive presentation cotangent complex and standard-smooth results (`RingTheory/Extension/Cotangent/*` and `RingTheory/Smooth/StandardSmoothCotangent.lean`), not this full cotangent-complex complete-intersection converse. No earlier manuscript result has been identified that proves the missing degeneration/theorem.
- **Chronological repair:** insert a rigorous proof of the complete-intersection cotangent criterion before Book 065's lci converse (or make it a fully proved earlier prerequisite), then cite that theorem at lines 896--920. Merely naming the Quillen criterion would violate the project rule.

### 2. Quaternionic strong approximation proof uses a non-global direction

- **Source / consumers:** Book 118, Section 6.2 (strong approximation for the quaternionic norm-one group); its component calculation is consumed in Book 120 and downstream Shimura-curve component/Hecke arguments.
- **Needed result:** density/strong approximation for the simply connected norm-one group of a quaternion algebra away from a split place, with the exact finite-adelic formulation used in the component quotient.
- **Gap:** the displayed proof chooses an isotropic pair over the local completion and then varies a purportedly global scalar in that local isotropic direction, although that direction need not be defined over the global field. Its denominator-clearing step also asks CRT to avoid every “new prime divisor” of a quadratic denominator; those primes depend on the element being chosen, so the finite CRT argument is circular and does not prove the denominator is an $S$-unit.
- **Availability check:** the local checkout has no theorem matching quaternionic/algebraic-group strong approximation (a repository search for `strong approximation` supplies no such result), and no earlier assigned manuscript has yet been found to prove this theorem.
- **Chronological repair:** establish the required simply connected strong-approximation theorem, with a valid global-to-local proof, in an earlier book before 118; then replace Section 6.2's argument by a citation and carry its exact hypotheses into Books 120 and later consumers.

### 3. Lenstra's equality-implies-complete-intersection step is only sketched

- **Source / consumers:** Book 071, Section 7.3, especially lines 1157--1196 (the asserted filtered determinant implication (7.3.1)); consumed by the relation--determinant lemma at lines 1128--1210, Lenstra's complete-intersection characterization at lines 1212--1235, the source-unrestricted Wiles--Lenstra theorem in Section 8, Book 071's later reusable/deformation--Hecke criteria, and the abstract $R=T$ argument in Book 146, especially Sections 9.6 and 16.2.
- **Needed result:** if $B=S/(g_1,\ldots,g_n)$ is the complete-intersection parameter reduction constructed there and $A=B/L$ remains finite flat, then a nonzero extra kernel $L$ forces a strict enlargement $\eta_B\subsetneq\eta_A$; equivalently, equality of the cotangent Fitting ideal and branch congruence ideal forces the original presentation ideal to have exactly height-many generators.
- **Gap:** the text invokes an unspecified “comparison” of the Koszul complexes, says that a first associated-graded class of $L$ has a nonzero Koszul boundary, and asserts that exterior multiplication carries it to a nonzero class in $\operatorname{Ann}_A(I_A)/\operatorname{Ann}_B(I_B)$. No chain maps, filtered complexes, associated-graded differential, or map from that boundary to the annihilator quotient are defined, and the claim that a hypothetical later boundary would yield $\varpi^c b\in L$ with $b\notin L$ is asserted without derivation. Artin--Rees and $\varpi$-saturation alone do not supply these missing identifications. Thus (7.3.1), the only step excluding higher-order extra relations, has not been proved.
- **Availability check:** the local Mathlib checkout contains no Wiles--Lenstra numerical criterion, congruence-ideal relation--determinant theorem, or equivalent complete-intersection converse (searches for `Lenstra`, `Wiles.*criterion`, `congruence ideal`, and related complete-intersection/cotangent phrases find only unrelated Galois-category references). Books 064--070 provide presentations, depth, regular sequences, Fitting ideals, and the forward complete-intersection calculation, but not this determinant-defect theorem.
- **Chronological repair:** replace lines 1157--1196 with a complete proof of the determinant-defect theorem, defining the comparison complexes and every induced map and proving strictness, before stating the Section 7.3 characterization. Only then may Section 8 and Book 146 invoke the source-unrestricted Wiles--Lenstra criterion.

## Repairs already committed in this range

- `cbd2ee3` -- restored 34 damaged display-equation relations in Books 068, 070--072, 075, 079, 082--084, 088, 092, 095--096, 099, 103--104, 106--108, and 125; each repaired relation was checked in context.
- `65b29c6` -- repaired the malformed local-conditions summary table in Book 067.
- Book 070, Section 9.2 -- repaired the regular-minimal-generator step in the Auslander--Buchsbaum--Serre proof by inserting the necessary faithfully flat infinite-residue-field reduction.
- Book 071, Sections 11.5 and 16.6 -- restored the missing strict-inequality relations in two display equations.

## Pending targeted classifications

These are not yet verdicts because their books have not completed the full-read pass:

- Book 079's mention of Book 080 appears to be future scope/roadmap rather than a proof dependency.
- Book 081's mention of Book 108 appears to prescribe a later local input, not use Book 108 to prove Book 081.
- Book 082's mention of Book 083 appears to be roadmap for the later automorphic model.
- Book 084's mention of Book 085 appears to be roadmap for the later congruence comparison.
- Book 085's finite-free automorphic module and Hecke family appear to be explicit object data supplied by Books 083--084; its level-injectivity paragraph appears to state a boundary rather than assert the missing theorem. The full read will verify that no later conclusion silently uses it.
- Book 120's PEL-realizability, fine-level, and component-stability clauses appear to be visible theorem hypotheses, but its use of Book 118 strong approximation inherits confirmed finding 2.
