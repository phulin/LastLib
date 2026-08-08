1. **Valuations, DVRs, and Completions**
   Develop the basic language of nonarchimedean arithmetic from the point where ordinary commutative algebra leaves off. Cover valuations and absolute values, valuation rings, discrete valuation rings, uniformizers, residue fields, filtrations by powers of the maximal ideal, completions, extension of valuations to finite field extensions, and integral closure of DVRs. The endpoint should be a clean Lean API for moving freely among a local field, its valuation ring, residue field, and completion, with the basic finiteness and compatibility results required throughout arithmetic geometry.

2. **Finite Extensions of Local Fields**
   Study finite extensions (L/K) of complete discretely valued fields. Develop ramification index and residue degree, the fundamental equality, extension of the valuation, norms and traces, decomposition and inertia groups in the Galois case, unramified extensions, totally ramified extensions, and the structure of unit groups. The endpoint is a usable theory of finite local extensions in which statements about inertia, residue-field Frobenius, and local Galois groups can be expressed without repeatedly descending to raw valuation-theoretic arguments.

3. **Ramification Theory**
   Build the finer structure of ramified extensions needed for Galois representations. Cover tame and wild ramification, lower and upper ramification filtrations, Herbrand functions, the different, discriminant exponents, ramification of towers, and Artin and Swan conductors for finite representations. The book should culminate in formulas relating ramification groups, conductors, and discriminants strongly enough to support later calculations for elliptic curves, torsion fields, finite-flat representations, and Fontaine-style discriminant estimates.

4. **Adeles and Ideles**
   Develop restricted products over all places of a number field, first for additive groups and then multiplicative groups. Cover finite and full adeles, ideles, their topologies, diagonal embeddings of the number field, compactness statements, idele class groups, local-global norm maps, and ray-class-type quotients. The endpoint is a stable adelic language suitable both for class field theory and for defining adelic automorphic forms later, with the relevant topological and algebraic finiteness results exposed as reusable lemmas.

5. **Local Class Field Theory**
   Give a self-contained formal development of reciprocity for nonarchimedean local fields. Introduce the local Artin map, describe it on uniformizers and units, prove functoriality under extensions, characterize norm subgroups, construct abelian extensions corresponding to open finite-index subgroups, and derive the classification of continuous one-dimensional Galois characters through local reciprocity. The FLT-facing endpoint is the ability to translate cleanly between local Galois characters and characters of (K^\times), especially in deformation theory and automorphic representation theory.

6. **Global Class Field Theory**
   Develop the global Artin reciprocity map from the idele class group, including its compatibility with all local reciprocity maps. Prove the existence and norm theorems for finite abelian extensions, formulate ray class fields, analyze ramification and Frobenius elements, and develop Hecke characters as adelic characters. The endpoint should support later use of class-field-theoretic characters in automorphic induction, dihedral representations, potential modularity, and the control of one-dimensional constituents of Galois representations.

7. **Elliptic Curves over DVRs**
   Develop the integral theory of Weierstrass models over discrete valuation rings. Cover integral equations, coordinate changes, discriminants and (c)-invariants, minimal models, reduction modulo the maximal ideal, good, multiplicative, and additive reduction, Néron-type criteria to the extent needed, and semistability. The endpoint should make it routine to prove the reduction type and minimal discriminant of a concrete curve such as the Frey curve directly from its equation.

8. **Tate Curves and Multiplicative Reduction**
   Study elliptic curves with split and nonsplit multiplicative reduction through Tate uniformization. Construct the Tate curve, describe its points and torsion, analyze the Galois action on the Tate parameter and torsion modules, and relate the Tate description to reduction type, inertia, and conductor. The endpoint is a precise local description of residual and (\ell)-adic Galois representations at multiplicative primes, which is one of the principal local inputs in semistable modularity arguments.

9. **Torsion and Tate Modules of Elliptic Curves**
   Develop (E[n]), the Weil pairing, Tate modules (T_\ell E), and residual representations (E[\ell]) over arbitrary fields of the required characteristic. Prove the determinant is cyclotomic, explain how reduction controls inertia, develop duality and functoriality under isogenies, and connect rational subgroups with reducibility of the Galois representation. The endpoint is the package of representation-theoretic facts needed to turn the arithmetic of the Frey curve into a two-dimensional residual Galois representation with explicit local properties.

10. **Finite Locally Free Schemes and Algebras**
    Develop the scheme theory of finite locally free morphisms at the level required for group schemes, avoiding a wholesale reconstruction of algebraic geometry. Cover finite projective algebras, rank, fibers, base change, composition, dual modules, finite flatness over local rings and DVRs, and elementary descent properties. The endpoint is a robust API in which “finite flat of rank (n)” behaves predictably enough that later group-scheme constructions can be formalized without repeatedly unfolding module-theoretic definitions.

11. **Affine Group Schemes and Hopf Algebras**
    Introduce group objects in affine schemes through commutative Hopf algebras. Develop multiplication, identity, inverse, subgroup schemes, kernels, quotient-like constructions that are needed later, base change, morphisms of group schemes, and exactness notions appropriate for finite group schemes. The endpoint should establish a reusable translation layer between geometric statements and Hopf-algebra calculations, sufficient for building the theory of torsion subgroup schemes without requiring a general theory of algebraic groups.

12. **Finite Flat Commutative Group Schemes**
    Specialize the preceding theory to finite flat commutative group schemes over local and arithmetic bases. Cover rank, fibers, connected and étale behavior, kernels of multiplication, schematic closure of generic-fiber subgroups, finite-flat subgroup schemes of abelian schemes, and stability under the standard operations. The endpoint is the category in which finite-flat models of residual Galois representations naturally live, with enough exactness and closure results to formulate deformation conditions.

13. **Cartier Duality**
    Develop Cartier duality for finite flat commutative group schemes. Construct the dual through Hopf algebras, identify constant and diagonalizable examples, prove biduality, study pairings and kernels, and relate Cartier duality to the duality on torsion of elliptic curves and abelian varieties. The endpoint is a duality formalism compatible with base change and generic fibers, required both for finite-flat local conditions and for the duality statements that enter Galois-cohomological tangent-space calculations.

14. **Finite-Flat Galois Representations**
    Relate finite flat group schemes over valuation rings to finite continuous representations of local Galois groups. Develop the generic-fiber functor, finite-flat models of (G_K)-modules, uniqueness or nonuniqueness phenomena as appropriate, scalar extension, subobjects, quotients, duals, and extensions. The book should end with a precise predicate saying that a residual representation is finite flat and with the basic closure properties needed to make “finite flat at (v\mid\ell)” a legitimate local deformation condition.

15. **Continuous Cohomology of Profinite Groups**
    Develop continuous group cohomology for profinite groups acting on discrete or topological modules in the forms needed later. Construct cochains, cocycles, coboundaries, (H^i), long exact sequences, connecting homomorphisms, restriction and corestriction, inflation–restriction, Shapiro’s lemma, and cup products. The endpoint should be a practical cohomological toolkit that can express deformation-theoretic tangent and obstruction spaces without appealing to abstract derived-category machinery at every use.

16. **Local Galois Cohomology**
    Apply continuous cohomology to absolute Galois groups of local fields. Compute and bound (H^0), (H^1), and (H^2) for finite modules and (\ell)-adic representations, develop unramified cohomology, analyze restriction to inertia, establish cohomological-dimension statements, and prove the local Euler characteristic formula. The endpoint is the collection of explicit dimension formulas used when calculating tangent spaces for local deformation conditions.

17. **Tate Local Duality**
    Develop the local duality pairing between the cohomology of a finite Galois module and the cohomology of its Tate-twisted dual. Construct cup-product pairings, the local invariant map, perfectness statements, annihilators of natural local conditions, and consequences for dimensions of (H^1). The endpoint is the exact duality theorem used later to identify orthogonal deformation conditions and to compare local tangent dimensions with their duals.

18. **Global Galois Cohomology and Selmer Groups**
    Develop Galois cohomology for number fields with ramification restricted to a finite set of places. Define localization maps and general Selmer structures by specifying subspaces of local (H^1), construct dual Selmer structures, and establish the basic exact sequences comparing global and local classes. The endpoint is a reusable framework in which the tangent space of a global deformation problem is literally a Selmer group assembled from the local deformation conditions developed earlier.

19. **Poitou–Tate Duality**
    Prove the global duality theorem that relates a Selmer condition to its dual. Develop the Poitou–Tate exact sequence, local-global pairings, orthogonal complements, global Euler characteristic formulas, and numerical identities comparing dimensions of Selmer and dual Selmer groups. The FLT-facing endpoint is the dimension formula that drives the Taylor–Wiles method and explains exactly how many auxiliary primes must be introduced to kill the dual Selmer group.

20. **Artinian and Complete Local Coefficient Rings**
    Develop the coefficient categories used in deformation theory. Cover local Artinian rings with fixed residue field, complete Noetherian local rings, inverse limits, continuous homomorphisms, formal power-series rings, completed tensor products, small extensions, and basic topological algebra. The endpoint is a clean categorical setting in which deformation functors can be defined on Artinian test rings and represented by complete local rings without continually rebuilding completeness and continuity arguments.

21. **Deformation Functors of Representations**
    Introduce deformations of a residual Galois representation over local Artinian coefficient rings. Define lifts, strict equivalence, framed and unframed deformations, fixed determinant, base change, infinitesimal deformations, and the identification of tangent spaces with (H^1) of the adjoint representation. Develop obstruction classes in (H^2). The endpoint is the general deformation functor whose variants will later encode local and global deformation problems.

22. **Representability of Deformation Problems**
    Develop the criteria ensuring that a deformation functor is pro-representable or admits a versal hull. Formalize Schlessinger-style conditions, small-extension arguments, automorphism issues, framed representability, passage from framed to unframed problems, and fixed-determinant variants. The endpoint is a theorem producing universal deformation rings under standard hypotheses, so later local and global rings can be constructed by invoking a reusable representability package rather than repeating ad hoc arguments.

23. **Local Deformation Conditions Away from (\ell)**
    Develop deformation subfunctors imposed at primes whose residue characteristic differs from (\ell). Treat unramified, minimally ramified, tame, Steinberg or special, and fixed-inertial-type conditions in the cases required for FLT. Prove representability, calculate tangent spaces, and establish formal smoothness or dimension statements where applicable. The endpoint is a menu of reusable local deformation conditions that can be assembled into a global deformation problem.

24. **Finite-Flat Deformation Conditions at (\ell)**
    Build the local deformation condition at primes dividing the coefficient characteristic from the finite-flat theory developed earlier. Define a lift to be finite flat through an integral group-scheme model, prove invariance under equivalence and base change, analyze extensions and tangent vectors, and establish the representability and dimension properties needed downstream. The endpoint is the exact finite-flat local deformation functor that enters the modularity lifting theorem relevant to the Frey representation.

25. **Global Deformation Problems**
    Assemble residual representations and chosen local conditions into a global deformation problem. Construct the corresponding universal deformation ring, relate its tangent space to a Selmer group and its obstruction theory to global (H^2), compare framed and unframed variants, impose determinants, and derive dimension inequalities using Poitou–Tate. The endpoint is a general global ring (R_{\mathcal D}) equipped with precisely the numerical invariants needed for Taylor–Wiles patching.

26. **Complete Local Algebra for Deformation Theory**
    Develop the commutative algebra most immediately used to analyze universal deformation rings. Cover cotangent spaces, embedding dimension, presentations by formal power series, Krull dimension in the complete local setting, regular local rings, finite maps, Nakayama’s lemma in topological form, and behavior under completed tensor product. The endpoint is the ability to turn cohomological tangent and obstruction calculations into concrete statements about generators and relations of deformation rings.

27. **Depth, Complete Intersections, and Fitting Ideals**
    Develop the deeper module-theoretic commutative algebra used in (R=T) arguments. Cover regular sequences, depth, projective dimension, Cohen–Macaulay modules, complete-intersection rings, Fitting ideals, support, and the behavior of these notions under finite local maps. The endpoint is a collection of criteria allowing freeness or faithfulness of patched modules to force strong structural conclusions about the rings acting on them.

28. **Numerical Criteria for (R=T)**
    Develop Wiles–Lenstra-style numerical criteria independently of automorphic forms. Introduce congruence modules and cotangent modules, compare their lengths, derive complete-intersection criteria, and prove abstract theorems under which a surjection (R\to T) between complete local rings must be an isomorphism. The endpoint is a small number of reusable algebraic (R=T) lemmas that later proofs can invoke once the required numerical equality has been established.

29. **Taylor–Wiles Primes**
    Study the auxiliary primes used to alter a deformation problem while controlling its global cohomology. Use Chebotarev to choose primes satisfying congruence and Frobenius conditions, describe the enlarged local deformation rings, compute their tangent contribution, and prove that a suitably chosen collection kills the relevant dual Selmer group. The endpoint is the existence theorem for Taylor–Wiles sets of prescribed cardinality and level.

30. **Taylor–Wiles Systems**
    Abstract the finite-level algebra produced by adjoining Taylor–Wiles primes. Define systems of deformation rings, Hecke algebras, modules, finite quotient group actions, transition maps, and compatibility conditions across levels. Prove the structural properties that survive passage through the tower. The endpoint is a formal notion of Taylor–Wiles datum from which patching can proceed without retaining details about modular or quaternionic forms.

31. **Patching Modules and Rings**
    Construct patched deformation rings and modules from a Taylor–Wiles system. Develop the relevant inverse-limit or ultraproduct machinery, auxiliary power-series rings, completed group rings, patched modules, support and depth calculations, and freeness over the auxiliary ring. The endpoint is the standard patched pair ((R_\infty,M_\infty)) satisfying the dimension and depth properties that make the final (R=T) argument almost purely commutative algebra.

32. **The Abstract (R=T) Argument**
    Complete the Taylor–Wiles method at an axiomatic level. Show how the patched module forces faithfulness of the action of (R_\infty), compare dimensions and complete-intersection properties, descend from infinite level to the original deformation and Hecke rings, and derive (R\simeq T). The endpoint should be a theorem whose hypotheses mention only an abstract Taylor–Wiles system, so all automorphic applications become separate instantiations of one patching result.

33. **Quaternion Algebras over Number Fields**
    Develop quaternion algebras as central simple algebras of degree two over local and global fields. Cover reduced trace and norm, Hilbert symbols, splitting and division criteria, ramification at places, tensoring to completions, and the local-global classification by ramification set. The endpoint is the ability to construct and characterize the totally definite quaternion algebra with exactly the ramification behavior required in the automorphic side of the modularity lifting argument.

34. **Orders in Quaternion Algebras**
    Develop integral structures inside quaternion algebras. Define orders, maximal orders, Eichler orders, localization at finite places, one-sided ideals and ideal classes, norm and discriminant of orders, and the finiteness of relevant class sets. Reinterpret these structures adelically. The endpoint is a concrete class of compact open subgroups of (D^\times(\mathbb A_f)) from which levels and finite double-coset spaces of quaternionic automorphic forms can be built.

35. **Automorphic Forms on Definite Quaternion Algebras**
    Define algebraic automorphic forms on a totally definite quaternion algebra through functions on adelic double quotients. Develop weights, central characters, compact-open level structures, finite-dimensionality, decomposition into finite sets, and integral coefficient structures. Because the group is compact at infinity modulo center, avoid unnecessary analytic theory. The endpoint is the exact finite combinatorial automorphic space on which the Hecke algebra appearing in (R=T) will act.

36. **Hecke Operators on Quaternionic Forms**
    Construct Hecke operators from local double cosets and prove their algebraic properties. Develop the local spherical Hecke algebra at unramified primes, global commuting families of operators, operators at level primes, compatibility with change of level, and formulas on finite double-coset models. The endpoint is a canonical Hecke action on the quaternionic automorphic modules used in the deformation-theoretic comparison.

37. **Hecke Algebras and Congruences**
    Study the commutative algebras generated by Hecke operators acting on integral automorphic forms. Cover localization and completion at maximal ideals, residual systems of eigenvalues, congruences between eigenforms, old and new subspaces as needed, finite freeness properties, and control under changing level. The endpoint is the localized complete Hecke algebra (T) and its modules in precisely the form required to receive a map from a universal deformation ring.

38. **Smooth Representations of (p)-adic Groups**
    Develop the general representation theory of totally disconnected locally compact groups needed for (GL_2) and quaternionic groups. Cover smooth representations, admissibility, invariant vectors under compact opens, compact induction, contragredients, intertwiners, and Hecke algebras attached to compact subgroups. The endpoint is a reusable language in which local components of automorphic representations and local transfer theorems can be stated cleanly.

39. **Representations of (GL_2(K))**
    Study the smooth irreducible representations of (GL_2) over a nonarchimedean local field to the extent needed downstream. Develop principal series, special or Steinberg representations, supercuspidal cases at the required level, spherical vectors, conductors, twists, central characters, and newvector theory. The endpoint is the classification and local invariants necessary to formulate both local Jacquet–Langlands and the local behavior of automorphic representations attached to Galois representations.

40. **Representations of Quaternion Division Algebras**
    Develop smooth representations of (D^\times) when (D) is the quaternion division algebra over a local field. Analyze compactness modulo center, admissibility, irreducible representations, conductors and levels, characters, compact induction constructions, and the invariants that correspond to discrete-series representations of (GL_2(K)). The endpoint is a local representation category prepared for a precise Jacquet–Langlands correspondence.

41. **Local Jacquet–Langlands**
    Construct the local correspondence between irreducible smooth representations of (D^\times) and discrete-series representations of (GL_2(K)). Develop matching regular conjugacy classes and characters or an equivalent formalism, prove compatibility with central characters and twisting, and compare conductors and local factors to the extent required later. The endpoint is a canonical transfer preserving exactly the local data used in global automorphic arguments.

42. **Automorphic Representations of (GL_2)**
    Develop the global language of automorphic representations of (GL_2(\mathbb A_F)). Cover restricted tensor products, cuspidal automorphic forms, central characters, local components, unramified Hecke eigenvalues, multiplicity one, and the newform decomposition needed to control level. The endpoint is a representation-theoretic description of classical or Hilbert modular forms compatible with both base change and Galois representations.

43. **Automorphic Representations of (D^\times)**
    Develop automorphic representations of the multiplicative group of a quaternion algebra. Relate adelic automorphic forms to irreducible global representations, decompose them into local components, prove the required multiplicity statements, and connect the representation-theoretic formulation with the finite algebraic automorphic spaces used in the (R=T) argument. The endpoint is the global quaternionic side prepared for transfer to (GL_2).

44. **Global Jacquet–Langlands**
    Prove the global correspondence between appropriate automorphic representations of (D^\times(\mathbb A_F)) and (GL_2(\mathbb A_F)). Establish the local-global matching of components, Hecke eigenvalues, central characters, levels, and ramification behavior, together with the multiplicity statements needed for applications. The endpoint is the ability to transport a quaternionic Hecke eigensystem arising in the modularity lifting argument to the (GL_2) world where base change and Galois representations are available.

45. **Hecke Characters and Automorphic Induction from (GL_1)**
    Develop algebraic and finite-order Hecke characters of number fields and their relation to one-dimensional Galois characters by class field theory. Construct the automorphic representations of (GL_2) obtained by induction from characters of quadratic or more general extensions, analyze their local components and cuspidality, and identify the associated dihedral Galois representations. The endpoint supplies the automorphic starting points used in potential modularity and residual modularity arguments.

46. **Cyclic Base Change: Local Theory**
    Study how local representations behave under extension of local fields. Formulate base change in terms of restriction of local parameters or an equivalent representation-theoretic construction, treat unramified and ramified cases, calculate behavior of principal, special, and discrete-series representations, and prove compatibility with twisting and local Jacquet–Langlands. The endpoint is a local transfer operation suitable for assembling into global cyclic base change.

47. **Cyclic Base Change for (GL_2)**
    Develop the global base-change theorem for a cyclic extension of number fields. Construct the lift of a cuspidal automorphic representation, characterize its local components, prove compatibility with Hecke eigenvalues, identify when the lift remains cuspidal, and establish the basic descent or image criterion. The endpoint is the precise cyclic base-change theorem required in the modularity-lifting and potential-modularity portions of the FLT proof.

48. **Solvable Base Change and Descent**
    Iterate cyclic base change through towers of cyclic extensions to obtain solvable base change. Develop descent of invariant automorphic representations, twisting ambiguities, compatibility through towers, and control of local components. The endpoint is a practical theorem allowing modularity or automorphy to be moved up and down suitable solvable totally real extensions, rather than requiring each later argument to manipulate cyclic towers by hand.

49. **Finite Étale Covers and Fundamental Groups**
    Develop the finite étale site and étale fundamental group at the level required for curves over fields and arithmetic bases. Cover geometric points, finite étale covers, Galois categories, fundamental groups, exact sequences under base change, specialization where needed, and the relationship with absolute Galois groups. The endpoint is a rigorous mechanism by which geometric coverings and locally constant sheaves produce continuous Galois representations.

50. **Étale Sheaves and Cohomology on Curves**
    Develop étale cohomology sufficiently far to handle smooth proper curves and their local systems. Introduce constructible and lisse sheaves, derived cohomology in low degrees, proper and smooth base change in the needed cases, cup products, Frobenius actions, and Poincaré duality for curves. The endpoint is a usable (H^1_{\mathrm{\acute et}}) carrying continuous Galois actions and functorial actions of algebraic correspondences.

51. **Jacobians and (H^1) of Curves**
    Develop the Jacobian or Picard variety of a smooth proper curve to the extent needed for modular and Shimura curves. Relate torsion and Tate modules of the Jacobian to étale (H^1), develop polarizations and duality, and formalize the action of correspondences on the Jacobian and its Tate module. The endpoint is a bridge between geometric Hecke correspondences and finite-dimensional (\ell)-adic Galois representations.

52. **Modular and Shimura Curves**
    Construct the modular curves and quaternionic Shimura curves required later from their moduli problems. Develop level structures, compactifications, cusps where present, connected components, actions of Hecke correspondences, and enough integral-model theory at relevant primes to control reduction. The endpoint is a geometric object realizing the desired automorphic Hecke modules inside étale cohomology or Jacobian Tate modules.

53. **Hecke Correspondences on Curves and Jacobians**
    Construct Hecke operators geometrically as correspondences between modular or Shimura curves. Prove compatibility with adelic double-coset Hecke operators, induce actions on divisors, Jacobians, and étale cohomology, and establish the polynomial relations between Hecke operators and Frobenius at good primes. The endpoint is a common Hecke algebra acting simultaneously on automorphic forms and on Galois representations extracted from geometry.

54. **Galois Representations Attached to Weight-Two Automorphic Forms**
    Extract two-dimensional (\ell)-adic Galois representations from Hecke eigensystems in the cohomology of modular or Shimura curves. Prove the characteristic polynomial of Frobenius at unramified primes, determine determinants, control ramification, construct integral lattices and residual representations, and prove the local-global compatibility statements required by modularity lifting. The endpoint is the theorem “automorphic representation (\Rightarrow) compatible Galois representation” in the exact weight-two setting used by FLT.

55. **Minimal Modularity Lifting**
    Assemble the deformation-theoretic and automorphic machinery in the minimal case. Define matching minimal deformation and Hecke problems, construct the natural map (R\to T) from the Galois representation attached to Hecke eigenforms, verify the Taylor–Wiles hypotheses, invoke the abstract patching theorem, and conclude (R=T). The endpoint is a modularity lifting theorem under minimal local ramification assumptions, with the difficult infrastructure delegated to the preceding reusable books.

56. **Nonminimal Modularity Lifting**
    Extend the minimal theorem to the local conditions actually needed for the Frey representation. Develop level-changing arguments, comparison between minimal and nonminimal deformation rings, congruence techniques, and the Skinner–Wiles-style maneuver involving solvable base change and Jacquet–Langlands where required. The endpoint is the precise modularity lifting theorem for “hardly ramified” or otherwise suitably controlled two-dimensional representations appearing in the FLT reduction.

57. **Hilbert Irreducibility and Arithmetic Approximation**
    Develop Hilbertian methods for imposing simultaneous local and global conditions on rational points and field extensions. Cover Hilbert irreducibility, weak approximation, control of decomposition at finitely many places, linear disjointness, avoidance of prescribed extensions, and construction of totally real extensions. The endpoint is a toolkit for choosing auxiliary number fields satisfying many independent conditions at once, as required in potential modularity.

58. **Moret–Bailly’s Theorem**
    Develop the arithmetic-geometric existence theorem underlying many potential-modularity constructions. Formulate the existence of points on varieties after finite extensions subject to prescribed local open conditions, establish the totally real variant needed for (GL_2) modularity, and derive practical corollaries incorporating linear disjointness and splitting requirements. The endpoint is a black-box theorem that turns local points on a moduli variety into a global point over a suitably chosen totally real field.

59. **Moduli Constructions for Potential Modularity**
    Build the specific moduli spaces used to realize prescribed residual Galois representations through torsion of elliptic curves or related abelian varieties. Develop twisted level structures, representability and smoothness of the required moduli problem, local solvability, geometric irreducibility, and the auxiliary-prime conditions needed to force a second residual representation with known automorphy. The endpoint is the geometric input to the Moret–Bailly argument.

60. **Potential Modularity of Two-Dimensional Representations**
    Combine the moduli construction, Moret–Bailly theorem, known automorphic residual representations, and modularity lifting. Starting from a suitable residual representation (\bar\rho), construct a totally real extension and an auxiliary elliptic curve whose one torsion representation realizes (\bar\rho) while another is already known to be modular. Lift modularity across the two primes. The endpoint is modularity of the original representation after restriction to a well-controlled totally real extension.

61. **Compatible Systems of Galois Representations**
    Develop weakly and strongly compatible systems of two-dimensional (\ell)-adic representations. Define common Frobenius polynomials, ramification sets, determinants, residual members, restriction and induction, and the level of independence-of-(\ell) actually needed later. Construct compatible systems from automorphic representations using the preceding Galois-representation theorem. The endpoint is the ability to regard one modular (\ell)-adic representation as one member of an arithmetic family indexed by primes.

62. **Brauer Induction and Descent of Automorphy**
    Develop the finite-group representation theory and automorphic bookkeeping required to descend compatible systems from solvable extensions. Prove the relevant Brauer induction theorem, express representations virtually as inductions from solvable subgroups, and combine this with automorphic induction and solvable base change. The endpoint is a descent mechanism that turns potential modularity over auxiliary fields into global compatible systems over the original field.

63. **Changing the Prime**
    Formalize the standard technique of replacing an (\ell)-adic representation by another member of its compatible system at a more convenient prime. Track Frobenius polynomials, determinants, residual reducibility, local ramification conditions, and finite-flat behavior across the system as far as available. The FLT-facing endpoint is the passage from an inconvenient representation to its (3)-adic companion while retaining enough arithmetic structure for the final classification argument.

64. **Discriminants of Galois Representations**
    Relate ramification of finite Galois modules to discriminants of the number fields cut out by those modules. Develop local differents, discriminants in towers, discriminant bounds derived from upper ramification constraints, and especially the strong bounds implied by finite-flat group schemes at the residue characteristic. The endpoint is an explicit root-discriminant estimate for fields generated by torsion of the small-ramification Galois representations appearing in the change-of-prime argument.

65. **Odlyzko Bounds and Fontaine’s Argument**
    Develop the analytic or precomputed number-theoretic lower bounds on root discriminants needed to contradict the upper bounds obtained from finite-flat ramification. Formalize the Odlyzko–Poitou inequalities in a usable form, explain their dependence on degree and signature, and reconstruct Fontaine’s small-ramification method. The endpoint is a theorem saying that certain large extensions with the prescribed very small ramification simply cannot exist.

66. **Hardly Ramified (3)-adic Representations**
    Apply the preceding discriminant machinery to classify the relevant small-ramification (3)-adic representations. Analyze their residual mod-(3) representations, build the tower of fields cut out by successive (3^n)-torsion quotients, control each field’s discriminant, and use global bounds to restrict the image. The endpoint is the specific reducibility or (1\oplus\chi_3)-type conclusion required to contradict the representation coming from the Frey curve.

67. **Modular Curves (X_0(N)) and (X_1(N))**
    Develop modular curves from their moduli interpretation in enough detail to study rational cyclic subgroups and torsion points of elliptic curves. Cover level structures, compactification, cusps, degeneracy maps, rational points, reduction at primes, and the interpretation of a (K)-rational point of (X_0(N)) as a (K)-rational cyclic isogeny. The endpoint is the geometric translation of reducibility of (E[p]) into rational points on modular curves.

68. **Jacobians of Modular Curves**
    Develop the Jacobians (J_0(N)) and the arithmetic structures used in the proof of rational-isogeny results. Construct the Hecke action, cuspidal subgroup, Albanese maps from the modular curve, reduction maps, duality, and the relevant quotients of the Jacobian. The endpoint is a sufficiently explicit arithmetic theory of (J_0(p)) to turn information about rational points on (X_0(p)) into statements about finite subgroups and Hecke modules.

69. **The Eisenstein Ideal**
    Develop the Eisenstein part of the Hecke algebra acting on modular Jacobians. Define the Eisenstein ideal, analyze its quotient, study the cuspidal and Shimura subgroups, prove the necessary torsion and congruence statements, and connect the Eisenstein quotient to rational points on modular curves. The endpoint is the algebraic engine in Mazur’s method that severely restricts the possible rational (p)-isogenies of elliptic curves over (\mathbf Q).

70. **Rational Isogenies of Prime Degree**
    Assemble the modular-curve, Jacobian, and Eisenstein-ideal theory into the classification result actually needed for FLT. Analyze a rational point corresponding to a prime-degree isogeny, use reduction and Eisenstein arguments to eliminate the prohibited primes, and isolate exactly the exceptional degrees. The FLT-facing endpoint need not maximize generality: it should prove the irreducibility of the Frey curve’s mod-(p) representation for every prime exponent (p\ge5) occurring in the argument.

71. **The Frey Curve and Fermat’s Last Theorem**
    Make the final book almost entirely an assembly of previously formalized interfaces. Reduce Fermat’s equation to the relevant prime-exponent cases, construct the Frey curve, calculate its discriminant and local reduction behavior, prove its residual representation is irreducible using the rational-isogeny branch, and establish the required small-ramification conditions. Invoke modularity lifting, potential modularity, compatible systems, changing the prime, and the classification of hardly ramified (3)-adic representations to obtain the contradiction and conclude Fermat’s Last Theorem.

