# Rough book dependency graph

An arrow `A --> B` means that book A supplies substantial prerequisites for book B.
This is an architectural sketch rather than a strict reading order: transitive edges and
small shared prerequisites are omitted, and several books could profitably be developed
in parallel.

```mermaid
flowchart LR
    subgraph local[Local and global arithmetic]
        B01["1 Valuations and DVRs"]
        B02["2 Local field extensions"]
        B03["3 Ramification"]
        B04["4 Adeles and ideles"]
        B05["5 Local CFT"]
        B06["6 Global CFT"]
        B07["7 Elliptic curves over DVRs"]
        B08["8 Tate curves"]
        B09["9 Torsion and Tate modules"]
    end

    subgraph flat[Finite-flat geometry]
        B10["10 Finite locally free schemes"]
        B11["11 Affine group schemes"]
        B12["12 Finite flat group schemes"]
        B13["13 Cartier duality"]
        B14["14 Finite-flat representations"]
    end

    subgraph deformation[Cohomology and deformation theory]
        B15["15 Continuous cohomology"]
        B16["16 Local Galois cohomology"]
        B17["17 Tate local duality"]
        B18["18 Selmer groups"]
        B19["19 Poitou-Tate duality"]
        B20["20 Coefficient rings"]
        B21["21 Deformation functors"]
        B22["22 Representability"]
        B23["23 Conditions away from ell"]
        B24["24 Finite-flat conditions"]
        B25["25 Global deformation problems"]
    end

    subgraph patching[Commutative algebra and patching]
        B26["26 Complete local algebra"]
        B27["27 Depth and complete intersections"]
        B28["28 Numerical R=T criteria"]
        B29["29 Taylor-Wiles primes"]
        B30["30 Taylor-Wiles systems"]
        B31["31 Patching modules and rings"]
        B32["32 Abstract R=T"]
    end

    subgraph automorphic[Quaternionic and automorphic theory]
        B33["33 Quaternion algebras"]
        B34["34 Quaternion orders"]
        B35["35 Definite quaternionic forms"]
        B36["36 Hecke operators"]
        B37["37 Hecke algebras"]
        B38["38 Smooth representations"]
        B39["39 Representations of GL2"]
        B40["40 Representations of division algebras"]
        B41["41 Local Jacquet-Langlands"]
        B42["42 Automorphic representations of GL2"]
        B43["43 Automorphic representations of D*"]
        B44["44 Global Jacquet-Langlands"]
        B45["45 Automorphic induction"]
        B46["46 Local cyclic base change"]
        B47["47 Global cyclic base change"]
        B48["48 Solvable base change"]
    end

    subgraph geometry[Etale geometry and Galois representations]
        B49["49 Finite etale covers"]
        B50["50 Etale cohomology of curves"]
        B51["51 Jacobians and H1"]
        B52["52 Modular and Shimura curves"]
        B53["53 Hecke correspondences"]
        B54["54 Galois representations from forms"]
    end

    subgraph lifting[Modularity lifting]
        B55["55 Minimal modularity lifting"]
        B56["56 Nonminimal modularity lifting"]
    end

    subgraph potential[Potential modularity and changing prime]
        B57["57 Hilbert irreducibility"]
        B58["58 Moret-Bailly"]
        B59["59 Potential-modularity moduli"]
        B60["60 Potential modularity"]
        B61["61 Compatible systems"]
        B62["62 Brauer induction and descent"]
        B63["63 Changing the prime"]
        B64["64 Discriminants of representations"]
        B65["65 Odlyzko and Fontaine"]
        B66["66 Hardly ramified 3-adic reps"]
    end

    subgraph isogenies[Modular curves and rational isogenies]
        B67["67 X0(N) and X1(N)"]
        B68["68 Modular Jacobians"]
        B69["69 Eisenstein ideal"]
        B70["70 Rational prime-degree isogenies"]
    end

    B71["71 Frey curve and FLT"]

    B01 --> B02 --> B03
    B01 --> B04
    B02 --> B05
    B04 --> B06
    B05 --> B06
    B01 --> B07
    B02 --> B08
    B07 --> B08
    B07 --> B09
    B08 --> B09

    B10 --> B11 --> B12 --> B13
    B02 --> B14
    B09 --> B14
    B12 --> B14
    B13 --> B14

    B15 --> B16 --> B17
    B15 --> B18
    B16 --> B18
    B17 --> B19
    B18 --> B19
    B20 --> B21 --> B22
    B15 --> B21
    B03 --> B23
    B16 --> B23
    B22 --> B23
    B14 --> B24
    B16 --> B24
    B22 --> B24
    B18 --> B25
    B19 --> B25
    B22 --> B25
    B23 --> B25
    B24 --> B25

    B20 --> B26 --> B27 --> B28
    B06 --> B29
    B19 --> B29
    B25 --> B29
    B25 --> B30
    B29 --> B30
    B27 --> B31
    B30 --> B31
    B28 --> B32
    B31 --> B32

    B33 --> B34 --> B35 --> B36 --> B37
    B38 --> B39
    B33 --> B40
    B38 --> B40
    B39 --> B41
    B40 --> B41
    B04 --> B42
    B39 --> B42
    B35 --> B43
    B40 --> B43
    B41 --> B44
    B42 --> B44
    B43 --> B44
    B06 --> B45
    B39 --> B45
    B42 --> B45
    B39 --> B46
    B41 --> B46
    B42 --> B47
    B45 --> B47
    B46 --> B47 --> B48

    B49 --> B50 --> B51
    B34 --> B52
    B49 --> B52
    B36 --> B53
    B51 --> B53
    B52 --> B53
    B03 --> B54
    B09 --> B54
    B42 --> B54
    B50 --> B54
    B53 --> B54

    B32 --> B55
    B37 --> B55
    B54 --> B55
    B23 --> B56
    B24 --> B56
    B44 --> B56
    B48 --> B56
    B55 --> B56

    B57 --> B58
    B49 --> B59
    B52 --> B59
    B45 --> B60
    B48 --> B60
    B54 --> B60
    B56 --> B60
    B58 --> B60
    B59 --> B60
    B54 --> B61
    B60 --> B61
    B45 --> B62
    B48 --> B62
    B61 --> B62
    B14 --> B63
    B61 --> B63
    B03 --> B64
    B14 --> B64
    B64 --> B65
    B63 --> B66
    B64 --> B66
    B65 --> B66

    B07 --> B67
    B09 --> B67
    B49 --> B67
    B51 --> B68
    B53 --> B68
    B67 --> B68
    B37 --> B69
    B68 --> B69
    B09 --> B70
    B67 --> B70
    B68 --> B70
    B69 --> B70

    B07 --> B71
    B08 --> B71
    B09 --> B71
    B56 --> B71
    B60 --> B71
    B63 --> B71
    B66 --> B71
    B70 --> B71
```
