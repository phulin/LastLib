# Example Prompt for Book 2

Work in `/home/phulin/LastLib`. Write only Book 2. Do not search or browse the internet under any circumstances. Read `BOOKS.md` and the completed Book 1, `books/001-valuations-dvrs-and-completions.md`, before writing. You may inspect the local Mathlib checkout, and you may assume the reader knows its mathematical results, but do not let that prevent a complete and pedagogically coherent treatment. The book text must never mention Lean, Mathlib, formalization, APIs, theorem identifiers from code, or proof assistants.

Create `books/002-finite-extensions-of-local-fields.md`. Do not alter Book 1, `BOOKS.md`, or the Mathlib checkout, and do not make a git commit.

Write a polished graduate-level textbook titled “Finite Extensions of Local Fields,” following the second description in `BOOKS.md`. Aim for the substance and scale of roughly 100 typically typeset pages, but treat that as a soft editorial target rather than a word-count requirement. Completeness, explanatory depth, and logical coherence matter more than length.

Book 1 is established background. Refer to its definitions and results where appropriate instead of awkwardly reconstructing them, while briefly recalling notation when needed. Book 2 must nevertheless read as one continuous mathematical narrative: a reader familiar with Book 1 should encounter no unexplained gaps.

Before important definitions, explain the mathematical problem they solve and why they take their stated form. Give every chapter and every section a thorough motivation that explains its underlying ideas, its purpose in the theory, and its relationship to what precedes and follows; Book 1 was somewhat sparse, so err toward sustained explanation rather than compressed exposition. Develop intuition alongside precise statements. Include worked examples and illuminating counterexamples throughout. Before substantial proofs, explain the proof strategy; within proofs, make the decisive reasoning explicit; afterward, explain the consequences. Avoid a compressed definition–theorem–proof catalogue.

Develop the following arc:

- finite extensions $L/K$ of complete discretely valued fields and the uniquely extended valuation;
- completeness and discreteness of $L$, the valuation rings $\mathcal O_K\subseteq\mathcal O_L$, maximal ideals, residue fields, and normalized valuations;
- integral closure and finite freeness of $\mathcal O_L$ over $\mathcal O_K$;
- ramification index $e(L/K)$ and residue degree $f(L/K)$;
- the fundamental equality $[L:K]=e(L/K)f(L/K)$, with exact hypotheses and a detailed proof;
- multiplicativity of $e$ and $f$ in towers;
- behavior under completion and scalar extension where relevant;
- field trace and norm, their integral restrictions, transitivity, interaction with valuations, and their residue-field shadows;
- embeddings, automorphism groups, and the Galois case;
- decomposition and inertia groups, their action on the residue field, and the exact sequence relating inertia to residue-field Galois groups;
- Frobenius for finite residue fields, including arithmetic versus geometric normalization;
- unramified extensions and their equivalent characterizations;
- construction and classification of finite unramified extensions, especially over finite residue fields;
- totally ramified extensions, Eisenstein polynomials, uniformizers, and monogenicity under the correct hypotheses;
- the maximal unramified subextension and the decomposition of a finite extension into unramified and totally ramified parts;
- tame statements only insofar as they naturally complete this structural picture, leaving systematic tame and wild ramification filtrations to Book 3;
- the structure and filtration of unit groups, including

  $$
  U^0=\mathcal O_L^\times,\qquad U^n=1+\mathfrak m_L^n,
  $$

  the quotients $U^0/U^1$ and $U^n/U^{n+1}$, and the basic behavior of norms on these layers;
- a final synthesis giving a reusable language for inertia, residue-field Frobenius, norms, traces, and local Galois groups.

Carefully distinguish separable, inseparable, normal, Galois, unramified, and totally ramified hypotheses. State where residue-field perfection or finiteness is required. Do not silently assume characteristic zero. Use concrete examples such as unramified extensions of $\mathbf Q_p$, Eisenstein extensions, extensions of $k((t))$, and examples illustrating mixed versus equal characteristic.

Reserve lower and upper ramification filtrations, Herbrand functions, the different, discriminant formulas, and Artin and Swan conductors for Book 3. Mention those topics only when necessary to define the boundary of Book 2.

Use Markdown with `$...$` for inline mathematics and `$$...$$` for display mathematics. Do not use `\(...\)` or `\[...\]`. ASCII diagrams are allowed. Do not include exercises, appendices, optional sections, further-reading notes, bibliographic commentary, or implementation discussion.

Write incrementally to the target file. Once the entire book is finished and its chapter and section structure is final, write a useful linked table of contents at the top that accurately reflects that completed structure. Self-review the completed manuscript for mathematical correctness, consistent notation, coherent cross-references, adequate explanations, and complete coverage. Finish with a genuine mathematical conclusion rather than planning notes. Report the path, word count, line count, chapter count, and a concise coverage summary.
