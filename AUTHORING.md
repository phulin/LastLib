These are instructions for authoring textbooks in LastLib. Our overall goal is to build a library of textbooks, each of which is a self-contained, polished, graduate-level textbook covering a specified topic. You have been assigned authoring or revision of the textbook for one of these topics. 

Textbooks are allowed to assume any result that is in "basic" graduate-level mathematics; as a proxy for this, you can assume any machinery or theorems that are fully built out in Mathlib. You may also use any result from a chronologically previous book in this library. Eventually, we will formalize all these textbooks in Lean, but keep the textbooks self-contained: don't mention Lean or Mathlib. DO NOT assume any prerequisite result outside of Mathlib. EVERYTHING else must be developed from scratch, and you may want to include some results that are proved in Mathlib to keep the textbook pedagogically coherent. 

Your assigned scope should cover roughly 100 pages of typically-typeset mathematics, or 10k-15k words. Treat that as a soft editorial target rather than a word-count requirement. Completeness, explanatory depth, and logical coherence matter more than length.

Before important definitions, explain the mathematical problem they solve and why they take their stated form. Give every chapter and every section a thorough motivation that explains its underlying ideas, its purpose in the theory, and its relationship to what precedes and follows. Err toward sustained explanation rather than compressed exposition. Develop intuition alongside precise statements. Include worked examples and illuminating counterexamples throughout. Before substantial proofs, explain the proof strategy; within proofs, make the decisive reasoning explicit; afterward, explain the consequences. Avoid a compressed definition–theorem–proof catalogue.

## General instructions

- Do not search or browse the internet under any circumstances.
- You may inspect the local Mathlib checkout.
- Do not mention Lean, Mathlib, formalization, APIs, theorem identifiers from code, or proof assistants.
- Do not assume any result not in Mathlib or a prior book. Outside of Mathlib results and prior books, do not specify anything that sounds like a preqrequisite, conditional result, prior hypothesis, etc. (these are all names prior agents have used to sneak in results they needed but were too lazy to prove).
- Previous books are established background. Refer to their definitions and results where appropriate instead of reconstructing them, while briefly recalling notation when needed.
- Don't add appendices, supplementary content, bibliography, etc. The textbook should be one self-contained sequence of chapters that elaborate one mathematical area.

## Formatting

Use Markdown with `$...$` for inline mathematics and `$$...$$` for display mathematics. Do not use `\(...\)` or `\[...\]`. ASCII diagrams are allowed. Do not include exercises, appendices, optional sections, further-reading notes, bibliographic commentary, or implementation discussion.

## Process

Write incrementally to the target file. Once the entire book is finished and its chapter and section structure is final, write a useful linked table of contents at the top that accurately reflects that completed structure. Self-review the completed manuscript for mathematical correctness, consistent notation, coherent cross-references, adequate explanations, and complete coverage. Finish with a genuine mathematical conclusion rather than planning notes. Report the path, word count, line count, chapter count, and a concise coverage summary.
