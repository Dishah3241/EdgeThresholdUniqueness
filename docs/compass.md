# Compass list

The declarations whose meaning decides whether the statement says what it claims: for every
`d ≥ 6`, a graph with exactly `C(d + 2, 2)` edges, no isolated vertex and no unit-distance
representation in `ℝᵈ` is `K_{d+2}`. This is the owner's whole review surface, and **its sign-off is
the statement freeze** for this result. Everything else, including the whole proof interior and the
GraphDimension library, is checked by the kernel and the gates.

The project declarations are in
`EdgeThresholdUniqueness/Standalone/Mathlib/InlineEdgeThresholdUniqueness.lean`, namespace
`EdgeThresholdUniqueness.Standalone.Mathlib.InlineEdgeThresholdUniqueness`. Rows 11–14 are Mathlib's.

**Owner sign-off: confirmed on 2026-09-24 for rows 1–14** (the owner, in the Math driver session: "do 1",
answering the request to sign this list), on the list as committed at `5d4621b`. This freezes the
statement. Any change to a row cancels it.

- The owner chose the statement's form on 2026-09-23: every `d ≥ 6`, the hypothesis "no
  representation in `ℝᵈ`" rather than "dimension exactly `d + 1`", and no isolated vertex with the
  conclusion "isomorphic to `K_{d+2}`".
- It is authored, not inherited: no `formal-conjectures` statement exists. Stage 1 wrote it twice,
  blind: statement A by cursor (Grok 4.7), statement B by codex (gpt-6-astra). pi (glm-5.3-flash), a
  third lineage, proved `A ↔ B` in Lean (`EdgeThresholdUniqueness/Stage1/Equivalence.lean`). The
  inline statement is A, and the kernel checks that too (`inlineIffStatementA`, `Iff.rfl`).
- The proof reaches the statement through the library's `SimpleGraph.UnitDistEmbeddable`, whose body
  is row 1's; the kernel identifies them, so that bridge needs no row.

| # | Declaration | Must mean | Check |
|---|---|---|---|
| 1 | `UnitDistanceRepresentable G d` | an **injective** placement of the vertices in `ℝᵈ` with every edge at distance one | Non-edges are unconstrained (Erdős–Harary–Tutte). Note the argument order `G d`. |
| 2 | `UniqueKComplete` | for every `d ≥ 6` and every graph `G` on `Fin n`: if `G` has **exactly** `C(d + 2, 2)` edges, every vertex has a neighbour, and `G` has no representation in `ℝᵈ`, then `G ≅ K_{d+2}` | Equality in the edge count, not `≤`. "Every vertex has a neighbour" is the no-isolated-vertex hypothesis. `Fin n` for every `n` covers every finite graph up to relabelling. |
| 3 | `EdgeThresholdUniqueness.Palomar.target` | exactly row 2 | It is `UniqueKComplete` itself, with no extra hypothesis. `Solution.lean` proves it. |
| 4 | `UniqueKComplete.witness` | the claim holds, and `K₈` at `d = 6` meets every hypothesis: 28 edges, no isolated vertex, no representation in `ℝ⁶` | Guards against vacuity: the hypotheses are jointly satisfiable. |
| 5 | `UniqueKComplete.dropHd` | without `d ≥ 6` the claim is false | Its witness is at `d = 1`: the star `K₁,₃` has 3 edges, no isolated vertex and no representation in `ℝ¹`, and is not `K₃`. (At `d = 4`, `K₁,₃,₃` is another.) |
| 6 | `UniqueKComplete.dropHcard` | without the exact edge count the claim is false | `K₉` at `d = 6`: no representation in `ℝ⁶`, no isolated vertex, not `K₈`. |
| 7 | `UniqueKComplete.dropHdeg` | without the no-isolated-vertex hypothesis the claim is false | `K₈` plus one isolated vertex at `d = 6`: 28 edges, no representation, not `K₈`. |
| 8 | `UniqueKComplete.dropHrep` | without "no representation" the claim is false | A path with 28 edges at `d = 6`: the right edge count and no isolated vertex, but it is not `K₈`. |
| 9 | `UnitDistanceRepresentable.separating`, first half | a graph with an edge has a representation in `ℝ¹` in which a **non-edge** is at distance one | Separates row 1 from the stricter unit-distance-graph reading. |
| 10 | `UnitDistanceRepresentable.separating`, second half | the star `K₁,₃` has a non-injective unit-length map into `ℝ¹` but no injective one | Separates row 1 from the reading without injectivity. |
| 11 | Mathlib `completeGraph (Fin (d + 2))` | `K_{d+2}` | Every two distinct vertices are adjacent. |
| 12 | Mathlib `G ≃g H` | a graph isomorphism: a bijection preserving and reflecting adjacency | Stronger than an embedding or a homomorphism. |
| 13 | Mathlib `G.edgeSet.ncard` | the number of edges | `ncard` is `0` on an infinite set, but every graph here is on `Fin n`, so this is the true count. |
| 14 | Mathlib `dist` on `EuclideanSpace ℝ (Fin d)`, and `Nat.choose (d + 2) 2` | the Euclidean (L²) distance, and `C(d + 2, 2)` | `EuclideanSpace` is `PiLp 2`; the plain `Fin d → ℝ` would carry the sup metric. `C(8, 2) = 28`. |
