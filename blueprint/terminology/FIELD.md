# Field vocabulary

**Fill this in before naming any declaration.** Terminology drift is not cosmetic: once models
start coining vocabulary, nobody can tell which claims are real. The reference project's first
three weeks produced "stage-1 obstruction", "designed resonance", and "window equations", none of
which meant anything, and it could not be detected until someone tried to check the mathematics.

Build this from the actual references — the papers in `formalization.yaml` under `sources`, and the
standard texts of the subfield. Every term below must be traceable to one of them at a
pinpoint, not to a model's summary.

References, abbreviated below:

- **FKS** = Frankl, Kupavskii and Swanepoel, *Embedding graphs in Euclidean space*, J. Combin.
  Theory Ser. A **171** (2020), 105146, arXiv 1802.03092. Line numbers are to `main.tex` of the
  arXiv LaTeX source (`~/src/papers/fks-1802.03092/`), checked against the rendered source.
- **EHT** = the Erdős–Harary–Tutte notion of realizability that FKS's Definition (l. 55–57)
  records: the edge set is a *subset* of the unit-distance pairs.

## Part 0 — Terms this project uses

| Term | Meaning | Source, at a pinpoint |
|---|---|---|
| unit-distance graph in $\mathbb{R}^d$ | a graph whose vertex set lies in $\mathbb{R}^d$ and whose edge set is contained in the unit-distance pairs; non-edges may also sit at distance one | FKS l. 55–56, including the note that not every unit-distance pair must be an edge (EHT) |
| unit-distance representation | an injective placement $f : V(G) \to \mathbb{R}^d$ with $\lVert f(u) - f(v)\rVert = 1$ on every edge; this repository's statement word for FKS's "realized" | FKS l. 55–57; injectivity is explicit in the inlined definition |
| realizable in $X \subseteq \mathbb{R}^d$ | isomorphic to a unit-distance graph on vertices of $X$ | FKS l. 57 |
| $\mathbb{S}^{d-1}$ | the sphere of radius $1/\sqrt 2$ about the origin of $\mathbb{R}^d$ | FKS l. 57, 47 |
| $f(d)$ | the least number of edges of a graph not realizable in $\mathbb{R}^d$ | FKS l. 82 |
| Theorem 3 | for $d > 3$, fewer than $\binom{d+2}{2}$ edges realizes in $\mathbb{R}^d$; avoiding $K_{d+1}$ and $K_{d+2}-K_3$ realizes on $\mathbb{S}^{d-1}$ | FKS l. 91 |
| $g(d)$ | $g(2)=3$, $g(3)=8$, $g(d) = \binom{d+2}{2} - 1$ for $d \ge 4$; the budget of the induction | FKS l. 343 |
| $S(d)$, the induction statement | at most $g(d)$ edges realizes in $\mathbb{R}^d$; avoiding $K_{d+1}$ and $K_{d+2}-K_3$ realizes on $\mathbb{S}^{d-1}$ | FKS l. 344 |
| $K_n - K_3$ | the complete graph on $n$ vertices minus the three edges of a triangle | FKS l. 91, 344 |
| $(d-1)$-core | what remains after deleting vertices of degree at most $d-2$ one by one: a subgraph of minimum degree at least $d-1$, maximal with that property. Our (and the library's) name — FKS uses the pruning without naming its result | FKS l. 348–350; GraphDimension `Extremal/FKS/CoreAssembly.lean` |
| equality budget | the count $\binom{d+2}{2}$, i.e. $f(d)$'s upper bound from $K_{d+2}$ (l. 85), at which this project's theorem operates. Our term for the setting, not FKS's | FKS l. 85; ADR 0004 rung 4 |

## Part 1 — Terms deliberately avoided

Record terms that appear in the literature but are **not** used here, and why. A term with two
incompatible conventions in the field belongs here with the convention this project picked.

| Term | Why avoided / which convention chosen | Source |
|---|---|---|
| "extremal unit distance graph" | in the current plane-problem literature this means fewest unit distances, not fewest edges before non-realizability. Avoided as ambiguous; retrieval only (A11) | finding A11, literature-census note |
| "dimension-critical" | Noble's term for graphs $G$ with $\dim G \ge k$ attained at $e(G)$; not used in prose, since this project states uniqueness directly at the threshold | finding A11 retrieval terms; Chaffee–Noble 2016 |
| "embeds"/"embedded" for realizability | FKS's proof text switches between "embedded" and "realized"; the blueprint keeps "realizable/realization" throughout, matching FKS's definitions | FKS l. 57 vs l. 344 |

## Spelling

Lean declaration names follow Mathlib spelling. Reader-facing prose and the blueprint follow the
field's spelling. Where those differ, both are correct in their place — Lean writes
`Factorization` while prose writes "factorisation" — and cited titles stay verbatim.
