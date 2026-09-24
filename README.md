# The complete graph is the only extremal graph at C(d + 2, 2) edges, for d ≥ 6

A Lean 4 proof that for every `d ≥ 6`, a finite simple graph with exactly `C(d + 2, 2)` edges, no
isolated vertex, and no unit-distance representation in `ℝᵈ` is isomorphic to `K_{d+2}`.

> A **unit-distance representation** of a graph in `ℝᵈ` places its vertices at distinct points so
> that every edge is a unit segment; non-edges may also be at distance one (Erdős, Harary and Tutte,
> 1965). Frankl, Kupavskii and Swanepoel proved that for `d ≥ 4` every graph with fewer than
> `C(d + 2, 2)` edges has one, and `K_{d+2}` shows the bound is sharp
> ([FKSEdgeThreshold](https://github.com/Dishah3241/FKSEdgeThreshold) formalizes that theorem). This
> repository proves that for `d ≥ 6`, up to isolated vertices, `K_{d+2}` is the only graph at the
> threshold. At `d = 4` it is not: `K₁,₃,₃` also has 15 edges and no representation in `ℝ⁴`
> (Chaffee and Noble). To our knowledge this statement has not appeared in the literature before.

| | |
|---|---|
| Proof | complete: no `sorry`; only `propext`, `Classical.choice` and `Quot.sound` |
| Comparator | accepted by Lean's kernel and by NanoDa ([record](docs/comparator-2026-09-24.md)) |
| Library | [GraphDimension](https://github.com/Dishah3241/GraphDimension), which Lake fetches at the revision pinned in `lake-manifest.json`; the proof is `SimpleGraph.nonempty_iso_completeGraph_of_not_unitDistEmbeddable` there |
| Statement review | the statement was written twice, independently, and the two versions are proved equivalent in Lean (`EdgeThresholdUniqueness/Stage1/`); the owner signed the [Compass list](docs/compass.md) |
| Review | an independent, read-only review ([record](docs/review-2026-09-24.md)) |
| Blueprint | `blueprint/src/content.tex`, checked against the Lean by `leanblueprint checkdecls` |
| `formal-conjectures` link | none: the statement is not in `formal-conjectures` |
| Palomar entry | not yet submitted |

## The statement

`EdgeThresholdUniqueness/Standalone/Mathlib/InlineEdgeThresholdUniqueness.lean` states the claim
with Mathlib alone; `Challenge.lean` repeats it and `Solution.lean` proves it:

```lean
def UnitDistanceRepresentable {V : Type*} (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∃ f : V → EuclideanSpace ℝ (Fin d),
    Function.Injective f ∧ ∀ u v : V, G.Adj u v → dist (f u) (f v) = 1

def UniqueKComplete : Prop :=
  ∀ (d : ℕ) (_hd : 6 ≤ d) (n : ℕ) (G : SimpleGraph (Fin n))
    (_hcard : G.edgeSet.ncard = (d + 2).choose 2)
    (_hdeg : ∀ v : Fin n, ∃ w : Fin n, G.Adj v w)
    (_hrep : ¬ UnitDistanceRepresentable G d),
    Nonempty (G ≃g completeGraph (Fin (d + 2)))
```

## The proof

The library reruns the case analysis of Frankl, Kupavskii and Swanepoel's induction once more, with
the edge budget raised to exactly `C(d + 2, 2)`, on top of their statement for dimension `d − 1`.
Every count in their proof has slack `d − 4`, except one with slack `d − 5`, so at `d ≥ 6` each branch
either places the graph or forces `K_{d+2}`. Three pieces of geometry are new relative to their proof:
a tail of up to three extra edges attached to two unit simplices sharing a facet, vertices attached
over cliques of a regular simplex, and a bound on the circumradius of the triangles those need. A
tempting general version of that bound is false; the proof uses only the special triangles that
occur (see the blueprint).

## Checking it

Every gate below passes on the published commit. CI runs the same list.

```sh
lake build && lake exe axioms && lake exe fidelity && lake exe module-system \
  && lake exe standalone-mathlib && lake exe proof-links && lake exe style \
  && lake exe documentation && lake exe layering && lake exe palomar-compatibility \
  && scripts/check-palomar-challenge.sh && scripts/lint-env.sh \
  && leanblueprint checkdecls && scripts/audit-probes.sh
```

`formalization.yaml` records the sources, the AI assistance used for every phase, and the review.
