# Uniqueness of K_{d+2} at C(d+2,2) edges for d >= 6

For every natural number `d ≥ 6`, a finite simple graph with exactly `C(d + 2, 2)` edges, with no
isolated vertex, and with no unit-distance representation in Euclidean `d`-space, is isomorphic to
`K_{d+2}`.

| | |
|---|---|
| Stage | proved statement; blueprint checkdecls is Stage 2 |
| Palomar entry | not yet submitted |
| `formal_proof` PR | not yet opened |
| Mathlib PR | not yet opened |
| Writeup | not yet published |

Built with the workspace at [`~/Code/Math`](../..). `AGENTS.md` holds the working rules;
`../../docs/PLAYBOOK.md` holds the pipeline.

## Gates

```sh
lake build && lake exe axioms && lake exe fidelity && lake exe module-system \
  && lake exe standalone-mathlib && lake exe proof-links && lake exe style \
  && lake exe documentation && lake exe layering && lake exe palomar-compatibility \
  && scripts/check-palomar-challenge.sh && scripts/lint-env.sh \
  && leanblueprint checkdecls && scripts/audit-probes.sh
```
