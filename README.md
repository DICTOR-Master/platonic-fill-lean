# Aristotle's Error, Machine-Checked: Regular Tetrahedra Do Not Fill Space (Lean 4 + Mathlib)

Author: DICTO.

## The theorems

A tiling of 3-space here is a family of convex polytopes (bounded intersections of finitely many closed half-spaces)
with interior points, covering space, with pairwise disjoint interiors, finitely many near each point (local finiteness
is part of the definition). Tiles need not meet face to face. A tile is a similar copy of a polyhedron: a positive scaling followed by an isometry
(reflections allowed), each tile at its own scale. Each polyhedron is one fixed set in exact coordinates (`teSet`,
`ocSet`, `cuSet`, `dhSet`, `ihSet`); that every regular tetrahedron is a similar copy of `teSet` (and so on) is the
standard fact behind the informal reading, not proved in Lean.

- **Aristotle's error** (`aristotle_error`): there is no tiling of 3-space by similar copies of the regular
  tetrahedron.
- **The octahedron, the dodecahedron, the icosahedron alone** (`octa_alone`, `dodeca_alone`, `icosa_alone`): the
  same for each of these regular polyhedra.
- **With rational-angle helpers** (`no_tetra`, `no_octa`, `no_dodeca`, `no_icosa`): in a tiling by similar copies of
  one of these polyhedra and convex polytopes whose dihedral angles are nonnegative rational multiples of π (the cube
  is one: `cu_edgeAngle` in the library), no tile is a copy of that polyhedron.
- **Mixtures of Platonic polyhedra** (`platonic_mix`): in a tiling by similar copies of the five Platonic
  polyhedra and such rational-angle polytopes, no tile is a dodecahedron or an icosahedron.

Dihedral angles are read from the set itself: at an edge point, the share of a small disc across the edge that lies
in the polytope. Around an edge point of any tile the angles of the tiles there add up to 2π, each a dihedral angle
of its tile, π or 2π (no face-to-face assumption). Every Platonic angle is q·π + a·α + b·β + c·γ with
α = arctan φ, β = arccos(1/√6), γ = arccos √(2/3), and π, α, β, γ are linearly independent over ℚ (by Niven's
theorem, Mathlib `niven`, and a field argument). A rational weight on these four numbers, nonnegative on every angle that can occur, then
bounds every angle in a ring by 2; the regular tetrahedron's angle arccos(1/3) = 2γ has weight 4 under the weight
t = 2 on γ, so it cannot occur.

- `Challenge.lean`: the definitions and the nine statements, with every proof `sorry`. It imports only Mathlib.
- `Solution.lean`: the proofs, from the library.
- `PlatonicFill/`: the new library (namespace `PlatonicFill`).
- `Packets/`: the library of the Dehn packets entry, unchanged (with the Dehn Canon modules in `Packets/Canon/`).

Toolchain `leanprover/lean4:v4.35.0-rc2`, Mathlib `v4.35.0-rc2`. The theorems depend only on the axioms `propext`,
`Classical.choice` and `Quot.sound`. The library and `Solution.lean` use neither `sorry` nor `native_decide`. Every Lean file uses the module
system.

## How to check

```
lake exe cache get
lake build
```

## Files

| file | content |
|---|---|
| `PlatonicFill/GenTE.lean`, `GenOC.lean`, `GenCU.lean` | the regular tetrahedron, octahedron and cube from exact coordinates: edge data, boundedness, interior point, Gram values of the face normals (generated; every fact rechecked by Lean on integer tables) |
| `PlatonicFill/Solids.lean` | the dihedral angle of each of the five Platonic polyhedra, read from the set: arccos(1/3), arccos(−1/3), π/2, arccos(−1/√5), arccos(−√5/3) |
| `PlatonicFill/Fill.lean` | the weight, the ring bound, the nine theorems |
| `Packets/` | tilings, the edge-angle sum (Lemma 2), the independence of π, α, β, γ (Lemma 3), similar copies, the dodecahedron and the icosahedron |
| `Packets/Canon/` | the set-defined angle and the Dehn invariant (Dehn Canon) |

## Earlier work

The claim is Aristotle's (*De Caelo* III.8): that regular tetrahedra fill space. Its refutation is credited to
Regiomontanus (15th century); the history is told by J. C. Lagarias and C. Zong, "Mysteries in packing regular
tetrahedra", Notices AMS 59 (2012) 1540–1549. The angle step is Niven's theorem (I. Niven, *Irrational Numbers*,
Carus Mathematical Monographs 11, 1956), used through Mathlib's `niven`. The edge-angle argument for pairs of regular
polyhedra, not necessarily face to face, is stated by R. Gabbrielli, Y. Jiao and S. Torquato, Phys. Rev. E 86 (2012)
041141 (pairs of regular polyhedra; `platonic_mix` treats any mixture of the five with rational-angle helpers). The
rational independence of these dihedral angles is also in J. H. Conway, C. Radin, L. Sadun, Discrete Comput. Geom. 22
(1999) 321–332 (arXiv:math-ph/9812019); the Lean proof does not follow it. None of these theorems is new; this entry gives their Lean proofs.

We found no earlier machine-checked proof that regular tetrahedra do not fill space, nor of any Platonic
non-tiling result proved through dihedral angles. Sources checked (24 November 2026): web searches for formal proofs
(Lean, Isabelle, Coq, HOL) of the non-tiling by regular tetrahedra; Mathlib (`Mathlib.NumberTheory.Niven`; no tilings
of space by polytopes); the Isabelle AFP search page; Formalizing 100 Theorems, #50 "The Number of Platonic Solids"
(Lean, HOL Light, Isabelle), which classifies the five polyhedra and is the nearest formal neighbour, not a tiling
result; Flyspeck (HOL Light), which handles tetrahedra and dihedral angles inside the Kepler proof but does not state
this non-tiling; formal tiling impossibility proofs found elsewhere (the mutilated chessboard in Isabelle, Keller's
conjecture in dimension 8 in Lean, 2D triangle tilings), none using dihedral angles in 3D. Mizar and Metamath were
checked by web search only. `formalization.yaml` lists the sources in full.

## How it was made

DICTO set the question and the order of the work, with Claude (Anthropic): the Lean code was written by a Claude Code
agent. `formalization.yaml` (section `automation`) records this in full.

## Checks

`scripts/check-lean-sources.py` and `scripts/verify-comparator.sh` come from Palomar's entry template (PalomarRegistry).
They check the source rules and run `lake comparator` the way Palomar does.

## Licence

Apache-2.0 (see `LICENSE`). Copyright 2026 DICTO.

## Other work by DICTO

- ORCID (all works): https://orcid.org/0009-0001-2620-2036
- Website: https://dictospheres.com
