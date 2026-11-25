module

public import Mathlib

@[expose] public section

/-!
# Aristotle's error: regular tetrahedra do not fill space, and three more Platonic polyhedra

**Informal statement.** A convex polytope is a bounded intersection of finitely many closed half-spaces (`IsPoly`).
A tiling (`ConvexTiling`) covers space with convex polytopes that have interior points and pairwise disjoint
interiors, finitely many near each point; it need not be face to face. A similar copy (`SimilarCopy`) is the image
of a positive scaling under an isometry (reflections allowed); each tile has its own scale. Angles are read from
the set alone: at `x` the directions that stay in the set form a cone (`tcone`); where the directions `v` with `v`,
`-v` both in it span a line `K` (`linSpace`), the angle is 2π times the share of the unit disc of `Kᗮ` in the cone
(`wedgeAngle`); `EdgeAngle P θ` says that `θ` occurs so. `RationalAngles P`: every such angle of `P` is a
nonnegative rational multiple of π.

The regular polyhedra are the solution sets of their face inequalities `⟪N k, x⟫ ≤ B k`: the tetrahedron `teSet`
(corners (1,1,1), (1,−1,−1), (−1,1,−1), (−1,−1,1)), the octahedron `ocSet` (corners ±e₁, ±e₂, ±e₃), the cube
`cuSet` (corners (±1,±1,±1)), the dodecahedron `dhSet` and the icosahedron `ihSet` (exact in ℚ(√5)).

1. `aristotle_error` (**Aristotle's error**): there is no tiling of ℝ³ by similar copies of the regular
   tetrahedron.
2. `octa_alone`, `dodeca_alone`, `icosa_alone`: the same for the regular octahedron, dodecahedron, icosahedron.
3. `no_tetra`, `no_octa`, `no_dodeca`, `no_icosa`: in a tiling of ℝ³ by similar copies of one of these polyhedra
   and convex polytopes with `RationalAngles` (cubes, for instance), no tile is a copy of that polyhedron.
4. `platonic_mix`: in a tiling of ℝ³ by similar copies of the five Platonic polyhedra and convex polytopes with
   `RationalAngles`, no tile is a dodecahedron or an icosahedron.

**Sources.** Aristotle, *De Caelo* III.8, claimed that regular tetrahedra fill space; the refutation is credited
to Regiomontanus (15th century), and the history is told by J. C. Lagarias and C. Zong, Notices AMS 59 (2012)
1540–1549. The angle step rests on Niven's
theorem (I. Niven, *Irrational Numbers*, 1956; Mathlib `niven`). The edge-angle argument for pairs of regular
polyhedra is stated by Gabbrielli, Jiao and Torquato, Phys. Rev. E 86 (2012) 041141. Every definition and statement
is copied from the Lean library (namespaces `DehnCanon.Library`, `Packets`, `PacketsGen`,
`PlatonicFill`; qualifiers dropped, docstrings lightly reworded); the comment before each group names its file.
-/

namespace PlatonicFillLean

-- from Dehn2Poly.lean
section
open scoped RealInnerProductSpace
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The solution set of a system of linear inequalities `⟪a i, x⟫ ≤ b i`. -/
def sol {ι : Type} (a : ι → E) (b : ι → ℝ) : Set E := {x | ∀ i, ⟪a i, x⟫ ≤ b i}

/-- A convex polytope: a bounded intersection of finitely many closed half-spaces. -/
def IsPoly (P : Set E) : Prop :=
  Bornology.IsBounded P ∧ ∃ (ι : Type) (_ : Fintype ι) (a : ι → E) (b : ι → ℝ), P = sol a b

end

-- from Dehn2Local.lean
section
open scoped RealInnerProductSpace
open Set MeasureTheory Module TensorProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The cone of directions that stay in `P` near the point `x` of `P` (empty when `x ∉ P`). -/
def tcone (P : Set E) (x : E) : Set E := {v | x ∈ P ∧ ∃ t : ℝ, 0 < t ∧ x + t • v ∈ P}

/-- The span of the directions `v` of a cone for which `-v` is in the cone too. -/
def linSpace (T : Set E) : Submodule ℝ E := Submodule.span ℝ {v | v ∈ T ∧ -v ∈ T}

/-- The part of the cone `T` inside the open unit disc of the space perpendicular to `K`. -/
def wedgeSet (T : Set E) (K : Submodule ℝ E) : Set Kᗮ := {w | (w : E) ∈ T ∧ ‖w‖ < 1}

/-- The angle of the cone `T` around the line `K`: 2π × area(T ∩ unit disc of Kᗮ) / area(unit disc of Kᗮ). -/
noncomputable def wedgeAngle (T : Set E) (K : Submodule ℝ E) : ℝ :=
  2 * Real.pi * ((volume (wedgeSet T K)).toReal / (volume (Metric.ball (0 : Kᗮ) 1)).toReal)

end

-- from Dehn2R3.lean
section
open scoped RealInnerProductSpace
open Set MeasureTheory Measure Module TensorProduct

/-- Coordinate 3-space. -/
abbrev R3 := EuclideanSpace ℝ (Fin 3)

end

-- from Lemma2.lean
section
open Set MeasureTheory Module Filter Topology
open scoped RealInnerProductSpace

/-- **A tiling of space by convex polytopes.** -/
structure ConvexTiling (ι : Type*) (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  /-- The tiles. -/
  P : ι → Set E
  poly : ∀ i, IsPoly (P i)
  nonempty_interior : ∀ i, (interior (P i)).Nonempty
  cover : ∀ x, ∃ i, x ∈ P i
  disjoint : Pairwise fun i j => Disjoint (interior (P i)) (interior (P j))
  locallyFinite : LocallyFinite P

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fact (finrank ℝ E = 3)]

/-- `θ` is a dihedral angle of `P`, read from the set at an edge point. -/
def EdgeAngle (P : Set E) (θ : ℝ) : Prop :=
  ∃ x ∈ P, finrank ℝ (linSpace (tcone P x)) = 1 ∧ wedgeAngle (tcone P x) (linSpace (tcone P x)) = θ

end

-- from Pieces.lean
section
open Set MeasureTheory Module Filter Topology
open scoped RealInnerProductSpace Pointwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `Q` is a similar copy of `S`: the image of a positive scaling of `S` under a rigid motion (reflections
allowed). -/
def SimilarCopy (Q S : Set E) : Prop := ∃ (g : E ≃ᵃⁱ[ℝ] E) (c : ℝ), 0 < c ∧ Q = g '' (c • S)

end

-- from GenTE.lean
section
open scoped RealInnerProductSpace Real
open Set Module

/-- Outward face normals. -/
noncomputable def teN : Fin 4 → R3 :=
  ![!₂[(-1), (-1), (-1)], !₂[(-1), 1, 1], !₂[1, (-1), 1], !₂[1, 1, (-1)]]

/-- Offsets. -/
noncomputable def teB : Fin 4 → ℝ := ![1, 1, 1, 1]

/-- The polyhedron. -/
def teSet : Set R3 := sol teN teB

end

-- from GenOC.lean
section
open scoped RealInnerProductSpace Real
open Set Module

/-- Outward face normals. -/
noncomputable def ocN : Fin 8 → R3 :=
  ![!₂[1, 1, 1], !₂[1, 1, (-1)], !₂[1, (-1), 1], !₂[1, (-1), (-1)],
    !₂[(-1), 1, 1], !₂[(-1), 1, (-1)], !₂[(-1), (-1), 1], !₂[(-1), (-1), (-1)]]

/-- Offsets. -/
noncomputable def ocB : Fin 8 → ℝ := ![1, 1, 1, 1, 1, 1, 1, 1]

/-- The polyhedron. -/
def ocSet : Set R3 := sol ocN ocB

end

-- from GenCU.lean
section
open scoped RealInnerProductSpace Real
open Set Module

/-- Outward face normals. -/
noncomputable def cuN : Fin 6 → R3 :=
  ![!₂[1, 0, 0], !₂[(-1), 0, 0], !₂[0, 1, 0], !₂[0, (-1), 0],
    !₂[0, 0, 1], !₂[0, 0, (-1)]]

/-- Offsets. -/
noncomputable def cuB : Fin 6 → ℝ := ![1, 1, 1, 1, 1, 1]

/-- The polyhedron. -/
def cuSet : Set R3 := sol cuN cuB

end

-- from GenDH.lean
section
open scoped RealInnerProductSpace Real
open Set Module

/-- Outward face normals. -/
noncomputable def dhN : Fin 12 → R3 :=
  ![!₂[0, 2, (1 + √5)], !₂[0, 2, (-1 - √5)], !₂[0, (-2), (1 + √5)], !₂[0, (-2), (-1 - √5)],
    !₂[(1 + √5), 0, 2], !₂[(1 + √5), 0, (-2)], !₂[(-1 - √5), 0, 2], !₂[(-1 - √5), 0, (-2)],
    !₂[2, (1 + √5), 0], !₂[2, (-1 - √5), 0], !₂[(-2), (1 + √5), 0], !₂[(-2), (-1 - √5), 0]]

/-- Offsets. -/
noncomputable def dhB : Fin 12 → ℝ := ![(6 + 2 * √5), (6 + 2 * √5), (6 + 2 * √5), (6 + 2 * √5), (6 + 2 * √5), (6 + 2 * √5), (6 + 2 * √5), (6 + 2 * √5), (6 + 2 * √5), (6 + 2 * √5), (6 + 2 * √5), (6 + 2 * √5)]

/-- The polyhedron. -/
def dhSet : Set R3 := sol dhN dhB

end

-- from GenIH.lean
section
open scoped RealInnerProductSpace Real
open Set Module

/-- Outward face normals. -/
noncomputable def ihN : Fin 20 → R3 :=
  ![!₂[2, 2, 2], !₂[2, 2, (-2)], !₂[2, (-2), 2], !₂[2, (-2), (-2)],
    !₂[(-2), 2, 2], !₂[(-2), 2, (-2)], !₂[(-2), (-2), 2], !₂[(-2), (-2), (-2)],
    !₂[0, (1 + √5), (-1 + √5)], !₂[0, (1 + √5), (1 - √5)], !₂[0, (-1 - √5), (-1 + √5)], !₂[0, (-1 - √5), (1 - √5)],
    !₂[(-1 + √5), 0, (1 + √5)], !₂[(-1 + √5), 0, (-1 - √5)], !₂[(1 - √5), 0, (1 + √5)], !₂[(1 - √5), 0, (-1 - √5)],
    !₂[(1 + √5), (-1 + √5), 0], !₂[(1 + √5), (1 - √5), 0], !₂[(-1 - √5), (-1 + √5), 0], !₂[(-1 - √5), (1 - √5), 0]]

/-- Offsets. -/
noncomputable def ihB : Fin 20 → ℝ := ![(6 + 2 * √5), (6 + 2 * √5), (6 + 2 * √5), (6 + 2 * √5), (6 + 2 * √5), (6 + 2 * √5), (6 + 2 * √5), (6 + 2 * √5), (6 + 2 * √5), (6 + 2 * √5), (6 + 2 * √5), (6 + 2 * √5), (6 + 2 * √5), (6 + 2 * √5), (6 + 2 * √5), (6 + 2 * √5), (6 + 2 * √5), (6 + 2 * √5), (6 + 2 * √5), (6 + 2 * √5)]

/-- The polyhedron. -/
def ihSet : Set R3 := sol ihN ihB

end

-- from Fill.lean
section
open Set Module Real

/-- A convex piece whose dihedral angles, read from the set, are nonnegative rational multiples of π. -/
def RationalAngles (P : Set R3) : Prop := ∀ θ, EdgeAngle P θ → ∃ q : ℚ, 0 ≤ q ∧ θ = q * π

/-- In a tiling of 3-space by similar copies of the regular tetrahedron and convex pieces with rational
dihedral angles (cubes, for instance), no tile is a tetrahedron. -/
theorem no_tetra {ι : Type*} (T : ConvexTiling ι R3)
    (hk : ∀ i, SimilarCopy (T.P i) teSet ∨ RationalAngles (T.P i)) (i : ι) : ¬ SimilarCopy (T.P i) teSet := by
  sorry

/-- **Aristotle's error.** There is no tiling of 3-space by similar copies of the regular tetrahedron (any
sizes, reflections allowed, not necessarily face-to-face). -/
theorem aristotle_error {ι : Type*} (T : ConvexTiling ι R3) : ¬ ∀ i, SimilarCopy (T.P i) teSet := by
  sorry

theorem no_octa {ι : Type*} (T : ConvexTiling ι R3)
    (hk : ∀ i, SimilarCopy (T.P i) ocSet ∨ RationalAngles (T.P i)) (i : ι) : ¬ SimilarCopy (T.P i) ocSet := by
  sorry

theorem no_dodeca {ι : Type*} (T : ConvexTiling ι R3)
    (hk : ∀ i, SimilarCopy (T.P i) dhSet ∨ RationalAngles (T.P i)) (i : ι) : ¬ SimilarCopy (T.P i) dhSet := by
  sorry

theorem no_icosa {ι : Type*} (T : ConvexTiling ι R3)
    (hk : ∀ i, SimilarCopy (T.P i) ihSet ∨ RationalAngles (T.P i)) (i : ι) : ¬ SimilarCopy (T.P i) ihSet := by
  sorry

/-- No tiling of 3-space by similar copies of the regular octahedron. -/
theorem octa_alone {ι : Type*} (T : ConvexTiling ι R3) : ¬ ∀ i, SimilarCopy (T.P i) ocSet := by
  sorry

/-- No tiling of 3-space by similar copies of the regular dodecahedron. -/
theorem dodeca_alone {ι : Type*} (T : ConvexTiling ι R3) : ¬ ∀ i, SimilarCopy (T.P i) dhSet := by
  sorry

/-- No tiling of 3-space by similar copies of the regular icosahedron. -/
theorem icosa_alone {ι : Type*} (T : ConvexTiling ι R3) : ¬ ∀ i, SimilarCopy (T.P i) ihSet := by
  sorry

/-- **In a tiling of 3-space by similar copies of the five Platonic polyhedra** (and convex pieces with rational
dihedral angles), **no tile is a dodecahedron or an icosahedron.** -/
theorem platonic_mix {ι : Type*} (T : ConvexTiling ι R3)
    (hk : ∀ i, SimilarCopy (T.P i) teSet ∨ SimilarCopy (T.P i) ocSet ∨ SimilarCopy (T.P i) cuSet ∨
      SimilarCopy (T.P i) dhSet ∨ SimilarCopy (T.P i) ihSet ∨ RationalAngles (T.P i)) (i : ι) :
    ¬ SimilarCopy (T.P i) dhSet ∧ ¬ SimilarCopy (T.P i) ihSet := by
  sorry

end

end PlatonicFillLean
