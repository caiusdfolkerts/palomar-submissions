module

public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

public import Mathlib.LinearAlgebra.Matrix.Notation

/-! # A nonrational four-polytope with fifteen vertices

The vertex labels run through A, B, C, D, E, F, U, V, X₀, X₁, X₂, Y₁,
Y₂, Z₁, Z₂. The positive scaling factors identify the specified rays in
the affine section whose coordinates sum to one. The field criterion
quantifies over every realization with the same face lattice.
-/

@[expose] public section
noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

/-- The Euclidean model space `ℝⁿ`. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A **convex polytope** in `ℝⁿ`: the convex hull of a finite nonempty set
whose listed vertices are exactly the extreme points of the hull. -/
structure ConvexPolytope (n : ℕ) where
  vertices : Finset (E n)
  vertices_nonempty : vertices.Nonempty
  vertices_eq_extremePoints :
    (vertices : Set (E n)) =
      Set.extremePoints ℝ (convexHull ℝ ((vertices : Set (E n))))

namespace ConvexPolytope

/-- The underlying convex set of the polytope. -/
def toSet {n : ℕ} (P : ConvexPolytope n) : Set (E n) :=
  convexHull ℝ ((P.vertices : Set (E n)))

/-- The affine dimension of `P`. -/
noncomputable def dim {n : ℕ} (P : ConvexPolytope n) : ℕ :=
  Module.finrank ℝ (vectorSpan ℝ P.toSet)

/-- `P` is **full-dimensional** if `dim P = n`. -/
def IsFullDim {n : ℕ} (P : ConvexPolytope n) : Prop := P.dim = n

/-- A **face** of `P` is a nonempty exposed subset. -/
def IsFace {n : ℕ} (P : ConvexPolytope n) (F : Set (E n)) : Prop :=
  IsExposed ℝ P.toSet F ∧ F.Nonempty

end ConvexPolytope

open ConvexPolytope
variable {n : ℕ}

/-- The nonempty geometric face poset, ordered by inclusion. -/
abbrev FaceType (P : ConvexPolytope n) := {F : Set (E n) // P.IsFace F}

end LeanEval.Geometry.PlatonicClassification

open Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

namespace Papers.Polytopes

variable {d : ℕ}

/-- Isomorphism of the nonempty faces under inclusion. Adjoining the empty
face to both posets gives the ordinary complete face lattices. -/
def CombinatoriallyEquivalent (P Q : ConvexPolytope d) : Prop :=
  Nonempty (FaceType P ≃o FaceType Q)

/-- Every coordinate of every vertex lies in the given real subfield. -/
def CoordinatesIn (K : Subfield ℝ) (P : ConvexPolytope d) : Prop :=
  ∀ v ∈ P.vertices, ∀ i : Fin d, v i ∈ K

/-- The face lattice admits a realization with all vertex coordinates in K. -/
def RealizableOver (P : ConvexPolytope d) (K : Subfield ℝ) : Prop :=
  ∃ Q : ConvexPolytope d, CombinatoriallyEquivalent P Q ∧ CoordinatesIn K Q

end Papers.Polytopes

namespace Papers.Nonrational.Fifteen
open Papers.Polytopes
/-- Homogeneous representatives, in the vertex order of the manuscript. -/
def manuscriptRay : Fin 15 → Fin 5 → ℝ :=
  let t : ℝ := (1 + Real.sqrt 5) / 2 - 1
  ![![1,1,1,0,0], ![1,1+t,1,0,0], ![0,1,1,1,1],
    ![t,1,1,0,0], ![t,1+t,1,0,t], ![1,1,0,t,0],
    ![0,0,0,3+t,1], ![0,0,0,1,1], ![1,0,0,1,1],
    ![1,0,0,4*(1+t+1/3),1/3], ![1,0,0,4*(1+t+2/3),2/3],
    ![0,1,0,0,2-2*(2-t)/15], ![0,1,0,0,2-(2-t)/15],
    ![0,0,1,2+t/3,0], ![0,0,1,2+2*t/3,0]]

def sectionCoordinates (w : E 4) : Fin 5 → ℝ :=
  ![1 - w 0 - w 1 - w 2 - w 3,w 0,w 1,w 2,w 3]

/-- The paper's fifteen rays define a full-dimensional convex four-polytope.
Its combinatorial type is realizable over precisely the real subfields
containing the square root of five. -/
theorem explicitFifteenVertexField :
    ∃ (P : ConvexPolytope 4) (p : Fin 15 → E 4),
      P.vertices = Finset.univ.image p ∧ P.IsFullDim ∧ P.vertices.card = 15 ∧
      (∀ i, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a • sectionCoordinates (p i) = b • manuscriptRay i) ∧
      ∀ K : Subfield ℝ, RealizableOver P K ↔ Real.sqrt 5 ∈ K := by
  sorry
end Papers.Nonrational.Fifteen
