module
public import Cubical.Polytope.SottoPolitopo
public import Cubical.Polytope.DueVertici
public import Cubical.Polytope.ConnettivitaGlobale
public import Cubical.Polytope.FacciaArgmax
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Order.Interval.Set.Monotone
public import Mathlib.Analysis.Convex.Between
public import Mathlib.Order.Hom.WithTopBot
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Nonsingular
public import Mathlib.Tactic.Ring
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.Rat
public import Mathlib.Topology.NhdsWithin
public import Mathlib.Data.Finset.Sum
public import Mathlib.Tactic.FunProp
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

/-!
# Finite face sets of genuine convex polytopes

These results concern exposed geometric faces of a convex hull.  No
combinatorial incidence or face-count property is assumed in the definitions.
-/

open Set

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- A finite convex polytope has only finitely many nonempty faces. -/
theorem finite_isFace (P : ConvexPolytope n) :
    Set.Finite {F : Set (E n) | P.IsFace F} := by
  classical
  apply (P.vertices.powerset.finite_toSet.image
    (fun s : Finset (E n) => convexHull ℝ (s : Set (E n)))).subset
  intro F hF
  refine ⟨P.vertices.filter (· ∈ F), ?_, ?_⟩
  · exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  · exact (face_eq_hull_vertices P hF).symm

/-- Geometric faces are determined by the vertices they contain. -/
theorem face_eq_iff_vertices_eq (P : ConvexPolytope n)
    {F G : Set (E n)} (hF : P.IsFace F) (hG : P.IsFace G) :
    F = G ↔ (∀ v ∈ P.vertices, v ∈ F ↔ v ∈ G) := by
  classical
  constructor
  · intro h v hv
    rw [h]
  · intro h
    rw [face_eq_hull_vertices P hF, face_eq_hull_vertices P hG]
    congr 2
    ext v
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hv, hvF⟩
      exact ⟨hv, (h v hv).mp hvF⟩
    · rintro ⟨hv, hvG⟩
      exact ⟨hv, (h v hv).mpr hvG⟩

/-- Nonempty intersections of faces are common faces, geometrically. -/
theorem isFace_inter (P : ConvexPolytope n)
    {F G : Set (E n)} (hF : P.IsFace F) (hG : P.IsFace G)
    (hne : (F ∩ G).Nonempty) : P.IsFace (F ∩ G) :=
  ⟨hF.1.inter hG.1, hne⟩

/-- All nonempty faces, represented as geometric subsets. -/
noncomputable def faceSet (P : ConvexPolytope n) : Finset (Set (E n)) :=
  (finite_isFace P).toFinset

@[simp] theorem mem_faceSet (P : ConvexPolytope n) (F : Set (E n)) :
    F ∈ faceSet P ↔ P.IsFace F := by
  classical
  simp [faceSet]

/-- The number of geometric faces of affine dimension `i`. -/
noncomputable def faceNumber (P : ConvexPolytope n) (i : ℕ) : ℕ := by
  classical
  exact ((faceSet P).filter (fun F => faceDim F = i)).card

end LeanEval.Geometry.PlatonicClassification

end
