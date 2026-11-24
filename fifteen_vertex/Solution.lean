module
public import Fifteen
@[expose] public section
noncomputable section
namespace Papers.Nonrational.Fifteen
open scoped Classical
open Papers.Polytopes LeanEval.Geometry.PlatonicClassification
/-- Homogeneous representatives, in the vertex order of the manuscript. -/
def manuscriptRay : Fin 15 → Fin 5 → ℝ :=
  let t : ℝ := (1 + Real.sqrt 5) / 2 - 1
  ![![1,1,1,0,0], ![1,1+t,1,0,0], ![0,1,1,1,1],
    ![t,1,1,0,0], ![t,1+t,1,0,t], ![1,1,0,t,0],
    ![0,0,0,3+t,1], ![0,0,0,1,1], ![1,0,0,1,1],
    ![1,0,0,4*(1+t+1/3),1/3], ![1,0,0,4*(1+t+2/3),2/3],
    ![0,1,0,0,2-2*(2-t)/15], ![0,1,0,0,2-(2-t)/15],
    ![0,0,1,2+t/3,0], ![0,0,1,2+2*t/3,0]]

/-- The paper's fifteen rays define a full-dimensional convex four-polytope.
Its combinatorial type is realizable over precisely the real subfields
containing the square root of five. -/
theorem explicitFifteenVertexField :
    ∃ (P : ConvexPolytope 4) (p : Fin 15 → E 4),
      P.vertices = Finset.univ.image p ∧ P.IsFullDim ∧ P.vertices.card = 15 ∧
      (∀ i, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a • sectionCoordinates (p i) = b • manuscriptRay i) ∧
      ∀ K : Subfield ℝ, RealizableOver P K ↔ Real.sqrt 5 ∈ K := by
  refine ⟨polytope, point, polytope_vertices, polytope_fullDim, polytope_card, ?_, realizable_iff_sqrt_five⟩
  intro i
  exact ⟨_, _, chartValue_pos i, Nat.cast_pos.mpr (denominator_pos i), section_coordinates_of_point i⟩
end Papers.Nonrational.Fifteen
