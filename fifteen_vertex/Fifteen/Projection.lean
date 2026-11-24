module
public import Fifteen.PaperCoordinates
@[expose] public section
noncomputable section
namespace Papers.Nonrational.Fifteen
open Set FifteenRankData Papers.Polytopes
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

/-- Recover (x,y,z,u,v) on the section x+y+z+u+v=1. -/
def sectionCoordinates (w : E 4) : Fin 5 → ℝ :=
  ![1 - w 0 - w 1 - w 2 - w 3,w 0,w 1,w 2,w 3]

theorem section_coordinates_of_point (v : Fin 15) :
    chartValue v • sectionCoordinates (point v) = (denominator v : ℝ) • paperRay v := by
  have h (j : Fin 5) := congrFun (construction_uses_paper_rays v) j
  have hc := (chartValue_pos v).ne'
  funext j
  fin_cases j
  · change chartValue v * (1 - homogeneous v 1 / chartValue v -
        homogeneous v 2 / chartValue v - homogeneous v 3 / chartValue v -
        homogeneous v 4 / chartValue v) = (denominator v : ℝ) * paperRay v 0
    field_simp
    have h₀ : homogeneous v 0 = (denominator v : ℝ) *
        (paperRay v 0 + 2 * paperRay v 1 + 2 * paperRay v 2 + paperRay v 4) := h 0
    have h₁ : homogeneous v 1 = (denominator v : ℝ) * paperRay v 1 := h 1
    have h₂ : homogeneous v 2 = (denominator v : ℝ) * paperRay v 2 := h 2
    have h₄ : homogeneous v 4 = (denominator v : ℝ) * paperRay v 4 := h 4
    linear_combination chart_identity v + h₀ - 2 * h₁ - 2 * h₂ - h₄
  all_goals
    change chartValue v * (_ / chartValue v) = _ * _
    rw [mul_div_cancel₀ _ hc]
  · exact h 1
  · exact h 2
  · exact h 3
  · exact h 4

theorem coordinate_facets (i : Fin 5) :
    (reconstructionFace (facetFace i)).val =
      {w ∈ polytope.toSet | sectionCoordinates w i = 0} := by
  ext w
  change (_ ∧ faceSupport (facetFace i) w = faceOffset (facetFace i)) ↔ (_ ∧ _)
  apply and_congr_right
  intro _
  fin_cases i <;> norm_num [faceSupport, faceOffset, faceCoefficient, faceForms, facetFace,
    coordinate_apply, QuadInt.eval, sectionCoordinates]
  constructor <;> intro h <;> linarith

def kernelFace : Set (E 4) :=
  ((reconstructionFace 7).val ∩ (reconstructionFace 8).val) ∩ (reconstructionFace 9).val

theorem point_mem_kernelFace (v : Fin 15) : point v ∈ kernelFace ↔ v = 6 ∨ v = 7 := by
  change ((_ ∧ _) ∧ _) ↔ _
  simp only [point_mem_reconstructionFace]
  revert v
  decide

theorem kernelFace_isFace : polytope.IsFace kernelFace := by
  have hu := (point_mem_kernelFace 6).mpr (Or.inl rfl)
  exact isFace_inter polytope
    (isFace_inter polytope (reconstructionFace 7).property (reconstructionFace 8).property
      ⟨point 6,hu.1⟩) (reconstructionFace 9).property ⟨point 6,hu⟩

theorem kernelFace_eq_segment : kernelFace = segment ℝ (point 6) (point 7) := by
  rw [face_eq_hull_vertices polytope kernelFace_isFace, ← convexHull_pair]
  congr 1
  ext w
  simp only [Finset.mem_coe, Finset.mem_filter, polytope_vertices,
    Finset.mem_image, Finset.mem_univ, true_and, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨i,rfl⟩,hi⟩
    rcases (point_mem_kernelFace i).mp hi with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨⟨6,rfl⟩,(point_mem_kernelFace 6).mpr (Or.inl rfl)⟩
    · exact ⟨⟨7,rfl⟩,(point_mem_kernelFace 7).mpr (Or.inr rfl)⟩

theorem kernelFace_dimension : faceDim kernelFace = 1 := by
  rw [faceDim, kernelFace_eq_segment, vectorSpan_segment]
  apply finrank_span_singleton
  exact sub_ne_zero.mpr (fun h => (by decide : (7 : Fin 15) ≠ 6) (point_injective h))

/-- Proposition 2, with the specified construction as witness. The order of
the seven polygons and the five coordinate facets is documented in faceVertices. -/
theorem propositionTwo :
    polytope.vertices.card = 15 ∧
    (∀ K : Subfield ℝ, Real.sqrt 5 ∈ K → CoordinatesIn K polytope) ∧
    (∀ f, (reconstructionFace f).val = convexHull ℝ (point '' (faceVertices f : Set (Fin 15)))) ∧
    (∀ f, faceDim (reconstructionFace (planeFace f)).val = 2) ∧
    (∀ f, faceDim (reconstructionFace (facetFace f)).val = 3) ∧
    (∀ i, (reconstructionFace (facetFace i)).val =
      {w ∈ polytope.toSet | sectionCoordinates w i = 0}) ∧
    kernelFace = segment ℝ (point 6) (point 7) :=
  ⟨polytope_card, coordinates_in_of_sqrt_five, reconstructionFace_eq_hull,
    plane_face_dimension, facet_face_dimension, coordinate_facets, kernelFace_eq_segment⟩
end Papers.Nonrational.Fifteen
