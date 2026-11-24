module
public import Fifteen.Chart
public import Fifteen.FaceCertificate
public import Fifteen.RankLemma

/-! # The exposed faces of the fifteen-vertex hull -/
@[expose] public section

/-! Certified ranks and dimensions of the faces used in reconstruction. -/

noncomputable section
namespace Papers.Nonrational.Fifteen
open Set Module
open Papers.Coordinates Papers.Polytopes
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open FifteenRankData

theorem plane_raw_rank (f : Fin 7) :
    finrank ℝ (Submodule.span ℝ (homogeneous '' (faceVertices (planeFace f) : Set (Fin 15)))) = 3 := by
  apply finrank_span_of_certificate homogeneous (faceVertices (planeFace f))
    (planeBasis f) (planeColumns f) (plane_basis_mem f)
    (QuadInt.eval (planeDelta f))
    (ne_of_gt (eval_pos_of_certificate _ (plane_delta_positive f)))
    (a := fun v i => QuadInt.eval (planeCoefficients f v i))
  · change Matrix.det (Matrix.of (fun i j =>
      QuadInt.eval (FifteenData.vertices (planeBasis f i) (planeColumns f j)))) = _
    rw [← QuadInt.eval_det3, plane_minor]
  · intro v hv
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    change QuadInt.eval (planeDelta f) * QuadInt.eval (FifteenData.vertices v j) = _
    rw [← QuadInt.eval_mul, plane_spanning f v hv j, QuadInt.eval_combine3]
    rfl

theorem facet_raw_rank (f : Fin 5) :
    finrank ℝ (Submodule.span ℝ (homogeneous '' (faceVertices (facetFace f) : Set (Fin 15)))) = 4 := by
  apply finrank_span_of_certificate homogeneous (faceVertices (facetFace f))
    (facetBasis f) (facetColumns f) (facet_basis_mem f)
    (QuadInt.eval (facetDelta f))
    (ne_of_gt (eval_pos_of_certificate _ (facet_delta_positive f)))
    (a := fun v i => QuadInt.eval (facetCoefficients f v i))
  · change Matrix.det (Matrix.of (fun i j =>
      QuadInt.eval (FifteenData.vertices (facetBasis f i) (facetColumns f j)))) = _
    rw [← QuadInt.eval_det4, facet_minor]
  · intro v hv
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    change QuadInt.eval (facetDelta f) * QuadInt.eval (FifteenData.vertices v j) = _
    rw [← QuadInt.eval_mul, facet_spanning f v hv j, QuadInt.eval_combine4]
    rfl

def faceCoefficient (f : Fin 12) (i : Fin 5) : ℝ := QuadInt.eval (faceForms f i)
def faceValue (f : Fin 12) (v : Fin 15) : ℝ := QuadInt.eval (faceValues f v)
def faceOffset (f : Fin 12) : ℝ := -faceCoefficient f 0

def faceSupport (f : Fin 12) : E 4 →L[ℝ] ℝ :=
  (faceCoefficient f 0 + faceCoefficient f 1) • coordinate 0 +
  (faceCoefficient f 0 + faceCoefficient f 2) • coordinate 1 +
  (faceCoefficient f 3 - faceCoefficient f 0) • coordinate 2 +
  faceCoefficient f 4 • coordinate 3

theorem faceValue_nonneg (f : Fin 12) (v : Fin 15) : 0 ≤ faceValue f v := by
  rcases face_nonnegative f v with h | h
  · simp [faceValue, h]
  · exact (eval_pos_of_certificate _ h).le

theorem faceSupport_at_point (f : Fin 12) (v : Fin 15) :
    faceSupport f (point v) = faceValue f v / chartValue v + faceOffset f := by
  have hval : faceValue f v = ∑ i : Fin 5, faceCoefficient f i * homogeneous v i := by
    rw [faceValue, ← face_dot, QuadInt.eval_dot5]
    rfl
  rw [hval]
  simp only [faceSupport, add_apply,
    smul_apply, coordinate_apply, smul_eq_mul, point_apply,
    Fin.sum_univ_succ]
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    show (2 : Fin 3).succ = (3 : Fin 4) from rfl,
    show (2 : Fin 4).succ = (3 : Fin 5) from rfl,
    show (3 : Fin 4).succ = (4 : Fin 5) from rfl]
  dsimp only [faceOffset]
  have hc := ne_of_gt (chartValue_pos v)
  field_simp
  linear_combination faceCoefficient f 0 * chart_identity v

theorem faceSupport_bound (f : Fin 12) (v : Fin 15) :
    faceOffset f ≤ faceSupport f (point v) := by
  rw [faceSupport_at_point]
  exact le_add_of_nonneg_left (div_nonneg (faceValue_nonneg f v) (chartValue_pos v).le)

theorem faceSupport_incidence (f : Fin 12) (v : Fin 15) :
    faceSupport f (point v) = faceOffset f ↔ v ∈ faceVertices f := by
  rw [← face_membership]
  constructor
  · intro h
    rcases face_nonnegative f v with hz | hp
    · exact hz
    · have hpos : 0 < faceValue f v := eval_pos_of_certificate _ hp
      have hdiv := div_pos hpos (chartValue_pos v)
      rw [faceSupport_at_point] at h
      linarith
  · intro h
    rw [faceSupport_at_point]
    simp [faceValue, h]

def reconstructionFaceSet (f : Fin 12) : Set (E 4) :=
  minimumFace polytope (faceSupport f) (faceOffset f)

theorem reconstructionFaceSet_isFace (f : Fin 12) :
    polytope.IsFace (reconstructionFaceSet f) := by
  apply minimumFace_isFace
  · intro x hx
    rw [polytope_vertices] at hx
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
    exact faceSupport_bound f v
  · obtain ⟨v, hv⟩ := face_nonempty f
    exact ⟨point v, point_mem_vertices v, (faceSupport_incidence f v).mpr hv⟩

def reconstructionFace (f : Fin 12) : FaceType polytope :=
  ⟨reconstructionFaceSet f, reconstructionFaceSet_isFace f⟩

theorem point_mem_reconstructionFace (f : Fin 12) (v : Fin 15) :
    point v ∈ (reconstructionFace f).val ↔ v ∈ faceVertices f := by
  change (point v ∈ polytope.toSet ∧ faceSupport f (point v) = faceOffset f) ↔ _
  rw [faceSupport_incidence, and_iff_right (vertex_mem_body polytope (point_mem_vertices v))]

theorem reconstructionFace_eq_hull (f : Fin 12) :
    (reconstructionFace f).val = convexHull ℝ (point '' (faceVertices f : Set (Fin 15))) := by
  classical
  rw [face_eq_hull_vertices polytope (reconstructionFace f).property]
  congr 1
  ext x
  simp only [Finset.mem_coe, Finset.mem_filter, polytope_vertices, Finset.mem_image,
    Finset.mem_univ, true_and, Set.mem_image]
  constructor
  · rintro ⟨⟨v, rfl⟩, hv⟩
    exact ⟨v, (point_mem_reconstructionFace f v).mp hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨⟨v, rfl⟩, (point_mem_reconstructionFace f v).mpr hv⟩

theorem face_homogeneous_rank (f : Fin 12) :
    finrank ℝ (homogeneousSpan (K := ℝ) (reconstructionFace f).val) =
      finrank ℝ (Submodule.span ℝ (homogeneous '' (faceVertices f : Set (Fin 15)))) := by
  rw [reconstructionFace_eq_hull,
    homogeneousSpan_convexHull _ (Set.Nonempty.image _ (face_nonempty f)),
    finrank_homogeneousSpan_points]

theorem plane_face_dimension (f : Fin 7) : faceDim (reconstructionFace (planeFace f)).val = 2 := by
  have h := face_homogeneous_rank (planeFace f)
  rw [plane_raw_rank, finrank_homogeneousSpan (reconstructionFace (planeFace f)).property.2] at h
  change finrank ℝ (vectorSpan ℝ (reconstructionFace (planeFace f)).val) = 2
  omega

theorem facet_face_dimension (f : Fin 5) : faceDim (reconstructionFace (facetFace f)).val = 3 := by
  have h := face_homogeneous_rank (facetFace f)
  rw [facet_raw_rank, finrank_homogeneousSpan (reconstructionFace (facetFace f)).property.2] at h
  change finrank ℝ (vectorSpan ℝ (reconstructionFace (facetFace f)).val) = 3
  omega

end Papers.Nonrational.Fifteen

end
end
