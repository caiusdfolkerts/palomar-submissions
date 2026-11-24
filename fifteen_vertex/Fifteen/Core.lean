module
public import Fifteen.PaperCoordinates
@[expose] public section
noncomputable section
namespace Papers.Nonrational.Fifteen.Core
open Module Papers.Coordinates Papers.Polytopes
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open QuadInt FifteenData

/-- The nine facet labels run over the omitted ABC vertex and the omitted DEF vertex. -/
def basis : Fin 9 → Fin 4 → Fin 6 :=
  ![![1, 2, 4, 5],
    ![1, 2, 3, 5],
    ![1, 2, 3, 4],
    ![0, 2, 4, 5],
    ![0, 2, 3, 5],
    ![0, 2, 3, 4],
    ![0, 1, 4, 5],
    ![0, 1, 3, 5],
    ![0, 1, 3, 4]]

def columns : Fin 9 → Fin 4 → Fin 5 :=
  ![![0, 1, 2, 3],
    ![0, 1, 2, 3],
    ![0, 1, 2, 3],
    ![1, 0, 2, 3],
    ![1, 0, 2, 3],
    ![1, 0, 2, 3],
    ![1, 0, 2, 3],
    ![0, 1, 2, 3],
    ![0, 1, 2, 4]]

def normal : Fin 9 → Fin 5 → QuadInt :=
  ![![(-4, 3), (4, -4), (10, -7), (-5, 3), (11, -7)],
    ![(2, -1), (-1, 0), (-4, 2), (3, -2), (-8, 5)],
    ![(2, -1), (-1, 0), (-4, 2), (0, 0), (-5, 3)],
    ![(-1, 0), (6, -2), (-1, 2), (2, -1), (-2, 1)],
    ![(0, 0), (-3, 2), (3, -2), (-2, 1), (2, -1)],
    ![(0, 0), (-3, 2), (3, -2), (-3, 2), (3, -2)],
    ![(3, -2), (-6, 4), (-9, 6), (2, -1), (-8, 5)],
    ![(0, 0), (0, 0), (0, 0), (0, 0), (5, -3)],
    ![(0, 0), (0, 0), (0, 0), (5, -3), (0, 0)]]

def minorValue : Fin 9 → QuadInt :=
  ![(-11, 7), (-8, 5), (5, -3), (2, -1), (2, -1), (-3, 2), (-8, 5), (5, -3), (5, -3)]


def label (i : Fin 6) : Fin 15 := i.castLE (by decide)
def value (f : Fin 9) (i : Fin 6) := dot5 (normal f) (vertices (label i))

private theorem incidences : ∀ f i, value f i = (0,0) ↔ ∃ j, basis f j = i := by decide
private theorem signs : ∀ f i, value f i = (0,0) ∨ positiveAt scale lo hi (value f i) := by decide
private theorem minors : ∀ f, det4 (fun i j => vertices (label (basis f i)) (columns f j)) =
    minorValue f := by decide
private theorem positive_minors : ∀ f, positiveAt scale lo hi (minorValue f) = true := by decide

def core : ConvexPolytope 4 := polytopeOfSeparatingSupports (point ∘ label) (by decide)
  support offset (fun f i => support_bound f (label i))
    (fun i j hij => support_separation _ _ (fun h => hij (Fin.ext (congrArg (fun k : Fin 15 => k.val) h))))

theorem core_vertices : core.vertices = Finset.univ.image (point ∘ label) := rfl

def coeff (f : Fin 9) (j : Fin 5) := eval (normal f j)
def functional (f : Fin 9) : E 4 →L[ℝ] ℝ :=
  (coeff f 0 + coeff f 1) • coordinate 0 + (coeff f 0 + coeff f 2) • coordinate 1 +
    (coeff f 3 - coeff f 0) • coordinate 2 + coeff f 4 • coordinate 3

private theorem evaluation (f i) :
    functional f (point (label i)) = eval (value f i) / chartValue (label i) - coeff f 0 := by
  rw [value, eval_dot5]
  change _ = (∑ j : Fin 5, coeff f j * homogeneous (label i) j) / _ - _
  simp only [functional, add_apply, smul_apply, coordinate_apply, smul_eq_mul, point_apply,
    Fin.sum_univ_succ]
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    show (2 : Fin 3).succ = (3 : Fin 4) from rfl,
    show (2 : Fin 4).succ = (3 : Fin 5) from rfl,
    show (3 : Fin 4).succ = (4 : Fin 5) from rfl]
  have hc := ne_of_gt (chartValue_pos (label i))
  field_simp
  linear_combination coeff f 0 * chart_identity (label i)

private theorem lower (f i) : -coeff f 0 ≤ functional f (point (label i)) := by
  rw [evaluation]
  rcases signs f i with h | h
  · simp [h]
  · linarith [div_pos (eval_pos_of_certificate _ h) (chartValue_pos (label i))]

private theorem equality (f i) :
    functional f (point (label i)) = -coeff f 0 ↔ ∃ j, basis f j = i := by
  rw [← incidences, evaluation]
  rcases signs f i with h | h
  · simp [h]
  · have hpos := div_pos (eval_pos_of_certificate _ h) (chartValue_pos (label i))
    constructor
    · intro he
      linarith
    · intro hz
      rw [hz] at hpos
      simp at hpos

def facet (f : Fin 9) := minimumFace core (functional f) (-coeff f 0)

theorem facet_isFace (f : Fin 9) : core.IsFace (facet f) := by
  apply minimumFace_isFace
  · intro v hv
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp (core_vertices ▸ hv)
    exact lower f i
  · let i := basis f 0
    exact ⟨point (label i),Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,
      (equality f i).mpr ⟨0,rfl⟩⟩

theorem facet_hull (f : Fin 9) :
    facet f = convexHull ℝ (point '' Set.range (label ∘ basis f)) := by
  rw [face_eq_hull_vertices core (facet_isFace f)]
  congr 1
  ext w
  simp only [Finset.mem_coe, Finset.mem_filter, core_vertices, Finset.mem_image,
    Finset.mem_univ, true_and, Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨⟨i,rfl⟩,hi⟩
    obtain ⟨j,hj⟩ := (equality f i).mp hi.2
    exact ⟨label i,⟨j,congrArg label hj⟩,rfl⟩
  · rintro ⟨_,⟨j,rfl⟩,rfl⟩
    have hm : point (label (basis f j)) ∈ core.vertices :=
      Finset.mem_image.mpr ⟨basis f j,Finset.mem_univ _,rfl⟩
    exact ⟨⟨basis f j,rfl⟩,vertex_mem_body core hm,(equality f _).mpr ⟨j,rfl⟩⟩

theorem tetrahedral_facets (f : Fin 9) : faceDim (facet f) = 3 := by
  have hi : LinearIndependent ℝ (homogeneous ∘ label ∘ basis f) := by
    apply independent_of_minor _ (columns f)
    change Matrix.det (Matrix.of (fun i j => eval (vertices (label (basis f i)) (columns f j)))) ≠ 0
    rw [← eval_det4, minors]
    exact ne_of_gt (eval_pos_of_certificate _ (positive_minors f))
  have h := finrank_homogeneousSpan (K := ℝ) (facet_isFace f).2
  rw [facet_hull, homogeneousSpan_convexHull _ (Set.range_nonempty _ |>.image _),
    finrank_homogeneousSpan_points, ← Set.range_comp, finrank_span_eq_card hi,
    Fintype.card_fin] at h
  change Module.finrank ℝ (vectorSpan ℝ (facet f)) = 3
  rw [facet_hull]
  omega

theorem core_fullDim : core.IsFullDim := by
  have hv : point (label 0) ∈ core.vertices :=
    Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  have hproper : facet 0 ⊂ core.toSet := by
    refine ⟨face_subset_toSet core (facet_isFace 0), ?_⟩
    intro h
    have hm := h (vertex_mem_body core hv)
    exact (by decide : ¬ ∃ j, basis 0 j = 0) ((equality 0 0).mp hm.2)
  have h := faceDim_lt_of_ssubset core (facet_isFace 0) (toSet_isFace core) hproper
  rw [tetrahedral_facets] at h
  have hu := Submodule.finrank_le (vectorSpan ℝ core.toSet)
  rw [finrank_euclideanSpace_fin] at hu
  change 3 < finrank ℝ (vectorSpan ℝ core.toSet) at h
  change finrank ℝ (vectorSpan ℝ core.toSet) = 4
  omega

end Papers.Nonrational.Fifteen.Core
