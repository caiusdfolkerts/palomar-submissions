module
public import Fifteen.Projection
public import Fifteen.Reconstruction
public import Fifteen.Perles
public import Fifteen.Core
@[expose] public section
noncomputable section
namespace Papers.Nonrational.Fifteen
open Module FifteenRankData Papers.Polytopes
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

theorem polytope_fullDim : polytope.IsFullDim := by
  let F := reconstructionFace (facetFace 0)
  have hproper : F.val ⊂ polytope.toSet := by
    refine ⟨face_subset_toSet polytope F.property, ?_⟩
    intro h
    have hm := h (subset_convexHull ℝ (polytope.vertices : Set (E 4)) (point_mem_vertices 0))
    exact (by decide : (0 : Fin 15) ∉ faceVertices (facetFace 0))
      ((point_mem_reconstructionFace _ _).mp hm)
  have h := faceDim_lt_of_ssubset polytope F.property (toSet_isFace polytope) hproper
  have hd : faceDim F.val = 3 := facet_face_dimension 0
  have hu := Submodule.finrank_le (vectorSpan ℝ polytope.toSet)
  rw [finrank_euclideanSpace_fin] at hu
  change faceDim F.val < finrank ℝ (vectorSpan ℝ polytope.toSet) at h
  change finrank ℝ (vectorSpan ℝ polytope.toSet) = 4
  omega

theorem sqrt_five_of_realizable (K : Subfield ℝ) (h : RealizableOver polytope K) :
    Real.sqrt 5 ∈ K := by
  obtain ⟨Q, ⟨φ⟩, hK⟩ := h
  let p := fieldPoint φ K hK
  let W := fieldFaceSpan φ K hK
  have inc (f i) : p i ∈ W f ↔ i ∈ faceVertices f := by
    constructor
    · contrapose
      exact fieldPoint_notMem_faceSpan φ K hK f i
    · intro hi
      exact Submodule.subset_span ⟨i, hi, rfl⟩
  have hp (f : Fin 7) : finrank K (W (f.castLE (by decide))) = 3 := by
    have h := fieldFaceSpan_rank φ K hK (planeFace f)
    rw [plane_face_dimension] at h
    fin_cases f <;> exact h
  have hf (f : Fin 3) : finrank K (W ⟨7 + f.val, by omega⟩) = 4 := by
    let g : Fin 5 := f.castLE (by decide)
    have h := fieldFaceSpan_rank φ K hK (facetFace g)
    rw [facet_face_dimension] at h
    fin_cases f <;> exact h
  obtain ⟨s, hs⟩ := golden_root_of_faces p W inc (fieldPoint_triples φ K hK) hp hf
  have he : (2 * (s : ℝ) + 1)^2 = 5 := by
    have hreal : (s : ℝ)^2 + (s : ℝ) - 1 = 0 := by exact_mod_cast hs
    linear_combination 4 * hreal
  have hm : 2 * (s : ℝ) + 1 ∈ K := K.add_mem (K.mul_mem (by norm_num) s.property) K.one_mem
  have hsqrt : (Real.sqrt 5)^2 = 5 := Real.sq_sqrt (by norm_num)
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (he.trans hsqrt.symm) with h | h
  · rwa [h] at hm
  · simpa [h] using K.neg_mem hm

theorem realizable_iff_sqrt_five (K : Subfield ℝ) :
    RealizableOver polytope K ↔ Real.sqrt 5 ∈ K :=
  ⟨sqrt_five_of_realizable K, realizable_of_sqrt_five K⟩

/-- Theorem 1 of A nonrational four-polytope with fifteen vertices. -/
theorem theoremOne : ∃ P : ConvexPolytope 4, P.IsFullDim ∧ P.vertices.card = 15 ∧
    ∀ K : Subfield ℝ, RealizableOver P K ↔ Real.sqrt 5 ∈ K :=
  ⟨polytope, polytope_fullDim, polytope_card, realizable_iff_sqrt_five⟩
theorem sqrt_five_notMem_rationalSubfield :
    Real.sqrt 5 ∉ rationalSubfield := by
  have hi : Irrational (Real.sqrt 5) := by
    simpa using Nat.Prime.irrational_sqrt (show Nat.Prime 5 by decide)
  exact hi

theorem not_rationallyRealizable : ¬RationallyRealizable polytope := by
  intro h
  apply sqrt_five_notMem_rationalSubfield
  exact (realizable_iff_sqrt_five rationalSubfield).mp
    ((rationallyRealizable_iff_realizableOver polytope).mp h)

theorem exists_fifteen_vertex_nonrational_polytope :
    ∃ P : ConvexPolytope 4,
      P.IsFullDim ∧ P.vertices.card = 15 ∧ ¬RationallyRealizable P :=
  ⟨polytope, polytope_fullDim, polytope_card, not_rationallyRealizable⟩

end Papers.Nonrational.Fifteen
