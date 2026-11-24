module
public import Fifteen.Faces

/-! # Transport through a face-poset isomorphism -/
@[expose] public section

/-!
# Coordinates in an arbitrary realization

Every rank and exclusion below is derived from an ordinary face-poset
isomorphism. No projective incidence data are added to that isomorphism.
-/

noncomputable section
namespace Papers.Nonrational.Fifteen
open Set Module
open Papers.Coordinates Papers.Polytopes
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open FifteenRankData

def labelledVertex (v : Fin 15) : VertexType polytope := ⟨point v, point_mem_vertices v⟩

theorem labelledVertex_bijective : Function.Bijective labelledVertex := by
  constructor
  · intro v w h
    exact point_injective (congrArg Subtype.val h)
  · rintro ⟨x, hx⟩
    rw [polytope_vertices] at hx
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨v, rfl⟩

def labelEquiv : Fin 15 ≃ VertexType polytope := Equiv.ofBijective labelledVertex labelledVertex_bijective

variable {Q : ConvexPolytope 4} (φ : FaceType polytope ≃o FaceType Q)

def realizationVertex (v : Fin 15) : VertexType Q := imageVertex φ (labelledVertex v)
def realizationPoint (v : Fin 15) : E 4 := (realizationVertex φ v).val

theorem realizationVertex_bijective : Function.Bijective (realizationVertex φ) :=
  (vertexEquivOfFaceOrder φ).bijective.comp labelledVertex_bijective

theorem realizationPoint_injective : Function.Injective (realizationPoint φ) := by
  intro v w h
  exact (realizationVertex_bijective φ).1 (Subtype.ext h)

theorem realizationPoint_mem_face (f : Fin 12) (v : Fin 15) :
    realizationPoint φ v ∈ (φ (reconstructionFace f)).val ↔ v ∈ faceVertices f := by
  exact (imageVertex_mem_iff φ (labelledVertex v) (reconstructionFace f)).trans
    (point_mem_reconstructionFace f v)

theorem realizationFace_eq_hull (f : Fin 12) :
    (φ (reconstructionFace f)).val =
      convexHull ℝ (realizationPoint φ '' (faceVertices f : Set (Fin 15))) := by
  classical
  rw [face_eq_hull_vertices Q (φ (reconstructionFace f)).property]
  congr 1
  ext x
  simp only [Finset.mem_coe, Finset.mem_filter, Set.mem_image]
  constructor
  · rintro ⟨hx, hxf⟩
    obtain ⟨v, hv⟩ := (realizationVertex_bijective φ).2 ⟨x, hx⟩
    have hvx : realizationPoint φ v = x := congrArg Subtype.val hv
    refine ⟨v, ?_, hvx⟩
    exact (realizationPoint_mem_face φ f v).mp (hvx.symm ▸ hxf)
  · rintro ⟨v, hv, rfl⟩
    exact ⟨(realizationVertex φ v).property, (realizationPoint_mem_face φ f v).mpr hv⟩

def realizationHomogeneous (v : Fin 15) : Fin 5 → ℝ :=
  chartEquiv (homogenize (K := ℝ) (realizationPoint φ v))

theorem realization_homogeneous_span (f : Fin 12) :
    Submodule.span ℝ (realizationHomogeneous φ '' (faceVertices f : Set (Fin 15))) =
      Submodule.map chartEquiv.toLinearMap
        (homogeneousSpan (K := ℝ) (φ (reconstructionFace f)).val) := by
  rw [realizationFace_eq_hull,
    homogeneousSpan_convexHull _ (Set.Nonempty.image _ (face_nonempty f)),
    homogeneousSpan, Submodule.map_span]
  simp only [Set.image_image, LinearEquiv.coe_coe, realizationHomogeneous]
  rfl

theorem realization_homogeneous_rank (f : Fin 12) :
    finrank ℝ (Submodule.span ℝ
      (realizationHomogeneous φ '' (faceVertices f : Set (Fin 15)))) =
      faceDim (reconstructionFace f).val + 1 := by
  rw [realization_homogeneous_span, chartEquiv.finrank_map_eq,
    finrank_homogeneousSpan (φ (reconstructionFace f)).property.2]
  change faceDim (φ (reconstructionFace f)).val + 1 = _
  rw [faceOrderIso_dimension]

theorem realization_homogeneous_triples (i j k : Fin 15)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    LinearIndependent ℝ ![realizationHomogeneous φ i,
      realizationHomogeneous φ j, realizationHomogeneous φ k] := by
  have hnc := vertices_not_collinear Q
    (realizationVertex φ i).property (realizationVertex φ j).property
    (realizationVertex φ k).property
    (fun h => hij (realizationPoint_injective φ h))
    (fun h => hik (realizationPoint_injective φ h))
    (fun h => hjk (realizationPoint_injective φ h))
  have ha := affineIndependent_iff_not_collinear_set.mpr hnc
  have hi := (linearIndependent_homogenize_iff _).mpr ha
  have hm := hi.map' chartEquiv.toLinearMap (LinearMap.ker_eq_bot.mpr chartEquiv.injective)
  convert hm using 1
  ext a
  fin_cases a <;> rfl

theorem realization_homogeneous_notMem_span (f : Fin 12) (v : Fin 15)
    (hv : v ∉ faceVertices f) :
    realizationHomogeneous φ v ∉ Submodule.span ℝ
      (realizationHomogeneous φ '' (faceVertices f : Set (Fin 15))) := by
  intro h
  rw [realization_homogeneous_span] at h
  obtain ⟨z, hz, heq⟩ := h
  have hzeq : z = homogenize (K := ℝ) (realizationPoint φ v) := chartEquiv.injective heq
  rw [hzeq] at hz
  have haf := (homogenize_mem_span_iff (φ (reconstructionFace f)).property.2 _).mp hz
  exact vertex_notMem_affineSpan_face Q (φ (reconstructionFace f)).property
    (realizationVertex φ v).property
    (fun hm => hv ((realizationPoint_mem_face φ f v).mp hm)) haf

variable (K : Subfield ℝ) (hK : CoordinatesIn K Q)

include hK in
theorem realizationHomogeneous_mem (v : Fin 15) (i : Fin 5) :
    realizationHomogeneous φ v i ∈ K := by
  have hm (j : Fin 4) : realizationPoint φ v j ∈ K :=
    hK _ (realizationVertex φ v).property j
  fin_cases i
  · exact K.sub_mem (K.add_mem (K.add_mem K.one_mem (hm 0)) (hm 1)) (hm 2)
  all_goals exact hm _

def fieldPoint (v : Fin 15) (i : Fin 5) : K :=
  ⟨realizationHomogeneous φ v i, realizationHomogeneous_mem φ K hK v i⟩

@[simp] theorem coordinateMap_fieldPoint (v : Fin 15) :
    coordinateMap K.subtype 5 (fieldPoint φ K hK v) = realizationHomogeneous φ v := rfl

def fieldFaceSpan (f : Fin 12) : Submodule K (Fin 5 → K) :=
  Submodule.span K (fieldPoint φ K hK '' (faceVertices f : Set (Fin 15)))

theorem fieldFaceSpan_rank (f : Fin 12) :
    finrank K (fieldFaceSpan φ K hK f) = faceDim (reconstructionFace f).val + 1 := by
  rw [fieldFaceSpan, ← finrank_span_coordinateMap K.subtype,
    Set.image_image]
  simp_rw [coordinateMap_fieldPoint]
  exact realization_homogeneous_rank φ f

theorem fieldPoint_triples (i j k : Fin 15) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    LinearIndependent K ![fieldPoint φ K hK i, fieldPoint φ K hK j, fieldPoint φ K hK k] := by
  apply linearIndependent_of_coordinate_map K.subtype
  convert realization_homogeneous_triples φ i j k hij hik hjk using 1
  ext a b
  fin_cases a <;> rfl

theorem fieldPoint_notMem_faceSpan (f : Fin 12) (v : Fin 15)
    (hv : v ∉ faceVertices f) : fieldPoint φ K hK v ∉ fieldFaceSpan φ K hK f := by
  intro h
  have hm := coordinateMap_mem_span K.subtype h
  simp only [Set.image_image, coordinateMap_fieldPoint] at hm
  exact realization_homogeneous_notMem_span φ f v hv hm

end Papers.Nonrational.Fifteen

end
end
