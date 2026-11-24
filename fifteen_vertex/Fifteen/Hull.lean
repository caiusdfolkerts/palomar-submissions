module
public import Fifteen.Certificate

/-! # Four-dimensional affine chart and convex hull -/
@[expose] public section

/-!
# The actual fifteen-vertex convex hull

Coordinates are obtained by dehomogenizing the supplied exact construction in
its positive chart. Supporting forms are evaluated on real points, and the
convex-polytope structure is derived from their strict separation properties.
-/

noncomputable section

open Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes

namespace Papers.Nonrational.Fifteen

def homogeneous (v : Fin 15) (i : Fin 5) : ℝ := QuadInt.eval (FifteenData.vertices v i)
def chartValue (v : Fin 15) : ℝ := QuadInt.eval (FifteenData.chartValues v)
def formCoordinate (f : Fin 15) (i : Fin 5) : ℝ := QuadInt.eval (FifteenData.forms f i)
def supportValue (f : Fin 15) (v : Fin 15) : ℝ := QuadInt.eval (FifteenData.values f v)

theorem eval_pos_of_certificate (x : QuadInt)
    (h : QuadInt.positiveAt FifteenData.scale FifteenData.lo FifteenData.hi x = true) :
    0 < QuadInt.eval x :=
  QuadInt.eval_pos_of_positiveAt FifteenData.scale FifteenData.lo FifteenData.hi
    (by norm_num [FifteenData.scale]) FifteenData.interval.1 FifteenData.interval.2 x h

theorem chartValue_pos (v : Fin 15) : 0 < chartValue v :=
  eval_pos_of_certificate _ (FifteenData.chart_positive v)

theorem supportValue_nonneg (f : Fin 15) (v : Fin 15) : 0 ≤ supportValue f v := by
  rcases FifteenData.values_nonnegative f v with h | h
  · simp [supportValue, h]
  · exact (eval_pos_of_certificate _ h).le

theorem chart_identity (v : Fin 15) :
    chartValue v = homogeneous v 0 - homogeneous v 1 - homogeneous v 2 + homogeneous v 3 := by
  rw [chartValue, ← FifteenData.chart_values, QuadInt.eval_dot5]
  norm_num [FifteenData.chart, QuadInt.eval, homogeneous, Fin.sum_univ_succ]
  ring

theorem support_identity (f : Fin 15) (v : Fin 15) :
    supportValue f v = ∑ i : Fin 5, formCoordinate f i * homogeneous v i := by
  rw [supportValue, ← FifteenData.dot_values, QuadInt.eval_dot5]
  rfl

def point (v : Fin 15) : E 4 :=
  WithLp.toLp 2 (fun i : Fin 4 => homogeneous v i.succ / chartValue v)

@[simp] theorem point_apply (v : Fin 15) (i : Fin 4) :
    point v i = homogeneous v i.succ / chartValue v := rfl

def coordinate (i : Fin 4) : E 4 →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun x => x i
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

@[simp] theorem coordinate_apply (i : Fin 4) (x : E 4) : coordinate i x = x i := rfl

def support (f : Fin 15) : E 4 →L[ℝ] ℝ :=
  (formCoordinate f 0 + formCoordinate f 1) • coordinate 0 +
  (formCoordinate f 0 + formCoordinate f 2) • coordinate 1 +
  (formCoordinate f 3 - formCoordinate f 0) • coordinate 2 +
  formCoordinate f 4 • coordinate 3

def offset (f : Fin 15) : ℝ := -formCoordinate f 0

@[simp] theorem support_apply (f : Fin 15) (x : E 4) :
    support f x = (formCoordinate f 0 + formCoordinate f 1) * x 0 +
      (formCoordinate f 0 + formCoordinate f 2) * x 1 +
      (formCoordinate f 3 - formCoordinate f 0) * x 2 + formCoordinate f 4 * x 3 := rfl

theorem support_at_point (f : Fin 15) (v : Fin 15) :
    support f (point v) = supportValue f v / chartValue v + offset f := by
  rw [support_apply, support_identity]
  simp only [point_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  simp only [Fin.sum_univ_succ]
  dsimp [offset]
  have hc := ne_of_gt (chartValue_pos v)
  field_simp
  linear_combination formCoordinate f 0 * chart_identity v

theorem support_bound (f : Fin 15) (v : Fin 15) : offset f ≤ support f (point v) := by
  rw [support_at_point]
  exact le_add_of_nonneg_left (div_nonneg (supportValue_nonneg f v) (chartValue_pos v).le)

theorem support_incidence (f : Fin 15) (v : Fin 15) :
    support f (point v) = offset f ↔ FifteenData.values f v = (0, 0) := by
  constructor
  · intro h
    rcases FifteenData.values_nonnegative f v with hz | hp
    · exact hz
    · have hp' : 0 < supportValue f v := eval_pos_of_certificate _ hp
      have hdiv := div_pos hp' (chartValue_pos v)
      rw [support_at_point] at h
      linarith
  · intro h
    rw [support_at_point]
    simp [supportValue, h]

theorem support_separation (v w : Fin 15) (hvw : v ≠ w) :
    ∃ f, support f (point v) = offset f ∧ offset f < support f (point w) := by
  obtain ⟨f, hfv, hfw⟩ := FifteenData.distinguish_vertices v w hvw
  refine ⟨f, (support_incidence f v).mpr hfv, ?_⟩
  rw [support_at_point]
  exact lt_add_of_pos_left _ (div_pos (eval_pos_of_certificate _ hfw) (chartValue_pos w))

theorem point_injective : Function.Injective point :=
  separatingSupports_injective point support offset support_separation

def polytope : ConvexPolytope 4 :=
  polytopeOfSeparatingSupports point (by decide) support offset support_bound support_separation

@[simp] theorem polytope_vertices : polytope.vertices = Finset.univ.image point := rfl

theorem polytope_card : polytope.vertices.card = 15 :=
  polytopeOfSeparatingSupports_card point (by decide) support offset support_bound support_separation

theorem point_mem_vertices (v : Fin 15) : point v ∈ polytope.vertices := by
  classical
  rw [polytope_vertices]
  exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩

def face (f : Fin 15) : Set (E 4) := minimumFace polytope (support f) (offset f)

theorem point_mem_face_iff (f : Fin 15) (v : Fin 15) :
    point v ∈ face f ↔ FifteenData.values f v = (0, 0) := by
  change (point v ∈ polytope.toSet ∧ support f (point v) = offset f) ↔ _
  have hv : point v ∈ polytope.toSet :=
    subset_convexHull ℝ _ (point_mem_vertices v)
  rw [support_incidence, and_iff_right hv]

theorem face_isFace (f : Fin 15)
    (hne : ∃ v, FifteenData.values f v = (0, 0)) : polytope.IsFace (face f) := by
  apply minimumFace_isFace
  · intro x hx
    rw [polytope_vertices] at hx
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
    exact support_bound f v
  · obtain ⟨v, hv⟩ := hne
    exact ⟨point v, point_mem_vertices v, (support_incidence f v).mpr hv⟩

theorem eval_mem_subfield (K : Subfield ℝ) (hphi : phi ∈ K) (x : QuadInt) :
    QuadInt.eval x ∈ K :=
  K.add_mem (K.intCast_mem x.1) (K.mul_mem (K.intCast_mem x.2) hphi)

theorem point_coordinates_in (K : Subfield ℝ) (hphi : phi ∈ K)
    (v : Fin 15) (i : Fin 4) : point v i ∈ K := by
  exact K.div_mem (eval_mem_subfield K hphi _) (eval_mem_subfield K hphi _)

theorem coordinates_in_of_sqrt_five (K : Subfield ℝ) (hsqrt : Real.sqrt 5 ∈ K) :
    CoordinatesIn K polytope := by
  have hphi : phi ∈ K := K.div_mem (K.add_mem K.one_mem hsqrt) (by norm_num)
  intro x hx i
  rw [polytope_vertices] at hx
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
  exact point_coordinates_in K hphi v i

/-- The construction side of Theorem 1, with the actual convex-polytope
definition and its ordinary face poset.  The converse is a separate theorem. -/
theorem realizable_of_sqrt_five (K : Subfield ℝ) (hsqrt : Real.sqrt 5 ∈ K) :
    RealizableOver polytope K :=
  ⟨polytope, CombinatoriallyEquivalent.refl polytope, coordinates_in_of_sqrt_five K hsqrt⟩

end Papers.Nonrational.Fifteen

end
end
