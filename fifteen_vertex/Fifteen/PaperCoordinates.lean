module
public import Fifteen.Construction
@[expose] public section
noncomputable section
namespace Papers.Nonrational.Fifteen
open FifteenRankData
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

def t : ℝ := phi - 1

theorem t_eq : t = (Real.sqrt 5 - 1) / 2 := by unfold t phi; ring
theorem t_pos : 0 < t := sub_pos.mpr phi_basic_bounds.1
theorem t_quadratic : t ^ 2 + t = 1 := by unfold t; linear_combination phi_sq

/-- Homogeneous coordinates (x,y,z,u,v) of the paper. The face certificate
uses the integral shear (x+2y+2z+v,y,z,u,v) and clears positive denominators. -/
def paperRay : Fin 15 → Fin 5 → ℝ :=
  ![![1,1,1,0,0], ![1,1+t,1,0,0], ![0,1,1,1,1],
    ![t,1,1,0,0], ![t,1+t,1,0,t], ![1,1,0,t,0],
    ![0,0,0,3+t,1], ![0,0,0,1,1], ![1,0,0,1,1],
    ![1,0,0,4*(1+t+1/3),1/3], ![1,0,0,4*(1+t+2/3),2/3],
    ![0,1,0,0,2-2*(2-t)/15], ![0,1,0,0,2-(2-t)/15],
    ![0,0,1,2+t/3,0], ![0,0,1,2+2*t/3,0]]

def denominator : Fin 15 → ℕ := ![1,1,1,1,1,1,1,1,1,3,3,15,15,3,3]

def shear (w : Fin 5 → ℝ) : Fin 5 → ℝ :=
  ![w 0 + 2*w 1 + 2*w 2 + w 4, w 1, w 2, w 3, w 4]

theorem denominator_pos : ∀ v, 0 < denominator v := by decide

set_option maxHeartbeats 800000 in
theorem construction_uses_paper_rays (v : Fin 15) :
    homogeneous v = (denominator v : ℝ) • shear (paperRay v) := by
  funext i
  fin_cases v <;> fin_cases i <;>
    norm_num [homogeneous, FifteenData.vertices, QuadInt.eval, denominator, shear, paperRay, t] <;> ring

/-- The two displayed heights above Y trisect the interval in (11). -/
theorem y_step : (2-t)/15 = (1/(3+t))/3 := by
  have hp : 0 < 3 + t := by linarith [t_pos]
  field_simp
  nlinarith [t_quadratic]

def project (w : Fin 5 → ℝ) : Fin 3 → ℝ := ![w 0,w 1,w 2]

theorem projected_rays :
    (fun i => project (paperRay i)) =
    ![![1,1,1], ![1,1+t,1], ![0,1,1], ![t,1,1], ![t,1+t,1], ![1,1,0],
      0,0, ![1,0,0], ![1,0,0], ![1,0,0], ![0,1,0], ![0,1,0], ![0,0,1], ![0,0,1]] := by
  funext v j
  fin_cases v <;> fin_cases j <;> rfl

/-- The three planar dependencies in (3). -/
theorem planar_relations :
    project (paperRay 4) = t • project (paperRay 5) + project (paperRay 2) ∧
    project (paperRay 3) = t • project (paperRay 0) + t^2 • project (paperRay 2) ∧
    project (paperRay 1) = t^2 • project (paperRay 4) + t • project (paperRay 3) +
      t^2 • project (paperRay 5) := by
  refine ⟨?_,?_,?_⟩ <;> funext i <;> fin_cases i <;> norm_num [project,paperRay] <;>
    nlinarith [t_quadratic, congrArg (fun a : ℝ => a*t) t_quadratic]

/-- The common interior ray of the two core triangles, equation (4). -/
theorem core_relation : paperRay 0 + (2+t) • paperRay 1 + t • paperRay 2 =
    (2*(1+t)) • paperRay 3 + paperRay 4 + paperRay 5 := by
  funext j
  fin_cases j <;> norm_num [paperRay] <;> nlinarith [t_quadratic]

/-- Equation (7) puts the kernel rays in their two polygon planes. -/
theorem kernel_relations :
    paperRay 4 + t^2 • paperRay 6 = t • paperRay 5 + paperRay 2 ∧
    paperRay 3 + t^2 • paperRay 7 = t • paperRay 0 + t^2 • paperRay 2 := by
  constructor <;> funext j <;> fin_cases j <;> norm_num [paperRay] <;>
    nlinarith [t_quadratic, congrArg (fun a : ℝ => a*t) t_quadratic]

/-- The named polygon and facet vertex sets and their affine dimensions. -/
theorem supporting_faces :
    (∀ f v, point v ∈ (reconstructionFace f).val ↔ v ∈ faceVertices f) ∧
    (∀ f, faceDim (reconstructionFace (planeFace f)).val = 2) ∧
    (∀ f, faceDim (reconstructionFace (facetFace f)).val = 3) :=
  ⟨point_mem_reconstructionFace, plane_face_dimension, facet_face_dimension⟩

end Papers.Nonrational.Fifteen
