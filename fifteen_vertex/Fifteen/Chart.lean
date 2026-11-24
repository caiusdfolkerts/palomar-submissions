module
public import Fifteen.Hull

/-! # Homogeneous rank in the positive chart -/
@[expose] public section

/-! The positive affine chart preserves the exact homogeneous face ranks. -/

noncomputable section
namespace Papers.Nonrational.Fifteen
open Set Module
open Papers.Coordinates
open LeanEval.Geometry.PlatonicClassification

def chartEquiv : (E 4 × ℝ) ≃ₗ[ℝ] (Fin 5 → ℝ) where
  toFun z := ![z.2 + z.1 0 + z.1 1 - z.1 2, z.1 0, z.1 1, z.1 2, z.1 3]
  invFun w := (WithLp.toLp 2 (fun i : Fin 4 => w i.succ), w 0 - w 1 - w 2 + w 3)
  left_inv z := by
    apply Prod.ext
    · ext i
      fin_cases i <;> rfl
    · dsimp
      ring
  right_inv w := by
    ext i
    fin_cases i <;> simp
    ring
  map_add' x y := by
    ext i
    fin_cases i <;> simp
    ring
  map_smul' c x := by
    ext i
    fin_cases i <;> simp
    ring

theorem chartEquiv_homogenize (v : Fin 15) :
    chartEquiv (homogenize (K := ℝ) (point v)) = (chartValue v)⁻¹ • homogeneous v := by
  have hc := ne_of_gt (chartValue_pos v)
  ext i
  fin_cases i
  · change 1 + homogeneous v 1 / chartValue v + homogeneous v 2 / chartValue v -
      homogeneous v 3 / chartValue v = (chartValue v)⁻¹ * homogeneous v 0
    field_simp
    linear_combination chart_identity v
  all_goals simp [chartEquiv, homogenize, point_apply, div_eq_mul_inv, mul_comm]

theorem chart_map_homogeneousSpan (S : Set (Fin 15)) :
    Submodule.map chartEquiv.toLinearMap (homogeneousSpan (K := ℝ) (point '' S)) =
      Submodule.span ℝ (homogeneous '' S) := by
  rw [homogeneousSpan, Submodule.map_span]
  simp only [Set.image_image, LinearEquiv.coe_coe]
  simp_rw [chartEquiv_homogenize]
  exact span_scaled_image homogeneous (fun v => (chartValue v)⁻¹) S
    (fun v _ => inv_ne_zero (ne_of_gt (chartValue_pos v)))

theorem finrank_homogeneousSpan_points (S : Set (Fin 15)) :
    finrank ℝ (homogeneousSpan (K := ℝ) (point '' S)) =
      finrank ℝ (Submodule.span ℝ (homogeneous '' S)) := by
  rw [← chart_map_homogeneousSpan S]
  exact (chartEquiv.finrank_map_eq _).symm

end Papers.Nonrational.Fifteen

end
end
