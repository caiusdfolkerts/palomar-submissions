module
public import Fifteen.Incidences
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Nonsingular
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Framework.FieldCoordinates
public import Framework.FieldSpan
public import Framework.FiniteHullCertificates
public import Framework.HomogeneousConvex
public import Framework.PolytopeTargets
public import Framework.RationalCoordinates

/-! # Arithmetic in the real quadratic field -/
@[expose] public section

/-!
# Exact arithmetic for the 15-vertex certificate

The integer-pair operations encode `a + b φ`, where `φ² = φ + 1`.
All finite certificate checks use ordinary kernel reduction (`decide`).
The bridge from integer arithmetic to real geometry is proved here.
-/

namespace Papers.Nonrational

noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

theorem phi_sq : phi ^ 2 = phi + 1 := by
  have h : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  dsimp [phi]
  nlinarith

theorem phi_basic_bounds : 1 < phi ∧ phi < 2 := by
  have h : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg (5 : ℝ)
  dsimp [phi]
  constructor <;> nlinarith

/-- Integers representing an element of `ℤ[φ]`. -/
abbrev QuadInt := ℤ × ℤ

namespace QuadInt

def add (x y : QuadInt) : QuadInt := (x.1 + y.1, x.2 + y.2)
def neg (x : QuadInt) : QuadInt := (-x.1, -x.2)
def mul (x y : QuadInt) : QuadInt :=
  (x.1 * y.1 + x.2 * y.2, x.1 * y.2 + x.2 * y.1 + x.2 * y.2)

noncomputable def eval (x : QuadInt) : ℝ := (x.1 : ℝ) + (x.2 : ℝ) * phi

@[simp] theorem eval_zero : eval (0, 0) = 0 := by simp [eval]

@[simp] theorem eval_add (x y : QuadInt) : eval (add x y) = eval x + eval y := by
  simp only [eval, add, Int.cast_add]
  ring

@[simp] theorem eval_neg (x : QuadInt) : eval (neg x) = -eval x := by
  simp only [eval, neg, Int.cast_neg]
  ring

@[simp] theorem eval_mul (x y : QuadInt) : eval (mul x y) = eval x * eval y := by
  simp only [eval, mul, Int.cast_add, Int.cast_mul]
  linear_combination -((x.2 : ℝ) * (y.2 : ℝ)) * phi_sq

/-- A five-coordinate dot product, expressed with integer-pair operations. -/
def dot5 (x y : Fin 5 → QuadInt) : QuadInt :=
  add (mul (x 0) (y 0)) (add (mul (x 1) (y 1))
    (add (mul (x 2) (y 2)) (add (mul (x 3) (y 3)) (mul (x 4) (y 4)))))

theorem eval_dot5 (x y : Fin 5 → QuadInt) :
    eval (dot5 x y) = ∑ k : Fin 5, eval (x k) * eval (y k) := by
  simp [dot5, Fin.sum_univ_succ]

/-- A rational lower bound obtained by choosing the appropriate endpoint
of a certified interval for `φ`. -/
def positiveAt (scale lo hi : ℤ) (x : QuadInt) : Bool :=
  if 0 ≤ x.2 then decide (0 < scale * x.1 + lo * x.2)
  else decide (0 < scale * x.1 + hi * x.2)

theorem eval_pos_of_positiveAt (scale lo hi : ℤ)
    (hscale : 0 < scale)
    (hlo : (lo : ℝ) / scale ≤ phi) (hhi : phi ≤ (hi : ℝ) / scale)
    (x : QuadInt) (hx : positiveAt scale lo hi x = true) : 0 < eval x := by
  have hscale' : (0 : ℝ) < scale := by exact_mod_cast hscale
  by_cases hb : 0 ≤ x.2
  · have hsum : 0 < scale * x.1 + lo * x.2 := by
      simpa [positiveAt, hb] using hx
    have hsum' : (0 : ℝ) < scale * (x.1 : ℝ) + lo * (x.2 : ℝ) := by
      exact_mod_cast hsum
    have hb' : (0 : ℝ) ≤ x.2 := by exact_mod_cast hb
    have hmul := mul_le_mul_of_nonneg_right ((div_le_iff₀ hscale').mp hlo) hb'
    have hproduct : 0 < (scale : ℝ) * eval x := by
      dsimp [eval]
      nlinarith
    exact (mul_pos_iff_of_pos_left hscale').mp hproduct
  · have hsum : 0 < scale * x.1 + hi * x.2 := by
      simpa [positiveAt, hb] using hx
    have hsum' : (0 : ℝ) < scale * (x.1 : ℝ) + hi * (x.2 : ℝ) := by
      exact_mod_cast hsum
    have hb' : (x.2 : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (lt_of_not_ge hb))
    have hmul := mul_le_mul_of_nonpos_right ((le_div_iff₀ hscale').mp hhi) hb'
    have hproduct : 0 < (scale : ℝ) * eval x := by
      dsimp [eval]
      nlinarith
    exact (mul_pos_iff_of_pos_left hscale').mp hproduct

end QuadInt
end Papers.Nonrational

end
