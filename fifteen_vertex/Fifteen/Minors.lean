module
public import Fifteen.Arithmetic

/-! # Small determinants over the quadratic integers -/
@[expose] public section

/-! Small exact determinants for the supplied homogeneous face coordinates. -/

namespace Papers.Nonrational.QuadInt

def det2 (M : Fin 2 → Fin 2 → QuadInt) : QuadInt :=
  add (mul (M 0 0) (M 1 1)) (neg (mul (M 0 1) (M 1 0)))

def det3 (M : Fin 3 → Fin 3 → QuadInt) : QuadInt :=
  add (mul (M 0 0) (det2 (fun i j => M i.succ ((0 : Fin 3).succAbove j))))
    (add (neg (mul (M 0 1) (det2 (fun i j => M i.succ ((1 : Fin 3).succAbove j)))))
      (mul (M 0 2) (det2 (fun i j => M i.succ ((2 : Fin 3).succAbove j)))))

def det4 (M : Fin 4 → Fin 4 → QuadInt) : QuadInt :=
  add (mul (M 0 0) (det3 (fun i j => M i.succ ((0 : Fin 4).succAbove j))))
    (add (neg (mul (M 0 1) (det3 (fun i j => M i.succ ((1 : Fin 4).succAbove j)))))
      (add (mul (M 0 2) (det3 (fun i j => M i.succ ((2 : Fin 4).succAbove j))))
        (neg (mul (M 0 3) (det3 (fun i j => M i.succ ((3 : Fin 4).succAbove j)))))))

theorem eval_det2 (M : Fin 2 → Fin 2 → QuadInt) :
    eval (det2 M) = Matrix.det (Matrix.of (fun i j => eval (M i j))) := by
  simp [det2, Matrix.det_fin_two, sub_eq_add_neg]

theorem eval_det3 (M : Fin 3 → Fin 3 → QuadInt) :
    eval (det3 M) = Matrix.det (Matrix.of (fun i j => eval (M i j))) := by
  simp [det3, eval_det2, Matrix.det_fin_two, Matrix.det_fin_three,
    Fin.succAbove, Fin.lt_def, -Fin.val_fin_lt]; ring

theorem eval_det4 (M : Fin 4 → Fin 4 → QuadInt) :
    eval (det4 M) = Matrix.det (Matrix.of (fun i j => eval (M i j))) := by
  simp only [det4, eval_add, eval_mul, eval_neg, eval_det3]
  rw [Matrix.det_succ_row_zero (n := 3)]
  simp [Fin.sum_univ_succ, Matrix.of_apply, Matrix.submatrix]; ring

def combine3 (a : Fin 3 → QuadInt) (p : Fin 3 → Fin 5 → QuadInt) : Fin 5 → QuadInt :=
  fun j => add (mul (a 0) (p 0 j)) (add (mul (a 1) (p 1 j)) (mul (a 2) (p 2 j)))

def combine4 (a : Fin 4 → QuadInt) (p : Fin 4 → Fin 5 → QuadInt) : Fin 5 → QuadInt :=
  fun j => add (mul (a 0) (p 0 j)) (add (mul (a 1) (p 1 j))
    (add (mul (a 2) (p 2 j)) (mul (a 3) (p 3 j))))

theorem eval_combine3 (a : Fin 3 → QuadInt) (p : Fin 3 → Fin 5 → QuadInt) (j : Fin 5) :
    eval (combine3 a p j) = ∑ i : Fin 3, eval (a i) * eval (p i j) := by
  simp [combine3, Fin.sum_univ_succ]

theorem eval_combine4 (a : Fin 4 → QuadInt) (p : Fin 4 → Fin 5 → QuadInt) (j : Fin 5) :
    eval (combine4 a p j) = ∑ i : Fin 4, eval (a i) * eval (p i j) := by
  simp [combine4, Fin.sum_univ_succ]

end Papers.Nonrational.QuadInt

end
