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

/-! # A nonzero minor and spanning equations determine rank -/
@[expose] public section

/-! Exact rank certificates: a nonzero minor and explicit spanning relations. -/

noncomputable section
namespace Papers.Coordinates
open Set Submodule Module

variable {K : Type*} [Field K]

def selectCoordinates {d r : ℕ} (columns : Fin r → Fin d) :
    (Fin d → K) →ₗ[K] (Fin r → K) where
  toFun x := x ∘ columns
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem independent_of_minor {d r : ℕ} (p : Fin r → Fin d → K)
    (columns : Fin r → Fin d)
    (hdet : Matrix.det (Matrix.of (fun i j => p i (columns j))) ≠ 0) :
    LinearIndependent K p := by
  apply LinearIndependent.of_comp (selectCoordinates columns)
  exact Matrix.linearIndependent_rows_of_det_ne_zero hdet

theorem finrank_span_of_certificate {ι : Type*} {d r : ℕ}
    (p : ι → Fin d → K) (S : Set ι)
    (basis : Fin r → ι) (columns : Fin r → Fin d)
    (hb : ∀ i, basis i ∈ S)
    (Δ : K) (hΔ : Δ ≠ 0)
    (hdet : Matrix.det (Matrix.of (fun i j => p (basis i) (columns j))) = Δ)
    (a : ι → Fin r → K)
    (hspan : ∀ v ∈ S, Δ • p v = ∑ i : Fin r, a v i • p (basis i)) :
    finrank K (Submodule.span K (p '' S)) = r := by
  let q : Fin r → Fin d → K := p ∘ basis
  have hq : LinearIndependent K q := independent_of_minor q columns (by
    change Matrix.det (Matrix.of (fun i j => p (basis i) (columns j))) ≠ 0
    rw [hdet]
    exact hΔ)
  have heq : Submodule.span K (p '' S) = Submodule.span K (Set.range q) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨v, hv, rfl⟩
      apply (Submodule.smul_mem_iff _ hΔ).mp
      rw [hspan v hv]
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_range_self i)))
    · apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      exact Set.mem_image_of_mem p (hb i)
  rw [heq, finrank_span_eq_card hq, Fintype.card_fin]

end Papers.Coordinates

end
end
