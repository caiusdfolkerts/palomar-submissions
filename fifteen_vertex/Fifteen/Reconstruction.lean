module
public import Fifteen.Incidences
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp
@[expose] public section
namespace Papers.Nonrational.Fifteen
open Module FifteenRankData
variable {K : Type*} [Field K]
abbrev Space (K : Type*) := Fin 5 → K

/-- A facet span is the kernel of a field-valued form. -/
theorem exists_facet_form (W : Submodule K (Space K)) (hw : finrank K W = 4) :
    ∃ f : Space K →ₗ[K] K, LinearMap.ker f = W := by
  have hd : finrank K (Space K) = 5 := by simp [Space]
  have hlt : W < ⊤ := lt_top_iff_ne_top.mpr (by
    intro e
    rw [e, finrank_top, hd] at hw
    omega)
  obtain ⟨f, hf, hle⟩ := W.exists_le_ker_of_lt_top hlt
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  exact ⟨f, (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm⟩

/-- Three distinct polygon vertices span the entire homogeneous face plane. -/
private theorem propagate {p : Fin 15 → Space K} (W : Submodule K (Space K))
    (hW : finrank K W = 3) {a b c d : Fin 15}
    (hi : LinearIndependent K ![p a,p b,p c])
    (ha : p a ∈ W) (hb : p b ∈ W) (hc : p c ∈ W) (hd : p d ∈ W)
    (l : Space K →ₗ[K] K) (za : l (p a) = 0) (zb : l (p b) = 0) (zc : l (p c) = 0) :
    l (p d) = 0 := by
  let T := Submodule.span K (Set.range ![p a,p b,p c])
  have hs (S : Submodule K (Space K)) (a' : p a ∈ S) (b' : p b ∈ S) (c' : p c ∈ S) :
      T ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    fin_cases i <;> assumption
  have eq : T = W := Submodule.eq_of_le_of_finrank_eq (hs W ha hb hc)
    (by simpa [T, finrank_span_eq_card hi] using hW.symm)
  exact hs (LinearMap.ker l) za zb zc (eq ▸ hd)

/-- Reconstruction uses only the ranks and vertex incidences of the named faces. -/
theorem golden_root_of_faces (p : Fin 15 → Space K) (W : Fin 12 → Submodule K (Space K))
    (inc : ∀ f i, p i ∈ W f ↔ i ∈ faceVertices f)
    (trip : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → LinearIndependent K ![p i,p j,p k])
    (planes : ∀ f : Fin 7, finrank K (W (f.castLE (by decide))) = 3)
    (facets : ∀ f : Fin 3, finrank K (W ⟨7 + f.val, by omega⟩) = 4) :
    ∃ s : K, s ^ 2 + s - 1 = 0 := by
  classical
  obtain ⟨x, hx⟩ := exists_facet_form (W 7) (facets 0)
  have xinc (i : Fin 15) : x (p i) = 0 ↔ i ∈ faceVertices 7 := by
    change p i ∈ LinearMap.ker x ↔ _
    rw [hx, inc]
  obtain ⟨y, hy⟩ := exists_facet_form (W 8) (facets 1)
  have yinc (i : Fin 15) : y (p i) = 0 ↔ i ∈ faceVertices 8 := by
    change p i ∈ LinearMap.ker y ↔ _
    rw [hy, inc]
  obtain ⟨z, hz⟩ := exists_facet_form (W 9) (facets 2)
  have zinc (i : Fin 15) : z (p i) = 0 ↔ i ∈ faceVertices 9 := by
    change p i ∈ LinearMap.ker z ↔ _
    rw [hz, inc]

  let X := (z (p 2) * y (p 5)) • x
  let Y := (z (p 2) * x (p 5)) • y
  let Z := (y (p 2) * x (p 5)) • z
  have Xinc (i : Fin 15) : X (p i) = 0 ↔ i ∈ faceVertices 7 := by
    have h₁ : z (p 2) ≠ 0 := fun h => (by decide : (2 : Fin 15) ∉ faceVertices 9) ((zinc _).mp h)
    have h₂ : y (p 5) ≠ 0 := fun h => (by decide : (5 : Fin 15) ∉ faceVertices 8) ((yinc _).mp h)
    simpa [X, smul_eq_mul, h₁, h₂] using xinc i
  have Yinc (i : Fin 15) : Y (p i) = 0 ↔ i ∈ faceVertices 8 := by
    have h₁ : z (p 2) ≠ 0 := fun h => (by decide : (2 : Fin 15) ∉ faceVertices 9) ((zinc _).mp h)
    have h₂ : x (p 5) ≠ 0 := fun h => (by decide : (5 : Fin 15) ∉ faceVertices 7) ((xinc _).mp h)
    simpa [Y, smul_eq_mul, h₁, h₂] using yinc i
  have Zinc (i : Fin 15) : Z (p i) = 0 ↔ i ∈ faceVertices 9 := by
    have h₁ : y (p 2) ≠ 0 := fun h => (by decide : (2 : Fin 15) ∉ faceVertices 8) ((yinc _).mp h)
    have h₂ : x (p 5) ≠ 0 := fun h => (by decide : (5 : Fin 15) ∉ faceVertices 7) ((xinc _).mp h)
    simpa [Z, smul_eq_mul, h₁, h₂] using zinc i

  have cf : Y (p 2) = Z (p 2) := by dsimp [Y,Z]; ring
  have ff : X (p 5) = Y (p 5) := by dsimp [X,Y]; ring
  let s := X (p 3) / Z (p 3)
  let r := Y (p 1) / Z (p 1)
  have nz (i : Fin 15) (hi : i ∉ faceVertices 9) : Z (p i) ≠ 0 :=
    fun h => hi ((Zinc i).mp h)
  have sd : X (p 3) = s * Z (p 3) := (div_mul_cancel₀ _ (nz 3 (by decide))).symm
  have rb : Y (p 1) = r * Z (p 1) := (div_mul_cancel₀ _ (nz 1 (by decide))).symm
  have line (f : Fin 7) (a b c d : Fin 15)
      (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
      (ha : a ∈ faceVertices (f.castLE (by decide))) (hb : b ∈ faceVertices (f.castLE (by decide)))
      (hc : c ∈ faceVertices (f.castLE (by decide))) (hd : d ∈ faceVertices (f.castLE (by decide)))
      (l : Space K →ₗ[K] K) := propagate (W (f.castLE (by decide))) (planes f)
        (trip a b c hab hac hbc) ((inc _ _).mpr ha) ((inc _ _).mpr hb)
        ((inc _ _).mpr hc) ((inc _ _).mpr hd) l
  have X2 := (Xinc 2).mpr (by decide)
  have X6 := (Xinc 6).mpr (by decide)
  have X7 := (Xinc 7).mpr (by decide)
  have X11 := (Xinc 11).mpr (by decide)
  have X12 := (Xinc 12).mpr (by decide)
  have X13 := (Xinc 13).mpr (by decide)
  have X14 := (Xinc 14).mpr (by decide)
  have Y6 := (Yinc 6).mpr (by decide)
  have Y7 := (Yinc 7).mpr (by decide)
  have Y8 := (Yinc 8).mpr (by decide)
  have Y9 := (Yinc 9).mpr (by decide)
  have Y10 := (Yinc 10).mpr (by decide)
  have Y13 := (Yinc 13).mpr (by decide)
  have Y14 := (Yinc 14).mpr (by decide)
  have Z5 := (Zinc 5).mpr (by decide)
  have Z6 := (Zinc 6).mpr (by decide)
  have Z7 := (Zinc 7).mpr (by decide)
  have Z8 := (Zinc 8).mpr (by decide)
  have Z9 := (Zinc 9).mpr (by decide)
  have Z10 := (Zinc 10).mpr (by decide)
  have Z11 := (Zinc 11).mpr (by decide)
  have Z12 := (Zinc 12).mpr (by decide)
  have ac := line 6 2 8 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (Y - Z)
    (by simp only [LinearMap.sub_apply]; linear_combination cf)
    (by simp only [LinearMap.sub_apply, Y8, Z8]; ring)
    (by simp only [LinearMap.sub_apply, Y7, Z7]; ring)
  simp only [LinearMap.sub_apply] at ac
  have dc := line 6 2 8 7 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (Y - Z)
    (by simp only [LinearMap.sub_apply]; linear_combination cf)
    (by simp only [LinearMap.sub_apply, Y8, Z8]; ring)
    (by simp only [LinearMap.sub_apply, Y7, Z7]; ring)
  simp only [LinearMap.sub_apply] at dc
  have af := line 2 5 13 14 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (X - Y)
    (by simp only [LinearMap.sub_apply]; linear_combination ff)
    (by simp only [LinearMap.sub_apply, X13, Y13]; ring)
    (by simp only [LinearMap.sub_apply, X14, Y14]; ring)
  simp only [LinearMap.sub_apply] at af
  have ab := line 0 0 11 12 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (X - Z)
    (by simp only [LinearMap.sub_apply]; linear_combination af + ac)
    (by simp only [LinearMap.sub_apply, X11, Z11]; ring)
    (by simp only [LinearMap.sub_apply, X12, Z12]; ring)
  simp only [LinearMap.sub_apply] at ab
  have de := line 1 3 11 12 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (X - s • Z)
    (by simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]; linear_combination sd)
    (by simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, X11, Z11]; ring)
    (by simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, X12, Z12]; ring)
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at de
  have be := line 4 1 9 10 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (Y - r • Z)
    (by simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]; linear_combination rb)
    (by simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, Y9, Z9]; ring)
    (by simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, Y10, Z10]; ring)
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at be
  have ce := line 5 2 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (Y - X - Z)
    (by simp only [LinearMap.sub_apply, X2]; linear_combination cf)
    (by simp only [LinearMap.sub_apply, Z5]; linear_combination -ff)
    (by simp only [LinearMap.sub_apply, X6, Y6, Z6]; ring)
  simp only [LinearMap.sub_apply] at ce
  have bd := line 3 1 13 14 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (Y - r • X)
    (by simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]; linear_combination rb - r * ab)
    (by simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, X13, Y13]; ring)
    (by simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, X14, Y14]; ring)
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at bd

  have h₁ : (r - s - 1) * Z (p 4) = 0 := by linear_combination ce - be + de
  have h₂ : (1 - r*s) * Z (p 3) = 0 := by linear_combination bd - dc + r * sd
  have e₁ := (mul_eq_zero.mp h₁).resolve_right (nz 4 (by decide))
  have e₂ := (mul_eq_zero.mp h₂).resolve_right (nz 3 (by decide))
  refine ⟨s, ?_⟩
  linear_combination -s * e₁ - e₂
end Papers.Nonrational.Fifteen
