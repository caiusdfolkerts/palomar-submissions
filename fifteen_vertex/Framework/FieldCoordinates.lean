module
public import Framework.Faces

@[expose] public section

/-!
# Field changes and homogeneous coordinates

Finite coordinate matrices have the same linear-dependence relations after
an embedding of fields. The proof extends an independent rectangular family
to a square basis, then uses the determinant and its functoriality. This
supplies the field-of-definition step in the projective reconstruction.
-/

noncomputable section

namespace Papers.Coordinates

section Homogeneous

variable {K V ι : Type*} [CommRing K] [AddCommGroup V] [Module K V]

def homogenize (p : V) : V × K := (p, 1)

theorem linearIndependent_homogenize_iff (p : ι → V) :
    LinearIndependent K (fun i => homogenize (K := K) (p i)) ↔ AffineIndependent K p := by
  rw [linearIndependent_iff', affineIndependent_iff]
  constructor
  · intro h s w hw hsum i hi
    apply h s w ?_ i hi
    apply Prod.ext
    · simpa only [Prod.fst_sum, Prod.smul_fst, homogenize, Prod.fst_zero] using hsum
    · simpa only [Prod.snd_sum, Prod.smul_snd, homogenize, smul_eq_mul, mul_one,
        Prod.snd_zero] using hw
  · intro h s w hsum i hi
    have hw := congrArg Prod.snd hsum
    have hp := congrArg Prod.fst hsum
    simp only [Prod.snd_sum, Prod.smul_snd, homogenize, smul_eq_mul, mul_one,
      Prod.snd_zero] at hw
    simp only [Prod.fst_sum, Prod.smul_fst, homogenize, Prod.fst_zero] at hp
    exact h s w hw hp i hi

end Homogeneous

section FieldEmbedding

variable {K L : Type*} [Field K] [Field L]

theorem linearIndependent_coordinate_map {m n : ℕ} (σ : K →+* L)
    (p : Fin m → Fin n → K) (hp : LinearIndependent K p) :
    LinearIndependent L (fun i j => σ (p i j)) := by
  have step : ∀ k m, ∀ p : Fin m → Fin n → K, n - m = k → LinearIndependent K p →
      LinearIndependent L (fun i j => σ (p i j)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro m p hnm hp
      have hle : m ≤ n := by simpa using hp.fintype_card_le_finrank
      rcases lt_or_eq_of_le hle with hlt | heq
      · obtain ⟨w, hw⟩ := exists_linearIndependent_snoc_of_lt_finrank hp
          (by simpa using hlt)
        have hcast := ih (n - (m + 1)) (by omega) (m + 1) (Fin.snoc p w) rfl hw
        change LinearIndependent L
          ((fun x : Fin n → K => fun j => σ (x j)) ∘ Fin.snoc p w) at hcast
        rw [Fin.comp_snoc] at hcast
        exact (linearIndependent_finSnoc.mp hcast).1
      · subst m
        have hdet : Matrix.det (Matrix.of p) ≠ 0 := Matrix.nonsingular_iff_det_ne_zero.mp
          (Matrix.Nonsingular.of_linearIndependent_row hp)
        apply Matrix.linearIndependent_rows_of_det_ne_zero (A := σ.mapMatrix (Matrix.of p))
        rw [← σ.map_det]
        intro hzero
        exact hdet (σ.injective (by simpa using hzero))
  exact step (n - m) m p rfl hp

theorem linearIndependent_of_coordinate_map {m n : ℕ} (σ : K →+* L)
    (p : Fin m → Fin n → K) (hp : LinearIndependent L (fun i j => σ (p i j))) :
    LinearIndependent K p := by
  rw [linearIndependent_iff']
  intro s w hsum i hi
  have hmap : ∑ j ∈ s, σ (w j) • (fun k => σ (p j k)) = (0 : Fin n → L) := by
    ext k
    have h := congrArg σ (congrFun hsum k)
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      map_sum, map_mul, map_zero] using h
  have hzero := (linearIndependent_iff'.mp hp) s (fun j => σ (w j)) hmap i hi
  exact σ.injective (by simpa using hzero)

/-- Both directions are needed: real geometric dependence can be transported
back to the field in which the coordinate entries lie. -/
theorem linearIndependent_coordinate_map_iff {m n : ℕ} (σ : K →+* L)
    (p : Fin m → Fin n → K) :
    LinearIndependent L (fun i j => σ (p i j)) ↔ LinearIndependent K p :=
  ⟨linearIndependent_of_coordinate_map σ p, linearIndependent_coordinate_map σ p⟩

end FieldEmbedding

end Papers.Coordinates

end
end
