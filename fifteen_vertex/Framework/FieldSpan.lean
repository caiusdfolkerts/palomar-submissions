module
public import Framework.FieldCoordinates

@[expose] public section

/-!
# Spans under an embedding of coordinate fields

These lemmas compare linear spans over the two different fields, rather than
restricting scalars on the larger vector space. In particular the dimension
statement is equality, not just monotonicity under an injective linear map.
-/

noncomputable section
namespace Papers.Coordinates

open Set

variable {K L : Type*} [Field K] [Field L]

def coordinateMap (σ : K →+* L) (n : ℕ) : (Fin n → K) →ₛₗ[σ] (Fin n → L) where
  toFun x j := σ (x j)
  map_add' x y := by ext j; exact σ.map_add _ _
  map_smul' c x := by ext j; exact σ.map_mul _ _

@[simp] theorem coordinateMap_apply (σ : K →+* L) (n : ℕ)
    (x : Fin n → K) (j : Fin n) : coordinateMap σ n x j = σ (x j) := rfl

theorem coordinateMap_mem_span (σ : K →+* L) {n : ℕ}
    {S : Set (Fin n → K)} {x : Fin n → K} (hx : x ∈ Submodule.span K S) :
    coordinateMap σ n x ∈ Submodule.span L (coordinateMap σ n '' S) := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (Set.mem_image_of_mem _ hx)
  | zero => simpa only [map_zero] using (Submodule.span L (coordinateMap σ n '' S)).zero_mem
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using (Submodule.span L (coordinateMap σ n '' S)).add_mem ihx ihy
  | smul c x hx ih =>
    simpa only [map_smulₛₗ] using
      (Submodule.span L (coordinateMap σ n '' S)).smul_mem (σ c) ih

theorem span_coordinateMap_span (σ : K →+* L) {n : ℕ} (S : Set (Fin n → K)) :
    Submodule.span L (coordinateMap σ n '' (Submodule.span K S : Set (Fin n → K))) =
      Submodule.span L (coordinateMap σ n '' S) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    exact coordinateMap_mem_span σ hx
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

/-- The rank of a coordinate span is unchanged by a field embedding. -/
theorem finrank_span_coordinateMap (σ : K →+* L) {n : ℕ} (S : Set (Fin n → K)) :
    Module.finrank L (Submodule.span L (coordinateMap σ n '' S)) =
      Module.finrank K (Submodule.span K S) := by
  let W := Submodule.span K S
  let b := Module.finBasis K W
  let q : Fin (Module.finrank K W) → Fin n → K := W.subtype ∘ b
  have hq : LinearIndependent K q :=
    b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hspan : Submodule.span K (Set.range q) = W := by
    dsimp only [q]
    rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have himage : Submodule.span L (coordinateMap σ n '' S) =
      Submodule.span L (Set.range (fun i => coordinateMap σ n (q i))) := by
    calc
      _ = Submodule.span L (coordinateMap σ n '' (W : Set (Fin n → K))) :=
        (span_coordinateMap_span σ S).symm
      _ = Submodule.span L
          (coordinateMap σ n '' (Submodule.span K (Set.range q) : Set (Fin n → K))) := by
        rw [hspan]
      _ = Submodule.span L (coordinateMap σ n '' Set.range q) :=
        span_coordinateMap_span σ (Set.range q)
      _ = _ := by rw [← Set.range_comp]; rfl
  rw [himage]
  change Module.finrank L (Submodule.span L (Set.range (fun i j => σ (q i j)))) =
    Module.finrank K W
  simpa only [Fintype.card_fin] using
    finrank_span_eq_card (linearIndependent_coordinate_map σ q hq)

/-- Linear membership also reflects back to the smaller field. -/
theorem coordinateMap_mem_span_iff (σ : K →+* L) {n : ℕ}
    (S : Set (Fin n → K)) (x : Fin n → K) :
    coordinateMap σ n x ∈ Submodule.span L (coordinateMap σ n '' S) ↔
      x ∈ Submodule.span K S := by
  constructor
  · intro hx
    have hm : Submodule.span L (coordinateMap σ n '' insert x S) =
        Submodule.span L (coordinateMap σ n '' S) := by
      rw [Set.image_insert_eq, Submodule.span_insert_eq_span hx]
    have hd : Module.finrank K (Submodule.span K S) =
        Module.finrank K (Submodule.span K (insert x S)) := by
      rw [← finrank_span_coordinateMap σ S,
        ← finrank_span_coordinateMap σ (insert x S), hm]
    have heq := Submodule.eq_of_le_of_finrank_eq
      (Submodule.span_mono (Set.subset_insert x S)) hd
    rw [heq]
    exact Submodule.subset_span (Set.mem_insert x S)
  · exact coordinateMap_mem_span σ

end Papers.Coordinates

end
end
