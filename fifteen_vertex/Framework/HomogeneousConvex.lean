module
public import Framework.HomogeneousSpan

@[expose] public section

noncomputable section
namespace Papers.Coordinates
open Set

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem homogeneousSpan_mono {S T : Set V} (h : S ⊆ T) :
    homogeneousSpan (K := ℝ) S ≤ homogeneousSpan (K := ℝ) T :=
  Submodule.span_mono (Set.image_mono h)

theorem homogeneousSpan_convexHull (S : Set V) (hS : S.Nonempty) :
    homogeneousSpan (K := ℝ) (convexHull ℝ S) = homogeneousSpan (K := ℝ) S := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    exact (homogenize_mem_span_iff hS x).mpr (convexHull_subset_affineSpan (𝕜 := ℝ) S hx)
  · exact homogeneousSpan_mono (subset_convexHull ℝ S)

end Papers.Coordinates

namespace Papers.Coordinates
open Set
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem span_scaled_image (p : ι → V) (c : ι → K) (S : Set ι)
    (hc : ∀ i ∈ S, c i ≠ 0) :
    Submodule.span K ((fun i => c i • p i) '' S) = Submodule.span K (p '' S) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_image_of_mem p hi))
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    apply (Submodule.smul_mem_iff _ (hc i hi)).mp
    exact Submodule.subset_span (Set.mem_image_of_mem _ hi)

end Papers.Coordinates

end
end
