module
public import Framework.FieldCoordinates

@[expose] public section

/-! The exact relation between affine dimension and homogeneous linear rank. -/

noncomputable section
namespace Papers.Coordinates
open Set
open scoped Pointwise

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def homogeneousSpan (S : Set V) : Submodule K (V × K) :=
  Submodule.span K (homogenize (K := K) '' S)

theorem homogenize_mem_span {S : Set V} {p : V} (hp : p ∈ S) :
    homogenize (K := K) p ∈ homogeneousSpan (K := K) S :=
  Submodule.subset_span (Set.mem_image_of_mem _ hp)

theorem direction_lift_mem_homogeneousSpan {S : Set V} {v : V}
    (hv : v ∈ vectorSpan K S) : (v, (0 : K)) ∈ homogeneousSpan (K := K) S := by
  rw [vectorSpan_def] at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨p, hp, q, hq, rfl⟩ := Set.mem_vsub.mp hv
    have h := (homogeneousSpan (K := K) S).sub_mem
      (homogenize_mem_span hp) (homogenize_mem_span hq)
    simpa only [homogenize, Prod.mk_sub_mk, sub_self, vsub_eq_sub] using h
  | zero => exact (homogeneousSpan (K := K) S).zero_mem
  | add x y hx hy ihx ihy =>
    simpa only [Prod.mk_add_mk, add_zero] using
      (homogeneousSpan (K := K) S).add_mem ihx ihy
  | smul c x hx ih =>
    simpa only [Prod.smul_mk, smul_zero] using
      (homogeneousSpan (K := K) S).smul_mem c ih

def homogeneousParam (S : Set V) (p₀ : V) :
    (vectorSpan K S × K) →ₗ[K] (V × K) where
  toFun z := (z.1.val + z.2 • p₀, z.2)
  map_add' x y := by
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, add_smul]
      module
    · rfl
  map_smul' c x := by
    apply Prod.ext
    · simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, smul_add, smul_smul]
      rfl
    · rfl

theorem homogeneousParam_injective (S : Set V) (p₀ : V) :
    Function.Injective (homogeneousParam (K := K) S p₀) := by
  rintro ⟨v, c⟩ ⟨w, d⟩ heq
  have hcd : c = d := congrArg Prod.snd heq
  subst d
  apply Prod.ext
  · apply Subtype.ext
    exact add_right_cancel (show v.val + c • p₀ = w.val + c • p₀ from
      congrArg Prod.fst heq)
  · rfl

theorem homogeneousSpan_eq_range {S : Set V} {p₀ : V} (hp₀ : p₀ ∈ S) :
    homogeneousSpan (K := K) S = (homogeneousParam (K := K) S p₀).range := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨p, hp, rfl⟩
    refine ⟨(⟨p - p₀, ?_⟩, 1), ?_⟩
    · exact vsub_mem_vectorSpan K hp hp₀
    · simp [homogeneousParam, homogenize]
  · rintro _ ⟨⟨v, c⟩, rfl⟩
    have h₁ := direction_lift_mem_homogeneousSpan (K := K) v.property
    have h₂ := (homogeneousSpan (K := K) S).smul_mem c (homogenize_mem_span hp₀)
    simpa [homogeneousParam, homogenize] using (homogeneousSpan (K := K) S).add_mem h₁ h₂

/-- A homogeneous vector of last coordinate one is in the homogeneous span
exactly when its affine point is in the original affine span. -/
theorem homogenize_mem_span_iff {S : Set V} (hS : S.Nonempty) (p : V) :
    homogenize (K := K) p ∈ homogeneousSpan (K := K) S ↔ p ∈ affineSpan K S := by
  obtain ⟨p₀, hp₀⟩ := hS
  constructor
  · intro hp
    rw [homogeneousSpan_eq_range hp₀] at hp
    obtain ⟨⟨v, c⟩, hv⟩ := hp
    have hc : c = 1 := congrArg Prod.snd hv
    subst c
    apply (mem_affineSpan_iff_exists K).mpr
    refine ⟨p₀, hp₀, v.val, v.property, ?_⟩
    have hv' := congrArg Prod.fst hv
    simpa [homogeneousParam, homogenize] using hv'.symm
  · intro hp
    obtain ⟨q, hq, v, hv, rfl⟩ := (mem_affineSpan_iff_exists K).mp hp
    have h₁ := direction_lift_mem_homogeneousSpan (K := K) hv
    have h₂ := homogenize_mem_span (K := K) hq
    simpa [homogenize, vadd_eq_add] using (homogeneousSpan (K := K) S).add_mem h₁ h₂

/-- Nonempty affine sets gain exactly one dimension on homogenization. -/
theorem finrank_homogeneousSpan [FiniteDimensional K V] {S : Set V}
    (hS : S.Nonempty) :
    Module.finrank K (homogeneousSpan (K := K) S) =
      Module.finrank K (vectorSpan K S) + 1 := by
  obtain ⟨p₀, hp₀⟩ := hS
  rw [homogeneousSpan_eq_range hp₀,
    LinearMap.finrank_range_of_inj (homogeneousParam_injective S p₀),
    Module.finrank_prod]
  simp

end Papers.Coordinates

end
end
