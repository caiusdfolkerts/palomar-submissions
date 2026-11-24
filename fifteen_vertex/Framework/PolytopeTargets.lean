module
public import Framework.CompleteFaceLattice

@[expose] public section

/-!
# Exact geometric targets for the two polytope papers

All objects below are actual finite convex hulls with their extreme vertices.
Faces are exposed faces, and combinatorial equivalence is an order isomorphism
of their ordinary face posets. In particular, neither field realizability nor
Minkowski decomposability is encoded by a conclusion to be proved.

The declarations ending in `Claim` are proposition-valued definitions recording
the original targets. Their presence does NOT assert or prove these claims.
-/

noncomputable section

open Set
open scoped Classical
open scoped Pointwise
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

namespace Papers.Polytopes

variable {d : ℕ}

/-- The actual combinatorial equivalence relation on nonempty face posets.
The omitted empty face can be adjoined as a new least element. -/
def CombinatoriallyEquivalent (P Q : ConvexPolytope d) : Prop :=
  Nonempty (FaceType P ≃o FaceType Q)

/-- Adjoining the empty face gives exactly the ordinary complete face-lattice
notion of combinatorial equivalence. -/
theorem combinatoriallyEquivalent_iff_complete_face_iso (P Q : ConvexPolytope d) :
    CombinatoriallyEquivalent P Q ↔
      Nonempty (CompleteFaceType P ≃o CompleteFaceType Q) :=
  nonempty_face_iso_iff_complete_face_iso P Q

theorem CombinatoriallyEquivalent.refl (P : ConvexPolytope d) :
    CombinatoriallyEquivalent P P := ⟨OrderIso.refl _⟩

theorem CombinatoriallyEquivalent.symm {P Q : ConvexPolytope d}
    (h : CombinatoriallyEquivalent P Q) : CombinatoriallyEquivalent Q P :=
  h.elim (fun e => ⟨e.symm⟩)

theorem CombinatoriallyEquivalent.trans {P Q R : ConvexPolytope d}
    (h₁ : CombinatoriallyEquivalent P Q) (h₂ : CombinatoriallyEquivalent Q R) :
    CombinatoriallyEquivalent P R :=
  h₁.elim (fun e₁ => h₂.elim (fun e₂ => ⟨e₁.trans e₂⟩))

def CoordinatesIn (K : Subfield ℝ) (P : ConvexPolytope d) : Prop :=
  ∀ v ∈ P.vertices, ∀ i : Fin d, v i ∈ K

def RationalCoordinates (P : ConvexPolytope d) : Prop :=
  ∀ v ∈ P.vertices, ∀ i : Fin d, ∃ q : ℚ, (q : ℝ) = v i

def RealizableOver (P : ConvexPolytope d) (K : Subfield ℝ) : Prop :=
  ∃ Q : ConvexPolytope d, CombinatoriallyEquivalent P Q ∧ CoordinatesIn K Q

theorem realizableOver_iff_complete_face_iso (P : ConvexPolytope d) (K : Subfield ℝ) :
    RealizableOver P K ↔ ∃ Q : ConvexPolytope d,
      Nonempty (CompleteFaceType P ≃o CompleteFaceType Q) ∧ CoordinatesIn K Q := by
  constructor
  · rintro ⟨Q, hPQ, hK⟩
    exact ⟨Q, (combinatoriallyEquivalent_iff_complete_face_iso P Q).mp hPQ, hK⟩
  · rintro ⟨Q, hPQ, hK⟩
    exact ⟨Q, (combinatoriallyEquivalent_iff_complete_face_iso P Q).mpr hPQ, hK⟩

def RationallyRealizable (P : ConvexPolytope d) : Prop :=
  ∃ Q : ConvexPolytope d, CombinatoriallyEquivalent P Q ∧ RationalCoordinates Q

end Papers.Polytopes

end
end
