module
public import Framework.PolytopeTargets

@[expose] public section

/-!
# Rational coordinates as coordinates in an actual real subfield

The subfield is the image of the usual rational embedding. Thus the
existential rational-coordinate definition and the arbitrary-subfield
realizability definition agree literally at this subfield.
-/

noncomputable section
namespace Papers.Polytopes
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

def rationalSubfield : Subfield ℝ := (Rat.castHom ℝ).fieldRange

@[simp] theorem mem_rationalSubfield (x : ℝ) :
    x ∈ rationalSubfield ↔ ∃ q : ℚ, (q : ℝ) = x := Iff.rfl

theorem rationalCoordinates_iff_coordinatesIn {d : ℕ} (P : ConvexPolytope d) :
    RationalCoordinates P ↔ CoordinatesIn rationalSubfield P := Iff.rfl

theorem rationallyRealizable_iff_realizableOver {d : ℕ} (P : ConvexPolytope d) :
    RationallyRealizable P ↔ RealizableOver P rationalSubfield := Iff.rfl

end Papers.Polytopes

end
end
