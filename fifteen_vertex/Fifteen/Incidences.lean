module
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.Finset.Basic
@[expose] public section
namespace Papers.Nonrational.FifteenRankData
/-- Column order A,B,C,D,E,F,U,V,X₀,X₁,X₂,Y₁,Y₂,Z₁,Z₂.
Rows are AB, DE, AF, BD, BE, CF, AC, x, y, z, u, v. -/
def faceVertices : Fin 12 → Finset (Fin 15) :=
  ![{0, 1, 11, 12}, {3, 4, 11, 12}, {0, 5, 13, 14}, {1, 3, 13, 14}, {1, 4, 9, 10}, {2, 4, 5, 6}, {0, 2, 3, 7, 8}, {2, 6, 7, 11, 12, 13, 14}, {6, 7, 8, 9, 10, 13, 14}, {5, 6, 7, 8, 9, 10, 11, 12}, {0, 1, 3, 4, 11, 12}, {0, 1, 3, 5, 13, 14}]
end Papers.Nonrational.FifteenRankData
