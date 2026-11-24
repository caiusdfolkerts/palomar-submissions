# A nonrational four-polytope with fifteen vertices

Lean formalization of Caius Folkerts’ paper, using Lean 4.35.0 and the mathlib revision pinned in `lake-manifest.json`.

`Papers.Nonrational.Fifteen.theoremOne` constructs a full-dimensional convex polytope in real four-space with exactly fifteen extreme vertices. For every subfield K of the reals, an isomorphic face lattice has a realization with vertex coordinates in K precisely when √5 belongs to K. The separate theorem `not_rationallyRealizable` rules out rational coordinates.

## Build

With Elan installed, run these commands in this directory.

```sh
lake exe cache get
lake build
```

To inspect the exact theorem statement and its transitive axioms, open `Fifteen.lean` in Lean or run

```sh
printf '%s\n' 'import Fifteen' '#print Papers.Nonrational.Fifteen.theoremOne' '#print axioms Papers.Nonrational.Fifteen.theoremOne' | lake env lean --stdin
```

## Proof map

| Paper | Lean source |
| --- | --- |
| Section 2, rectangle normalization, uniqueness of the positive solution and realizability over K | [Perles](Fifteen/Perles.lean) |
| Core lifts, planar and lifted relations, heights, projected rays, and their conversion to the certificate coordinates | [Paper coordinates](Fifteen/PaperCoordinates.lean) |
| Six-vertex core and its nine tetrahedral facets | [Core](Fifteen/Core.lean) |
| Fifteen extreme vertices and realization over each field containing √5 | [Hull](Fifteen/Hull.lean) |
| Seven polygons and five facets, with their precise vertex sets and dimensions | [Incidences](Fifteen/Incidences.lean), [face certificates](Fifteen/FaceCertificate.lean), [faces](Fifteen/Faces.lean) |
| Proposition 2, coordinate sections and the projection edge | [Projection](Fifteen/Projection.lean) |
| Passing to arbitrary face-lattice realizations over K | [Construction](Fifteen/Construction.lean) |
| Recovering the Perles equations from the transported faces | [Reconstruction](Fifteen/Reconstruction.lean) |
| Theorem 1 and the nonrationality corollary | [Main theorem](Fifteen.lean) |

Vertex indices follow A, B, C, D, E, F, U, V, X₀, X₁, X₂, Y₁, Y₂, Z₁, Z₂. Face rows follow AB, DE, AF, BD, BE, CF, AC, x, y, z, u, v.

The construction uses the paper’s trisection points. Pairs of integers encode coefficients in the basis 1, φ with φ = (1 + √5)/2. Ordinary Lean kernel reduction verifies supplied supporting forms, exact zero sets, one small nonzero minor per named face, and spanning identities. The converse works symbolically. A field-linear form that vanishes at three vertices of a polygon vanishes throughout its homogeneous span. Applying this fact to the seven polygons gives r = s + 1 and sr = 1.

The geometric foundations in `Framework/` and `Cubical/` are adapted from the existing small nonrational four-polytopes formalization. The finite hull, face-poset transport, field embedding, and quadratic certificate proofs are reused. See [the notices](NOTICE) and [third-party provenance](THIRD_PARTY.md).

Manuscript checked against `nonrational_four_polytope_current (3).pdf`, SHA-256 `2d3d58742a9453c52dedf9d08293ff35a4a7fc213f07a4b25b1b084aa6e915b6`.
