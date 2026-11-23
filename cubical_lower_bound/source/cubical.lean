module

public import cubical.polytope.main
public import cubical.polytope.face_bounds
public import cubical.polytope.generic_theorems
public import cubical.polytope.stacking_sharpness_real
public import cubical.pl.homology_manifold

@[expose] public section

/-!
# Complete formalization of “The cubical lower bound theorem”

This entry point imports every principal mathematical claim of the paper:
Theorem 1.1, Lemma 2.1, Corollary 3.1, the strengthened face-number
formulas, the homology-manifold extension and stacked-cubical sharpness.

See `README.md` for the correspondence and `cubical.audit` for the
transitive axiom guards and machine-readable dependency graphs.
-/
