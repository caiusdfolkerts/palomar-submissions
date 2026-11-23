module

public import cubical.pl.manifold_links

@[expose] public section

/-! # The homology-manifold extension of the cubical lower bound

For a face of dimension r in a pure m-dimensional cubical complex, the
order complex of its strict cofaces triangulates its normal link. The
closed homology-manifold condition asks that these links have the
homology of spheres of dimension m-r-1 over the chosen field.
-/

noncomputable section
namespace Cubical.PL.CubeComplex
open Cubical.PL.OrderCohomology Cubical.Bipartite

variable {V : Type*} [Fintype V] [DecidableEq V] (K : CubeComplex V)

/-- Finite pure cubical homology manifold without boundary. A facet has
empty normal link by purity, so only positive codimensions occur below. -/
structure IsClosedHomologyManifold (k : Type*) [Field k] (m : ℕ) : Prop where
  pure : ∀ R : K.Cell, ∃ F : K.Facet m, R ≤ F.val
  link : ∀ R : K.Cell, K.dimension R.val < m →
    OrderCohomology.IsSphere k (K.Cofaces R) (m - K.dimension R.val - 1)

variable {K} {k : Type*} [Field k] {m : ℕ}

theorem IsClosedHomologyManifold.normalIncidence (h : K.IsClosedHomologyManifold k m)
    (hc : (comparableGraph K.Cell).Connected) : K.NormalIncidence m := by
  refine ⟨h.pure, hc, fun R hd => ?_, fun R hd => ?_⟩
  · exact (h.link R (by omega)).preconnected (by omega)
  · have hzero : m - K.dimension R.val - 1 = 0 := by omega
    have hs := h.link R (by omega)
    rw [hzero] at hs
    apply hs.card_of_discrete
    intro a b hab
    obtain ⟨F, hF⟩ := h.pure b.val
    have hmax := (K.dimension_mono _ _ hF).trans_eq F.property
    have ha := K.dimension_lt_of_lt _ _ a.property
    have hb := K.dimension_lt_of_lt _ _ (show a.val < b.val from hab)
    omega

/-- Equation (3.1) on every finite connected closed cubical homology
manifold over a field, for each bipartition of its original graph. -/
theorem IsClosedHomologyManifold.strengthened_edge_bound {d : ℕ} (hd : 4 ≤ d)
    (h : K.IsClosedHomologyManifold k (d - 1)) (hc : (comparableGraph K.Cell).Connected)
    (c : K.graph.Coloring Bool) :
    ((d : ℝ) + 1) / 2 * K.faceNumber 0 - 2 ^ (d - 1) + ((d : ℝ) - 1) / 2 *
      |(Fintype.card (Black c) : ℝ) - Fintype.card (White c)| ≤ K.faceNumber 1 :=
  (h.normalIncidence hc).strengthened_edge_bound d hd c

/-- A cubical homology sphere has the local link homology of a closed
manifold and the global homology of the sphere in its own dimension. -/
structure IsHomologySphere (K : CubeComplex V) (k : Type*) [Field k] (m : ℕ) : Prop
    extends K.IsClosedHomologyManifold k m where
  globalCohomology : OrderCohomology.IsSphere k K.Cell m

theorem IsHomologySphere.exists_coloring (h : K.IsHomologySphere (ZMod 2) m) (hm : 2 ≤ m) :
    Nonempty (K.graph.Coloring Bool) := by
  have tri (A B C : K.Cell) (hab : A < B) (hbc : B < C) :
      K.edgeParity A B + K.edgeParity B C = K.edgeParity A C := by
    apply K.edgeParity_triangle
    refine ⟨by simp, ?_⟩
    intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first | exact Or.inl le_rfl | exact Or.inl hab.le | exact Or.inr hab.le |
        exact Or.inl hbc.le | exact Or.inr hbc.le | exact Or.inl (hab.le.trans hbc.le) |
        exact Or.inr (hab.le.trans hbc.le)
  obtain ⟨f, hf⟩ := h.globalCohomology.exactOneModTwo hm K.edgeParity K.edgeParity_self tri
  obtain ⟨c, hc⟩ := K.bipartite_of_parityPotential f hf
  exact ⟨SimpleGraph.Coloring.mk c (fun {v w} hvw => hc v w hvw)⟩

/-- For a mod-two homology sphere the coloring exists and (3.1) holds
for every coloring. -/
theorem IsHomologySphere.strengthened_edge_bound {d : ℕ} (hd : 4 ≤ d)
    (h : K.IsHomologySphere (ZMod 2) (d - 1)) :
    Nonempty (K.graph.Coloring Bool) ∧ ∀ c : K.graph.Coloring Bool,
      ((d : ℝ) + 1) / 2 * K.faceNumber 0 - 2 ^ (d - 1) + ((d : ℝ) - 1) / 2 *
        |(Fintype.card (Black c) : ℝ) - Fintype.card (White c)| ≤ K.faceNumber 1 := by
  classical
  have hn : d - 1 ≠ 0 := by omega
  have hcard : Nat.card (comparableGraph K.Cell).ConnectedComponent = 1 := by
    simpa [hn] using h.globalCohomology.components
  have hpos : 0 < Nat.card (comparableGraph K.Cell).ConnectedComponent := by omega
  obtain ⟨t⟩ := (Nat.card_pos_iff.mp hpos).1
  obtain ⟨R, _⟩ := t.exists_rep
  let _ : Nonempty K.Cell := ⟨R⟩
  exact ⟨h.exists_coloring (by omega), fun c =>
    h.toIsClosedHomologyManifold.strengthened_edge_bound hd
      ⟨h.globalCohomology.preconnected hn⟩ c⟩

end Cubical.PL.CubeComplex
