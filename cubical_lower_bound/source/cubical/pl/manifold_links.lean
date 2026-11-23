module

public import cubical.pl.lower_bound
public import cubical.pl.order_cohomology
public import cubical.indexed_pseudomanifold
public import cubical.simplicial_ridge_count

@[expose] public section

/-! # Cubical complexes with connected links

The local information used in the edge bound is the number of connected
components of the link of each non-facet. Its barycentric subdivision is
the order complex of the strict cofaces. -/

noncomputable section
namespace Cubical.PL.CubeComplex
open Classical Cubical.Simplicial Cubical.PL.OrderCohomology
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] (K : CubeComplex V)

abbrev Cofaces (R : K.Cell) := {S : K.Cell // R < S}

structure NormalIncidence (m : ℕ) : Prop where
  pure : ∀ R : K.Cell, ∃ F : K.Facet m, R ≤ F.val
  connected : (comparableGraph K.Cell).Connected
  linkConnected : ∀ R : K.Cell, K.dimension R.val + 1 < m →
    (comparableGraph (K.Cofaces R)).Preconnected
  ridgeCard : ∀ R : K.Cell, K.dimension R.val + 1 = m → Nat.card (K.Cofaces R) = 2

variable {K} {m : ℕ}

private theorem gallery_of_comparables {P F : Type*} [PartialOrder P]
    (hc : (comparableGraph P).Preconnected) (chosen : P → F)
    (r : F → F → Prop) (h : ∀ a b : P, a ≤ b → Relation.ReflTransGen r (chosen a) (chosen b))
    (h' : ∀ a b : P, a ≤ b → Relation.ReflTransGen r (chosen b) (chosen a))
    (a b : P) : Relation.ReflTransGen r (chosen a) (chosen b) := by
  obtain ⟨w⟩ := hc a b
  induction w with
  | nil => exact .refl
  | @cons x y z e w ih =>
    rcases e with e | e
    · exact (h x y e.le).trans ih
    · exact (h' y x e.le).trans ih

/-- Gallery steps in the star keep the intervening ridge in that star. -/
def starStep (K : CubeComplex V) (m : ℕ) (R : K.Cell) (F G : K.Facet m) : Prop :=
  ∃ S : K.Cell, R ≤ S ∧ S ≤ F.val ∧ S ≤ G.val ∧ K.dimension S.val + 1 = m

theorem NormalIncidence.starGallery (hK : K.NormalIncidence m) (R : K.Cell)
    (F G : K.Facet m) (hF : R ≤ F.val) (hG : R ≤ G.val) :
    Relation.ReflTransGen (K.starStep m R) F G := by
  classical
  have dimle (S : K.Cell) : K.dimension S.val ≤ m := by
    obtain ⟨T, hT⟩ := hK.pure S
    exact (K.dimension_mono S T.val hT).trans_eq T.property
  by_cases htop : K.dimension R.val = m
  · have hRF := (K.dimension_eq_iff_eq R F.val hF).mp (htop.trans F.property.symm)
    have hRG := (K.dimension_eq_iff_eq R G.val hG).mp (htop.trans G.property.symm)
    exact (Subtype.ext (hRF.symm.trans hRG) : F = G) ▸ Relation.ReflTransGen.refl
  by_cases hridge : K.dimension R.val + 1 = m
  · exact .single ⟨R, le_rfl, hF, hG, hridge⟩
  have hsmall : K.dimension R.val + 1 < m := by have := dimle R; omega
  let pick (S : K.Cofaces R) := (hK.pure S.val).choose
  have hpick (S : K.Cofaces R) : S.val ≤ (pick S).val := (hK.pure S.val).choose_spec
  have liftGallery (S : K.Cofaces R) (A B : K.Facet m) (ha : S.val ≤ A.val)
      (hb : S.val ≤ B.val) : Relation.ReflTransGen (K.starStep m R) A B := by
    have hs := hK.starGallery S.val A B ha hb
    exact Relation.ReflTransGen.mono (fun X Y ⟨T, hST, hTX, hTY, hd⟩ =>
      ⟨T, S.property.le.trans hST, hTX, hTY, hd⟩) _ _ hs
  let a : K.Cofaces R := ⟨F.val, lt_of_le_of_ne hF (fun he =>
    htop ((congrArg (fun X : K.Cell => K.dimension X.val) he).trans F.property))⟩
  let b : K.Cofaces R := ⟨G.val, lt_of_le_of_ne hG (fun he =>
    htop ((congrArg (fun X : K.Cell => K.dimension X.val) he).trans G.property))⟩
  exact (liftGallery a F (pick a) le_rfl (hpick a)).trans
    ((gallery_of_comparables (hK.linkConnected R hsmall) pick (K.starStep m R)
      (fun x y hxy => liftGallery x _ _ (hpick x) ((show x.val ≤ y.val from hxy).trans (hpick y)))
      (fun x y hxy => liftGallery x _ _ ((show x.val ≤ y.val from hxy).trans (hpick y)) (hpick x)) a b).trans
      (liftGallery b (pick b) G (hpick b) le_rfl))
termination_by m - K.dimension R.val
decreasing_by
  have := K.dimension_lt_of_lt R S.val S.property
  have := dimle S.val
  omega

theorem NormalIncidence.connectedFacetCover (hK : K.NormalIncidence m) :
    K.ConnectedFacetCover m := by
  refine ⟨fun v => ?_, fun F G => ?_⟩
  · obtain ⟨F, hF⟩ := hK.pure (K.vertexCell v)
    exact ⟨F, (K.vertexCell_le_iff v F.val).mp hF⟩
  · let pick (S : K.Cell) := (hK.pure S).choose
    have hpick (S : K.Cell) : S ≤ (pick S).val := (hK.pure S).choose_spec
    have star (S : K.Cell) (A B : K.Facet m) (ha : S ≤ A.val) (hb : S ≤ B.val) :
        Relation.ReflTransGen (K.facetStep m) A B :=
      Relation.ReflTransGen.mono
        (fun _ _ ⟨T, _, hA, hB, hd⟩ => ⟨T, hA, hB, hd⟩) _ _ (hK.starGallery S A B ha hb)
    exact (star F.val F (pick F.val) le_rfl (hpick _)).trans
      ((gallery_of_comparables hK.connected.preconnected pick (K.facetStep m)
        (fun x y h => star x _ _ (hpick x) (h.trans (hpick y)))
        (fun x y h => star x _ _ (h.trans (hpick y)) (hpick x)) F.val G.val).trans
        (star G.val (pick G.val) G (hpick _) le_rfl))

private abbrev LinkFacet (K : CubeComplex V) (m : ℕ) (v : V) :=
  {F : K.Facet m // v ∈ F.val.val}

private def linkFacet (K : CubeComplex V) (m : ℕ) (v : V) (F : LinkFacet K m v) :=
  K.neighborSimplex F.val.val v

private theorem linkFacet_card (v : V) (F : LinkFacet K m v) :
    (linkFacet K m v F).card = m :=
  (K.neighborSimplex_card _ _ F.property).trans F.val.property

private theorem linkFacet_contains (hK : K.NormalIncidence m) (v : V)
    (s : Finset (K.Neighbor v)) (hs : s ∈ (K.neighborComplex v).faces) :
    ∃ F : LinkFacet K m v, s ⊆ linkFacet K m v F := by
  obtain ⟨_, S, hv, rfl⟩ := hs
  obtain ⟨F, hF⟩ := hK.pure S
  exact ⟨⟨F, hF hv⟩, K.neighborSimplex_mono hF v⟩

private theorem linkFacet_mem (v : V) (F : LinkFacet K m v) (hm : 0 < m) :
    linkFacet K m v F ∈ (K.neighborComplex v).faces :=
  ⟨Finset.card_pos.mp ((linkFacet_card v F).symm ▸ hm), F.val.val, F.property, rfl⟩

private theorem coface_dimension (hK : K.NormalIncidence m) {R : K.Cell}
    (hr : K.dimension R.val + 1 = m) (S : K.Cofaces R) : K.dimension S.val.val = m := by
  obtain ⟨F, hF⟩ := hK.pure S.val
  have hle := (K.dimension_mono _ _ hF).trans_eq F.property
  have hlt := K.dimension_lt_of_lt _ _ S.property
  omega

private theorem linkFacet_ridgePairing (hK : K.NormalIncidence m) (v : V) (hm : 3 ≤ m) :
    RidgePairing (linkFacet K m v) := by
  intro i r hr
  obtain ⟨hsub, hcard⟩ := mem_simplexBoundary_iff.mp hr
  rw [linkFacet_card] at hcard
  have hface := ((K.neighborComplex v).isRelLowerSet_faces
    (linkFacet_mem v i (by omega))).2 hsub (Finset.card_pos.mp (by omega))
  let R := K.simplexCell v r
  obtain ⟨hv, heq, _⟩ := K.simplexCell_spec v hface
  have hR : K.dimension R.val + 1 = m := by
    rwa [← K.neighborSimplex_card R v hv, heq]
  have mem_iff (F : LinkFacet K m v) :
      r ∈ simplexBoundary (linkFacet K m v F) ↔ R < F.val.val := by
    rw [mem_simplexBoundary_iff, linkFacet_card, and_iff_left hcard, ← heq]
    change K.neighborSimplex R v ⊆ K.neighborSimplex F.val.val v ↔ _
    rw [K.neighborSimplex_subset_iff R F.val.val v hv F.property]
    refine ⟨fun h => lt_of_le_of_ne h ?_, le_of_lt⟩
    intro e
    have := congrArg (fun T : K.Cell => K.dimension T.val) e
    have := F.val.property
    omega
  let toFacet (S : K.Cofaces R) : LinkFacet K m v :=
    ⟨⟨S.val, coface_dimension hK hR S⟩, S.property.le hv⟩
  let a : K.Cofaces R := ⟨i.val.val, (mem_iff i).mp hr⟩
  classical
  have htwo : (Finset.univ : Finset (K.Cofaces R)).card = 2 := by
    simpa only [Finset.card_univ, Nat.card_eq_fintype_card] using hK.ridgeCard R hR
  obtain ⟨x, y, hxy, he⟩ := Finset.card_eq_two.mp htwo
  have cases' (s : K.Cofaces R) : s = x ∨ s = y := by
    have : s ∈ ({x,y} : Finset _) := he ▸ Finset.mem_univ s
    simpa using this
  obtain ⟨b, hab, hall⟩ : ∃ b : K.Cofaces R, a ≠ b ∧ ∀ s, s = a ∨ s = b := by
    rcases cases' a with eq | eq
    · exact ⟨y, eq ▸ hxy, fun s => eq ▸ cases' s⟩
    · exact ⟨x, eq ▸ hxy.symm, fun s => eq ▸ (cases' s).symm⟩
  refine ⟨toFacet b, fun h => hab (Subtype.ext (congrArg (fun T : LinkFacet K m v => T.val.val) h)), ?_⟩
  intro k
  rw [mem_iff]
  constructor
  · intro hk
    rcases hall ⟨k.val.val, hk⟩ with e | e
    · exact Or.inl (Subtype.ext (Subtype.ext (congrArg (fun t : K.Cofaces R => t.val) e)))
    · exact Or.inr (Subtype.ext (Subtype.ext (congrArg (fun t : K.Cofaces R => t.val) e)))
  · rintro (rfl | rfl)
    · exact a.property
    · exact b.property

private theorem linkFacet_connected (hK : K.NormalIncidence m) (v : V) :
    (indexedFacetGraph (linkFacet K m v)).Connected := by
  classical
  let R := K.vertexCell v
  obtain ⟨base, hbase⟩ := hK.pure R
  let _ : Nonempty (LinkFacet K m v) := ⟨⟨base, (K.vertexCell_le_iff v base.val).mp hbase⟩⟩
  refine ⟨fun i j => ?_⟩
  let G := indexedFacetGraph (linkFacet K m v)
  have lift {F : K.Facet m} (h : Relation.ReflTransGen (K.starStep m R) i.val F) :
      ∀ hv : v ∈ F.val.val, G.Reachable i ⟨F,hv⟩ := by
    induction h with
    | refl => intro _; exact .refl _
    | @tail A B prev step ih =>
      intro hB
      obtain ⟨T, hRT, hA, hTB, hd⟩ := step
      have hvT := (K.vertexCell_le_iff v T).mp hRT
      let a : LinkFacet K m v := ⟨A, hA hvT⟩
      let b : LinkFacet K m v := ⟨B, hB⟩
      have ha : G.Reachable i a := ih _
      by_cases eq : a = b
      · rw [eq] at ha
        exact ha
      have ridge (k : LinkFacet K m v) (hk : T ≤ k.val.val) :
          K.neighborSimplex T v ∈ simplexBoundary (linkFacet K m v k) :=
        mem_simplexBoundary_iff.mpr ⟨K.neighborSimplex_mono hk v, by
          rw [K.neighborSimplex_card T v hvT, linkFacet_card]; exact hd⟩
      exact ha.trans (SimpleGraph.Adj.reachable (G := G)
        (show G.Adj a b from ⟨eq, _, ridge a hA, ridge b hTB⟩))
  exact lift (hK.starGallery R i.val j.val ((K.vertexCell_le_iff _ _).mpr i.property)
    ((K.vertexCell_le_iff _ _).mpr j.property)) j.property

theorem NormalIncidence.linkRigid (hK : K.NormalIncidence m) (v : V) (hm : 3 ≤ m) :
    Cubical.Rigidity.GenericallyRigid (K.neighborGraph v) (EuclideanSpace ℝ (Fin m)) := by
  classical
  let σ := linkFacet K m v
  have used (a : K.Neighbor v) : a ∈ vertices σ Finset.univ := by
    obtain ⟨F, hF⟩ := linkFacet_contains hK v _ (K.singleton_mem_neighborComplex v a)
    exact (mem_vertices _ _ _).mpr ⟨F, Finset.mem_univ _, hF (Finset.mem_singleton_self _)⟩
  let e : supportGraph σ Finset.univ ≃g K.neighborGraph v := {
    toEquiv := { toFun := Subtype.val, invFun := fun a => ⟨a, used a⟩,
                 left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    map_rel_iff' := by
      intro a b
      simp only [supportGraph, SimpleGraph.induce_adj, oneSkeleton_adj]
      constructor
      · rintro ⟨hne, hf⟩
        obtain ⟨F, hF⟩ := linkFacet_contains hK v _ hf
        exact ⟨hne, F, Finset.mem_univ _, hF (by simp), hF (by simp)⟩
      · rintro ⟨hne, F, _, ha, hb⟩
        exact ⟨hne, ((K.neighborComplex v).isRelLowerSet_faces
          (linkFacet_mem v F (by omega))).2 (Finset.insert_subset_iff.mpr
            ⟨ha, Finset.singleton_subset_iff.mpr hb⟩) (by simp)⟩ }
  have hc := facetCircuit_of_ridgePairing_connected
    (linkFacet_ridgePairing hK v hm) (linkFacet_connected hK v)
  exact (hc.genericallyRigid (E := EuclideanSpace ℝ (Fin m)) hm
    (fun F _ => linkFacet_card v F) (by simp)).of_iso e

/-- The cubical lower bound holds on every finite bipartite normal cubical
pseudomanifold, including the absolute color-class correction. -/
theorem NormalIncidence.strengthened_edge_bound (d : ℕ) (hd : 4 ≤ d)
    (hK : K.NormalIncidence (d - 1)) (c : K.graph.Coloring Bool) :
    ((d : ℝ) + 1) / 2 * K.faceNumber 0 - 2 ^ (d - 1) + ((d : ℝ) - 1) / 2 *
      |(Fintype.card (Cubical.Bipartite.Black c) : ℝ) -
        Fintype.card (Cubical.Bipartite.White c)| ≤ K.faceNumber 1 := by
  obtain ⟨R⟩ := hK.connected.nonempty
  obtain ⟨F, _⟩ := hK.pure R
  exact K.strengthened_edge_bound_of_rigid_links d hd hK.connectedFacetCover ⟨F⟩
    (fun v => hK.linkRigid v (by omega)) c

end Cubical.PL.CubeComplex
