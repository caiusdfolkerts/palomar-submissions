module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Order.Fin.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Tactic

/-! # Sphere cohomology of a finite order complex

A simplex is a strictly ascending chain. The coboundary is the alternating
sum over deletions. In degree zero the cohomology is the space of functions
on components. Over a field these cohomology dimensions are the homology
dimensions of the same finite complex. -/

@[expose] public section

noncomputable section
namespace Cubical.PL.OrderCohomology

variable (k P : Type*) [Field k] [PartialOrder P]

def comparableGraph : SimpleGraph P where
  Adj a b := a < b ∨ b < a
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => h.elim (lt_irrefl _) (lt_irrefl _)⟩

abbrev Simplex (q : ℕ) := Fin (q + 1) ↪o P
abbrev Cochain (q : ℕ) := Simplex P q → k

def coboundary (q : ℕ) : Cochain k P q →ₗ[k] Cochain k P (q+1) where
  toFun f s := ∑ i : Fin (q+2), (-1 : k)^i.val * f ((Fin.succAboveOrderEmb i).trans s)
  map_add' f g := by ext; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by ext; simp [Finset.mul_sum, mul_left_comm]

/-- Ordinary cohomology of a sphere, including the two components of the
zero-sphere. Positive non-top degrees impose exactness of the ordinary
simplicial cochain complex. -/
structure IsSphere (n : ℕ) : Prop where
  zero : Module.finrank k ((comparableGraph P).ConnectedComponent → k) =
    if n = 0 then 2 else 1
  exact : ∀ q : ℕ, q + 1 ≠ n →
    LinearMap.ker (coboundary k P (q+1)) ≤ LinearMap.range (coboundary k P q)
  top : ∀ q : ℕ, q + 1 = n →
    Module.finrank k (LinearMap.ker (coboundary k P (q+1))) =
    Module.finrank k (LinearMap.range (coboundary k P q)) + 1

variable {k P}

section
variable [Finite P]

theorem IsSphere.components {n : ℕ} (h : IsSphere k P n) :
    Nat.card (comparableGraph P).ConnectedComponent = if n = 0 then 2 else 1 := by
  classical
  let _ := Fintype.ofFinite (comparableGraph P).ConnectedComponent
  simpa only [Module.finrank_pi, Nat.card_eq_fintype_card] using h.zero

theorem IsSphere.preconnected {n : ℕ} (h : IsSphere k P n) (hn : n ≠ 0) :
    (comparableGraph P).Preconnected := by
  classical
  let G := comparableGraph P
  let _ := Fintype.ofFinite G.ConnectedComponent
  have one : Fintype.card G.ConnectedComponent = 1 := by
    simpa [Nat.card_eq_fintype_card, hn, G] using h.components
  obtain ⟨t, ht⟩ := Fintype.card_eq_one_iff.mp one
  exact fun a b => SimpleGraph.ConnectedComponent.exact
    ((ht (G.connectedComponentMk a)).trans (ht (G.connectedComponentMk b)).symm)

theorem IsSphere.card_of_discrete (h : IsSphere k P 0)
    (hd : ∀ a b : P, ¬ a < b) : Nat.card P = 2 := by
  classical
  let G := comparableGraph P
  have hempty : G = ⊥ := by
    ext a b
    change (a < b ∨ b < a) ↔ False
    simp [hd]
  have hc := h.components
  change Nat.card G.ConnectedComponent = 2 at hc
  rw [hempty] at hc
  let B := (⊥ : SimpleGraph P)
  let e : P ≃ B.ConnectedComponent := Equiv.ofBijective B.connectedComponentMk
    ⟨fun _ _ eq => SimpleGraph.reachable_bot.mp (SimpleGraph.ConnectedComponent.exact eq),
      fun c => c.exists_rep⟩
  exact (Nat.card_congr e).trans hc

end

private def point (a : P) : Simplex P 0 :=
  OrderEmbedding.ofStrictMono (fun _ : Fin 1 => a) (by intro i j hij; omega)

private def interval (a b : P) (h : a < b) : Simplex P 1 :=
  OrderEmbedding.ofStrictMono ![a,b] (by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all)

/-- In dimension at least two, every additive edge cocycle on the order
complex of a homology sphere over the two-element field has a potential. -/
theorem IsSphere.exactOneModTwo {n : ℕ} (h : IsSphere (ZMod 2) P n) (hn : 2 ≤ n)
    (e : P → P → ZMod 2) (hrefl : ∀ a, e a a = 0)
    (htriangle : ∀ a b c : P, a < b → b < c → e a b + e b c = e a c) :
    ∃ f : P → ZMod 2, ∀ a b, a ≤ b → e a b = f a + f b := by
  let z : Cochain (ZMod 2) P 1 := fun s => e (s 0) (s 1)
  have hz : z ∈ LinearMap.ker (coboundary (ZMod 2) P 1) := by
    apply LinearMap.mem_ker.mpr
    funext s
    have ht := htriangle (s 0) (s 1) (s 2) (s.strictMono (by decide)) (s.strictMono (by decide))
    have neg : (-1 : ZMod 2) = 1 := by decide
    simp only [coboundary, LinearMap.coe_mk, AddHom.coe_mk,
      neg, one_pow, one_mul, Pi.zero_apply]
    change (∑ i : Fin 3, z ((Fin.succAboveOrderEmb i).trans s)) = 0
    rw [Fin.sum_univ_three]
    change e (s 1) (s 2) + e (s 0) (s 2) + e (s 0) (s 1) = 0
    rw [← ht]
    ring_nf
    simp [show (2 : ZMod 2) = 0 by decide]
  obtain ⟨g, hg⟩ := h.exact 0 (by omega) hz
  refine ⟨fun a => g (point a), fun a b hab => ?_⟩
  rcases hab.eq_or_lt with rfl | hlt
  · rw [hrefl, CharTwo.add_self_eq_zero]
  · let s := interval a b hlt
    have lhs : (Fin.succAboveOrderEmb (0 : Fin 2)).trans s = point b := by
      ext i; fin_cases i; rfl
    have rhs : (Fin.succAboveOrderEmb (1 : Fin 2)).trans s = point a := by
      ext i; fin_cases i; rfl
    have he := congrFun hg s
    simp only [coboundary, LinearMap.coe_mk, AddHom.coe_mk,
      show (-1 : ZMod 2) = 1 by decide, one_pow, one_mul] at he
    change (∑ i : Fin 2, g ((Fin.succAboveOrderEmb i).trans s)) = e a b at he
    rw [Fin.sum_univ_two, lhs, rhs] at he
    exact he.symm.trans (add_comm _ _)

end Cubical.PL.OrderCohomology
