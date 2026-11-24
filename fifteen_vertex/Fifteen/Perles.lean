module
public import Fifteen.Arithmetic
@[expose] public section
noncomputable section
namespace Papers.Nonrational.Perles

/-- In the chart with X,Y at infinity and Z at the origin, write C=(0,c)
and F=(f:g:0). A,B,D,E are finite. These eight scalar equalities are
precisely the incidences (1), allowing coincident input points. -/
structure Configuration (K : Type*) [Field K] where
  c : K
  f : K
  g : K
  ax : K
  ay : K
  bx : K
  byCoord : K
  dx : K
  dy : K
  ex : K
  ey : K
  c_ne : c ≠ 0
  f_ne : f ≠ 0
  g_ne : g ≠ 0
  ac : ay = c
  dc : dy = c
  ab : bx = ax
  de : ex = dx
  be : ey = byCoord
  af : ax * g = ay * f
  cf : ex * g = (ey - c) * f
  bd : bx * dy = byCoord * dx

variable {K : Type*} [Field K]

theorem rectangle (P : Configuration K) :
    ∃ s r : K, P.dx = s * P.ax ∧ P.byCoord = r * P.c ∧
      r = s + 1 ∧ s*r = 1 := by
  have ha := P.af
  have hc := P.cf
  have hb := P.bd
  rw [P.ac] at ha
  rw [P.de, P.be] at hc
  rw [P.ab, P.dc] at hb
  have hax : P.ax ≠ 0 := by
    intro h
    rw [h, zero_mul] at ha
    exact mul_ne_zero P.c_ne P.f_ne ha.symm
  have hcross : (P.dx*P.c - (P.byCoord-P.c)*P.ax)*P.f = 0 := by
    linear_combination P.ax * hc - P.dx * ha
  have he := (mul_eq_zero.mp hcross).resolve_right P.f_ne
  refine ⟨P.dx/P.ax, P.byCoord/P.c, (div_mul_cancel₀ _ hax).symm,
    (div_mul_cancel₀ _ P.c_ne).symm, ?_, ?_⟩
  · field_simp [P.c_ne,hax]
    linear_combination -he
  · field_simp [P.c_ne,hax]
    linear_combination -hb

/-- Positivity in the bounded triangle selects the positive conjugate. -/
theorem positive_rectangle (P : Configuration ℝ) (ha : 0 < P.ax) (hd : 0 < P.dx) :
    P.dx / P.ax = (Real.sqrt 5 - 1)/2 ∧ P.byCoord / P.c = (Real.sqrt 5 + 1)/2 := by
  obtain ⟨s,r,hx,hy,e,prod⟩ := rectangle P
  have hs : P.dx/P.ax = s := (div_eq_iff ha.ne').mpr hx
  have hr : P.byCoord/P.c = r := (div_eq_iff P.c_ne).mpr hy
  have hpos : 0 < s := hs ▸ div_pos hd ha
  rw [e] at prod
  have square : (2*s+1)^2 = (Real.sqrt 5)^2 := by
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)]
    linear_combination 4 * prod
  have root := (sq_eq_sq_iff_eq_or_eq_neg.mp square).resolve_right
    (by linarith [Real.sqrt_nonneg (5:ℝ)])
  rw [hs,hr]
  constructor <;> linarith

theorem field_iff (K : Subfield ℝ) : Nonempty (Configuration K) ↔ Real.sqrt 5 ∈ K := by
  constructor
  · rintro ⟨P⟩
    obtain ⟨s, r, _, _, hr, hp⟩ := rectangle P
    rw [hr] at hp
    have h : (s : ℝ) * ((s : ℝ) + 1) = 1 := by exact_mod_cast hp
    have he : (2*(s : ℝ)+1)^2 = (Real.sqrt 5)^2 := by
      rw [Real.sq_sqrt (by norm_num : 0 ≤ (5 : ℝ))]
      linear_combination 4*h
    have hm : 2*(s : ℝ)+1 ∈ K := K.add_mem (K.mul_mem (by norm_num) s.property) K.one_mem
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with e | e
    · rwa [e] at hm
    · simpa [e] using K.neg_mem hm
  · intro h
    let t : K := ⟨(Real.sqrt 5 - 1)/2, K.div_mem (K.sub_mem h K.one_mem) (by norm_num)⟩
    have ht : (1+t)*t = 1 := by
      apply Subtype.ext
      change (1 + (Real.sqrt 5 - 1)/2)*((Real.sqrt 5 - 1)/2) = 1
      nlinarith [Real.sq_sqrt (by norm_num : 0 ≤ (5 : ℝ))]
    exact ⟨⟨1,1,1,1,1,1,1+t,t,1,t,1+t,one_ne_zero,one_ne_zero,one_ne_zero,
      rfl,rfl,rfl,rfl,rfl,rfl,by ring,by simpa using ht.symm⟩⟩

end Papers.Nonrational.Perles
