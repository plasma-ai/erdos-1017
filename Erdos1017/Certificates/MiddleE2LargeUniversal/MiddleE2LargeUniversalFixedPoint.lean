module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp

/-!
# Outward fixed-point interval arithmetic

Outward fixed-point interval arithmetic with integer endpoints at the
fixed scale `S = 1000·2^30`. A real `x` is enclosed by `⟨lo, hi⟩` when
`lo ≤ x·S ≤ hi`. Every operation rounds outward with integer floor and
ceiling divisions, so no rational normalization is evaluated.
-/

@[expose] public section

namespace Erdos1017.MiddleE2LargeUniversal.FixedPoint

/-- The fixed scale. -/
def S : ℤ := 1073741824000

theorem S_pos : (0 : ℤ) < S := by decide

theorem S_posR : (0 : ℝ) < (S : ℝ) := by exact_mod_cast S_pos

/-- An integer interval at scale `S`. -/
structure FI where
  lo : ℤ
  hi : ℤ

/-- Real enclosure at scale `S`. -/
def SMem (x : ℝ) (a : FI) : Prop := (a.lo : ℝ) ≤ x * S ∧ x * S ≤ (a.hi : ℝ)

/-- Floor division by a positive integer. -/
def fl (n d : ℤ) : ℤ := n / d

/-- Ceiling division by a positive integer. -/
def ce (n d : ℤ) : ℤ := -((-n) / d)

theorem fl_le {n d : ℤ} (hd : 0 < d) : ((fl n d : ℤ) : ℝ) ≤ (n : ℝ) / d := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [le_div_iff₀ hd']
  exact_mod_cast Int.ediv_mul_le n hd.ne'

theorem le_ce {n d : ℤ} (hd : 0 < d) : (n : ℝ) / d ≤ ((ce n d : ℤ) : ℝ) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [div_le_iff₀ hd']
  have h := Int.ediv_mul_le (-n) hd.ne'
  have h' : ((-n / d * d : ℤ) : ℝ) ≤ ((-n : ℤ) : ℝ) := by exact_mod_cast h
  unfold ce
  push_cast at h' ⊢
  linarith

theorem SMem.of_eq {x y : ℝ} {a : FI} (h : SMem x a) (e : x = y) : SMem y a := e ▸ h

theorem SMem.le {x : ℝ} {a : FI} (h : SMem x a) : a.lo ≤ a.hi := by
  have : (a.lo : ℝ) ≤ a.hi := h.1.trans h.2
  exact_mod_cast this

theorem SMem.neg_of_hi {x : ℝ} {a : FI} (h : SMem x a) (hc : a.hi < 0) : x < 0 := by
  have h1 : (a.hi : ℝ) < 0 := by exact_mod_cast hc
  have : x * S < 0 := h.2.trans_lt h1
  exact neg_of_mul_neg_left this S_posR.le

theorem SMem.pos_of_lo {x : ℝ} {a : FI} (h : SMem x a) (hc : 0 < a.lo) : 0 < x := by
  have h1 : (0 : ℝ) < a.lo := by exact_mod_cast hc
  have : 0 < x * S := h1.trans_le h.1
  exact pos_of_mul_pos_left this S_posR.le

theorem SMem.nonpos_of_hi {x : ℝ} {a : FI} (h : SMem x a) (hc : a.hi ≤ 0) : x ≤ 0 := by
  have h1 : (a.hi : ℝ) ≤ 0 := by exact_mod_cast hc
  have : x * S ≤ 0 := h.2.trans h1
  nlinarith [S_posR]

theorem SMem.hi_nonneg {x : ℝ} {a : FI} (h : SMem x a) (hx : 0 ≤ x) : (0 : ℝ) ≤ a.hi :=
  (mul_nonneg hx S_posR.le).trans h.2

/-! Operations. -/

/-- The exact point `Q / S`. -/
def fpt (Q : ℤ) : FI := ⟨Q, Q⟩

/-- The integer constant `k`. -/
def fint (k : ℤ) : FI := ⟨k * S, k * S⟩

/-- The rational constant `p / d`. -/
def frat (p d : ℤ) : FI := ⟨fl (p * S) d, ce (p * S) d⟩

def fadd (a b : FI) : FI := ⟨a.lo + b.lo, a.hi + b.hi⟩

def fsub (a b : FI) : FI := ⟨a.lo - b.hi, a.hi - b.lo⟩

/-- Exact multiplication by a natural number. -/
def fnsmul (n : ℕ) (a : FI) : FI := ⟨n * a.lo, n * a.hi⟩

/-- Outward division by a positive natural number. -/
def fdivn (a : FI) (n : ℕ) : FI := ⟨fl a.lo n, ce a.hi n⟩

def fmin (a b : FI) : FI := ⟨min a.lo b.lo, min a.hi b.hi⟩

def fmax (a b : FI) : FI := ⟨max a.lo b.lo, max a.hi b.hi⟩

def fmul (a b : FI) : FI :=
  ⟨fl (min (min (a.lo * b.lo) (a.lo * b.hi)) (min (a.hi * b.lo) (a.hi * b.hi))) S,
    ce (max (max (a.lo * b.lo) (a.lo * b.hi)) (max (a.hi * b.lo) (a.hi * b.hi))) S⟩

def fsq (a : FI) : FI :=
  if 0 ≤ a.lo then ⟨fl (a.lo * a.lo) S, ce (a.hi * a.hi) S⟩
  else if a.hi ≤ 0 then ⟨fl (a.hi * a.hi) S, ce (a.lo * a.lo) S⟩
  else ⟨0, ce (max (a.lo * a.lo) (a.hi * a.hi)) S⟩

/-- Reciprocal; used only after a positive lower endpoint. -/
def frecip (a : FI) : FI := ⟨fl (S * S) a.hi, ce (S * S) a.lo⟩

def fdiv (a b : FI) : FI := fmul a (frecip b)

/-- Structural Newton iteration `x ↦ ⌊(x + ⌊n / x⌋) / 2⌋` for the floor square root of
`n`, stopped when a step does not decrease `x`. Its output is never trusted. -/
def isqrtAux : ℕ → ℕ → ℕ → ℕ
  | 0, _, x => x
  | k + 1, n, x =>
    let y := Nat.div (Nat.add x (Nat.div n x)) 2
    cond (Nat.ble x y) x (isqrtAux k n y)

/-- Newton's method from `2^48` for the integer square root of a natural number below
`2^96`. -/
def isqrt (n : ℕ) : ℕ := isqrtAux 64 n (Nat.pow 2 48)

/-- Square-root enclosure; both endpoints are re-verified by squaring. -/
def fsqrt (a : FI) : FI :=
  let l : ℤ := isqrt (a.lo * S).toNat
  let h : ℤ := isqrt (a.hi * S).toNat + 1
  ⟨if 0 ≤ l ∧ l * l ≤ a.lo * S then l else 0,
    if 0 ≤ h ∧ a.hi * S ≤ h * h then h else max S a.hi⟩

/-! Soundness. -/

theorem mem_fpt (Q : ℤ) : SMem ((Q : ℝ) / S) (fpt Q) := by
  have := S_posR.ne'
  unfold SMem fpt
  dsimp only
  rw [div_mul_cancel₀ _ this]
  exact ⟨le_rfl, le_rfl⟩

theorem mem_fint (k : ℤ) : SMem (k : ℝ) (fint k) := by
  unfold SMem fint
  push_cast
  exact ⟨le_rfl, le_rfl⟩

theorem mem_frat (p d : ℤ) (hd : 0 < d) : SMem ((p : ℝ) / d) (frat p d) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have e : (p : ℝ) / d * S = ((p * S : ℤ) : ℝ) / d := by push_cast; ring
  unfold SMem frat
  dsimp only
  rw [e]
  exact ⟨fl_le hd, le_ce hd⟩

theorem mem_fadd {x y : ℝ} {a b : FI} (hx : SMem x a) (hy : SMem y b) :
    SMem (x + y) (fadd a b) := by
  unfold SMem fadd at *
  push_cast
  constructor <;> nlinarith [hx.1, hx.2, hy.1, hy.2]

theorem mem_fsub {x y : ℝ} {a b : FI} (hx : SMem x a) (hy : SMem y b) :
    SMem (x - y) (fsub a b) := by
  unfold SMem fsub at *
  push_cast
  constructor <;> nlinarith [hx.1, hx.2, hy.1, hy.2]

theorem mem_fnsmul (n : ℕ) {x : ℝ} {a : FI} (hx : SMem x a) :
    SMem ((n : ℝ) * x) (fnsmul n a) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  unfold SMem fnsmul at *
  push_cast
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hx.1 hn]
  · nlinarith [mul_le_mul_of_nonneg_left hx.2 hn]

theorem mem_fdivn {x : ℝ} {a : FI} (n : ℕ) (hn : 0 < n) (hx : SMem x a) :
    SMem (x / n) (fdivn a n) := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have e : x / n * S = x * S / ((n : ℤ) : ℝ) := by push_cast; ring
  unfold SMem fdivn
  dsimp only
  rw [e]
  constructor
  · exact (fl_le hn').trans (div_le_div_of_nonneg_right hx.1 hnR.le)
  · exact (div_le_div_of_nonneg_right hx.2 hnR.le).trans (le_ce hn')

theorem mem_fmin {x y : ℝ} {a b : FI} (hx : SMem x a) (hy : SMem y b) :
    SMem (min x y) (fmin a b) := by
  unfold SMem fmin at *
  push_cast
  rw [min_mul_of_nonneg _ _ S_posR.le]
  exact ⟨min_le_min hx.1 hy.1, min_le_min hx.2 hy.2⟩

theorem mem_fmax {x y : ℝ} {a b : FI} (hx : SMem x a) (hy : SMem y b) :
    SMem (max x y) (fmax a b) := by
  unfold SMem fmax at *
  push_cast
  rw [max_mul_of_nonneg _ _ S_posR.le]
  exact ⟨max_le_max hx.1 hy.1, max_le_max hx.2 hy.2⟩

/-- A bilinear product lies between its corner products. -/
theorem corner_bounds {X Y a1 a2 b1 b2 : ℝ} (hx1 : a1 ≤ X) (hx2 : X ≤ a2)
    (hy1 : b1 ≤ Y) (hy2 : Y ≤ b2) :
    min (min (a1 * b1) (a1 * b2)) (min (a2 * b1) (a2 * b2)) ≤ X * Y ∧
      X * Y ≤ max (max (a1 * b1) (a1 * b2)) (max (a2 * b1) (a2 * b2)) := by
  constructor
  · rcases le_total 0 Y with hy0 | hy0
    · have h1 : a1 * Y ≤ X * Y := mul_le_mul_of_nonneg_right hx1 hy0
      rcases le_total 0 a1 with ha0 | ha0
      · have h2 : a1 * b1 ≤ a1 * Y := mul_le_mul_of_nonneg_left hy1 ha0
        exact (min_le_left _ _).trans ((min_le_left _ _).trans (h2.trans h1))
      · have h2 : a1 * b2 ≤ a1 * Y := mul_le_mul_of_nonpos_left hy2 ha0
        exact (min_le_left _ _).trans ((min_le_right _ _).trans (h2.trans h1))
    · have h1 : a2 * Y ≤ X * Y := mul_le_mul_of_nonpos_right hx2 hy0
      rcases le_total 0 a2 with ha0 | ha0
      · have h2 : a2 * b1 ≤ a2 * Y := mul_le_mul_of_nonneg_left hy1 ha0
        exact (min_le_right _ _).trans ((min_le_left _ _).trans (h2.trans h1))
      · have h2 : a2 * b2 ≤ a2 * Y := mul_le_mul_of_nonpos_left hy2 ha0
        exact (min_le_right _ _).trans ((min_le_right _ _).trans (h2.trans h1))
  · rcases le_total 0 Y with hy0 | hy0
    · have h1 : X * Y ≤ a2 * Y := mul_le_mul_of_nonneg_right hx2 hy0
      rcases le_total 0 a2 with ha0 | ha0
      · have h2 : a2 * Y ≤ a2 * b2 := mul_le_mul_of_nonneg_left hy2 ha0
        exact (h1.trans h2).trans ((le_max_right _ _).trans (le_max_right _ _))
      · have h2 : a2 * Y ≤ a2 * b1 := mul_le_mul_of_nonpos_left hy1 ha0
        exact (h1.trans h2).trans ((le_max_left _ _).trans (le_max_right _ _))
    · have h1 : X * Y ≤ a1 * Y := mul_le_mul_of_nonpos_right hx1 hy0
      rcases le_total 0 a1 with ha0 | ha0
      · have h2 : a1 * Y ≤ a1 * b2 := mul_le_mul_of_nonneg_left hy2 ha0
        exact (h1.trans h2).trans ((le_max_right _ _).trans (le_max_left _ _))
      · have h2 : a1 * Y ≤ a1 * b1 := mul_le_mul_of_nonpos_left hy1 ha0
        exact (h1.trans h2).trans ((le_max_left _ _).trans (le_max_left _ _))

theorem mem_fmul {x y : ℝ} {a b : FI} (hx : SMem x a) (hy : SMem y b) :
    SMem (x * y) (fmul a b) := by
  have hS := S_posR
  obtain ⟨c1, c2⟩ := corner_bounds hx.1 hx.2 hy.1 hy.2
  have e : x * y * S = (x * S) * (y * S) / S := by field_simp
  unfold SMem fmul
  dsimp only
  rw [e]
  constructor
  · refine (fl_le S_pos).trans (div_le_div_of_nonneg_right ?_ hS.le)
    push_cast
    exact c1
  · refine (div_le_div_of_nonneg_right ?_ hS.le).trans (le_ce S_pos)
    push_cast
    exact c2

theorem mem_fsq {x : ℝ} {a : FI} (hx : SMem x a) : SMem (x ^ 2) (fsq a) := by
  have hS := S_posR
  obtain ⟨h1, h2⟩ := hx
  have e : x ^ 2 * S = (x * S) * (x * S) / S := by field_simp
  unfold SMem fsq
  rw [e]
  split_ifs with g1 g2
  · have g1' : (0 : ℝ) ≤ a.lo := by exact_mod_cast g1
    constructor
    · refine (fl_le S_pos).trans (div_le_div_of_nonneg_right ?_ hS.le)
      push_cast
      nlinarith
    · refine (div_le_div_of_nonneg_right ?_ hS.le).trans (le_ce S_pos)
      push_cast
      nlinarith
  · have g2' : (a.hi : ℝ) ≤ 0 := by exact_mod_cast g2
    constructor
    · refine (fl_le S_pos).trans (div_le_div_of_nonneg_right ?_ hS.le)
      push_cast
      nlinarith
    · refine (div_le_div_of_nonneg_right ?_ hS.le).trans (le_ce S_pos)
      push_cast
      nlinarith
  · constructor
    · push_cast
      exact div_nonneg (mul_self_nonneg _) hS.le
    · refine (div_le_div_of_nonneg_right ?_ hS.le).trans (le_ce S_pos)
      push_cast
      rcases le_total 0 (x * S) with h0 | h0
      · exact le_trans (by nlinarith) (le_max_right _ _)
      · exact le_trans (by nlinarith) (le_max_left _ _)

theorem mem_frecip {y : ℝ} {b : FI} (hy : SMem y b) (hb : 0 < b.lo) :
    SMem (1 / y) (frecip b) := by
  have hS := S_posR
  have hb' : (0 : ℝ) < b.lo := by exact_mod_cast hb
  have hY : 0 < y * S := hb'.trans_le hy.1
  have hbh : (0 : ℤ) < b.hi := by
    have : (0 : ℝ) < b.hi := hY.trans_le hy.2
    exact_mod_cast this
  have e : 1 / y * S = ((S * S : ℤ) : ℝ) / (y * S) := by
    have : y ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hY; exact lt_irrefl _ hY
    push_cast
    field_simp
  unfold SMem frecip
  dsimp only
  rw [e]
  have hSS : (0 : ℝ) ≤ ((S * S : ℤ) : ℝ) := by push_cast; positivity
  constructor
  · exact (fl_le hbh).trans (div_le_div_of_nonneg_left hSS hY hy.2)
  · exact (div_le_div_of_nonneg_left hSS hb' hy.1).trans (le_ce hb)

theorem mem_fdiv {x y : ℝ} {a b : FI} (hx : SMem x a) (hy : SMem y b) (hb : 0 < b.lo) :
    SMem (x / y) (fdiv a b) := by
  rw [div_eq_mul_one_div]
  exact mem_fmul hx (mem_frecip hy hb)

theorem mem_fsqrt {x : ℝ} {a : FI} (hx : SMem x a) : SMem (Real.sqrt x) (fsqrt a) := by
  have hS := S_posR
  obtain ⟨h1, h2⟩ := hx
  -- `√x · S = √(x S · S)`.
  have e : Real.sqrt x * S = Real.sqrt (x * S * S) := by
    rw [mul_assoc, Real.sqrt_mul' _ (mul_self_nonneg _), Real.sqrt_mul_self hS.le]
  unfold SMem fsqrt
  dsimp only
  rw [e]
  constructor
  · split_ifs with g
    · obtain ⟨g0, gsq⟩ := g
      set l : ℤ := (isqrt (a.lo * S).toNat : ℤ)
      have g0' : (0 : ℝ) ≤ l := by exact_mod_cast g0
      have gsq' : (l : ℝ) * l ≤ a.lo * S := by exact_mod_cast gsq
      rw [← Real.sqrt_mul_self g0']
      exact Real.sqrt_le_sqrt (gsq'.trans (mul_le_mul_of_nonneg_right h1 hS.le))
    · push_cast
      exact Real.sqrt_nonneg _
  · split_ifs with g
    · obtain ⟨g0, gsq⟩ := g
      set h : ℤ := (isqrt (a.hi * S).toNat : ℤ) + 1
      have g0' : (0 : ℝ) ≤ h := by exact_mod_cast g0
      have gsq' : (a.hi : ℝ) * S ≤ h * h := by exact_mod_cast gsq
      rw [← Real.sqrt_mul_self g0']
      exact Real.sqrt_le_sqrt ((mul_le_mul_of_nonneg_right h2 hS.le).trans gsq')
    · push_cast
      rcases le_total x 1 with hx1 | hx1
      · -- `√x · S ≤ S`.
        rw [← e]
        have : Real.sqrt x ≤ 1 := Real.sqrt_le_one.mpr hx1
        exact (mul_le_of_le_one_left hS.le this).trans (le_max_left _ _)
      · rw [← e]
        have hxx : x ≤ x * x := by nlinarith
        have : Real.sqrt x ≤ x :=
          (Real.sqrt_le_sqrt hxx).trans_eq (Real.sqrt_mul_self (by linarith))
        exact ((mul_le_mul_of_nonneg_right this hS.le).trans h2).trans (le_max_right _ _)

end Erdos1017.MiddleE2LargeUniversal.FixedPoint
