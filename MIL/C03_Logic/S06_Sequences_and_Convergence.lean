import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n maxN
  have hs := hs n <| le_of_max_le_left maxN
  have ht := ht n <| le_of_max_le_right maxN
  have hst := add_lt_add hs ht
  have : ε / 2 + ε / 2 = ε := by norm_num
  rw[this] at hst
  have h_eq := sub_add_sub_comm (s n) a (t n) b
  rcases abs_add (s n - a) (t n - b) |>.eq_or_lt with h
                                                    | h
                                                    <;> rw[h_eq] at h;
  case h.inl =>
    rw[h]; assumption
  next =>
    convert lt_trans h _
    assumption

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  dsimp[ConvergesTo] at *;
  intro ε eh;
  rcases (cs (ε / |c|) (div_pos eh acpos)) with ⟨N, Nh⟩
  use N
  intro n nh
  have Nh := Nh n nh
  rw[<-mul_sub, abs_mul]
  have : |c| * |s n - a| < |c| * (ε / |c|) := mul_lt_mul_left acpos |>.mpr Nh
  calc
    |c| * |s n - a| < |c| * (ε / |c|) := this
    _ = ε := by rw[mul_div_cancel₀ ε (ne_of_gt acpos)]


theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n nh
  have h := h n nh
  apply sub_lt_sub_iff_right |a| |>.mp
  simp
  convert lt_of_le_of_lt (_ : |s n| - |a| <= |s n - a|) h
  apply le_of_sq_le_sq _ (abs_nonneg _)
  rw[(by rw[sq_abs]; ring : |s n - a|^2 = (s n)^2 - 2 * (s n) * a + a ^ 2)]
  rw[(by rw[sub_sq, sq_abs, sq_abs] : (|s n| - |a|)^2 = (s n) ^ 2 - 2 * |s n| * |a| + a^2)]
  repeat apply add_le_add
  case h₁.h₁ | h₂ => rfl
  simp
  repeat rw[mul_assoc]
  apply mul_le_mul_left (by norm_num : (0 : ℝ) < 2) |>.mpr
  rw[<-abs_mul]
  apply le_abs_self

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n nh
  have h₀ := h₀ n (le_of_max_le_left nh)
  have h₁ := h₁ n (le_of_max_le_right nh)
  have h01 := mul_lt_mul'' h₀ h₁ (abs_nonneg _) (abs_nonneg _)
  rw[mul_div_cancel₀ ε (ne_of_gt Bpos)] at h01
  simp at *; rw[abs_mul]; assumption

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by
    push_neg at abne;
    apply lt_of_le_of_ne <| abs_nonneg _;
    apply Ne.symm <| abs_ne_zero.mpr <| sub_ne_zero.mpr abne
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by
    exact hNa N (le_max_left _ _)
  have absb : |s N - b| < ε := by
    exact hNb N (le_max_right _ _)
  have : |a - b| < |a - b| := by
    simp[ε] at absa absb
    have hi := add_lt_add absa absb
    simp at hi
    calc |a - b|
      _ =  |a - s N + (s N - b)|     := by congr 1; ring
      _ <= |a - s N| + |s N - b|     := abs_add (a - s N) (s N - b)
      _ =  |s N - a| + |s N - b|     := by simp; apply abs_sub_comm
      _ <  |a - b|                   := hi
  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
