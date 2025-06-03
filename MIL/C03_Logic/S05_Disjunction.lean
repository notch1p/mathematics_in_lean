import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  match le_or_gt 0 x with
  | .inl h =>
    rw[abs_of_nonneg h]
  | .inr h =>
    rw[abs_of_neg h]
    linarith

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw[abs_of_nonneg h]
    linarith
  rw[abs_of_neg h]

theorem abs_add (x y: ℝ) : |x + y| ≤ |x| + |y| := by
  cases le_or_gt 0 (x + y) with
  | inl h =>
    rw[abs_of_nonneg h]
    have h₁ := le_abs_self x
    have h₂ := le_abs_self y
    by_contra c
    have : x + y <= |x| + |y| := add_le_add h₁ h₂
    apply c this
  | inr h =>
    rw[abs_of_neg h]
    have h₁ := neg_le_abs_self x
    have h₂ := neg_le_abs_self y
    have : -x - y ≤ |x| + |y| := add_le_add h₁ h₂
    rw[neg_add']; assumption

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  case mp =>
    intro h
    cases lt_or_ge y 0 with
    | inl h' =>
      right
      rw[abs_of_neg h'] at h
      exact h
    | inr h' =>
      left
      rw[abs_of_nonneg h'] at h
      exact h
  next =>
    intro h
    rcases h with h | h
    case inl =>
      cases le_or_gt 0 y with
      | inl h' => rw[abs_of_nonneg h']; exact h
      | inr h' => rw[abs_of_neg h']; linarith
    next =>
      cases le_or_gt 0 y with
      | inl h' => rw[abs_of_nonneg h']; linarith
      | inr h' => rw[abs_of_neg h']; exact h

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  rcases lt_or_ge x 0 with h | h
  case inl =>
    rw[abs_of_neg h]
    constructor <;> intro h'
    case mp => constructor <;> linarith
    case mpr => rcases h'; linarith
  case inr =>
    rw[abs_of_nonneg h]
    constructor <;> intro h'
    case mp => constructor <;> linarith
    next => exact h'.2

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, rfl | rfl⟩ <;> linarith[pow_two_nonneg x, pow_two_nonneg y]

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h : x ^ 2 - 1 = 0 := sub_eq_zero_of_eq h
  have : (1 : ℝ) = 1 ^ 2 := by ring
  rw[this, pow_two_sub_pow_two] at h
  have h := eq_zero_or_eq_zero_of_mul_eq_zero h
  rcases h with h | h
  right; symm
  apply neg_eq_of_add_eq_zero_left h
  left; apply sub_eq_zero.mp h



example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h : x ^ 2 - y ^ 2 = 0 := by rw[h]; ring
  rw[pow_two_sub_pow_two] at h
  have h := eq_zero_or_eq_zero_of_mul_eq_zero h
  cases h with
  | inl h => right; apply symm (neg_eq_of_add_eq_zero_left h)
  | inr h => left; apply sub_eq_zero.mp h

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)



example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h : x ^ 2 - 1 = 0 := sub_eq_zero_of_eq h
  have : (1 : R) = 1 ^ 2 := by ring
  rw[this, pow_two_sub_pow_two] at h
  have h := eq_zero_or_eq_zero_of_mul_eq_zero h
  rcases h with h | h
  right; symm
  apply neg_eq_of_add_eq_zero_left h
  left; apply sub_eq_zero.mp h

/- w/o commutativity -/
example {RR : Type*} {x : RR} [Ring RR] [IsDomain RR] (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h : x ^ 2 - 1 = 0 := sub_eq_zero_of_eq h
  have h' :=
  calc
    (x + 1) * (x - 1) = (x + 1) * x - (x + 1) := by rw[mul_sub, mul_one]
    _                 = (x + 1) * x - x - 1   := by rw[sub_sub]
    _                 = x * x + 1 * x - x - 1 := by rw[add_mul]
    _                 = x ^ 2 + x - x - 1     := by rw[<-pow_two, one_mul]
    _                 = x ^ 2 + (x - x) - 1   := by rw[<-add_sub]
    _                 = x ^ 2 + 0 - 1         := by rw[sub_self]
    _                 = x ^ 2 - 1             := by rw[add_zero]
    _                 = 0                     := h
  cases eq_zero_or_eq_zero_of_mul_eq_zero h' with
  | inl h => right; apply symm $ neg_eq_of_add_eq_zero_left h
  | inr h => left; apply sub_eq_zero.mp h

/- also provable as 1 is in the center of RR -/
example {RR : Type*} {x : RR} [Ring RR] [IsDomain RR] (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h : x ^ 2 - 1 = 0 := sub_eq_zero_of_eq h
  have h': x ^ 2 - 1 ^ 2 = 0 := by rw[one_pow]; assumption
  have : Commute x 1 := Commute.one_right x
  have : x ^ 2 - 1 ^ 2 = (x + 1) * (x - 1) := by
    apply Commute.sq_sub_sq; assumption
  have h : (x + 1) * (x - 1) = 0 := by rw[<-h']; symm; exact this
  have h := eq_zero_or_eq_zero_of_mul_eq_zero h
  cases h with
  | inl h => right; apply symm (neg_eq_of_add_eq_zero_left h)
  | inr h => left; apply sub_eq_zero.mp h

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h : x ^ 2 - y ^ 2 = 0 := by rw[h]; ring
  rw[pow_two_sub_pow_two] at h
  have h := eq_zero_or_eq_zero_of_mul_eq_zero h
  cases h with
  | inl h => right; apply symm (neg_eq_of_add_eq_zero_left h)
  | inr h => left; apply sub_eq_zero.mp h

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  intro h;
  by_cases h' : P
  case pos => right; apply h h'
  next => left; exact h'
  next =>
    intro h h'
    cases h with
    | inl h'' => exfalso; apply h'' h'
    | inr h'' => exact h''
