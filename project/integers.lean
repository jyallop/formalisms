import Mathlib.Init.Data.Int.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Init.Data.Int.DivModLemmas
import Mathlib.Data.Int.Defs

open Int
/-
def series : Nat -> Nat
| 0 => 0
| n@(succ x) => n ^ 2 + series x

theorem div_dist : (n m o: Nat) → (n + m) / o = n / o + m / o := by sorry

theorem add_mul_same : (n m o: Nat) → (n * m) + (o * m) = (n + o) * m := sorry

theorem div_mul_dist : (n m o : Nat) → n * m / o = (n / o) * m
| 0, m, o => by simp
| succ n, m, o => by sorry

theorem add_div_same : (n m o : Nat) → n / o + m / o = (n + m) / o :=
  by sorry

theorem mul_id : (n x : Nat) → n ≠ 0 → x = n * x / n := by
  sorry

lemma six_lemma : 6 ≠ 0 := by
  simp

lemma two_lemma : 2 = 12 / 6 := by simp

lemma helper_limit_one : (n : Nat) → 6 ∣  n * (n + 1) * (2 * n + 1)
| 0 => by simp
| (succ n) => by
  simp
  ring
  sorry

theorem limit_one : (n : Nat) → (series n) = n * (n + 1) * (2 * n + 1) / 6
| 0 => rfl
| succ n =>
  calc
    series (n + 1) = ((n + 1) ^ 2) + series n := rfl
    _ = ((n + 1) ^ 2) + n * (n + 1) * (2 * n + 1) / 6 := by
      rw [(limit_one n)]
    _ = n ^ 2 + 2 * n + 1 + n * (n + 1) * (2 * n + 1) / 6 := by
      ring
    _ = n ^ 2 + 2 * n + 1 + n * (2 * n ^ 2 + 3 * n + 1) / 6 := by
      ring_nf
    _ = n ^ 2 + 2 * n + 1 + (2 * n ^ 3 + 3 * n ^ 2 + n) / 6 := by
      ring_nf
    _ = n ^ 2 + 2 * n + 1 + (2 * n ^ 3) / 6 + (3 * n ^ 2) / 6 + n / 6 := by
      rw [div_dist, div_dist, ← add_assoc, ← add_assoc]
    _ = (3 * n ^ 2) / 6 + n ^ 2 + 2 * n + 1 + (2 * n ^ 3) / 6  + n / 6 := by
      rw [add_comm (n ^ 2 + 2 * n + 1 + (2 * n ^ 3) / 6) ((3 * n ^ 2) / 6), ← add_assoc, ← add_assoc, ← add_assoc]
    _ = (3 * n ^ 2 / 6) + (6 * n ^ 2 / 6) + (12 * n / 6) + (6 / 6) + (2 * n ^ 3 / 6) + (n / 6) := by
      simp
      rw [div_mul_dist]
    _ = (9 * n ^ 2 / 6) + (12 * n / 6) + (6 / 6) + (2 * n ^ 3 / 6) + (n / 6) := by
      rw [add_div_same, add_mul_same]
    _ = (9 * n ^ 2 / 6) + (n / 6) + (12 * n / 6) + (6 / 6) + (2 * n ^ 3 / 6) := by
      rw [add_comm, ← add_assoc, ← add_assoc, ← add_assoc]
      simp
      rw [add_comm]
    _ = (9 * n ^ 2 / 6) + (13 * n / 6) + (6 / 6) + (2 * n ^ 3 / 6) := by
      rw [add_assoc (9 * n ^ 2 / 6) (n / 6) (12 * n / 6), add_div_same n (12 * n) 6]
      simp
      ring_nf
    _ = (2 * n ^ 3 / 6) + (9 * n ^ 2 / 6) + (13 * n / 6) + (6 / 6) := by
      rw [add_comm, ← add_assoc, ← add_assoc]
    _ = (n + 1) * (n + 2) * (2 * n + 3) / 6 := by
      simp
      ring_nf
      rw [← add_div_same, ← add_div_same, ← add_div_same]
      ring

def series_two : Nat -> Nat
| 0 => 0
| n@(succ x) =>  8 * n - 5 + series_two x

lemma add_sub_assoc_loc : (k m n : ℕ) →  n - m + k = n + k - m
| 0, _, _ => by rfl
| succ k, m, n => by
  simp
  ring_nf
  sorry

lemma nat_le_mul_left : (a b c : ℕ) → a ≤ c → 0 < b → a ≤ b * c := by sorry
lemma nat_mul_sub_left_dist : (a b c : ℕ) → a * b - a * c = a * (b - c) := sorry
lemma sub_dist : (a b c : ℕ) → a - (b + c) = a - b - c := sorry
lemma sub_add_comm_loc  (a b c : ℕ) : a + b - c = a - c + b := sorry
lemma add_sub_dist (a b c : ℕ) : a + b - c = a + (b - c) := sorry

theorem limit_two : (n : Nat) → (series_two n) = 4 * n ^ 2 - n
| 0 => by
  rfl
| succ n => by
  calc
    series_two (n + 1) = 8 * (n + 1) - 5 + series_two n := by
      rfl
    _ = 8 * (n + 1) - 5 + (4 * n ^ 2 - n) := by
      rw [limit_two]
    _ = 8 * n + 3 + (4 * n ^ 2 - n) := by
      rw [mul_add]
      rfl
    _ = 4 * n ^ 2 - n + 8 * n + 3 := by
      rw [add_comm, ← add_assoc]
    _ = 4 * n ^ 2 + 7 * n + 3 := by
      rw [add_sub_assoc_loc (8 * n) n (4 * n ^ 2)]
      nth_rewrite 3 [← mul_one n]
      rw [mul_comm 8 n, add_sub_dist, nat_mul_sub_left_dist n 8 1]
      simp
      apply mul_comm
    _ = 4 * (n + 1) ^ 2 - (n + 1) := by
      ring_nf
      rw [add_assoc 4, sub_dist, sub_add_comm_loc 4 (n * 8 + n ^ 2 * 4) 1]
      ring_nf
      rw [add_assoc 3 (n * 8), sub_add_comm_loc, ← add_assoc, add_sub_assoc_loc]
      nth_rewrite 4 [← mul_one n]
      rw [add_sub_dist, nat_mul_sub_left_dist]
      simp

-/
def succ_ge_zero : (x : Int) → (0 ≤ Int.succ x) → (0 ≤ x) := by sorry

def sum_nat : Nat → Nat
| 0 => 0
| Nat.succ n => Nat.succ n + sum_nat n

def sum : Int -> Int
| 0 => 0
| ofNat (Nat.succ n) => ofNat (sum_nat (Nat.succ n))
| negSucc n => ofNat (sum_nat (Nat.succ n))

lemma sum_helper : (n : Int) → sum (n + 1) = sum n + (n + 1)
| 0 => by
  unfold sum
  simp
  unfold sum_nat
  unfold sum_nat
  simp
| ofNat (Nat.succ n) => by
  simp
  rw [sum_helper n, sum_helper (n + 1)]
  simp
  apply sum_helper
| negSucc n => by
  rw [sum_helper]

lemma mul_div_id : ∀ (a : ℤ) (b : ℤ), b ≠ 0 → a * b / b = a := by sorry

theorem basic : (n : Int) → (h: 0 ≤ n) → (sum n) = n * (n + 1) / 2
| 0, h => by
  unfold sum
  simp
| ofNat (Nat.succ n), h => by
  calc
    sum (n + 1) = sum n + (n + 1) := by
      apply sum_helper
    _ = n * (n + 1) / 2 + (n + 1) := by
      simp
      rw [basic n]
      apply (succ_ge_zero n h)
    _ = (n * (n + 1) + 2 * (n + 1)) / 2 := by
      ring_nf
      rw [← (mul_div_id (1 + n) 2), ← Int.add_ediv_of_dvd_left]
      ring_nf
      apply Int.dvd_mul_left
      simp
    _ = (n + 1) * (n + 2) / 2 := by
      ring_nf
    _ = ofNat n.succ * (ofNat n.succ + 1) / 2 := by
      simp
      ring_nf
| Int.negSucc n, h => by
  contradiction


def series_three : Int → Int
| 0 => 0
| n@(succ x) => n ^ 3 + series_three x



theorem exercise_three : (n : Int) → (series_three n) = (sum n) ^ 2
| 0 => by rfl
| succ n => by
  unfold sum
  unfold series_three
  simp
  rw [exercise_three]
  ring_nf

def series_four : Nat → Nat
| 0 => 0
| n@(succ x) => (2 * n - 1) + series_four x

theorem exercise_four : (n : Nat) → series_four n = n ^ 2
| 0 => by rfl
| succ n => by sorry

theorem exercise_six : (n : Nat) → 7 ∣ 11 ^ n - 4 ^ n
| 0 => by simp
| succ n => by
  simp
  ring_nf
