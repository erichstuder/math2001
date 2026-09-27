/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {x y : ℝ} (h : x = 1 ∨ y = -1) : x * y + x = y + 1 := by
  obtain hx | hy := h
  calc
    x * y + x = 1 * y + 1 := by rw [hx]
    _ = y + 1 := by ring
  calc
    x * y + x = x * -1 + x := by rw [hy]
    _ = -1 + 1 := by ring
    _ = y + 1 := by rw [hy]

example {n : ℕ} : n ^ 2 ≠ 2 := by
  have hn := le_or_succ_le n 1
  obtain ha | hb := hn
  apply ne_of_lt
  calc
    n ^ 2 ≤ 1 ^ 2 := by rel [ha]
    _ < 2 := by numbers
  apply ne_of_gt
  calc
    2 < 2 ^ 2 := by numbers
    _ ≤ n ^ 2 := by rel [hb]


example {x : ℝ} (hx : 2 * x + 1 = 5) : x = 1 ∨ x = 2 := by
  right
  calc
    x = (2 * x + 1 - 1) / 2 := by ring
    _ = (5 - 1) / 2 := by rw [hx]
    _ = 2 := by numbers


example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
  have h1 :=
    calc
    (x - 1) * (x - 2) = x ^ 2 - 3 * x + 2 := by ring
    _ = 0 := by rw [hx]
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  obtain ha | hb := h2
  left
  addarith [ha]
  right
  addarith [hb]


example {n : ℤ} : n ^ 2 ≠ 2 := by
  have hn0 := le_or_succ_le n 0
  obtain hn0 | hn0 := hn0
  · have : 0 ≤ -n := by addarith [hn0]
    have hn := le_or_succ_le (-n) 1
    obtain hn | hn := hn
    · apply ne_of_lt
      calc
        n ^ 2 = (-n) ^ 2 := by ring
        _ ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
    · apply ne_of_gt
      calc
        (2:ℤ) < 2 ^ 2 := by numbers
        _ ≤ (-n) ^ 2 := by rel [hn]
        _ = n ^ 2 := by ring
  · have hn := le_or_succ_le n 1
    obtain hn | hn := hn
    · apply ne_of_lt
      calc
        n ^ 2 ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
    · apply ne_of_gt
      calc
        (2:ℤ) < 2 ^ 2 := by numbers
        _ ≤ n ^ 2 := by rel [hn]


/-! # Exercises -/


example {x : ℚ} (h : x = 4 ∨ x = -4) : x ^ 2 + 1 = 17 := by
  obtain h1 | h2 := h
  calc
    x^2 + 1
      = 4^2 + 1 := by rw [h1]
    _ = 17 := by ring
  calc
    x^2 + 1
      = (-4)^2 + 1 := by rw [h2]
    _ = 17 := by ring


example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  obtain h1 | h2 := h
  calc
    x^2 - 3*x + 2
      = 1^2 - 3*1 + 2 := by rw [h1]
    _ = 0 := by ring
  calc
    x^2 - 3*x + 2
      = 2^2 - 3*2 + 2 := by rw [h2]
    _ = 0 := by ring


example {t : ℚ} (h : t = -2 ∨ t = 3) : t ^ 2 - t - 6 = 0 := by
  obtain h1 | h2 := h
  calc
    t^2 - t - 6
      = (-2)^2 - (-2) - 6 := by rw [h1]
    _ = 0 := by ring
  calc
    t^2 - t - 6
      = 3^2 - 3 - 6 := by rw [h2]
    _ = 0 := by ring


example {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by
  obtain h1 | h2 := h
  calc
    x*y + 2*x
      = 2*y + 2*2 := by rw [h1]
    _ = 2*y + 4 := by ring
  calc
    x*y + 2*x
    _ = x*(-2) + 2*x := by rw [h2]
    _ = 0 := by ring
    _ = 2*(-2) + 4 := by ring
    _ = 2*y + 4 := by rw [h2]


example {s t : ℚ} (h : s = 3 - t) : s + t = 3 ∨ s + t = 5 := by
  left
  calc
    s + t
      = 3 - t + t := by rw [h]
    _ = 3 := by ring


example {a b : ℚ} (h : a + 2 * b < 0) : b < a / 2 ∨ b < - a / 2 := by
  right
  calc
    b = (a + 2*b)/2 - a/2 := by ring
    _ < 0/2 - a/2 := by rel [h]
    _ = -a/2 := by ring


example {x y : ℝ} (h : y = 2 * x + 1) : x < y / 2 ∨ x > y / 2 := by
  left
  addarith [h]


example {x : ℝ} (hx : x ^ 2 + 2 * x - 3 = 0) : x = -3 ∨ x = 1 := by
  have h1 : (x + 3) * (x - 1) = 0 := by
    calc
      (x + 3) * (x - 1)
        = x^2 + 2*x - 3 := by ring
      _ = 0 := by rw [hx]
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  obtain ha | hb := h2
  left
  addarith [ha]
  right
  addarith [hb]


example {a b : ℝ} (hab : a ^ 2 + 2 * b ^ 2 = 3 * a * b) : a = b ∨ a = 2 * b := by
  have h1 : (a - b)*(a - 2*b) = 0 := by
    calc
      (a - b)*(a - 2*b)
        = a^2 + 2*b^2 - 3*a*b := by ring
      _ = 3*a*b - 3*a*b := by rw [hab]
      _ = 0 := by ring
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  obtain ha | hb := h2
  left
  addarith [ha]
  right
  addarith [hb]


example {t : ℝ} (ht : t ^ 3 = t ^ 2) : t = 1 ∨ t = 0 := by
  have h1 : (t-1)*t^2 = 0 := by
    calc
      (t-1)*t^2
        = t^3 - t^2 := by ring
      _ = t^2 - t^2 := by rw [ht]
      _ = 0 := by ring
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  obtain ha | hb := h2
  left
  addarith [ha]
  right
  cancel 2 at hb


example {n : ℕ} : n ^ 2 ≠ 7 := by
  have hn := le_or_succ_le n 2
  obtain ha | hb := hn
  apply ne_of_lt
  calc
    n^2
      <= 2^2 := by rel [ha]
    _ < 7 := by  numbers
  apply ne_of_gt
  calc
    7 < 3^2 := by numbers
    _ <= n^2 := by rel [hb]


example {x : ℤ} : 2 * x ≠ 3 := by
  have hn := le_or_succ_le x 1
  obtain ha | hb := hn
  apply ne_of_lt
  calc
    2*x
      <= 2*1 := by rel [ha]
    _ < 3 := by numbers
  apply ne_of_gt
  calc
    3 < 2*2 := by numbers
    _ <= 2*x := by rel [hb]


example {t : ℤ} : 5 * t ≠ 18 := by
  have hn := le_or_succ_le t 3
  obtain ha | hb := hn
  apply ne_of_lt
  calc
    5*t
      <= 5*3 := by rel [ha]
    _ < 18 := by numbers
  apply ne_of_gt
  calc
    18
      < 5*4 := by numbers
    _ <= 5*t := by rel [hb]


example {m : ℕ} : m ^ 2 + 4 * m ≠ 46 := by
  have hn := le_or_succ_le m 5
  obtain ha | hb := hn
  apply ne_of_lt
  calc
    m^2 + 4*m
      <= 5^2 + 4*5 := by rel [ha]
    _ < 46 := by numbers
  apply ne_of_gt
  calc
    46
      < 6^2 + 4*6 := by numbers
    _ <= m^2 + 4*m := by rel [hb]
