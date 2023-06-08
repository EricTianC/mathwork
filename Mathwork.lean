import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.LibrarySearch

open Real

-- example (A: ℝ) : sin (A)*sin (A) = 1 - cos (A) *cos (A) := by
--     library_search

example (a b c : ℕ) (h: a - b = c): a = b + c := by
    apply_fun λ x: ℕ => x + b at h
    ring_nf at h
    apply Eq.symm
    rw [←h, sub_eq_add_neg]

theorem sin_sq_minus_sq (A B : ℝ) : sin (A + B) * sin (A - B) = sin (A)*sin (A) - sin (B)*sin (B) := by
    rw [sin_add, sin_sub]
    ring_nf
    apply Eq.symm
    rw [cos_sq', cos_sq']
    ring_nf

theorem tan_add (A B: ℝ) : tan (A + B) = (tan A + tan B)/((1: ℝ) - tan A * tan B) := by
    sorry

theorem tri_tan_sum_eq_mul (A B C : ℝ) (h: A + B + C = π) (ha: cos A ≠ 0) (hb: cos B ≠ 0) (hc: cos C ≠ 0):
    tan A + tan B + tan C = tan A * tan B * tan C := by
    have s1 :=
        calc
            C = A + B + C - A - B := by ring
            _ = π - A - B := by rw [h]
            _ = π - (A + B) := by ring

    have s2 := 
        calc
            tan C = - tan (A + B) := by rw [s1, tan_pi_sub]
            _     = - ((tan A + tan B)/((1: ℝ) - tan A * tan B)) := by rw [tan_add]
    
    have s3 : tan C * ((1: ℝ) - tan A * tan B) = - (tan A + tan B) := by
        rw [s2, neg_mul ((tan A + tan B) / (1 - tan A * tan B)) (1 - tan A * tan B)]
        rw [mul_comm_div, div_self]
        simp
        sorry
    ring_nf at s3
    generalize_proofs
