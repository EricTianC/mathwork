import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.LibrarySearch

open Real

-- example (A: ℝ) : sin (A)*sin (A) = 1 - cos (A) *cos (A) := by
--     library_search


example (a b c : ℤ) (h: a - b = c): a = b + c := by
    apply_fun λ x: ℤ => x + b at h
    ring_nf at h
    assumption


theorem sin_sq_minus_sq (A B : ℝ) : sin (A + B) * sin (A - B) = sin (A)*sin (A) - sin (B)*sin (B) := by
    rw [sin_add, sin_sub]
    ring_nf
    rw [cos_sq', cos_sq']
    ring_nf


theorem tan_add (A B: ℝ) (ha: cos A ≠ 0) (hb: cos B ≠ 0): tan (A + B) = (tan A + tan B)/((1: ℝ) - tan A * tan B) := by
    simp [tan_eq_sin_div_cos]
    rw [sin_add, cos_add]
    field_simp
    ring
    


theorem tri_tan_sum_eq_mul (A B C : ℝ) (h: A + B + C = π) (ha: cos A ≠ 0) (hb: cos B ≠ 0) (hc: cos C ≠ 0):
    tan A + tan B + tan C = tan A * tan B * tan C := by
    have s1 : C = π - (A + B) 
        := by simp [←h]
    have s2 : tan C = - ((tan A + tan B)/((1: ℝ) - tan A * tan B)) 
        := by simp [s1, tan_pi_sub]; refine (tan_add A B ha hb)
    have s3 : (1: ℝ) - tan A * tan B ≠ 0
        := by field_simp [tan_eq_sin_div_cos, ←cos_add]; rw [←neg_eq_zero, ←cos_pi_sub (A + B), ←s1]; assumption
    have s4 : tan C * ((1: ℝ) - tan A * tan B) = - (tan A + tan B) := by
        field_simp [s2]
    ring_nf at s4
    apply_fun λ x: ℝ => x + tan C * tan A * tan B + tan A + tan B at s4
    ring_nf at s4
    rw [calc tan C + tan A + tan B = tan A + tan B + tan C := by ring_nf] at s4
    rw [s4]
    ring_nf
    exact trivial