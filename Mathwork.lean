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
    -- rw [calc
    --         (sin A / cos A + sin B / cos B) / (1 - sin A / cos A * (sin B / cos B)) = (sin A / cos A + sin B / cos B) / (1 - sin A / cos A * (sin B / cos B)) * 1 := by ring_nf
    --         _ = (sin A / cos A + sin B / cos B) / (1 - sin A / cos A * (sin B / cos B)) * ((cos A * cos B) / (cos A * cos B)) := by rw [←div_self (mul_ne_zero ha hb)]
    --         _ = (sin A / cos A + sin B / cos B) * (cos A * cos B) / ((1 - sin A / cos A * (sin B / cos B)) * (cos A * cos B)) := by rw [div_mul_div_comm]
    --         _ = (((sin A / cos A) * cos A) * cos B + ((sin B / cos B) *  cos B) * cos A) / ((1 - sin A / cos A  * cos A * ((sin B / cos B) * cos B))) := by sorry
    --     ]
    field_simp
    ring
    


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
            _     = - ((tan A + tan B)/((1: ℝ) - tan A * tan B)) := by rw [tan_add _ _ ha hb]
    
    have s3 : tan C * ((1: ℝ) - tan A * tan B) = - (tan A + tan B) := by
        rw [s2, neg_mul ((tan A + tan B) / (1 - tan A * tan B)) (1 - tan A * tan B)]
        rw [mul_comm_div, div_self]
        simp
        apply_fun λ x: ℝ => x * cos A * cos B
        ring_nf
        repeat rw [tan_eq_sin_div_cos]
        ring_nf
        rw [calc
            sin A * cos A * (cos A)⁻¹  * sin B * cos B * (cos B)⁻¹ = sin A * (cos A * (cos A)⁻¹)  * sin B * (cos B * (cos B)⁻¹) := by ring_nf 
            _ = sin A * 1 * sin B * 1 := by rw [mul_inv_cancel ha, mul_inv_cancel hb],
            calc
            -(sin A * 1 * sin B * 1) + cos A * cos B = cos A * cos B - sin A * sin B := by ring_nf,
            ←cos_add
            ]
        apply_fun λ x: ℝ => - cos x at s1
        rw [cos_pi_sub] at s1
        simp at s1
        rw [←s1, neg_ne_zero]
        assumption
    ring_nf at s3
    apply_fun λ x: ℝ => x + tan C * tan A * tan B + tan A + tan B at s3
    ring_nf at s3
    rw [calc tan C + tan A + tan B = tan A + tan B + tan C := by ring_nf] at s3
    rw [s3]
    ring_nf
    exact trivial