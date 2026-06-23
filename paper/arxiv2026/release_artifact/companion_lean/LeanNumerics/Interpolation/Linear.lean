import Mathlib.Tactic

namespace LeanNumerics
namespace Interpolation

noncomputable section

def affineInterp (θ y0 y1 : ℝ) : ℝ :=
  (1 - θ) * y0 + θ * y1

def linearInterp (x0 x1 y0 y1 x : ℝ) : ℝ :=
  ((x1 - x) / (x1 - x0)) * y0 + ((x - x0) / (x1 - x0)) * y1

theorem affineInterp_left (y0 y1 : ℝ) :
    affineInterp 0 y0 y1 = y0 := by
  unfold affineInterp
  ring

theorem affineInterp_right (y0 y1 : ℝ) :
    affineInterp 1 y0 y1 = y1 := by
  unfold affineInterp
  ring

theorem affineInterp_weights_sum (θ : ℝ) :
    (1 - θ) + θ = 1 := by
  ring

theorem affineInterp_const (θ c : ℝ) :
    affineInterp θ c c = c := by
  unfold affineInterp
  ring

theorem affineInterp_add (θ y0 y1 z0 z1 : ℝ) :
    affineInterp θ (y0 + z0) (y1 + z1) =
      affineInterp θ y0 y1 + affineInterp θ z0 z1 := by
  unfold affineInterp
  ring

theorem affineInterp_smul (θ c y0 y1 : ℝ) :
    affineInterp θ (c * y0) (c * y1) = c * affineInterp θ y0 y1 := by
  unfold affineInterp
  ring

theorem affineInterp_abs_le
    (θ y0 y1 M : ℝ)
    (hθ0 : 0 <= θ) (hθ1 : θ <= 1)
    (hy0 : |y0| <= M) (hy1 : |y1| <= M) :
    |affineInterp θ y0 y1| <= M := by
  unfold affineInterp
  have hleft_nonneg : 0 <= 1 - θ := by linarith
  calc
    |(1 - θ) * y0 + θ * y1| <= |(1 - θ) * y0| + |θ * y1| := by
      exact abs_add_le ((1 - θ) * y0) (θ * y1)
    _ = (1 - θ) * |y0| + θ * |y1| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hleft_nonneg, abs_of_nonneg hθ0]
    _ <= (1 - θ) * M + θ * M := by
      have h0 : (1 - θ) * |y0| <= (1 - θ) * M :=
        mul_le_mul_of_nonneg_left hy0 hleft_nonneg
      have h1 : θ * |y1| <= θ * M :=
        mul_le_mul_of_nonneg_left hy1 hθ0
      linarith
    _ = M := by
      ring

theorem linearInterp_at_left
    (x0 x1 y0 y1 : ℝ) (h : x1 - x0 ≠ 0) :
    linearInterp x0 x1 y0 y1 x0 = y0 := by
  unfold linearInterp
  field_simp [h]
  ring

theorem linearInterp_at_right
    (x0 x1 y0 y1 : ℝ) (h : x1 - x0 ≠ 0) :
    linearInterp x0 x1 y0 y1 x1 = y1 := by
  unfold linearInterp
  field_simp [h]
  ring

theorem linearInterp_const
    (x0 x1 c x : ℝ) (h : x1 - x0 ≠ 0) :
    linearInterp x0 x1 c c x = c := by
  unfold linearInterp
  field_simp [h]
  ring

theorem linearInterp_eq_affine
    (x0 x1 y0 y1 x : ℝ) (h : x1 - x0 ≠ 0) :
    linearInterp x0 x1 y0 y1 x =
      affineInterp ((x - x0) / (x1 - x0)) y0 y1 := by
  unfold linearInterp affineInterp
  field_simp [h]
  ring

theorem linearInterp_add
    (x0 x1 y0 y1 z0 z1 x : ℝ) :
    linearInterp x0 x1 (y0 + z0) (y1 + z1) x =
      linearInterp x0 x1 y0 y1 x + linearInterp x0 x1 z0 z1 x := by
  unfold linearInterp
  ring

theorem linearInterp_smul
    (x0 x1 c y0 y1 x : ℝ) :
    linearInterp x0 x1 (c * y0) (c * y1) x =
      c * linearInterp x0 x1 y0 y1 x := by
  unfold linearInterp
  ring

end

end Interpolation
end LeanNumerics
