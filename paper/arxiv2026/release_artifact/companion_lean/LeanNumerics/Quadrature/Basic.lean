import Mathlib.Tactic

namespace LeanNumerics
namespace Quadrature

noncomputable section

def midpoint1 (h fm : ℝ) : ℝ :=
  h * fm

def trapezoid2 (h f0 f1 : ℝ) : ℝ :=
  h * (f0 + f1) / 2

theorem midpoint1_const (h c : ℝ) :
    midpoint1 h c = h * c := by
  rfl

theorem midpoint1_add (h f g : ℝ) :
    midpoint1 h (f + g) = midpoint1 h f + midpoint1 h g := by
  unfold midpoint1
  ring

theorem midpoint1_smul (h c f : ℝ) :
    midpoint1 h (c * f) = c * midpoint1 h f := by
  unfold midpoint1
  ring

theorem trapezoid2_const (h c : ℝ) :
    trapezoid2 h c c = h * c := by
  unfold trapezoid2
  ring

theorem trapezoid2_add (h f0 f1 g0 g1 : ℝ) :
    trapezoid2 h (f0 + g0) (f1 + g1) =
      trapezoid2 h f0 f1 + trapezoid2 h g0 g1 := by
  unfold trapezoid2
  ring

theorem trapezoid2_smul (h c f0 f1 : ℝ) :
    trapezoid2 h (c * f0) (c * f1) = c * trapezoid2 h f0 f1 := by
  unfold trapezoid2
  ring

theorem trapezoid2_zero_h (f0 f1 : ℝ) :
    trapezoid2 0 f0 f1 = 0 := by
  unfold trapezoid2
  ring

theorem trapezoid2_eq_midpoint1_const (h c : ℝ) :
    trapezoid2 h c c = midpoint1 h c := by
  unfold trapezoid2 midpoint1
  ring

theorem trapezoid2_nonneg
    (h f0 f1 : ℝ) (hh : 0 <= h) (hf0 : 0 <= f0) (hf1 : 0 <= f1) :
    0 <= trapezoid2 h f0 f1 := by
  unfold trapezoid2
  nlinarith [mul_nonneg hh (add_nonneg hf0 hf1)]

end

end Quadrature
end LeanNumerics
