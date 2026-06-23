import Mathlib.Tactic

namespace LeanNumerics
namespace FiniteDifference

noncomputable section

def upwindStep (cfl uLeft u : ℝ) : ℝ :=
  (1 - cfl) * u + cfl * uLeft

theorem upwindWeights_sum (cfl : ℝ) :
    (1 - cfl) + cfl = 1 := by
  ring

theorem upwindWeights_nonneg
    (cfl : ℝ) (hcfl0 : 0 ≤ cfl) (hcfl1 : cfl ≤ 1) :
    0 ≤ 1 - cfl ∧ 0 ≤ cfl := by
  constructor <;> linarith

theorem upwindStep_const (cfl u : ℝ) :
    upwindStep cfl u u = u := by
  unfold upwindStep
  ring

theorem upwindStep_monotone
    (cfl uLeft u vLeft v : ℝ)
    (hcfl0 : 0 ≤ cfl) (hcfl1 : cfl ≤ 1)
    (hLeft : uLeft ≤ vLeft) (h : u ≤ v) :
    upwindStep cfl uLeft u ≤ upwindStep cfl vLeft v := by
  have hOneMinus : 0 ≤ 1 - cfl := by
    linarith
  unfold upwindStep
  have hA : (1 - cfl) * u ≤ (1 - cfl) * v :=
    mul_le_mul_of_nonneg_left h hOneMinus
  have hB : cfl * uLeft ≤ cfl * vLeft :=
    mul_le_mul_of_nonneg_left hLeft hcfl0
  linarith

theorem upwindStep_abs_le
    (cfl uLeft u M : ℝ)
    (hcfl0 : 0 ≤ cfl) (hcfl1 : cfl ≤ 1)
    (hLeft : |uLeft| ≤ M) (h : |u| ≤ M) :
    |upwindStep cfl uLeft u| ≤ M := by
  have hOneMinus : 0 ≤ 1 - cfl := by
    linarith
  unfold upwindStep
  calc
    |(1 - cfl) * u + cfl * uLeft|
        ≤ |(1 - cfl) * u| + |cfl * uLeft| := by
            exact abs_add_le ((1 - cfl) * u) (cfl * uLeft)
    _ = (1 - cfl) * |u| + cfl * |uLeft| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hOneMinus, abs_of_nonneg hcfl0]
    _ ≤ (1 - cfl) * M + cfl * M := by
        have hA : (1 - cfl) * |u| ≤ (1 - cfl) * M :=
          mul_le_mul_of_nonneg_left h hOneMinus
        have hB : cfl * |uLeft| ≤ cfl * M :=
          mul_le_mul_of_nonneg_left hLeft hcfl0
        linarith
    _ = M := by
        ring

end

end FiniteDifference
end LeanNumerics
