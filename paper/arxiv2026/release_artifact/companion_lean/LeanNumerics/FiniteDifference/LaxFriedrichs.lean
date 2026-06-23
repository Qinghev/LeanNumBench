import Mathlib.Tactic

namespace LeanNumerics
namespace FiniteDifference

noncomputable section

def laxFriedrichsLeftWeight (cfl : ℝ) : ℝ :=
  (1 + cfl) / 2

def laxFriedrichsRightWeight (cfl : ℝ) : ℝ :=
  (1 - cfl) / 2

def laxFriedrichsStep (cfl uLeft uRight : ℝ) : ℝ :=
  laxFriedrichsLeftWeight cfl * uLeft +
    laxFriedrichsRightWeight cfl * uRight

theorem laxFriedrichsWeights_sum (cfl : ℝ) :
    laxFriedrichsLeftWeight cfl + laxFriedrichsRightWeight cfl = 1 := by
  unfold laxFriedrichsLeftWeight laxFriedrichsRightWeight
  ring

theorem laxFriedrichsWeights_nonneg
    (cfl : ℝ) (hcflLower : -1 ≤ cfl) (hcflUpper : cfl ≤ 1) :
    0 ≤ laxFriedrichsLeftWeight cfl ∧
      0 ≤ laxFriedrichsRightWeight cfl := by
  unfold laxFriedrichsLeftWeight laxFriedrichsRightWeight
  constructor <;> linarith

theorem laxFriedrichsStep_const (cfl u : ℝ) :
    laxFriedrichsStep cfl u u = u := by
  unfold laxFriedrichsStep laxFriedrichsLeftWeight laxFriedrichsRightWeight
  ring

theorem laxFriedrichsStep_monotone
    (cfl uLeft uRight vLeft vRight : ℝ)
    (hcflLower : -1 ≤ cfl) (hcflUpper : cfl ≤ 1)
    (hLeft : uLeft ≤ vLeft) (hRight : uRight ≤ vRight) :
    laxFriedrichsStep cfl uLeft uRight ≤
      laxFriedrichsStep cfl vLeft vRight := by
  rcases laxFriedrichsWeights_nonneg cfl hcflLower hcflUpper with ⟨hWL, hWR⟩
  unfold laxFriedrichsStep
  have hA :
      laxFriedrichsLeftWeight cfl * uLeft ≤
        laxFriedrichsLeftWeight cfl * vLeft :=
    mul_le_mul_of_nonneg_left hLeft hWL
  have hB :
      laxFriedrichsRightWeight cfl * uRight ≤
        laxFriedrichsRightWeight cfl * vRight :=
    mul_le_mul_of_nonneg_left hRight hWR
  linarith

theorem laxFriedrichsStep_abs_le
    (cfl uLeft uRight M : ℝ)
    (hcflLower : -1 ≤ cfl) (hcflUpper : cfl ≤ 1)
    (hLeft : |uLeft| ≤ M) (hRight : |uRight| ≤ M) :
    |laxFriedrichsStep cfl uLeft uRight| ≤ M := by
  rcases laxFriedrichsWeights_nonneg cfl hcflLower hcflUpper with ⟨hWL, hWR⟩
  unfold laxFriedrichsStep
  calc
    |laxFriedrichsLeftWeight cfl * uLeft +
        laxFriedrichsRightWeight cfl * uRight|
        ≤ |laxFriedrichsLeftWeight cfl * uLeft| +
            |laxFriedrichsRightWeight cfl * uRight| := by
            exact abs_add_le
              (laxFriedrichsLeftWeight cfl * uLeft)
              (laxFriedrichsRightWeight cfl * uRight)
    _ = laxFriedrichsLeftWeight cfl * |uLeft| +
          laxFriedrichsRightWeight cfl * |uRight| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hWL, abs_of_nonneg hWR]
    _ ≤ laxFriedrichsLeftWeight cfl * M +
          laxFriedrichsRightWeight cfl * M := by
        have hA :
            laxFriedrichsLeftWeight cfl * |uLeft| ≤
              laxFriedrichsLeftWeight cfl * M :=
          mul_le_mul_of_nonneg_left hLeft hWL
        have hB :
            laxFriedrichsRightWeight cfl * |uRight| ≤
              laxFriedrichsRightWeight cfl * M :=
          mul_le_mul_of_nonneg_left hRight hWR
        linarith
    _ = M := by
        unfold laxFriedrichsLeftWeight laxFriedrichsRightWeight
        ring

end

end FiniteDifference
end LeanNumerics
