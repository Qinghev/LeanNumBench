import Mathlib.Tactic

namespace LeanNumerics
namespace FiniteDifference

noncomputable section

open scoped BigOperators

def heatLeftWeight (r : ℝ) : ℝ :=
  r

def heatCenterWeight (r : ℝ) : ℝ :=
  1 - 2 * r

def heatRightWeight (r : ℝ) : ℝ :=
  r

def heatStep (r uLeft u uRight : ℝ) : ℝ :=
  heatLeftWeight r * uLeft + heatCenterWeight r * u +
    heatRightWeight r * uRight

def heatStepGrid (r : ℝ) (u : ℕ → ℝ) (i : ℕ) : ℝ :=
  heatStep r (u i) (u (i + 1)) (u (i + 2))

def heatSecondDifference (u : ℕ → ℝ) (i : ℕ) : ℝ :=
  u i - 2 * u (i + 1) + u (i + 2)

def heatInteriorTotal (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, u (i + 1)

def heatStepGridTotal (r : ℝ) (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, heatStepGrid r u i

def heatBoundaryTerm (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  u 0 - u 1 + (u (n + 1) - u n)

theorem heatWeights_sum (r : ℝ) :
    heatLeftWeight r + heatCenterWeight r + heatRightWeight r = 1 := by
  unfold heatLeftWeight heatCenterWeight heatRightWeight
  ring

theorem heatWeights_nonneg
    (r : ℝ) (hr0 : 0 ≤ r) (hrCfl : 2 * r ≤ 1) :
    0 ≤ heatLeftWeight r ∧
      0 ≤ heatCenterWeight r ∧
      0 ≤ heatRightWeight r := by
  unfold heatLeftWeight heatCenterWeight heatRightWeight
  constructor
  · exact hr0
  constructor
  · linarith
  · exact hr0

theorem heatStep_const (r u : ℝ) :
    heatStep r u u u = u := by
  unfold heatStep heatLeftWeight heatCenterWeight heatRightWeight
  ring

theorem heatStep_monotone
    (r uLeft u uRight vLeft v vRight : ℝ)
    (hr0 : 0 ≤ r) (hrCfl : 2 * r ≤ 1)
    (hLeft : uLeft ≤ vLeft) (h : u ≤ v) (hRight : uRight ≤ vRight) :
    heatStep r uLeft u uRight ≤ heatStep r vLeft v vRight := by
  rcases heatWeights_nonneg r hr0 hrCfl with ⟨hWL, hWC, hWR⟩
  unfold heatStep
  have hA :
      heatLeftWeight r * uLeft ≤ heatLeftWeight r * vLeft :=
    mul_le_mul_of_nonneg_left hLeft hWL
  have hB :
      heatCenterWeight r * u ≤ heatCenterWeight r * v :=
    mul_le_mul_of_nonneg_left h hWC
  have hC :
      heatRightWeight r * uRight ≤ heatRightWeight r * vRight :=
    mul_le_mul_of_nonneg_left hRight hWR
  linarith

theorem heatStep_abs_le
    (r uLeft u uRight M : ℝ)
    (hr0 : 0 ≤ r) (hrCfl : 2 * r ≤ 1)
    (hLeft : |uLeft| ≤ M) (h : |u| ≤ M) (hRight : |uRight| ≤ M) :
    |heatStep r uLeft u uRight| ≤ M := by
  rcases heatWeights_nonneg r hr0 hrCfl with ⟨hWL, hWC, hWR⟩
  unfold heatStep
  calc
    |heatLeftWeight r * uLeft + heatCenterWeight r * u +
        heatRightWeight r * uRight|
        ≤ |heatLeftWeight r * uLeft + heatCenterWeight r * u| +
            |heatRightWeight r * uRight| := by
            exact abs_add_le
              (heatLeftWeight r * uLeft + heatCenterWeight r * u)
              (heatRightWeight r * uRight)
    _ ≤ (|heatLeftWeight r * uLeft| + |heatCenterWeight r * u|) +
          |heatRightWeight r * uRight| := by
        have hTri :
            |heatLeftWeight r * uLeft + heatCenterWeight r * u| ≤
              |heatLeftWeight r * uLeft| + |heatCenterWeight r * u| := by
          exact abs_add_le (heatLeftWeight r * uLeft) (heatCenterWeight r * u)
        linarith
    _ = heatLeftWeight r * |uLeft| + heatCenterWeight r * |u| +
          heatRightWeight r * |uRight| := by
        rw [abs_mul, abs_mul, abs_mul,
          abs_of_nonneg hWL, abs_of_nonneg hWC, abs_of_nonneg hWR]
    _ ≤ heatLeftWeight r * M + heatCenterWeight r * M +
          heatRightWeight r * M := by
        have hA :
            heatLeftWeight r * |uLeft| ≤ heatLeftWeight r * M :=
          mul_le_mul_of_nonneg_left hLeft hWL
        have hB :
            heatCenterWeight r * |u| ≤ heatCenterWeight r * M :=
          mul_le_mul_of_nonneg_left h hWC
        have hC :
            heatRightWeight r * |uRight| ≤ heatRightWeight r * M :=
          mul_le_mul_of_nonneg_left hRight hWR
        linarith
    _ = M := by
        unfold heatLeftWeight heatCenterWeight heatRightWeight
        ring

theorem heatStepGrid_eq_center_plus_second_difference
    (r : ℝ) (u : ℕ → ℝ) (i : ℕ) :
    heatStepGrid r u i =
      u (i + 1) + r * (u i - 2 * u (i + 1) + u (i + 2)) := by
  unfold heatStepGrid heatStep heatLeftWeight heatCenterWeight heatRightWeight
  ring

theorem heatStepGrid_eq_center_plus_heatSecondDifference
    (r : ℝ) (u : ℕ → ℝ) (i : ℕ) :
    heatStepGrid r u i = u (i + 1) + r * heatSecondDifference u i := by
  unfold heatStepGrid heatStep heatSecondDifference
    heatLeftWeight heatCenterWeight heatRightWeight
  ring

theorem heatStepGrid_const (r c : ℝ) (i : ℕ) :
    heatStepGrid r (fun _ => c) i = c := by
  unfold heatStepGrid
  rw [heatStep_const]

theorem heatStepGrid_abs_le
    (r : ℝ) (u : ℕ → ℝ) (i : ℕ) (M : ℝ)
    (hr0 : 0 ≤ r) (hrCfl : 2 * r ≤ 1)
    (hLeft : |u i| ≤ M) (h : |u (i + 1)| ≤ M)
    (hRight : |u (i + 2)| ≤ M) :
    |heatStepGrid r u i| ≤ M := by
  unfold heatStepGrid
  exact heatStep_abs_le r (u i) (u (i + 1)) (u (i + 2)) M
    hr0 hrCfl hLeft h hRight

theorem heatSecondDifference_sum_range (u : ℕ → ℝ) :
    ∀ n : ℕ,
      (∑ i ∈ Finset.range n, heatSecondDifference u i) =
        heatBoundaryTerm u n := by
  intro n
  induction n with
  | zero =>
      simp [heatSecondDifference, heatBoundaryTerm]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      unfold heatSecondDifference heatBoundaryTerm
      ring

theorem heatStepGridTotal_eq
    (r : ℝ) (u : ℕ → ℝ) (n : ℕ) :
    heatStepGridTotal r u n =
      heatInteriorTotal u n + r * heatBoundaryTerm u n := by
  unfold heatStepGridTotal heatInteriorTotal
  calc
    (∑ i ∈ Finset.range n, heatStepGrid r u i)
        = ∑ i ∈ Finset.range n,
            (u (i + 1) + r * heatSecondDifference u i) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [heatStepGrid_eq_center_plus_heatSecondDifference]
    _ = (∑ i ∈ Finset.range n, u (i + 1)) +
          ∑ i ∈ Finset.range n, r * heatSecondDifference u i := by
        rw [Finset.sum_add_distrib]
    _ = (∑ i ∈ Finset.range n, u (i + 1)) +
          r * (∑ i ∈ Finset.range n, heatSecondDifference u i) := by
        rw [← Finset.mul_sum]
    _ = (∑ i ∈ Finset.range n, u (i + 1)) +
          r * heatBoundaryTerm u n := by
        rw [heatSecondDifference_sum_range]

theorem heatStepGridTotal_change
    (r : ℝ) (u : ℕ → ℝ) (n : ℕ) :
    heatStepGridTotal r u n - heatInteriorTotal u n =
      r * heatBoundaryTerm u n := by
  rw [heatStepGridTotal_eq]
  ring

theorem heatBoundaryTerm_eq_zero_of_neumann
    (u : ℕ → ℝ) (n : ℕ)
    (hLeft : u 0 = u 1) (hRight : u (n + 1) = u n) :
    heatBoundaryTerm u n = 0 := by
  unfold heatBoundaryTerm
  rw [hLeft, hRight]
  ring

theorem heatStepGridTotal_of_boundary_zero
    (r : ℝ) (u : ℕ → ℝ) (n : ℕ)
    (hboundary : heatBoundaryTerm u n = 0) :
    heatStepGridTotal r u n = heatInteriorTotal u n := by
  rw [heatStepGridTotal_eq, hboundary]
  ring

theorem heatStepGridTotal_of_neumann_boundary
    (r : ℝ) (u : ℕ → ℝ) (n : ℕ)
    (hLeft : u 0 = u 1) (hRight : u (n + 1) = u n) :
    heatStepGridTotal r u n = heatInteriorTotal u n := by
  exact heatStepGridTotal_of_boundary_zero r u n
    (heatBoundaryTerm_eq_zero_of_neumann u n hLeft hRight)

end

end FiniteDifference
end LeanNumerics
