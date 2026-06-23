import Mathlib.Tactic

open scoped BigOperators

namespace LeanNumerics
namespace FEM

noncomputable section

def cellAverage2 (u0 u1 : Real) : Real :=
  (u0 + u1) / 2

def p0Projection2Left (u0 u1 : Real) : Real :=
  cellAverage2 u0 u1

def p0Projection2Right (u0 u1 : Real) : Real :=
  cellAverage2 u0 u1

def cellL2Sq2 (u0 u1 : Real) : Real :=
  u0 ^ 2 + u1 ^ 2

def p0ProjectionResidualSq2 (u0 u1 : Real) : Real :=
  (u0 - cellAverage2 u0 u1) ^ 2 + (u1 - cellAverage2 u0 u1) ^ 2

def constApproxError2 (u0 u1 c : Real) : Real :=
  (u0 - c) ^ 2 + (u1 - c) ^ 2

theorem cellAverage2_const (u : Real) :
    cellAverage2 u u = u := by
  unfold cellAverage2
  ring

theorem p0Projection2_preserves_const (u : Real) :
    p0Projection2Left u u = u /\ p0Projection2Right u u = u := by
  constructor
  · unfold p0Projection2Left
    exact cellAverage2_const u
  · unfold p0Projection2Right
    exact cellAverage2_const u

theorem p0Projection2_idempotent (u0 u1 : Real) :
    cellAverage2 (p0Projection2Left u0 u1) (p0Projection2Right u0 u1) =
      cellAverage2 u0 u1 := by
  unfold p0Projection2Left p0Projection2Right cellAverage2
  ring

theorem p0Projection2_residual_mean_zero (u0 u1 : Real) :
    (u0 - cellAverage2 u0 u1) + (u1 - cellAverage2 u0 u1) = 0 := by
  unfold cellAverage2
  ring

theorem p0Projection2_orthogonal_const (u0 u1 c : Real) :
    (u0 - cellAverage2 u0 u1) * c +
      (u1 - cellAverage2 u0 u1) * c = 0 := by
  calc
    (u0 - cellAverage2 u0 u1) * c +
        (u1 - cellAverage2 u0 u1) * c =
        ((u0 - cellAverage2 u0 u1) + (u1 - cellAverage2 u0 u1)) * c := by
      ring
    _ = 0 := by
      rw [p0Projection2_residual_mean_zero u0 u1]
      ring

theorem p0Projection2_pythagorean (u0 u1 : Real) :
    cellL2Sq2 u0 u1 =
      cellL2Sq2 (p0Projection2Left u0 u1) (p0Projection2Right u0 u1) +
        p0ProjectionResidualSq2 u0 u1 := by
  unfold cellL2Sq2 p0Projection2Left p0Projection2Right
    p0ProjectionResidualSq2 cellAverage2
  ring

theorem p0Projection2_l2_contract (u0 u1 : Real) :
    cellL2Sq2 (p0Projection2Left u0 u1) (p0Projection2Right u0 u1) <=
      cellL2Sq2 u0 u1 := by
  rw [p0Projection2_pythagorean u0 u1]
  unfold p0ProjectionResidualSq2
  nlinarith [sq_nonneg (u0 - cellAverage2 u0 u1),
    sq_nonneg (u1 - cellAverage2 u0 u1)]

theorem p0Projection2_best_const_approx (u0 u1 c : Real) :
    p0ProjectionResidualSq2 u0 u1 <= constApproxError2 u0 u1 c := by
  have h :
      constApproxError2 u0 u1 c =
        p0ProjectionResidualSq2 u0 u1 +
          constApproxError2 (cellAverage2 u0 u1) (cellAverage2 u0 u1) c := by
    unfold constApproxError2 p0ProjectionResidualSq2 cellAverage2
    ring
  have hnonneg :
      0 <= constApproxError2 (cellAverage2 u0 u1) (cellAverage2 u0 u1) c := by
    unfold constApproxError2
    nlinarith [sq_nonneg (cellAverage2 u0 u1 - c)]
  linarith

def weightedCellAverage2 (m0 m1 u0 u1 : Real) : Real :=
  (m0 * u0 + m1 * u1) / (m0 + m1)

def weightedP0Projection2Left (m0 m1 u0 u1 : Real) : Real :=
  weightedCellAverage2 m0 m1 u0 u1

def weightedP0Projection2Right (m0 m1 u0 u1 : Real) : Real :=
  weightedCellAverage2 m0 m1 u0 u1

def weightedCellL2Sq2 (m0 m1 u0 u1 : Real) : Real :=
  m0 * u0 ^ 2 + m1 * u1 ^ 2

def weightedP0ProjectionResidualSq2 (m0 m1 u0 u1 : Real) : Real :=
  m0 * (u0 - weightedCellAverage2 m0 m1 u0 u1) ^ 2 +
    m1 * (u1 - weightedCellAverage2 m0 m1 u0 u1) ^ 2

def weightedConstApproxError2 (m0 m1 u0 u1 c : Real) : Real :=
  m0 * (u0 - c) ^ 2 + m1 * (u1 - c) ^ 2

def weightedP0Average {ι : Type} (s : Finset ι)
    (m u : ι → Real) : Real :=
  (∑ i ∈ s, m i * u i) / (∑ i ∈ s, m i)

def weightedP0Residual {ι : Type} (s : Finset ι)
    (m u : ι → Real) (i : ι) : Real :=
  u i - weightedP0Average s m u

theorem weightedP0Average_const
    {ι : Type} (s : Finset ι) (m : ι → Real) (c : Real)
    (hmass : (∑ i ∈ s, m i) ≠ 0) :
    weightedP0Average s m (fun _ => c) = c := by
  unfold weightedP0Average
  calc
    (∑ i ∈ s, m i * c) / (∑ i ∈ s, m i) =
        ((∑ i ∈ s, m i) * c) / (∑ i ∈ s, m i) := by
      rw [Finset.sum_mul]
    _ = c := by
      field_simp [hmass]

theorem weightedP0Residual_const_zero
    {ι : Type} (s : Finset ι) (m : ι → Real) (c : Real) (i : ι)
    (hmass : (∑ j ∈ s, m j) ≠ 0) :
    weightedP0Residual s m (fun _ => c) i = 0 := by
  unfold weightedP0Residual
  rw [weightedP0Average_const s m c hmass]
  ring

theorem weightedP0Average_add
    {ι : Type} (s : Finset ι) (m u v : ι → Real) :
    weightedP0Average s m (fun i => u i + v i) =
      weightedP0Average s m u + weightedP0Average s m v := by
  unfold weightedP0Average
  have hmul :
      (∑ i ∈ s, m i * (u i + v i)) =
        ∑ i ∈ s, (m i * u i + m i * v i) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hmul, Finset.sum_add_distrib]
  ring

theorem weightedP0Average_smul
    {ι : Type} (s : Finset ι) (m u : ι → Real) (c : Real) :
    weightedP0Average s m (fun i => c * u i) =
      c * weightedP0Average s m u := by
  unfold weightedP0Average
  have hmul :
      (∑ i ∈ s, m i * (c * u i)) =
        ∑ i ∈ s, c * (m i * u i) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hmul, ← Finset.mul_sum]
  ring

theorem weightedP0Residual_add
    {ι : Type} (s : Finset ι) (m u v : ι → Real) (i : ι) :
    weightedP0Residual s m (fun j => u j + v j) i =
      weightedP0Residual s m u i + weightedP0Residual s m v i := by
  unfold weightedP0Residual
  rw [weightedP0Average_add s m u v]
  ring

theorem weightedP0Residual_smul
    {ι : Type} (s : Finset ι) (m u : ι → Real) (c : Real) (i : ι) :
    weightedP0Residual s m (fun j => c * u j) i =
      c * weightedP0Residual s m u i := by
  unfold weightedP0Residual
  rw [weightedP0Average_smul s m u c]
  ring

theorem weightedCellAverage2_const
    (m0 m1 u : Real) (hsum : m0 + m1 ≠ 0) :
    weightedCellAverage2 m0 m1 u u = u := by
  unfold weightedCellAverage2
  field_simp [hsum]

theorem weightedP0Projection2_preserves_const
    (m0 m1 u : Real) (hsum : m0 + m1 ≠ 0) :
    weightedP0Projection2Left m0 m1 u u = u /\
      weightedP0Projection2Right m0 m1 u u = u := by
  constructor
  · unfold weightedP0Projection2Left
    exact weightedCellAverage2_const m0 m1 u hsum
  · unfold weightedP0Projection2Right
    exact weightedCellAverage2_const m0 m1 u hsum

theorem weightedP0Projection2_idempotent
    (m0 m1 u0 u1 : Real) (hsum : m0 + m1 ≠ 0) :
    weightedCellAverage2 m0 m1
        (weightedP0Projection2Left m0 m1 u0 u1)
        (weightedP0Projection2Right m0 m1 u0 u1) =
      weightedCellAverage2 m0 m1 u0 u1 := by
  unfold weightedP0Projection2Left weightedP0Projection2Right
    weightedCellAverage2
  field_simp [hsum]

theorem weightedP0Projection2_residual_weighted_mean_zero
    (m0 m1 u0 u1 : Real) (hsum : m0 + m1 ≠ 0) :
    m0 * (u0 - weightedCellAverage2 m0 m1 u0 u1) +
      m1 * (u1 - weightedCellAverage2 m0 m1 u0 u1) = 0 := by
  unfold weightedCellAverage2
  field_simp [hsum]
  ring

theorem weightedP0Projection2_orthogonal_const
    (m0 m1 u0 u1 c : Real) (hsum : m0 + m1 ≠ 0) :
    m0 * (u0 - weightedCellAverage2 m0 m1 u0 u1) * c +
      m1 * (u1 - weightedCellAverage2 m0 m1 u0 u1) * c = 0 := by
  calc
    m0 * (u0 - weightedCellAverage2 m0 m1 u0 u1) * c +
        m1 * (u1 - weightedCellAverage2 m0 m1 u0 u1) * c =
        (m0 * (u0 - weightedCellAverage2 m0 m1 u0 u1) +
          m1 * (u1 - weightedCellAverage2 m0 m1 u0 u1)) * c := by
      ring
    _ = 0 := by
      rw [weightedP0Projection2_residual_weighted_mean_zero m0 m1 u0 u1 hsum]
      ring

theorem weightedCellL2Sq2_nonneg
    (m0 m1 u0 u1 : Real) (hm0 : 0 <= m0) (hm1 : 0 <= m1) :
    0 <= weightedCellL2Sq2 m0 m1 u0 u1 := by
  unfold weightedCellL2Sq2
  nlinarith [mul_nonneg hm0 (sq_nonneg u0), mul_nonneg hm1 (sq_nonneg u1)]

theorem weightedP0ProjectionResidualSq2_nonneg
    (m0 m1 u0 u1 : Real) (hm0 : 0 <= m0) (hm1 : 0 <= m1) :
    0 <= weightedP0ProjectionResidualSq2 m0 m1 u0 u1 := by
  unfold weightedP0ProjectionResidualSq2
  nlinarith [
    mul_nonneg hm0 (sq_nonneg (u0 - weightedCellAverage2 m0 m1 u0 u1)),
    mul_nonneg hm1 (sq_nonneg (u1 - weightedCellAverage2 m0 m1 u0 u1))]

theorem weightedConstApproxError2_nonneg
    (m0 m1 u0 u1 c : Real) (hm0 : 0 <= m0) (hm1 : 0 <= m1) :
    0 <= weightedConstApproxError2 m0 m1 u0 u1 c := by
  unfold weightedConstApproxError2
  nlinarith [mul_nonneg hm0 (sq_nonneg (u0 - c)),
    mul_nonneg hm1 (sq_nonneg (u1 - c))]

theorem weightedP0Projection2_pythagorean
    (m0 m1 u0 u1 : Real) (hsum : m0 + m1 ≠ 0) :
    weightedCellL2Sq2 m0 m1 u0 u1 =
      weightedCellL2Sq2 m0 m1
        (weightedP0Projection2Left m0 m1 u0 u1)
        (weightedP0Projection2Right m0 m1 u0 u1) +
        weightedP0ProjectionResidualSq2 m0 m1 u0 u1 := by
  unfold weightedCellL2Sq2 weightedP0Projection2Left
    weightedP0Projection2Right weightedP0ProjectionResidualSq2
    weightedCellAverage2
  field_simp [hsum]
  ring

theorem weightedP0Projection2_l2_contract
    (m0 m1 u0 u1 : Real)
    (hm0 : 0 <= m0) (hm1 : 0 <= m1) (hsum : m0 + m1 ≠ 0) :
    weightedCellL2Sq2 m0 m1
        (weightedP0Projection2Left m0 m1 u0 u1)
        (weightedP0Projection2Right m0 m1 u0 u1) <=
      weightedCellL2Sq2 m0 m1 u0 u1 := by
  rw [weightedP0Projection2_pythagorean m0 m1 u0 u1 hsum]
  exact le_add_of_nonneg_right
    (weightedP0ProjectionResidualSq2_nonneg m0 m1 u0 u1 hm0 hm1)

theorem weightedP0Projection2_error_decomposition
    (m0 m1 u0 u1 c : Real) (hsum : m0 + m1 ≠ 0) :
    weightedConstApproxError2 m0 m1 u0 u1 c =
      weightedP0ProjectionResidualSq2 m0 m1 u0 u1 +
        weightedConstApproxError2 m0 m1
          (weightedCellAverage2 m0 m1 u0 u1)
          (weightedCellAverage2 m0 m1 u0 u1) c := by
  unfold weightedConstApproxError2 weightedP0ProjectionResidualSq2
    weightedCellAverage2
  field_simp [hsum]
  ring

theorem weightedP0Projection2_best_const_approx
    (m0 m1 u0 u1 c : Real)
    (hm0 : 0 <= m0) (hm1 : 0 <= m1) (hsum : m0 + m1 ≠ 0) :
    weightedP0ProjectionResidualSq2 m0 m1 u0 u1 <=
      weightedConstApproxError2 m0 m1 u0 u1 c := by
  rw [weightedP0Projection2_error_decomposition m0 m1 u0 u1 c hsum]
  exact le_add_of_nonneg_right
    (weightedConstApproxError2_nonneg m0 m1
      (weightedCellAverage2 m0 m1 u0 u1)
      (weightedCellAverage2 m0 m1 u0 u1) c hm0 hm1)

theorem weightedP0Residual_mass_zero
    {ι : Type} (s : Finset ι) (m u : ι → Real)
    (hmass : (∑ i ∈ s, m i) ≠ 0) :
    ∑ i ∈ s, m i * weightedP0Residual s m u i = 0 := by
  unfold weightedP0Residual weightedP0Average
  calc
    ∑ i ∈ s, m i * (u i - (∑ j ∈ s, m j * u j) / ∑ j ∈ s, m j)
        = ∑ i ∈ s, (m i * u i - m i * ((∑ j ∈ s, m j * u j) / ∑ j ∈ s, m j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (∑ i ∈ s, m i * u i) -
        ∑ i ∈ s, m i * ((∑ j ∈ s, m j * u j) / ∑ j ∈ s, m j) := by
      rw [Finset.sum_sub_distrib]
    _ = (∑ i ∈ s, m i * u i) -
        (∑ i ∈ s, m i) * ((∑ j ∈ s, m j * u j) / ∑ j ∈ s, m j) := by
      rw [Finset.sum_mul]
    _ = 0 := by
      field_simp [hmass]
      ring

theorem weightedP0Projection_orthogonal_const
    {ι : Type} (s : Finset ι) (m u : ι → Real) (c : Real)
    (hmass : (∑ i ∈ s, m i) ≠ 0) :
    ∑ i ∈ s, m i * weightedP0Residual s m u i * c = 0 := by
  calc
    ∑ i ∈ s, m i * weightedP0Residual s m u i * c =
        (∑ i ∈ s, m i * weightedP0Residual s m u i) * c := by
      rw [Finset.sum_mul]
    _ = 0 := by
      rw [weightedP0Residual_mass_zero s m u hmass]
      ring

end

end FEM
end LeanNumerics
