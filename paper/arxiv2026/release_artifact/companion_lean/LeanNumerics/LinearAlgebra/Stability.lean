import Mathlib.Tactic

open scoped BigOperators

namespace LeanNumerics
namespace LinearAlgebra

noncomputable section

def vec2InfNorm (x y : Real) : Real :=
  max |x| |y|

def row2Apply (a b x y : Real) : Real :=
  a * x + b * y

def rowStochastic2First (a b x y : Real) : Real :=
  row2Apply a b x y

def rowStochastic2Second (c d x y : Real) : Real :=
  row2Apply c d x y

def diag2First (a x : Real) : Real :=
  a * x

def diag2Second (b y : Real) : Real :=
  b * y

def finiteRowApply {ι : Type} (s : Finset ι)
    (a x : ι → Real) : Real :=
  ∑ i ∈ s, a i * x i

/-- A finite weighted average with nonnegative weights summing to one stays inside any
uniform absolute-value bound on the entries. This is the Mathlib candidate distilled from
the row-stochastic stability proof below. -/
theorem finiteWeightedAbsSum_le
    {ι : Type} (s : Finset ι) (a x : ι → Real) (M : Real)
    (ha : ∀ i, i ∈ s → 0 <= a i)
    (hsum : ∑ i ∈ s, a i = 1)
    (hx : ∀ i, i ∈ s → |x i| <= M) :
    |∑ i ∈ s, a i * x i| <= M := by
  calc
    |∑ i ∈ s, a i * x i| <= ∑ i ∈ s, |a i * x i| := by
      exact Finset.abs_sum_le_sum_abs (fun i => a i * x i) s
    _ = ∑ i ∈ s, a i * |x i| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, abs_of_nonneg (ha i hi)]
    _ <= ∑ i ∈ s, a i * M := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hx i hi) (ha i hi)
    _ = (∑ i ∈ s, a i) * M := by
      rw [Finset.sum_mul]
    _ = M := by
      rw [hsum, one_mul]

theorem vec2InfNorm_nonneg (x y : Real) :
    0 <= vec2InfNorm x y := by
  unfold vec2InfNorm
  exact le_max_of_le_left (abs_nonneg x)

theorem abs_left_le_vec2InfNorm (x y : Real) :
    |x| <= vec2InfNorm x y := by
  unfold vec2InfNorm
  exact le_max_left |x| |y|

theorem abs_right_le_vec2InfNorm (x y : Real) :
    |y| <= vec2InfNorm x y := by
  unfold vec2InfNorm
  exact le_max_right |x| |y|

theorem row2Apply_const
    (a b u : Real) (hsum : a + b = 1) :
    row2Apply a b u u = u := by
  unfold row2Apply
  calc
    a * u + b * u = (a + b) * u := by ring
    _ = 1 * u := by rw [hsum]
    _ = u := by ring

theorem row2Apply_abs_le
    (a b x y M : Real)
    (ha : 0 <= a) (hb : 0 <= b) (hsum : a + b = 1)
    (hx : |x| <= M) (hy : |y| <= M) :
    |row2Apply a b x y| <= M := by
  unfold row2Apply
  calc
    |a * x + b * y| <= |a * x| + |b * y| := by
      exact abs_add_le (a * x) (b * y)
    _ = a * |x| + b * |y| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ <= a * M + b * M := by
      have hx' : a * |x| <= a * M := mul_le_mul_of_nonneg_left hx ha
      have hy' : b * |y| <= b * M := mul_le_mul_of_nonneg_left hy hb
      linarith
    _ = M := by
      calc
        a * M + b * M = (a + b) * M := by ring
        _ = 1 * M := by rw [hsum]
        _ = M := by ring

theorem rowStochastic2_const
    (a b c d u : Real)
    (hrow1 : a + b = 1) (hrow2 : c + d = 1) :
    rowStochastic2First a b u u = u /\
      rowStochastic2Second c d u u = u := by
  constructor
  · unfold rowStochastic2First
    exact row2Apply_const a b u hrow1
  · unfold rowStochastic2Second
    exact row2Apply_const c d u hrow2

theorem rowStochastic2_infNorm_abs_le
    (a b c d x y M : Real)
    (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c) (hd : 0 <= d)
    (hrow1 : a + b = 1) (hrow2 : c + d = 1)
    (hx : |x| <= M) (hy : |y| <= M) :
    |rowStochastic2First a b x y| <= M /\
      |rowStochastic2Second c d x y| <= M := by
  constructor
  · unfold rowStochastic2First
    exact row2Apply_abs_le a b x y M ha hb hrow1 hx hy
  · unfold rowStochastic2Second
    exact row2Apply_abs_le c d x y M hc hd hrow2 hx hy

theorem diag2_zero
    (a b : Real) :
    diag2First a 0 = 0 /\ diag2Second b 0 = 0 := by
  constructor
  · unfold diag2First
    ring
  · unfold diag2Second
    ring

theorem diag2_infNorm_le
    (a b rho x y : Real)
    (ha : |a| <= rho) (hb : |b| <= rho) (hrho : 0 <= rho) :
    vec2InfNorm (diag2First a x) (diag2Second b y) <=
      rho * vec2InfNorm x y := by
  unfold vec2InfNorm diag2First diag2Second
  apply max_le
  · rw [abs_mul]
    have hx : |x| <= max |x| |y| := le_max_left |x| |y|
    exact mul_le_mul ha hx (abs_nonneg x) hrho
  · rw [abs_mul]
    have hy : |y| <= max |x| |y| := le_max_right |x| |y|
    exact mul_le_mul hb hy (abs_nonneg y) hrho

theorem finiteRowApply_abs_le
    {ι : Type} (s : Finset ι) (a x : ι → Real) (M : Real)
    (ha : ∀ i, i ∈ s → 0 <= a i)
    (hsum : ∑ i ∈ s, a i = 1)
    (hx : ∀ i, i ∈ s → |x i| <= M) :
    |finiteRowApply s a x| <= M := by
  unfold finiteRowApply
  exact finiteWeightedAbsSum_le s a x M ha hsum hx

theorem finiteRowApply_const
    {ι : Type} (s : Finset ι) (a : ι → Real) (u : Real)
    (hsum : ∑ i ∈ s, a i = 1) :
    finiteRowApply s a (fun _ => u) = u := by
  unfold finiteRowApply
  calc
    (∑ i ∈ s, a i * u) = (∑ i ∈ s, a i) * u := by
      rw [Finset.sum_mul]
    _ = 1 * u := by rw [hsum]
    _ = u := by ring

theorem finiteRowApply_zero
    {ι : Type} (s : Finset ι) (a : ι → Real) :
    finiteRowApply s a (fun _ => 0) = 0 := by
  unfold finiteRowApply
  simp

theorem finiteRowApply_add
    {ι : Type} (s : Finset ι) (a x y : ι → Real) :
    finiteRowApply s a (fun i => x i + y i) =
      finiteRowApply s a x + finiteRowApply s a y := by
  unfold finiteRowApply
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end

end LinearAlgebra
end LeanNumerics
