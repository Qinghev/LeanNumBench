import Mathlib.Tactic

namespace LeanNumerics
namespace FiniteDifference

noncomputable section

open scoped BigOperators

def fluxDifference (flux : ℕ → ℝ) (i : ℕ) : ℝ :=
  flux (i + 1) - flux i

def conservativeUpdate (scale : ℝ) (u flux : ℕ → ℝ) (i : ℕ) : ℝ :=
  u i - scale * fluxDifference flux i

def totalOn (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, u i

def periodicBoundary (flux : ℕ → ℝ) (n : ℕ) : Prop :=
  flux n = flux 0

theorem fluxDifference_const_zero (c : ℝ) (i : ℕ) :
    fluxDifference (fun _ => c) i = 0 := by
  unfold fluxDifference
  ring

theorem conservativeUpdate_zero_scale
    (u flux : ℕ → ℝ) (i : ℕ) :
    conservativeUpdate 0 u flux i = u i := by
  unfold conservativeUpdate
  ring

theorem conservativeUpdate_const_flux
    (scale c : ℝ) (u : ℕ → ℝ) (i : ℕ) :
    conservativeUpdate scale u (fun _ => c) i = u i := by
  unfold conservativeUpdate fluxDifference
  ring

theorem fluxDifference_sum_range (flux : ℕ → ℝ) :
    ∀ n : ℕ, (∑ i ∈ Finset.range n, fluxDifference flux i) = flux n - flux 0 := by
  intro n
  induction n with
  | zero =>
      simp [fluxDifference]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      unfold fluxDifference
      ring

theorem totalOn_conservativeUpdate
    (scale : ℝ) (u flux : ℕ → ℝ) (n : ℕ) :
    totalOn (fun i => conservativeUpdate scale u flux i) n =
      totalOn u n - scale * (flux n - flux 0) := by
  unfold totalOn conservativeUpdate
  rw [Finset.sum_sub_distrib]
  rw [← Finset.mul_sum]
  rw [fluxDifference_sum_range]

theorem totalOn_conservativeUpdate_of_boundary_eq
    (scale : ℝ) (u flux : ℕ → ℝ) (n : ℕ)
    (hflux : flux n = flux 0) :
    totalOn (fun i => conservativeUpdate scale u flux i) n = totalOn u n := by
  rw [totalOn_conservativeUpdate]
  rw [hflux]
  ring

theorem totalOn_conservativeUpdate_of_periodicBoundary
    (scale : ℝ) (u flux : ℕ → ℝ) (n : ℕ)
    (hflux : periodicBoundary flux n) :
    totalOn (fun i => conservativeUpdate scale u flux i) n = totalOn u n := by
  exact totalOn_conservativeUpdate_of_boundary_eq scale u flux n hflux

theorem totalChange_conservativeUpdate
    (scale : ℝ) (u flux : ℕ → ℝ) (n : ℕ) :
    totalOn (fun i => conservativeUpdate scale u flux i) n - totalOn u n =
      -scale * (flux n - flux 0) := by
  rw [totalOn_conservativeUpdate]
  ring

theorem totalChange_conservativeUpdate_of_boundary_eq
    (scale : ℝ) (u flux : ℕ → ℝ) (n : ℕ)
    (hflux : flux n = flux 0) :
    totalOn (fun i => conservativeUpdate scale u flux i) n - totalOn u n = 0 := by
  rw [totalChange_conservativeUpdate]
  rw [hflux]
  ring

end

end FiniteDifference
end LeanNumerics
