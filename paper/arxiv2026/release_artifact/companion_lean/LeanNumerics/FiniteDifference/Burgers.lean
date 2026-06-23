import Mathlib.Tactic
import LeanNumerics.FiniteDifference.Conservation

namespace LeanNumerics
namespace FiniteDifference

noncomputable section

def burgersFlux (u : ℕ → ℝ) (i : ℕ) : ℝ :=
  (u i) ^ 2 / 2

def burgersConservativeUpdate (scale : ℝ) (u : ℕ → ℝ) (i : ℕ) : ℝ :=
  conservativeUpdate scale u (burgersFlux u) i

theorem burgersFlux_eq (u : ℕ → ℝ) (i : ℕ) :
    burgersFlux u i = (u i) ^ 2 / 2 := by
  rfl

theorem burgersFlux_const (c : ℝ) (i : ℕ) :
    burgersFlux (fun _ => c) i = c ^ 2 / 2 := by
  unfold burgersFlux
  ring

theorem burgersFlux_const_difference_zero (c : ℝ) (i : ℕ) :
    fluxDifference (burgersFlux (fun _ => c)) i = 0 := by
  unfold fluxDifference burgersFlux
  ring

theorem burgersConservativeUpdate_eq
    (scale : ℝ) (u : ℕ → ℝ) (i : ℕ) :
    burgersConservativeUpdate scale u i =
      u i - scale * (burgersFlux u (i + 1) - burgersFlux u i) := by
  unfold burgersConservativeUpdate conservativeUpdate fluxDifference
  rfl

theorem burgersConservativeUpdate_zero_scale
    (u : ℕ → ℝ) (i : ℕ) :
    burgersConservativeUpdate 0 u i = u i := by
  unfold burgersConservativeUpdate
  exact conservativeUpdate_zero_scale u (burgersFlux u) i

theorem burgersConservativeUpdate_const_state
    (scale c : ℝ) (i : ℕ) :
    burgersConservativeUpdate scale (fun _ => c) i = c := by
  unfold burgersConservativeUpdate conservativeUpdate fluxDifference burgersFlux
  ring

theorem totalOn_burgersConservativeUpdate
    (scale : ℝ) (u : ℕ → ℝ) (n : ℕ) :
    totalOn (fun i => burgersConservativeUpdate scale u i) n =
      totalOn u n - scale * (burgersFlux u n - burgersFlux u 0) := by
  unfold burgersConservativeUpdate
  exact totalOn_conservativeUpdate scale u (burgersFlux u) n

theorem totalOn_burgersConservativeUpdate_of_boundary_eq
    (scale : ℝ) (u : ℕ → ℝ) (n : ℕ)
    (hflux : burgersFlux u n = burgersFlux u 0) :
    totalOn (fun i => burgersConservativeUpdate scale u i) n = totalOn u n := by
  unfold burgersConservativeUpdate
  exact totalOn_conservativeUpdate_of_boundary_eq
    scale u (burgersFlux u) n hflux

theorem totalOn_burgersConservativeUpdate_of_periodicFlux
    (scale : ℝ) (u : ℕ → ℝ) (n : ℕ)
    (hflux : periodicBoundary (burgersFlux u) n) :
    totalOn (fun i => burgersConservativeUpdate scale u i) n = totalOn u n := by
  exact totalOn_burgersConservativeUpdate_of_boundary_eq scale u n hflux

theorem totalChange_burgersConservativeUpdate
    (scale : ℝ) (u : ℕ → ℝ) (n : ℕ) :
    totalOn (fun i => burgersConservativeUpdate scale u i) n - totalOn u n =
      -scale * (burgersFlux u n - burgersFlux u 0) := by
  rw [totalOn_burgersConservativeUpdate]
  ring

theorem totalChange_burgersConservativeUpdate_of_boundary_eq
    (scale : ℝ) (u : ℕ → ℝ) (n : ℕ)
    (hflux : burgersFlux u n = burgersFlux u 0) :
    totalOn (fun i => burgersConservativeUpdate scale u i) n - totalOn u n =
      0 := by
  rw [totalChange_burgersConservativeUpdate]
  rw [hflux]
  ring

end

end FiniteDifference
end LeanNumerics
