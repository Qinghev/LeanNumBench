import Mathlib.Tactic
import LeanNumerics.FiniteDifference.Conservation

namespace LeanNumerics
namespace FiniteDifference

noncomputable section

def secondForwardDifference (u : Nat -> Real) (i : Nat) : Real :=
  u (i + 2) - 2 * u (i + 1) + u i

def kdvConservativeFlux
    (nonlinear dispersion : Real) (u : Nat -> Real) (i : Nat) : Real :=
  nonlinear * (u i) ^ 2 + dispersion * secondForwardDifference u i

def kdvConservativeUpdate
    (scale nonlinear dispersion : Real) (u : Nat -> Real) (i : Nat) : Real :=
  conservativeUpdate scale u (kdvConservativeFlux nonlinear dispersion u) i

def discreteMass (u : Nat -> Real) (n : Nat) : Real :=
  totalOn u n

def kdvCanonicalFlux (u : Nat -> Real) (i : Nat) : Real :=
  kdvConservativeFlux 3 1 u i

def kdvCanonicalUpdate (scale : Real) (u : Nat -> Real) (i : Nat) : Real :=
  kdvConservativeUpdate scale 3 1 u i

theorem secondForwardDifference_const_zero (c : Real) (i : Nat) :
    secondForwardDifference (fun _ => c) i = 0 := by
  unfold secondForwardDifference
  ring

theorem kdvConservativeFlux_const
    (nonlinear dispersion c : Real) (i : Nat) :
    kdvConservativeFlux nonlinear dispersion (fun _ => c) i =
      nonlinear * c ^ 2 := by
  unfold kdvConservativeFlux secondForwardDifference
  ring

theorem kdvConservativeFlux_const_difference_zero
    (nonlinear dispersion c : Real) (i : Nat) :
    fluxDifference (kdvConservativeFlux nonlinear dispersion (fun _ => c)) i = 0 := by
  unfold fluxDifference kdvConservativeFlux secondForwardDifference
  ring

theorem kdvConservativeUpdate_eq
    (scale nonlinear dispersion : Real) (u : Nat -> Real) (i : Nat) :
    kdvConservativeUpdate scale nonlinear dispersion u i =
      u i - scale * fluxDifference (kdvConservativeFlux nonlinear dispersion u) i := by
  rfl

theorem kdvConservativeUpdate_zero_scale
    (nonlinear dispersion : Real) (u : Nat -> Real) (i : Nat) :
    kdvConservativeUpdate 0 nonlinear dispersion u i = u i := by
  unfold kdvConservativeUpdate
  exact conservativeUpdate_zero_scale u (kdvConservativeFlux nonlinear dispersion u) i

theorem kdvConservativeUpdate_const_state
    (scale nonlinear dispersion c : Real) (i : Nat) :
    kdvConservativeUpdate scale nonlinear dispersion (fun _ => c) i = c := by
  unfold kdvConservativeUpdate conservativeUpdate fluxDifference
  unfold kdvConservativeFlux secondForwardDifference
  ring

theorem discreteMass_eq_totalOn (u : Nat -> Real) (n : Nat) :
    discreteMass u n = totalOn u n := by
  rfl

theorem totalOn_kdvConservativeUpdate
    (scale nonlinear dispersion : Real) (u : Nat -> Real) (n : Nat) :
    totalOn (fun i => kdvConservativeUpdate scale nonlinear dispersion u i) n =
      totalOn u n -
        scale *
          (kdvConservativeFlux nonlinear dispersion u n -
            kdvConservativeFlux nonlinear dispersion u 0) := by
  unfold kdvConservativeUpdate
  rw [totalOn_conservativeUpdate]

theorem totalOn_kdvConservativeUpdate_of_boundary_eq
    (scale nonlinear dispersion : Real) (u : Nat -> Real) (n : Nat)
    (hflux :
      kdvConservativeFlux nonlinear dispersion u n =
        kdvConservativeFlux nonlinear dispersion u 0) :
    totalOn (fun i => kdvConservativeUpdate scale nonlinear dispersion u i) n =
      totalOn u n := by
  unfold kdvConservativeUpdate
  exact totalOn_conservativeUpdate_of_boundary_eq
    scale u (kdvConservativeFlux nonlinear dispersion u) n hflux

theorem totalOn_kdvConservativeUpdate_of_periodicFlux
    (scale nonlinear dispersion : Real) (u : Nat -> Real) (n : Nat)
    (hflux : periodicBoundary (kdvConservativeFlux nonlinear dispersion u) n) :
    totalOn (fun i => kdvConservativeUpdate scale nonlinear dispersion u i) n =
      totalOn u n := by
  exact totalOn_kdvConservativeUpdate_of_boundary_eq
    scale nonlinear dispersion u n hflux

theorem totalChange_kdvConservativeUpdate
    (scale nonlinear dispersion : Real) (u : Nat -> Real) (n : Nat) :
    totalOn (fun i => kdvConservativeUpdate scale nonlinear dispersion u i) n -
      totalOn u n =
        -scale *
          (kdvConservativeFlux nonlinear dispersion u n -
            kdvConservativeFlux nonlinear dispersion u 0) := by
  rw [totalOn_kdvConservativeUpdate]
  ring

theorem totalChange_kdvConservativeUpdate_of_boundary_eq
    (scale nonlinear dispersion : Real) (u : Nat -> Real) (n : Nat)
    (hflux :
      kdvConservativeFlux nonlinear dispersion u n =
        kdvConservativeFlux nonlinear dispersion u 0) :
    totalOn (fun i => kdvConservativeUpdate scale nonlinear dispersion u i) n -
      totalOn u n = 0 := by
  rw [totalChange_kdvConservativeUpdate]
  rw [hflux]
  ring

theorem discreteMass_kdvConservativeUpdate
    (scale nonlinear dispersion : Real) (u : Nat -> Real) (n : Nat) :
    discreteMass (fun i => kdvConservativeUpdate scale nonlinear dispersion u i) n =
      discreteMass u n -
        scale *
          (kdvConservativeFlux nonlinear dispersion u n -
            kdvConservativeFlux nonlinear dispersion u 0) := by
  unfold discreteMass
  exact totalOn_kdvConservativeUpdate scale nonlinear dispersion u n

theorem discreteMass_kdvConservativeUpdate_of_periodicFlux
    (scale nonlinear dispersion : Real) (u : Nat -> Real) (n : Nat)
    (hflux : periodicBoundary (kdvConservativeFlux nonlinear dispersion u) n) :
    discreteMass (fun i => kdvConservativeUpdate scale nonlinear dispersion u i) n =
      discreteMass u n := by
  unfold discreteMass
  exact totalOn_kdvConservativeUpdate_of_periodicFlux
    scale nonlinear dispersion u n hflux

theorem kdvCanonicalFlux_eq (u : Nat -> Real) (i : Nat) :
    kdvCanonicalFlux u i = 3 * (u i) ^ 2 + secondForwardDifference u i := by
  unfold kdvCanonicalFlux kdvConservativeFlux
  ring

theorem kdvCanonicalFlux_const (c : Real) (i : Nat) :
    kdvCanonicalFlux (fun _ => c) i = 3 * c ^ 2 := by
  unfold kdvCanonicalFlux
  exact kdvConservativeFlux_const 3 1 c i

theorem kdvCanonicalFlux_const_difference_zero (c : Real) (i : Nat) :
    fluxDifference (kdvCanonicalFlux (fun _ => c)) i = 0 := by
  unfold kdvCanonicalFlux
  exact kdvConservativeFlux_const_difference_zero 3 1 c i

theorem kdvCanonicalUpdate_eq (scale : Real) (u : Nat -> Real) (i : Nat) :
    kdvCanonicalUpdate scale u i =
      u i - scale * fluxDifference (kdvCanonicalFlux u) i := by
  unfold kdvCanonicalUpdate kdvConservativeUpdate conservativeUpdate fluxDifference kdvCanonicalFlux
  rfl

theorem kdvCanonicalUpdate_zero_scale (u : Nat -> Real) (i : Nat) :
    kdvCanonicalUpdate 0 u i = u i := by
  unfold kdvCanonicalUpdate
  exact kdvConservativeUpdate_zero_scale 3 1 u i

theorem kdvCanonicalUpdate_const_state (scale c : Real) (i : Nat) :
    kdvCanonicalUpdate scale (fun _ => c) i = c := by
  unfold kdvCanonicalUpdate
  exact kdvConservativeUpdate_const_state scale 3 1 c i

theorem totalOn_kdvCanonicalUpdate
    (scale : Real) (u : Nat -> Real) (n : Nat) :
    totalOn (fun i => kdvCanonicalUpdate scale u i) n =
      totalOn u n - scale * (kdvCanonicalFlux u n - kdvCanonicalFlux u 0) := by
  unfold kdvCanonicalUpdate kdvCanonicalFlux
  exact totalOn_kdvConservativeUpdate scale 3 1 u n

theorem totalOn_kdvCanonicalUpdate_of_boundary_eq
    (scale : Real) (u : Nat -> Real) (n : Nat)
    (hflux : kdvCanonicalFlux u n = kdvCanonicalFlux u 0) :
    totalOn (fun i => kdvCanonicalUpdate scale u i) n = totalOn u n := by
  unfold kdvCanonicalUpdate
  exact totalOn_kdvConservativeUpdate_of_boundary_eq scale 3 1 u n
    (by simpa [kdvCanonicalFlux] using hflux)

theorem totalOn_kdvCanonicalUpdate_of_periodicFlux
    (scale : Real) (u : Nat -> Real) (n : Nat)
    (hflux : periodicBoundary (kdvCanonicalFlux u) n) :
    totalOn (fun i => kdvCanonicalUpdate scale u i) n = totalOn u n := by
  exact totalOn_kdvCanonicalUpdate_of_boundary_eq scale u n hflux

theorem totalChange_kdvCanonicalUpdate
    (scale : Real) (u : Nat -> Real) (n : Nat) :
    totalOn (fun i => kdvCanonicalUpdate scale u i) n - totalOn u n =
      -scale * (kdvCanonicalFlux u n - kdvCanonicalFlux u 0) := by
  unfold kdvCanonicalUpdate kdvCanonicalFlux
  exact totalChange_kdvConservativeUpdate scale 3 1 u n

theorem totalChange_kdvCanonicalUpdate_of_boundary_eq
    (scale : Real) (u : Nat -> Real) (n : Nat)
    (hflux : kdvCanonicalFlux u n = kdvCanonicalFlux u 0) :
    totalOn (fun i => kdvCanonicalUpdate scale u i) n - totalOn u n = 0 := by
  unfold kdvCanonicalUpdate
  exact totalChange_kdvConservativeUpdate_of_boundary_eq scale 3 1 u n
    (by simpa [kdvCanonicalFlux] using hflux)

theorem discreteMass_kdvConservativeUpdate_of_boundary_eq
    (scale nonlinear dispersion : Real) (u : Nat -> Real) (n : Nat)
    (hflux :
      kdvConservativeFlux nonlinear dispersion u n =
        kdvConservativeFlux nonlinear dispersion u 0) :
    discreteMass (fun i => kdvConservativeUpdate scale nonlinear dispersion u i) n =
      discreteMass u n := by
  unfold discreteMass
  exact totalOn_kdvConservativeUpdate_of_boundary_eq scale nonlinear dispersion u n hflux

theorem discreteMass_kdvCanonicalUpdate
    (scale : Real) (u : Nat -> Real) (n : Nat) :
    discreteMass (fun i => kdvCanonicalUpdate scale u i) n =
      discreteMass u n - scale * (kdvCanonicalFlux u n - kdvCanonicalFlux u 0) := by
  unfold discreteMass
  exact totalOn_kdvCanonicalUpdate scale u n

theorem discreteMass_kdvCanonicalUpdate_of_boundary_eq
    (scale : Real) (u : Nat -> Real) (n : Nat)
    (hflux : kdvCanonicalFlux u n = kdvCanonicalFlux u 0) :
    discreteMass (fun i => kdvCanonicalUpdate scale u i) n =
      discreteMass u n := by
  unfold discreteMass
  exact totalOn_kdvCanonicalUpdate_of_boundary_eq scale u n hflux

theorem discreteMass_kdvCanonicalUpdate_of_periodicFlux
    (scale : Real) (u : Nat -> Real) (n : Nat)
    (hflux : periodicBoundary (kdvCanonicalFlux u) n) :
    discreteMass (fun i => kdvCanonicalUpdate scale u i) n = discreteMass u n := by
  exact discreteMass_kdvCanonicalUpdate_of_boundary_eq scale u n hflux

end

end FiniteDifference
end LeanNumerics
