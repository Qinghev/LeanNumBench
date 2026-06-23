import Mathlib.Tactic

namespace LeanNumerics
namespace Symplectic

noncomputable section

def leapfrogStep (omega dt x xPrev : ℝ) : ℝ :=
  2 * x - xPrev - dt ^ 2 * omega ^ 2 * x

def leapfrogInvariant (omega dt x xPrev : ℝ) : ℝ :=
  ((x - xPrev) / dt) ^ 2 + omega ^ 2 * x * xPrev

theorem leapfrogInvariant_preserved
    (omega dt x xPrev : ℝ) (hdt : dt ≠ 0) :
    leapfrogInvariant omega dt (leapfrogStep omega dt x xPrev) x =
      leapfrogInvariant omega dt x xPrev := by
  unfold leapfrogInvariant leapfrogStep
  field_simp [hdt]
  ring

def IsLeapfrogOrbit (omega dt : ℝ) (x : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, x (n + 2) = leapfrogStep omega dt (x (n + 1)) (x n)

theorem leapfrogInvariant_step_of_isLeapfrogOrbit
    (omega dt : ℝ) (hdt : dt ≠ 0) (x : ℕ → ℝ)
    (hx : IsLeapfrogOrbit omega dt x) (n : ℕ) :
    leapfrogInvariant omega dt (x (n + 2)) (x (n + 1)) =
      leapfrogInvariant omega dt (x (n + 1)) (x n) := by
  rw [hx n]
  exact leapfrogInvariant_preserved omega dt (x (n + 1)) (x n) hdt

theorem leapfrogInvariant_const_of_isLeapfrogOrbit
    (omega dt : ℝ) (hdt : dt ≠ 0) (x : ℕ → ℝ)
    (hx : IsLeapfrogOrbit omega dt x) :
    ∀ n : ℕ,
      leapfrogInvariant omega dt (x (n + 1)) (x n) =
        leapfrogInvariant omega dt (x 1) (x 0) := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      change leapfrogInvariant omega dt (x (n + 2)) (x (n + 1)) =
        leapfrogInvariant omega dt (x 1) (x 0)
      rw [leapfrogInvariant_step_of_isLeapfrogOrbit omega dt hdt x hx n]
      exact ih

end

end Symplectic
end LeanNumerics
