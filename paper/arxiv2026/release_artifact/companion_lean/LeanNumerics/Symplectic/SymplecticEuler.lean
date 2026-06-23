import Mathlib.Tactic

namespace LeanNumerics
namespace Symplectic

noncomputable section

def symplecticEulerPNext (omega dt q p : ℝ) : ℝ :=
  p - dt * omega ^ 2 * q

def symplecticEulerQNext (omega dt q p : ℝ) : ℝ :=
  q + dt * symplecticEulerPNext omega dt q p

def symplecticEulerInvariant (omega dt q p : ℝ) : ℝ :=
  p ^ 2 + omega ^ 2 * q ^ 2 - dt * omega ^ 2 * q * p

def det2 (a b c d : ℝ) : ℝ :=
  a * d - b * c

theorem symplecticEulerInvariant_preserved
    (omega dt q p : ℝ) :
    symplecticEulerInvariant omega dt
        (symplecticEulerQNext omega dt q p)
        (symplecticEulerPNext omega dt q p) =
      symplecticEulerInvariant omega dt q p := by
  unfold symplecticEulerInvariant symplecticEulerQNext symplecticEulerPNext
  ring

theorem symplecticEulerPNext_linear (omega dt q p : ℝ) :
    symplecticEulerPNext omega dt q p =
      (-dt * omega ^ 2) * q + 1 * p := by
  unfold symplecticEulerPNext
  ring

theorem symplecticEulerQNext_linear (omega dt q p : ℝ) :
    symplecticEulerQNext omega dt q p =
      (1 - dt ^ 2 * omega ^ 2) * q + dt * p := by
  unfold symplecticEulerQNext symplecticEulerPNext
  ring

theorem symplecticEulerLinear_det_eq_one (omega dt : ℝ) :
    det2 (1 - dt ^ 2 * omega ^ 2) dt (-dt * omega ^ 2) 1 = 1 := by
  unfold det2
  ring

def IsSymplecticEulerOrbit (omega dt : ℝ) (q p : ℕ → ℝ) : Prop :=
  ∀ n : ℕ,
    p (n + 1) = symplecticEulerPNext omega dt (q n) (p n) ∧
      q (n + 1) = symplecticEulerQNext omega dt (q n) (p n)

theorem symplecticEulerInvariant_step_of_isSymplecticEulerOrbit
    (omega dt : ℝ) (q p : ℕ → ℝ)
    (hqp : IsSymplecticEulerOrbit omega dt q p) (n : ℕ) :
    symplecticEulerInvariant omega dt (q (n + 1)) (p (n + 1)) =
      symplecticEulerInvariant omega dt (q n) (p n) := by
  rcases hqp n with ⟨hp, hq⟩
  rw [hq, hp]
  exact symplecticEulerInvariant_preserved omega dt (q n) (p n)

theorem symplecticEulerInvariant_const_of_isSymplecticEulerOrbit
    (omega dt : ℝ) (q p : ℕ → ℝ)
    (hqp : IsSymplecticEulerOrbit omega dt q p) :
    ∀ n : ℕ,
      symplecticEulerInvariant omega dt (q n) (p n) =
        symplecticEulerInvariant omega dt (q 0) (p 0) := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      change symplecticEulerInvariant omega dt (q (n + 1)) (p (n + 1)) =
        symplecticEulerInvariant omega dt (q 0) (p 0)
      rw [symplecticEulerInvariant_step_of_isSymplecticEulerOrbit omega dt q p hqp n]
      exact ih

end

end Symplectic
end LeanNumerics
