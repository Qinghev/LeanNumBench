import Mathlib.Tactic

namespace LeanNumerics
namespace ODE

noncomputable section

def explicitEulerStep (dt y f : ℝ) : ℝ :=
  y + dt * f

def explicitEulerLinearStep (dt a y : ℝ) : ℝ :=
  explicitEulerStep dt y (a * y)

def midpointRK2Step (dt a y : ℝ) : ℝ :=
  let k1 := a * y
  let k2 := a * (y + (dt / 2) * k1)
  y + dt * k2

def heunRK2Step (dt a y : ℝ) : ℝ :=
  let k1 := a * y
  let k2 := a * (y + dt * k1)
  y + dt * ((k1 + k2) / 2)

def linearTaylor2Step (dt a y : ℝ) : ℝ :=
  (1 + dt * a + (dt * a) ^ 2 / 2) * y

theorem explicitEulerStep_zero_dt (y f : ℝ) :
    explicitEulerStep 0 y f = y := by
  unfold explicitEulerStep
  ring

theorem explicitEulerLinearStep_eq (dt a y : ℝ) :
    explicitEulerLinearStep dt a y = (1 + dt * a) * y := by
  unfold explicitEulerLinearStep explicitEulerStep
  ring

theorem midpointRK2Step_zero_dt (a y : ℝ) :
    midpointRK2Step 0 a y = y := by
  unfold midpointRK2Step
  ring

theorem midpointRK2Step_eq_taylor2 (dt a y : ℝ) :
    midpointRK2Step dt a y = linearTaylor2Step dt a y := by
  unfold midpointRK2Step linearTaylor2Step
  ring

theorem heunRK2Step_eq_taylor2 (dt a y : ℝ) :
    heunRK2Step dt a y = linearTaylor2Step dt a y := by
  unfold heunRK2Step linearTaylor2Step
  ring

theorem midpointRK2Step_eq_heunRK2Step (dt a y : ℝ) :
    midpointRK2Step dt a y = heunRK2Step dt a y := by
  rw [midpointRK2Step_eq_taylor2, heunRK2Step_eq_taylor2]

end

end ODE
end LeanNumerics
