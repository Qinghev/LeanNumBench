import LeanNumerics.FEM.Projection
import LeanNumerics.FiniteDifference.Heat
import LeanNumerics.FiniteDifference.Kdv
import LeanNumerics.FiniteDifference.LaxFriedrichs
import LeanNumerics.FiniteDifference.Upwind
import LeanNumerics.LinearAlgebra.Stability
import LeanNumerics.Symplectic.Leapfrog

open scoped BigOperators

namespace LeanNumerics
namespace LeanNumBenchMinimalPairsV4

noncomputable section

theorem v4p01_easy_heat_three_step_outer_exposed_abs_le
    (r : Real) (u : Nat -> Real) (i : Nat) (M : Real)
    (hr0 : 0 <= r) (hrCfl : 2 * r <= 1)
    (h0 : |u i| <= M) (h1 : |u (i + 1)| <= M)
    (h2 : |u (i + 2)| <= M) (h3 : |u (i + 3)| <= M)
    (h4 : |u (i + 4)| <= M) (h5 : |u (i + 5)| <= M)
    (h6 : |u (i + 6)| <= M) :
    |FiniteDifference.heatStep r
        (FiniteDifference.heatStepGrid r
          (fun j => FiniteDifference.heatStepGrid r u j) i)
        (FiniteDifference.heatStepGrid r
          (fun j => FiniteDifference.heatStepGrid r u j) (i + 1))
        (FiniteDifference.heatStepGrid r
          (fun j => FiniteDifference.heatStepGrid r u j) (i + 2))| <= M := by
  have hOne0 : |FiniteDifference.heatStepGrid r u i| <= M := by
    exact FiniteDifference.heatStepGrid_abs_le r u i M
      hr0 hrCfl h0 h1 h2
  have hOne1 : |FiniteDifference.heatStepGrid r u (i + 1)| <= M := by
    exact FiniteDifference.heatStepGrid_abs_le r u (i + 1) M
      hr0 hrCfl h1 h2 h3
  have hOne2 : |FiniteDifference.heatStepGrid r u (i + 2)| <= M := by
    exact FiniteDifference.heatStepGrid_abs_le r u (i + 2) M
      hr0 hrCfl h2 h3 h4
  have hOne3 : |FiniteDifference.heatStepGrid r u (i + 3)| <= M := by
    exact FiniteDifference.heatStepGrid_abs_le r u (i + 3) M
      hr0 hrCfl h3 h4 h5
  have hOne4 : |FiniteDifference.heatStepGrid r u (i + 4)| <= M := by
    exact FiniteDifference.heatStepGrid_abs_le r u (i + 4) M
      hr0 hrCfl h4 h5 h6
  have hTwo0 :
      |FiniteDifference.heatStepGrid r
        (fun j => FiniteDifference.heatStepGrid r u j) i| <= M := by
    exact FiniteDifference.heatStepGrid_abs_le r
      (fun j => FiniteDifference.heatStepGrid r u j) i M
      hr0 hrCfl hOne0 hOne1 hOne2
  have hTwo1 :
      |FiniteDifference.heatStepGrid r
        (fun j => FiniteDifference.heatStepGrid r u j) (i + 1)| <= M := by
    exact FiniteDifference.heatStepGrid_abs_le r
      (fun j => FiniteDifference.heatStepGrid r u j) (i + 1) M
      hr0 hrCfl hOne1 hOne2 hOne3
  have hTwo2 :
      |FiniteDifference.heatStepGrid r
        (fun j => FiniteDifference.heatStepGrid r u j) (i + 2)| <= M := by
    exact FiniteDifference.heatStepGrid_abs_le r
      (fun j => FiniteDifference.heatStepGrid r u j) (i + 2) M
      hr0 hrCfl hOne2 hOne3 hOne4
  exact FiniteDifference.heatStep_abs_le r
    (FiniteDifference.heatStepGrid r
      (fun j => FiniteDifference.heatStepGrid r u j) i)
    (FiniteDifference.heatStepGrid r
      (fun j => FiniteDifference.heatStepGrid r u j) (i + 1))
    (FiniteDifference.heatStepGrid r
      (fun j => FiniteDifference.heatStepGrid r u j) (i + 2))
    M hr0 hrCfl hTwo0 hTwo1 hTwo2

theorem v4p01_hard_heat_three_step_grid_api_abs_le
    (r : Real) (u : Nat -> Real) (i : Nat) (M : Real)
    (hr0 : 0 <= r) (hrCfl : 2 * r <= 1)
    (h0 : |u i| <= M) (h1 : |u (i + 1)| <= M)
    (h2 : |u (i + 2)| <= M) (h3 : |u (i + 3)| <= M)
    (h4 : |u (i + 4)| <= M) (h5 : |u (i + 5)| <= M)
    (h6 : |u (i + 6)| <= M) :
    |FiniteDifference.heatStepGrid r
        (fun j => FiniteDifference.heatStepGrid r
          (fun k => FiniteDifference.heatStepGrid r u k) j) i| <= M := by
  have hOne0 : |FiniteDifference.heatStepGrid r u i| <= M := by
    exact FiniteDifference.heatStepGrid_abs_le r u i M
      hr0 hrCfl h0 h1 h2
  have hOne1 : |FiniteDifference.heatStepGrid r u (i + 1)| <= M := by
    exact FiniteDifference.heatStepGrid_abs_le r u (i + 1) M
      hr0 hrCfl h1 h2 h3
  have hOne2 : |FiniteDifference.heatStepGrid r u (i + 2)| <= M := by
    exact FiniteDifference.heatStepGrid_abs_le r u (i + 2) M
      hr0 hrCfl h2 h3 h4
  have hOne3 : |FiniteDifference.heatStepGrid r u (i + 3)| <= M := by
    exact FiniteDifference.heatStepGrid_abs_le r u (i + 3) M
      hr0 hrCfl h3 h4 h5
  have hOne4 : |FiniteDifference.heatStepGrid r u (i + 4)| <= M := by
    exact FiniteDifference.heatStepGrid_abs_le r u (i + 4) M
      hr0 hrCfl h4 h5 h6
  have hTwo0 :
      |FiniteDifference.heatStepGrid r
        (fun j => FiniteDifference.heatStepGrid r u j) i| <= M := by
    exact FiniteDifference.heatStepGrid_abs_le r
      (fun j => FiniteDifference.heatStepGrid r u j) i M
      hr0 hrCfl hOne0 hOne1 hOne2
  have hTwo1 :
      |FiniteDifference.heatStepGrid r
        (fun j => FiniteDifference.heatStepGrid r u j) (i + 1)| <= M := by
    exact FiniteDifference.heatStepGrid_abs_le r
      (fun j => FiniteDifference.heatStepGrid r u j) (i + 1) M
      hr0 hrCfl hOne1 hOne2 hOne3
  have hTwo2 :
      |FiniteDifference.heatStepGrid r
        (fun j => FiniteDifference.heatStepGrid r u j) (i + 2)| <= M := by
    exact FiniteDifference.heatStepGrid_abs_le r
      (fun j => FiniteDifference.heatStepGrid r u j) (i + 2) M
      hr0 hrCfl hOne2 hOne3 hOne4
  exact FiniteDifference.heatStepGrid_abs_le r
    (fun j => FiniteDifference.heatStepGrid r
      (fun k => FiniteDifference.heatStepGrid r u k) j) i M
    hr0 hrCfl hTwo0 hTwo1 hTwo2

theorem v4p04_easy_lax_three_step_exposed_final_weights_abs_le
    (cfl u0 u1 u2 u3 M : Real)
    (hcflLower : -1 <= cfl) (hcflUpper : cfl <= 1)
    (h0 : |u0| <= M) (h1 : |u1| <= M)
    (h2 : |u2| <= M) (h3 : |u3| <= M) :
    |FiniteDifference.laxFriedrichsLeftWeight cfl *
        (FiniteDifference.laxFriedrichsStep cfl
          (FiniteDifference.laxFriedrichsStep cfl u0 u1)
          (FiniteDifference.laxFriedrichsStep cfl u1 u2)) +
      FiniteDifference.laxFriedrichsRightWeight cfl *
        (FiniteDifference.laxFriedrichsStep cfl
          (FiniteDifference.laxFriedrichsStep cfl u1 u2)
          (FiniteDifference.laxFriedrichsStep cfl u2 u3))| <= M := by
  have hOne01 :
      |FiniteDifference.laxFriedrichsStep cfl u0 u1| <= M := by
    exact FiniteDifference.laxFriedrichsStep_abs_le
      cfl u0 u1 M hcflLower hcflUpper h0 h1
  have hOne12 :
      |FiniteDifference.laxFriedrichsStep cfl u1 u2| <= M := by
    exact FiniteDifference.laxFriedrichsStep_abs_le
      cfl u1 u2 M hcflLower hcflUpper h1 h2
  have hOne23 :
      |FiniteDifference.laxFriedrichsStep cfl u2 u3| <= M := by
    exact FiniteDifference.laxFriedrichsStep_abs_le
      cfl u2 u3 M hcflLower hcflUpper h2 h3
  have hTwo012 :
      |FiniteDifference.laxFriedrichsStep cfl
        (FiniteDifference.laxFriedrichsStep cfl u0 u1)
        (FiniteDifference.laxFriedrichsStep cfl u1 u2)| <= M := by
    exact FiniteDifference.laxFriedrichsStep_abs_le cfl
      (FiniteDifference.laxFriedrichsStep cfl u0 u1)
      (FiniteDifference.laxFriedrichsStep cfl u1 u2)
      M hcflLower hcflUpper hOne01 hOne12
  have hTwo123 :
      |FiniteDifference.laxFriedrichsStep cfl
        (FiniteDifference.laxFriedrichsStep cfl u1 u2)
        (FiniteDifference.laxFriedrichsStep cfl u2 u3)| <= M := by
    exact FiniteDifference.laxFriedrichsStep_abs_le cfl
      (FiniteDifference.laxFriedrichsStep cfl u1 u2)
      (FiniteDifference.laxFriedrichsStep cfl u2 u3)
      M hcflLower hcflUpper hOne12 hOne23
  simpa [FiniteDifference.laxFriedrichsStep] using
    FiniteDifference.laxFriedrichsStep_abs_le cfl
      (FiniteDifference.laxFriedrichsStep cfl
        (FiniteDifference.laxFriedrichsStep cfl u0 u1)
        (FiniteDifference.laxFriedrichsStep cfl u1 u2))
      (FiniteDifference.laxFriedrichsStep cfl
        (FiniteDifference.laxFriedrichsStep cfl u1 u2)
        (FiniteDifference.laxFriedrichsStep cfl u2 u3))
      M hcflLower hcflUpper hTwo012 hTwo123

theorem v4p04_hard_lax_three_step_nested_api_abs_le
    (cfl u0 u1 u2 u3 M : Real)
    (hcflLower : -1 <= cfl) (hcflUpper : cfl <= 1)
    (h0 : |u0| <= M) (h1 : |u1| <= M)
    (h2 : |u2| <= M) (h3 : |u3| <= M) :
    |FiniteDifference.laxFriedrichsStep cfl
        (FiniteDifference.laxFriedrichsStep cfl
          (FiniteDifference.laxFriedrichsStep cfl u0 u1)
          (FiniteDifference.laxFriedrichsStep cfl u1 u2))
        (FiniteDifference.laxFriedrichsStep cfl
          (FiniteDifference.laxFriedrichsStep cfl u1 u2)
          (FiniteDifference.laxFriedrichsStep cfl u2 u3))| <= M := by
  have hOne01 :
      |FiniteDifference.laxFriedrichsStep cfl u0 u1| <= M := by
    exact FiniteDifference.laxFriedrichsStep_abs_le
      cfl u0 u1 M hcflLower hcflUpper h0 h1
  have hOne12 :
      |FiniteDifference.laxFriedrichsStep cfl u1 u2| <= M := by
    exact FiniteDifference.laxFriedrichsStep_abs_le
      cfl u1 u2 M hcflLower hcflUpper h1 h2
  have hOne23 :
      |FiniteDifference.laxFriedrichsStep cfl u2 u3| <= M := by
    exact FiniteDifference.laxFriedrichsStep_abs_le
      cfl u2 u3 M hcflLower hcflUpper h2 h3
  have hTwo012 :
      |FiniteDifference.laxFriedrichsStep cfl
        (FiniteDifference.laxFriedrichsStep cfl u0 u1)
        (FiniteDifference.laxFriedrichsStep cfl u1 u2)| <= M := by
    exact FiniteDifference.laxFriedrichsStep_abs_le cfl
      (FiniteDifference.laxFriedrichsStep cfl u0 u1)
      (FiniteDifference.laxFriedrichsStep cfl u1 u2)
      M hcflLower hcflUpper hOne01 hOne12
  have hTwo123 :
      |FiniteDifference.laxFriedrichsStep cfl
        (FiniteDifference.laxFriedrichsStep cfl u1 u2)
        (FiniteDifference.laxFriedrichsStep cfl u2 u3)| <= M := by
    exact FiniteDifference.laxFriedrichsStep_abs_le cfl
      (FiniteDifference.laxFriedrichsStep cfl u1 u2)
      (FiniteDifference.laxFriedrichsStep cfl u2 u3)
      M hcflLower hcflUpper hOne12 hOne23
  exact FiniteDifference.laxFriedrichsStep_abs_le cfl
    (FiniteDifference.laxFriedrichsStep cfl
      (FiniteDifference.laxFriedrichsStep cfl u0 u1)
      (FiniteDifference.laxFriedrichsStep cfl u1 u2))
    (FiniteDifference.laxFriedrichsStep cfl
      (FiniteDifference.laxFriedrichsStep cfl u1 u2)
      (FiniteDifference.laxFriedrichsStep cfl u2 u3))
    M hcflLower hcflUpper hTwo012 hTwo123

theorem v4p06_easy_upwind_three_step_exposed_final_weights_abs_le
    (cfl uMinus u0 u1 u2 M : Real)
    (hcfl0 : 0 <= cfl) (hcfl1 : cfl <= 1)
    (hMinus : |uMinus| <= M) (h0 : |u0| <= M)
    (h1 : |u1| <= M) (h2 : |u2| <= M) :
    |(1 - cfl) *
        (FiniteDifference.upwindStep cfl
          (FiniteDifference.upwindStep cfl u0 u1)
          (FiniteDifference.upwindStep cfl u1 u2)) +
      cfl *
        (FiniteDifference.upwindStep cfl
          (FiniteDifference.upwindStep cfl uMinus u0)
          (FiniteDifference.upwindStep cfl u0 u1))| <= M := by
  have hOneMinus0 :
      |FiniteDifference.upwindStep cfl uMinus u0| <= M := by
    exact FiniteDifference.upwindStep_abs_le
      cfl uMinus u0 M hcfl0 hcfl1 hMinus h0
  have hOne01 :
      |FiniteDifference.upwindStep cfl u0 u1| <= M := by
    exact FiniteDifference.upwindStep_abs_le
      cfl u0 u1 M hcfl0 hcfl1 h0 h1
  have hOne12 :
      |FiniteDifference.upwindStep cfl u1 u2| <= M := by
    exact FiniteDifference.upwindStep_abs_le
      cfl u1 u2 M hcfl0 hcfl1 h1 h2
  have hTwoLeft :
      |FiniteDifference.upwindStep cfl
        (FiniteDifference.upwindStep cfl uMinus u0)
        (FiniteDifference.upwindStep cfl u0 u1)| <= M := by
    exact FiniteDifference.upwindStep_abs_le cfl
      (FiniteDifference.upwindStep cfl uMinus u0)
      (FiniteDifference.upwindStep cfl u0 u1)
      M hcfl0 hcfl1 hOneMinus0 hOne01
  have hTwoCenter :
      |FiniteDifference.upwindStep cfl
        (FiniteDifference.upwindStep cfl u0 u1)
        (FiniteDifference.upwindStep cfl u1 u2)| <= M := by
    exact FiniteDifference.upwindStep_abs_le cfl
      (FiniteDifference.upwindStep cfl u0 u1)
      (FiniteDifference.upwindStep cfl u1 u2)
      M hcfl0 hcfl1 hOne01 hOne12
  simpa [FiniteDifference.upwindStep] using
    FiniteDifference.upwindStep_abs_le cfl
      (FiniteDifference.upwindStep cfl
        (FiniteDifference.upwindStep cfl uMinus u0)
        (FiniteDifference.upwindStep cfl u0 u1))
      (FiniteDifference.upwindStep cfl
        (FiniteDifference.upwindStep cfl u0 u1)
        (FiniteDifference.upwindStep cfl u1 u2))
      M hcfl0 hcfl1 hTwoLeft hTwoCenter

theorem v4p06_hard_upwind_three_step_nested_api_abs_le
    (cfl uMinus u0 u1 u2 M : Real)
    (hcfl0 : 0 <= cfl) (hcfl1 : cfl <= 1)
    (hMinus : |uMinus| <= M) (h0 : |u0| <= M)
    (h1 : |u1| <= M) (h2 : |u2| <= M) :
    |FiniteDifference.upwindStep cfl
        (FiniteDifference.upwindStep cfl
          (FiniteDifference.upwindStep cfl uMinus u0)
          (FiniteDifference.upwindStep cfl u0 u1))
        (FiniteDifference.upwindStep cfl
          (FiniteDifference.upwindStep cfl u0 u1)
          (FiniteDifference.upwindStep cfl u1 u2))| <= M := by
  have hOneMinus0 :
      |FiniteDifference.upwindStep cfl uMinus u0| <= M := by
    exact FiniteDifference.upwindStep_abs_le
      cfl uMinus u0 M hcfl0 hcfl1 hMinus h0
  have hOne01 :
      |FiniteDifference.upwindStep cfl u0 u1| <= M := by
    exact FiniteDifference.upwindStep_abs_le
      cfl u0 u1 M hcfl0 hcfl1 h0 h1
  have hOne12 :
      |FiniteDifference.upwindStep cfl u1 u2| <= M := by
    exact FiniteDifference.upwindStep_abs_le
      cfl u1 u2 M hcfl0 hcfl1 h1 h2
  have hTwoLeft :
      |FiniteDifference.upwindStep cfl
        (FiniteDifference.upwindStep cfl uMinus u0)
        (FiniteDifference.upwindStep cfl u0 u1)| <= M := by
    exact FiniteDifference.upwindStep_abs_le cfl
      (FiniteDifference.upwindStep cfl uMinus u0)
      (FiniteDifference.upwindStep cfl u0 u1)
      M hcfl0 hcfl1 hOneMinus0 hOne01
  have hTwoCenter :
      |FiniteDifference.upwindStep cfl
        (FiniteDifference.upwindStep cfl u0 u1)
        (FiniteDifference.upwindStep cfl u1 u2)| <= M := by
    exact FiniteDifference.upwindStep_abs_le cfl
      (FiniteDifference.upwindStep cfl u0 u1)
      (FiniteDifference.upwindStep cfl u1 u2)
      M hcfl0 hcfl1 hOne01 hOne12
  exact FiniteDifference.upwindStep_abs_le cfl
    (FiniteDifference.upwindStep cfl
      (FiniteDifference.upwindStep cfl uMinus u0)
      (FiniteDifference.upwindStep cfl u0 u1))
    (FiniteDifference.upwindStep cfl
      (FiniteDifference.upwindStep cfl u0 u1)
      (FiniteDifference.upwindStep cfl u1 u2))
    M hcfl0 hcfl1 hTwoLeft hTwoCenter

theorem v4p10_easy_kdv_two_updates_mass_direct
    (scale : Real) (u : Nat -> Real) (n : Nat)
    (hflux0 :
      FiniteDifference.kdvCanonicalFlux u n =
        FiniteDifference.kdvCanonicalFlux u 0)
    (hflux1 :
      FiniteDifference.kdvCanonicalFlux
          (fun i => FiniteDifference.kdvCanonicalUpdate scale u i) n =
        FiniteDifference.kdvCanonicalFlux
          (fun i => FiniteDifference.kdvCanonicalUpdate scale u i) 0) :
    FiniteDifference.discreteMass
        (fun i => FiniteDifference.kdvCanonicalUpdate scale
          (fun j => FiniteDifference.kdvCanonicalUpdate scale u j) i) n =
      FiniteDifference.discreteMass u n := by
  have hFirst :
      FiniteDifference.discreteMass
          (fun i => FiniteDifference.kdvCanonicalUpdate scale u i) n =
        FiniteDifference.discreteMass u n := by
    exact FiniteDifference.discreteMass_kdvCanonicalUpdate_of_boundary_eq
      scale u n hflux0
  have hSecond :
      FiniteDifference.discreteMass
          (fun i => FiniteDifference.kdvCanonicalUpdate scale
            (fun j => FiniteDifference.kdvCanonicalUpdate scale u j) i) n =
        FiniteDifference.discreteMass
          (fun i => FiniteDifference.kdvCanonicalUpdate scale u i) n := by
    exact FiniteDifference.discreteMass_kdvCanonicalUpdate_of_boundary_eq
      scale (fun i => FiniteDifference.kdvCanonicalUpdate scale u i) n hflux1
  rw [hSecond, hFirst]

theorem v4p10_hard_kdv_two_updates_exposed_mass_change_zero
    (scale : Real) (u : Nat -> Real) (n : Nat)
    (hflux0 :
      FiniteDifference.kdvCanonicalFlux u n =
        FiniteDifference.kdvCanonicalFlux u 0)
    (hflux1 :
      FiniteDifference.kdvCanonicalFlux
          (fun i => FiniteDifference.kdvCanonicalUpdate scale u i) n =
        FiniteDifference.kdvCanonicalFlux
          (fun i => FiniteDifference.kdvCanonicalUpdate scale u i) 0) :
    Finset.sum (Finset.range n)
        (fun i => FiniteDifference.kdvCanonicalUpdate scale
          (fun j => FiniteDifference.kdvCanonicalUpdate scale u j) i) -
      Finset.sum (Finset.range n) (fun i => u i) = 0 := by
  have hmass :
      FiniteDifference.discreteMass
          (fun i => FiniteDifference.kdvCanonicalUpdate scale
            (fun j => FiniteDifference.kdvCanonicalUpdate scale u j) i) n =
        FiniteDifference.discreteMass u n := by
    exact v4p10_easy_kdv_two_updates_mass_direct
      scale u n hflux0 hflux1
  simpa [FiniteDifference.discreteMass, FiniteDifference.totalOn] using
    sub_eq_zero.mpr hmass

theorem v4p14_easy_weighted_p0_additive_orthogonal_split
    {alpha : Type} (s : Finset alpha) (m u v : alpha -> Real) (c : Real)
    (hmass : Ne (Finset.sum s (fun i => m i)) 0) :
    Finset.sum s (fun i => m i * FEM.weightedP0Residual s m u i * c) +
      Finset.sum s (fun i => m i * FEM.weightedP0Residual s m v i * c) = 0 := by
  have hu :
      Finset.sum s (fun i => m i * FEM.weightedP0Residual s m u i * c) = 0 := by
    exact FEM.weightedP0Projection_orthogonal_const s m u c hmass
  have hv :
      Finset.sum s (fun i => m i * FEM.weightedP0Residual s m v i * c) = 0 := by
    exact FEM.weightedP0Projection_orthogonal_const s m v c hmass
  rw [hu, hv]
  ring

theorem v4p14_hard_weighted_p0_additive_exposed_residual
    {alpha : Type} (s : Finset alpha) (m u v : alpha -> Real) (c : Real)
    (hmass : Ne (Finset.sum s (fun i => m i)) 0) :
    Finset.sum s
        (fun i => m i *
          ((u i + v i) - FEM.weightedP0Average s m (fun j => u j + v j)) *
          c) = 0 := by
  simpa [FEM.weightedP0Residual] using
    FEM.weightedP0Projection_orthogonal_const
      s m (fun j => u j + v j) c hmass

theorem v4p19_easy_finite_row_two_stage_exposed_sum_abs_le
    {alpha : Type} (s : Finset alpha) (a b x : alpha -> Real) (M : Real)
    (ha : forall i, Membership.mem s i -> 0 <= a i)
    (hsumA : Finset.sum s (fun i => a i) = 1)
    (hb : forall i, Membership.mem s i -> 0 <= b i)
    (hsumB : Finset.sum s (fun i => b i) = 1)
    (hx : forall i, Membership.mem s i -> |x i| <= M) :
    |Finset.sum s (fun i => a i * LinearAlgebra.finiteRowApply s b x)| <= M := by
  have hInner :
      |LinearAlgebra.finiteRowApply s b x| <= M := by
    exact LinearAlgebra.finiteRowApply_abs_le s b x M hb hsumB hx
  simpa [LinearAlgebra.finiteRowApply] using
    LinearAlgebra.finiteRowApply_abs_le s a
      (fun _ => LinearAlgebra.finiteRowApply s b x) M
      ha hsumA (by
        intro i hi
        exact hInner)

theorem v4p19_hard_finite_row_two_stage_nested_api_abs_le
    {alpha : Type} (s : Finset alpha) (a b x : alpha -> Real) (M : Real)
    (ha : forall i, Membership.mem s i -> 0 <= a i)
    (hsumA : Finset.sum s (fun i => a i) = 1)
    (hb : forall i, Membership.mem s i -> 0 <= b i)
    (hsumB : Finset.sum s (fun i => b i) = 1)
    (hx : forall i, Membership.mem s i -> |x i| <= M) :
    |LinearAlgebra.finiteRowApply s a
        (fun _ => LinearAlgebra.finiteRowApply s b x)| <= M := by
  have hInner :
      |LinearAlgebra.finiteRowApply s b x| <= M := by
    exact LinearAlgebra.finiteRowApply_abs_le s b x M hb hsumB hx
  exact LinearAlgebra.finiteRowApply_abs_le s a
    (fun _ => LinearAlgebra.finiteRowApply s b x) M
    ha hsumA (by
      intro i hi
      exact hInner)

theorem v4p20_easy_row2_three_stage_abs_le
    (a b c d e f g h p q r s x0 x1 x2 x3 M : Real)
    (ha : 0 <= a) (hb : 0 <= b) (hab : a + b = 1)
    (hc : 0 <= c) (hd : 0 <= d) (hcd : c + d = 1)
    (he : 0 <= e) (hf : 0 <= f) (hef : e + f = 1)
    (hg : 0 <= g) (hh : 0 <= h) (hgh : g + h = 1)
    (hp : 0 <= p) (hq : 0 <= q) (hpq : p + q = 1)
    (hr : 0 <= r) (hs : 0 <= s) (hrs : r + s = 1)
    (hx0 : |x0| <= M) (hx1 : |x1| <= M)
    (hx2 : |x2| <= M) (hx3 : |x3| <= M) :
    |LinearAlgebra.row2Apply a b
        (LinearAlgebra.row2Apply c d
          (LinearAlgebra.row2Apply g h x0 x1)
          (LinearAlgebra.row2Apply p q x1 x2))
        (LinearAlgebra.row2Apply e f
          (LinearAlgebra.row2Apply p q x1 x2)
          (LinearAlgebra.row2Apply r s x2 x3))| <= M := by
  have h01 :
      |LinearAlgebra.row2Apply g h x0 x1| <= M := by
    exact LinearAlgebra.row2Apply_abs_le g h x0 x1 M hg hh hgh hx0 hx1
  have h12 :
      |LinearAlgebra.row2Apply p q x1 x2| <= M := by
    exact LinearAlgebra.row2Apply_abs_le p q x1 x2 M hp hq hpq hx1 hx2
  have h23 :
      |LinearAlgebra.row2Apply r s x2 x3| <= M := by
    exact LinearAlgebra.row2Apply_abs_le r s x2 x3 M hr hs hrs hx2 hx3
  have h012 :
      |LinearAlgebra.row2Apply c d
        (LinearAlgebra.row2Apply g h x0 x1)
        (LinearAlgebra.row2Apply p q x1 x2)| <= M := by
    exact LinearAlgebra.row2Apply_abs_le c d
      (LinearAlgebra.row2Apply g h x0 x1)
      (LinearAlgebra.row2Apply p q x1 x2)
      M hc hd hcd h01 h12
  have h123 :
      |LinearAlgebra.row2Apply e f
        (LinearAlgebra.row2Apply p q x1 x2)
        (LinearAlgebra.row2Apply r s x2 x3)| <= M := by
    exact LinearAlgebra.row2Apply_abs_le e f
      (LinearAlgebra.row2Apply p q x1 x2)
      (LinearAlgebra.row2Apply r s x2 x3)
      M he hf hef h12 h23
  exact LinearAlgebra.row2Apply_abs_le a b
    (LinearAlgebra.row2Apply c d
      (LinearAlgebra.row2Apply g h x0 x1)
      (LinearAlgebra.row2Apply p q x1 x2))
    (LinearAlgebra.row2Apply e f
      (LinearAlgebra.row2Apply p q x1 x2)
      (LinearAlgebra.row2Apply r s x2 x3))
    M ha hb hab h012 h123

theorem v4p20_hard_row_stochastic_three_stage_wrapper_abs_le
    (a b c d e f g h p q r s x0 x1 x2 x3 M : Real)
    (ha : 0 <= a) (hb : 0 <= b) (hab : a + b = 1)
    (hc : 0 <= c) (hd : 0 <= d) (hcd : c + d = 1)
    (he : 0 <= e) (hf : 0 <= f) (hef : e + f = 1)
    (hg : 0 <= g) (hh : 0 <= h) (hgh : g + h = 1)
    (hp : 0 <= p) (hq : 0 <= q) (hpq : p + q = 1)
    (hr : 0 <= r) (hs : 0 <= s) (hrs : r + s = 1)
    (hx0 : |x0| <= M) (hx1 : |x1| <= M)
    (hx2 : |x2| <= M) (hx3 : |x3| <= M) :
    |LinearAlgebra.rowStochastic2First a b
        (LinearAlgebra.rowStochastic2First c d
          (LinearAlgebra.rowStochastic2First g h x0 x1)
          (LinearAlgebra.rowStochastic2First p q x1 x2))
        (LinearAlgebra.rowStochastic2First e f
          (LinearAlgebra.rowStochastic2First p q x1 x2)
          (LinearAlgebra.rowStochastic2First r s x2 x3))| <= M := by
  simpa [LinearAlgebra.rowStochastic2First] using
    v4p20_easy_row2_three_stage_abs_le
      a b c d e f g h p q r s x0 x1 x2 x3 M
      ha hb hab hc hd hcd he hf hef hg hh hgh hp hq hpq hr hs hrs
      hx0 hx1 hx2 hx3

theorem v4p22_easy_leapfrog_three_direct_steps
    (omega dt x xPrev : Real) (hdt : Ne dt 0) :
    Symplectic.leapfrogInvariant omega dt
        (Symplectic.leapfrogStep omega dt
          (Symplectic.leapfrogStep omega dt
            (Symplectic.leapfrogStep omega dt x xPrev) x)
          (Symplectic.leapfrogStep omega dt x xPrev))
        (Symplectic.leapfrogStep omega dt
          (Symplectic.leapfrogStep omega dt x xPrev) x) =
      Symplectic.leapfrogInvariant omega dt x xPrev := by
  calc
    Symplectic.leapfrogInvariant omega dt
        (Symplectic.leapfrogStep omega dt
          (Symplectic.leapfrogStep omega dt
            (Symplectic.leapfrogStep omega dt x xPrev) x)
          (Symplectic.leapfrogStep omega dt x xPrev))
        (Symplectic.leapfrogStep omega dt
          (Symplectic.leapfrogStep omega dt x xPrev) x)
        = Symplectic.leapfrogInvariant omega dt
            (Symplectic.leapfrogStep omega dt
              (Symplectic.leapfrogStep omega dt x xPrev) x)
            (Symplectic.leapfrogStep omega dt x xPrev) := by
            exact Symplectic.leapfrogInvariant_preserved omega dt
              (Symplectic.leapfrogStep omega dt
                (Symplectic.leapfrogStep omega dt x xPrev) x)
              (Symplectic.leapfrogStep omega dt x xPrev) hdt
    _ = Symplectic.leapfrogInvariant omega dt
          (Symplectic.leapfrogStep omega dt x xPrev) x := by
            exact Symplectic.leapfrogInvariant_preserved omega dt
              (Symplectic.leapfrogStep omega dt x xPrev) x hdt
    _ = Symplectic.leapfrogInvariant omega dt x xPrev := by
            exact Symplectic.leapfrogInvariant_preserved omega dt x xPrev hdt

theorem v4p22_hard_leapfrog_three_orbit_steps
    (omega dt : Real) (hdt : Ne dt 0) (x : Nat -> Real)
    (hx : Symplectic.IsLeapfrogOrbit omega dt x) (n : Nat) :
    Symplectic.leapfrogInvariant omega dt (x (n + 4)) (x (n + 3)) =
      Symplectic.leapfrogInvariant omega dt (x (n + 1)) (x n) := by
  calc
    Symplectic.leapfrogInvariant omega dt (x (n + 4)) (x (n + 3))
        = Symplectic.leapfrogInvariant omega dt (x (n + 3)) (x (n + 2)) := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              Symplectic.leapfrogInvariant_step_of_isLeapfrogOrbit
                omega dt hdt x hx (n + 2)
    _ = Symplectic.leapfrogInvariant omega dt (x (n + 2)) (x (n + 1)) := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              Symplectic.leapfrogInvariant_step_of_isLeapfrogOrbit
                omega dt hdt x hx (n + 1)
    _ = Symplectic.leapfrogInvariant omega dt (x (n + 1)) (x n) := by
            exact Symplectic.leapfrogInvariant_step_of_isLeapfrogOrbit
              omega dt hdt x hx n

end

end LeanNumBenchMinimalPairsV4
end LeanNumerics
