import Mathlib.Tactic

open scoped BigOperators

namespace LeanNumerics
namespace Spectral

noncomputable section

def dft2DC (u0 u1 : Real) : Real :=
  u0 + u1

def dft2Nyquist (u0 u1 : Real) : Real :=
  u0 - u1

def idft2First (low high : Real) : Real :=
  (low + high) / 2

def idft2Second (low high : Real) : Real :=
  (low - high) / 2

def dft2Energy (u0 u1 : Real) : Real :=
  dft2DC u0 u1 ^ 2 + dft2Nyquist u0 u1 ^ 2

def physical2Energy (u0 u1 : Real) : Real :=
  u0 ^ 2 + u1 ^ 2

def finiteDC {ι : Type} (s : Finset ι) (u : ι → Real) : Real :=
  ∑ i ∈ s, u i

def finiteMean {ι : Type} (s : Finset ι) (u : ι → Real) : Real :=
  finiteDC s u / (s.card : Real)

def centeredSignal {ι : Type} (s : Finset ι) (u : ι → Real) (i : ι) : Real :=
  u i - finiteMean s u

theorem dft2DC_const (u : Real) :
    dft2DC u u = 2 * u := by
  unfold dft2DC
  ring

theorem dft2Nyquist_const (u : Real) :
    dft2Nyquist u u = 0 := by
  unfold dft2Nyquist
  ring

theorem dft2DC_zero_sum (u0 u1 : Real) (h : u0 + u1 = 0) :
    dft2DC u0 u1 = 0 := by
  unfold dft2DC
  exact h

theorem idft2First_dft2 (u0 u1 : Real) :
    idft2First (dft2DC u0 u1) (dft2Nyquist u0 u1) = u0 := by
  unfold idft2First dft2DC dft2Nyquist
  ring

theorem idft2Second_dft2 (u0 u1 : Real) :
    idft2Second (dft2DC u0 u1) (dft2Nyquist u0 u1) = u1 := by
  unfold idft2Second dft2DC dft2Nyquist
  ring

theorem dft2_inverse (u0 u1 : Real) :
    idft2First (dft2DC u0 u1) (dft2Nyquist u0 u1) = u0 /\
      idft2Second (dft2DC u0 u1) (dft2Nyquist u0 u1) = u1 := by
  exact And.intro (idft2First_dft2 u0 u1) (idft2Second_dft2 u0 u1)

theorem dft2DC_swap (u0 u1 : Real) :
    dft2DC u1 u0 = dft2DC u0 u1 := by
  unfold dft2DC
  ring

theorem dft2Nyquist_swap (u0 u1 : Real) :
    dft2Nyquist u1 u0 = -dft2Nyquist u0 u1 := by
  unfold dft2Nyquist
  ring

theorem dft2Energy_eq_two_physical2Energy (u0 u1 : Real) :
    dft2Energy u0 u1 = 2 * physical2Energy u0 u1 := by
  unfold dft2Energy physical2Energy dft2DC dft2Nyquist
  ring

theorem dft2_parseval (u0 u1 : Real) :
    dft2Energy u0 u1 / 2 = physical2Energy u0 u1 := by
  rw [dft2Energy_eq_two_physical2Energy]
  ring

theorem finiteDC_centeredSignal_zero
    {ι : Type} (s : Finset ι) (u : ι → Real)
    (hcard : (s.card : Real) ≠ 0) :
    finiteDC s (centeredSignal s u) = 0 := by
  unfold centeredSignal finiteMean finiteDC
  rw [Finset.sum_sub_distrib, Finset.sum_const]
  simp [nsmul_eq_mul]
  field_simp [hcard]
  ring

theorem finiteDC_const {ι : Type} (s : Finset ι) (c : Real) :
    finiteDC s (fun _ => c) = (s.card : Real) * c := by
  unfold finiteDC
  rw [Finset.sum_const]
  simp [nsmul_eq_mul]

theorem finiteDC_add {ι : Type} (s : Finset ι) (u v : ι → Real) :
    finiteDC s (fun i => u i + v i) = finiteDC s u + finiteDC s v := by
  unfold finiteDC
  rw [Finset.sum_add_distrib]

theorem finiteDC_zero {ι : Type} (s : Finset ι) :
    finiteDC s (fun _ => 0) = 0 := by
  unfold finiteDC
  simp

theorem finiteDC_neg {ι : Type} (s : Finset ι) (u : ι → Real) :
    finiteDC s (fun i => -u i) = -finiteDC s u := by
  unfold finiteDC
  rw [← Finset.sum_neg_distrib]

theorem finiteDC_sub {ι : Type} (s : Finset ι) (u v : ι → Real) :
    finiteDC s (fun i => u i - v i) = finiteDC s u - finiteDC s v := by
  unfold finiteDC
  rw [Finset.sum_sub_distrib]

theorem finiteDC_smul {ι : Type} (s : Finset ι) (u : ι → Real) (c : Real) :
    finiteDC s (fun i => c * u i) = c * finiteDC s u := by
  unfold finiteDC
  rw [Finset.mul_sum]

theorem finiteMean_const {ι : Type} (s : Finset ι) (c : Real)
    (hcard : (s.card : Real) ≠ 0) :
    finiteMean s (fun _ => c) = c := by
  unfold finiteMean
  rw [finiteDC_const]
  field_simp [hcard]

theorem finiteMean_add {ι : Type} (s : Finset ι) (u v : ι → Real) :
    finiteMean s (fun i => u i + v i) = finiteMean s u + finiteMean s v := by
  unfold finiteMean
  rw [finiteDC_add]
  ring

theorem finiteMean_smul {ι : Type} (s : Finset ι) (u : ι → Real) (c : Real) :
    finiteMean s (fun i => c * u i) = c * finiteMean s u := by
  unfold finiteMean
  rw [finiteDC_smul]
  ring

theorem centeredSignal_const_zero {ι : Type} (s : Finset ι) (c : Real) (i : ι)
    (hcard : (s.card : Real) ≠ 0) :
    centeredSignal s (fun _ => c) i = 0 := by
  unfold centeredSignal
  rw [finiteMean_const s c hcard]
  ring

theorem centeredSignal_add {ι : Type} (s : Finset ι) (u v : ι → Real) (i : ι) :
    centeredSignal s (fun j => u j + v j) i =
      centeredSignal s u i + centeredSignal s v i := by
  unfold centeredSignal
  rw [finiteMean_add]
  ring

theorem centeredSignal_smul {ι : Type} (s : Finset ι) (u : ι → Real)
    (c : Real) (i : ι) :
    centeredSignal s (fun j => c * u j) i = c * centeredSignal s u i := by
  unfold centeredSignal
  rw [finiteMean_smul]
  ring

end

end Spectral
end LeanNumerics
