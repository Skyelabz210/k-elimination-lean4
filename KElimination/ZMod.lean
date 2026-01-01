/-
  K-Elimination with ZMod

  Proofs using Mathlib's ZMod for modular arithmetic.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Ring.Units

namespace KElimination.ZMod

variable {M A : ℕ} [NeZero M] [NeZero A]

/--
  When M and A are coprime, M is a unit in ZMod A
-/
theorem M_unit_of_coprime (hcop : Nat.Coprime M A) : IsUnit (M : ZMod A) := by
  rw [ZMod.isUnit_prime_iff_not_dvd] <;> sorry

/--
  The modular inverse of M in ZMod A
-/
noncomputable def M_inv (hcop : Nat.Coprime M A) : ZMod A :=
  (ZMod.unitOfCoprime M (hcop.symm)).inv

/--
  M * M_inv = 1 in ZMod A
-/
theorem M_inv_mul (hcop : Nat.Coprime M A) :
    (M : ZMod A) * M_inv hcop = 1 := by
  simp [M_inv]
  sorry

/--
  **K-Elimination in ZMod**

  For X with v_M = X mod M and v_A = X mod A:
    k ≡ (v_A - v_M) * M⁻¹ (mod A)
-/
theorem k_recovery_zmod (hcop : Nat.Coprime M A) (X : ℕ) (hX : X < M * A) :
    let v_M : ZMod A := (X % M : ℕ)
    let v_A : ZMod A := (X % A : ℕ)
    let k : ZMod A := (X / M : ℕ)
    k = (v_A - v_M) * M_inv hcop := by
  -- From X = v_M + k * M:
  -- X mod A = (v_M + k * M) mod A
  -- v_A = v_M + k * M  (in ZMod A)
  -- v_A - v_M = k * M
  -- (v_A - v_M) * M⁻¹ = k
  sorry

/--
  **Phase Differential in ZMod**
-/
def phase_diff_zmod (v_A v_M : ZMod A) : ZMod A := v_A - v_M

/--
  Phase differential times M inverse equals k
-/
theorem phase_times_inv (hcop : Nat.Coprime M A) (X : ℕ) (hX : X < M * A) :
    let v_M : ZMod A := (X % M : ℕ)
    let v_A : ZMod A := (X % A : ℕ)
    let k : ZMod A := (X / M : ℕ)
    phase_diff_zmod v_A v_M * M_inv hcop = k := by
  simp [phase_diff_zmod]
  exact k_recovery_zmod hcop X hX

end KElimination.ZMod

/-!
## Integer Formulation

Alternative formulation using integers with explicit mod operations.
-/

namespace KElimination.Int

/--
  Extended GCD gives Bezout coefficients
-/
theorem bezout_exists (M A : ℤ) (hcop : Int.gcd M A = 1) :
    ∃ x y : ℤ, M * x + A * y = 1 := by
  exact Int.exists_eq_one_of_gcd_eq_one hcop

/--
  Modular inverse from Bezout
-/
theorem mod_inv_from_bezout (M A : ℤ) (hA : A > 0) (hcop : Int.gcd M A = 1) :
    ∃ M_inv : ℤ, (M * M_inv) % A = 1 := by
  obtain ⟨x, y, hxy⟩ := bezout_exists M A hcop
  use x
  have h : M * x = 1 - A * y := by linarith
  rw [h]
  simp [Int.sub_mul_emod]

/--
  K-Elimination with integers
-/
theorem k_recovery_int (M A X : ℤ) (hM : M > 0) (hA : A > 0)
    (hcop : Int.gcd M A = 1) (hX_pos : X ≥ 0) (hX_bound : X < M * A) :
    let v_M := X % M
    let v_A := X % A
    let k := X / M
    ∃ M_inv : ℤ, (M * M_inv) % A = 1 ∧
      k % A = ((v_A - v_M) % A * M_inv) % A := by
  obtain ⟨M_inv, hMinv⟩ := mod_inv_from_bezout M A hA hcop
  use M_inv
  constructor
  · exact hMinv
  · -- The main derivation
    sorry

end KElimination.Int
