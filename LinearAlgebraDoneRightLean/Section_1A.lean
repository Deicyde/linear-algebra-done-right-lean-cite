import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Recall
import Mathlib.Tactic.Ring
import CompanionHelper
import LinearAlgebraDoneRightLean.Sources

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 1A: ℝⁿ and ℂⁿ
-/

namespace LADR.Section_1A

open Complex

/-! 1.1 Definition: complex numbers -/

cite ladr4e "1.1" in
example : ℂ := ⟨1, 2⟩
cite ladr4e "1.1" in
example : (⟨1, 2⟩ : ℂ).re = 1 := rfl
cite ladr4e "1.1" in
example : (⟨1, 2⟩ : ℂ).im = 2 := rfl

cite ladr4e "1.1" in
example : ℂ := I
cite ladr4e "1.1" in
example : I ^ 2 = -1 := I_sq

cite ladr4e "1.1" in
recall Complex.re_add_im (z : ℂ) : (z.re : ℂ) + z.im * I = z

cite ladr4e "1.1" in
example (z : ℂ) : ∃ a b : ℝ, z = a + b * I :=
  ⟨z.re, z.im, (re_add_im z).symm⟩

cite ladr4e "1.1" in
recall Complex.add_re (z w : ℂ) : (z + w).re = z.re + w.re
cite ladr4e "1.1" in
recall Complex.add_im (z w : ℂ) : (z + w).im = z.im + w.im
cite ladr4e "1.1" in
recall Complex.mul_re (z w : ℂ) : (z * w).re = z.re * w.re - z.im * w.im
cite ladr4e "1.1" in
recall Complex.mul_im (z w : ℂ) : (z * w).im = z.re * w.im + z.im * w.re

/-! 1.2 Example: complex arithmetic -/

cite ladr4e "1.2" in
example : (2 + 3 * I) * (4 + 5 * I) = -7 + 22 * I := by
  apply Complex.ext <;> simp <;> ring

/-! 1.3 Properties of complex arithmetic -/

@[cite ladr4e "Exercise 1A.1", cite ladr4e "1.3", avoiding Complex.commRing, Complex.instCommSemiring, Complex.instField]
theorem exercise_1A_1 (α β : ℂ) : α + β = β + α := by sorry

/-! 1.4 Example: commutativity of complex multiplication -/

@[cite ladr4e "1.4", cite ladr4e "1.3" (rel := hasPart), avoiding Complex.commRing, Complex.instCommSemiring, Complex.instField]
theorem mul_comm_example (α β : ℂ) : α * β = β * α := by
  apply Complex.ext
  · simp only [Complex.mul_re]; ring
  · simp only [Complex.mul_im]; ring

@[cite ladr4e "Exercise 1A.2", cite ladr4e "1.3" (rel := hasPart), avoiding Complex.commRing, Complex.instCommSemiring, Complex.instField]
theorem exercise_1A_2 (α β γ : ℂ) : (α + β) + γ = α + (β + γ) := by sorry

@[cite ladr4e "Exercise 1A.3", cite ladr4e "1.3" (rel := hasPart), avoiding Complex.commRing, Complex.instCommSemiring, Complex.instField]
theorem exercise_1A_3 (α β γ : ℂ) : (α * β) * γ = α * (β * γ) := by sorry

@[cite ladr4e "Exercise 1A.4", cite ladr4e "1.3" (rel := hasPart), avoiding Complex.commRing, Complex.instCommSemiring, Complex.instField]
theorem exercise_1A_4 (α β γ : ℂ) : γ * (α + β) = γ * α + γ * β := by sorry

cite ladr4e "1.3" (rel := hasPart) in
example (γ : ℂ) : γ + 0 = γ := add_zero γ
cite ladr4e "1.3" (rel := hasPart) in
example (γ : ℂ) : γ * 1 = γ := mul_one γ

@[cite ladr4e "Exercise 1A.5", cite ladr4e "1.3" (rel := hasPart), avoiding Complex.instNeg, Complex.instSub, Complex.commRing, Complex.instCommSemiring,
    Complex.instField]
theorem exercise_1A_5 (α : ℂ) : ∃! β : ℂ, α + β = 0 := by sorry

@[cite ladr4e "Exercise 1A.6", cite ladr4e "1.3" (rel := hasPart), avoiding Complex.instInv, Complex.instDivInvMonoid, Complex.commRing, Complex.instCommSemiring,
    Complex.instField]
theorem exercise_1A_6 (α : ℂ) (hα : α ≠ 0) : ∃! β : ℂ, α * β = 1 := by sorry

/-! 1.5 Definition: −α, subtraction, 1/α, division -/

cite ladr4e "1.5" in
example (α β : ℂ) : α - β = α + (-β) := sub_eq_add_neg α β
cite ladr4e "1.5" in
example (α : ℂ) : α⁻¹ = 1 / α := (one_div α).symm
cite ladr4e "1.5" in
example (α β : ℂ) : β / α = β * α⁻¹ := div_eq_mul_inv β α

/-! 1.6 Notation: F -/

variable {F : Type*} [Field F] {n : ℕ}

cite ladr4e "1.6" in
example (α : F) (m n : ℕ) : (α ^ m) ^ n = α ^ (m * n) := (pow_mul α m n).symm
cite ladr4e "1.6" in
example (α β : F) (m : ℕ) : (α * β) ^ m = α ^ m * β ^ m := mul_pow α β m

/-! 1.7 Example: ℝ² and ℝ³ -/

cite ladr4e "1.7" in
example : Fin 2 → ℝ := ![1, 2]
cite ladr4e "1.7" in
example : Fin 3 → ℝ := ![1, 2, 3]

/-! 1.8 Definition: list, length

Axler's *list of length {lit}`n` over {lit}`α`* is rendered here as
{lit}`Fin n → α`, with the length encoded in the type. **Beware:** Lean has a
separate built-in type {lit}`List α` (a variable-length linked list, written
with the {lit}`[…]` notation instead of {lit}`![…]`) — it is *not* what Axler
calls a list. -/

cite ladr4e "1.8" in
example : Fin 0 → ℝ := ![]

cite ladr4e "1.8" in
example {α : Type*} (x y : Fin n → α) : x = y ↔ ∀ i, x i = y i :=
  ⟨fun h _ => h ▸ rfl, funext⟩

/-! 1.9 Lists versus sets -/

cite ladr4e "1.9" in
example : (![3, 5] : Fin 2 → ℕ) ≠ ![5, 3] := by decide
cite ladr4e "1.9" in
example : ({3, 5} : Set ℕ) = ({5, 3} : Set ℕ) := by ext; simp; tauto
cite ladr4e "1.9" in
example : ({4, 4} : Set ℕ) = ({4} : Set ℕ) := by ext; simp

/-! 1.11 Definition: Fⁿ, coordinate -/

cite ladr4e "1.11" in
example : (![10, 20, 30] : Fin 3 → ℕ) 0 = 10 := rfl
cite ladr4e "1.11" in
example : (![10, 20, 30] : Fin 3 → ℕ) 2 = 30 := rfl

/-! 1.12 Example: ℂ⁴ -/

cite ladr4e "1.12" in
example : Fin 4 → ℂ := ![1 + 2 * I, 3, -I, 5 - 6 * I]

/-! 1.13 Definition: addition in Fⁿ -/

cite ladr4e "1.13" in
example (x y : Fin n → F) : x + y = fun i => x i + y i := rfl

/-! 1.14 Commutativity of addition in Fⁿ -/

cite ladr4e "1.14" (statement := 1) (rel := exactMatch) in
@[cite ladr4e "1.14"]
theorem add_comm_pi (x y : Fin n → F) : x + y = y + x := by
  cite ladr4e "1.14" step 2 exactMatch =>
    funext i
    exact add_comm (x i) (y i)

/-! 1.15 Notation: 0 -/

cite ladr4e "1.15" in
example : (0 : Fin n → F) = fun _ => 0 := rfl

/-! 1.16 Example: context determines which 0 is intended -/

cite ladr4e "1.16" in
example (x : Fin n → F) : x + 0 = x := add_zero x

/-! 1.17 Definition: additive inverse in Fⁿ, −x -/

cite ladr4e "1.17" in
example (x : Fin n → F) : -x = fun i => -(x i) := rfl

/-! 1.18 Definition: scalar multiplication in Fⁿ -/

cite ladr4e "1.18" in
example (a : F) (x : Fin n → F) : a • x = fun i => a * x i := rfl

/-! # Exercises

Exercises 1A.1–1A.6 are stated inline in Properties 1.3 above. -/

@[cite ladr4e "Exercise 1A.7"]
theorem exercise_1A_7 :
    ((-1 + Real.sqrt 3 * I) / 2) ^ 3 = 1 := by
  sorry

@[cite ladr4e "Exercise 1A.8"]
theorem exercise_1A_8 :
    ∃ z w : ℂ, z ≠ w ∧ z ^ 2 = I ∧ w ^ 2 = I := by
  sorry

@[cite ladr4e "Exercise 1A.9"]
theorem exercise_1A_9 :
    ∃ x : Fin 4 → ℝ,
      (![4, -3, 1, 7] : Fin 4 → ℝ) + (2 : ℝ) • x = ![5, 9, -6, 8] := by
  sorry

@[cite ladr4e "Exercise 1A.10"]
theorem exercise_1A_10 :
    ¬ ∃ lam : ℂ, lam • (![2 - 3 * I, 5 + 4 * I, -6 + 7 * I] : Fin 3 → ℂ) =
      ![12 - 5 * I, 7 + 22 * I, -32 - 9 * I] := by
  sorry

@[cite ladr4e "Exercise 1A.11", avoiding Pi.addSemigroup]
theorem exercise_1A_11 (x y z : Fin n → F) :
    (x + y) + z = x + (y + z) := by sorry

@[cite ladr4e "Exercise 1A.12", avoiding mul_smul, smul_smul]
theorem exercise_1A_12 (a b : F) (x : Fin n → F) :
    (a * b) • x = a • (b • x) := by
  sorry

@[cite ladr4e "Exercise 1A.13", avoiding one_smul]
theorem exercise_1A_13 (x : Fin n → F) : (1 : F) • x = x := by
  sorry

@[cite ladr4e "Exercise 1A.14", avoiding smul_add]
theorem exercise_1A_14 (γ : F) (x y : Fin n → F) :
    γ • (x + y) = γ • x + γ • y := by
  sorry

@[cite ladr4e "Exercise 1A.15", avoiding add_smul]
theorem exercise_1A_15 (a b : F) (x : Fin n → F) :
    (a + b) • x = a • x + b • x := by
  sorry

end LADR.Section_1A
