import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

open BigOperators

abbrev Vec4 := Fin 4 → ℝ

namespace Vec4
/-
dot product of two vectors defined as sum of their products
for their coordinates
-/
def dot (u v : Vec4) : ℝ :=
  ∑ i : Fin 4, u i * v i

/-
Squared norm of a vector is shown as the
dot product of the vector itself
-/
def sqNorm (u : Vec4) : ℝ :=
  dot u u

/-
basis vector equal to s dot product of zero
-/
def Orthogonal (u v : Vec4) : Prop :=
  dot u v = 0
/-
Standard basis vector corresponds to coordinate j.
It must be a 1 in pos and j and 0 in all other coordinates
-/

def basis (j : Fin 4) : Vec4 :=
  fun i => if i = j then 1 else 0

/-
dot product is symmetric
-/
theorem dot_comm (u v : Vec4) :
    dot u v = dot v u := by
  unfold dot
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-
distribute of vector addition with the right arguments
-/

theorem dot_add_right (u v w : Vec4) :
    dot u (v + w) = dot u v + dot u w := by
  unfold dot
  simp [mul_add, Finset.sum_add_distrib]
/-
distribute of vector addition with the left arguments
-/
theorem dot_add_left (u v w : Vec4) :
    dot (u + v) w = dot u w + dot v w := by
  calc
    dot (u + v) w = dot w (u + v) := by rw [dot_comm]
    _ = dot w u + dot w v := by rw [dot_add_right]
    _ = dot u w + dot v w := by rw [dot_comm w u, dot_comm w v]

/-
dot product with any vector with the zero vector is always zzero
-/
theorem dot_zero_right (u : Vec4) :
    dot u 0 = 0 := by
  unfold dot
  simp

/-
dot product with any vector with the zero vector is always zzero
-/
theorem dot_zero_left (u : Vec4) :
    dot 0 u = 0 := by
  rw [dot_comm]
  exact dot_zero_right u
/-
sum of coordinate squares
-/
theorem sqNorm_eq_sum_squares (u : Vec4) :
    sqNorm u = ∑ i : Fin 4, (u i)^2 := by
  unfold sqNorm dot
  apply Finset.sum_congr rfl
  intro i hi
  ring
/-
always nonnegative since it is a sum of squares
-/
theorem sqNorm_nonneg (u : Vec4) :
    0 ≤ sqNorm u := by
  rw [sqNorm_eq_sum_squares]
  exact Finset.sum_nonneg fun i hi => sq_nonneg (u i)
/-
A basis vector has squared norm equal to one
-/
theorem basis_dot_self (i : Fin 4) :
    dot (basis i) (basis i) = 1 := by
  unfold dot basis
  simp

/-
basis vectors are orthogonal if they are distinct
-/

theorem basis_dot_ne_zero {i j : Fin 4} (h : i ≠ j) :
    dot (basis i) (basis j) = 0 := by
  unfold dot basis
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hki : k = i
  · subst k
    simp [h]
  · simp [hki]

theorem basis_orthogonal {i j : Fin 4} (h : i ≠ j) :
    Orthogonal (basis i) (basis j) := by
  unfold Orthogonal
  exact basis_dot_ne_zero h


/-
four standard vectors of 4D
-/
def e₁ : Vec4 := basis 0
def e₂ : Vec4 := basis 1
def e₃ : Vec4 := basis 2
def e₄ : Vec4 := basis 3

/-
examples of orthogonality
-/

theorem e₁_orthogonal_e₂ :
    Orthogonal e₁ e₂ := by
  unfold e₁ e₂
  apply basis_orthogonal
  decide

theorem e₁_orthogonal_e₃ :
    Orthogonal e₁ e₃ := by
  unfold e₁ e₃
  apply basis_orthogonal
  decide

theorem e₁_orthogonal_e₄ :
    Orthogonal e₁ e₄ := by
  unfold e₁ e₄
  apply basis_orthogonal
  decide

end Vec4
