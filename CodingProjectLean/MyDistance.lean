import CodingProjectLean.MyCoreFile
import Mathlib.Tactic

open BigOperators

namespace Vec4
/-
Squared distance via two vectors
-/
def sqDist (u v : Vec4) : ℝ :=
  sqNorm (u - v)
/-
squared distance from a vector to itself would be zero
-/
theorem sqDist_self (u : Vec4) :
    sqDist u u = 0 := by
  unfold sqDist sqNorm dot
  simp
/-
Squared distance would always be a nonnegative since it is
defined via squared norm.
-/
theorem sqDist_nonneg (u v : Vec4) :
    0 ≤ sqDist u v := by
  unfold sqDist
  exact sqNorm_nonneg (u - v)

/-
symmetric squared distance
-/
theorem sqDist_comm (u v : Vec4) :
    sqDist u v = sqDist v u := by
  unfold sqDist sqNorm dot
  apply Finset.sum_congr rfl
  intro i hi
  simp
  ring_nf

/-
Express squared distance as a sum of coordinate squares.
-/
theorem sqDist_eq_sum_squares (u v : Vec4) :
    sqDist u v = ∑ i : Fin 4, (u i - v i)^2 := by
  unfold sqDist sqNorm dot
  apply Finset.sum_congr rfl
  intro i hi
  simp
  ring_nf
/- The squared distance from the zero vector to u is
equal to the squared norm of u. -/
theorem sqDist_zero_left (u : Vec4) :
    sqDist 0 u = sqNorm u := by
  unfold sqDist sqNorm dot
  apply Finset.sum_congr rfl
  intro i hi
  simp

theorem sqDist_zero_right (u : Vec4) :
    sqDist u 0 = sqNorm u := by
  unfold sqDist sqNorm dot
  apply Finset.sum_congr rfl
  intro i hi
  simp
/-
basis vector has zero distance from itself
-/
theorem sqDist_basis_self (i : Fin 4) :
    sqDist (basis i) (basis i) = 0 := by
  exact sqDist_self (basis i)
/- Future work: Prove that distinct basis vectors have squared distance -/
theorem sqDist_basis_ne {i j : Fin 4} (h : i ≠ j) :
    sqDist (basis i) (basis j) = 2 := by
 sorry

end Vec4
