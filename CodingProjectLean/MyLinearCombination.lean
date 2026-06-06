import CodingProjectLean.MyCoreFile
import CodingProjectLean.Orthonormal
import Mathlib.Tactic

namespace Vec4
/-
Scalar multiplication in 4D
-/
def scale (a : ℝ) (v : Vec4) : Vec4 :=
  fun i => a * v i

notation a " •₄ " v => scale a v
/-
Applying scaled vector to the coordinate system
which returns a scalar multiplied by the corresponding coordinate
-/
theorem scale_apply (a : ℝ) (v : Vec4) (i : Fin 4) :
    (a •₄ v) i = a * v i := by
  rfl

/-
Taking dot product with a basis vector extracts the
corresponding coordinate of a vector
-/
theorem basis_coordinate (v : Vec4) (j : Fin 4) :
    dot v (basis j) = v j := by
  unfold dot basis
  fin_cases j <;> simp

/-
Reconstruct a vector from the coordinates relative
to the standard basis vectors
-/
def reconstruct (v : Vec4) : Vec4 :=
  fun i =>
    (v 0) * e₁ i +
    (v 1) * e₂ i +
    (v 2) * e₃ i +
    (v 3) * e₄ i
/-
Every 4D vector is equal to the reconstruction
from standard basis coordinates
-/
theorem reconstruct_eq (v : Vec4) :
    reconstruct v = v := by
  funext i
  fin_cases i <;>
    simp [reconstruct, e₁, e₂, e₃, e₄, basis]
/-
Every 4D vector can be shown as a linear combination
-/
theorem standardBasis_expansion (v : Vec4) :
    v = reconstruct v := by
  symm
  exact reconstruct_eq v

end Vec4
