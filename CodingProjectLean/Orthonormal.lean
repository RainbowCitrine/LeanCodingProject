import CodingProjectLean.MyCoreFile
import CodingProjectLean.MyDistance
import Mathlib.Tactic

open BigOperators

namespace Vec4

def UnitVector (u : Vec4) : Prop :=
  sqNorm u = 1
/-
Orthonomral pair has two unit vectors that
are orthogonal to one another
-/
def OrthonormalPair (u v : Vec4) : Prop :=
  UnitVector u ∧ UnitVector v ∧ Orthogonal u v
/-
collection of four vectors such that each vector has unit length
-/
def OrthonormalBasis4 (b : Fin 4 → Vec4) : Prop :=
  (∀ i : Fin 4, UnitVector (b i)) ∧
  (∀ i j : Fin 4, i ≠ j → Orthogonal (b i) (b j))
/-
Standard basis of 4D consist of the four coordinate basis vectors
-/
def standardBasis : Fin 4 → Vec4 :=
  basis

/- Each basis vector is a unit vector because its squared norm is equal to one. -/
theorem basis_unit (i : Fin 4) :
    UnitVector (basis i) := by
  unfold UnitVector
  exact basis_dot_self i

/- Every vector in the standard basis is a unit vector. -/
theorem standardBasis_unit (i : Fin 4) :
    UnitVector (standardBasis i) := by
  unfold standardBasis
  exact basis_unit i

/- Distinct vectors in the standard basis are orthogonal. -/
theorem standardBasis_orthogonal {i j : Fin 4} (h : i ≠ j) :
    Orthogonal (standardBasis i) (standardBasis j) := by
  unfold standardBasis
  exact basis_orthogonal h

/-
Standard basis forms an orthonormal basis of 4D
The result combines the facts that each basis vector
has a unit legnth and that distinct basis vectors
are orthogonal.
-/
theorem standardBasis_orthonormal :
    OrthonormalBasis4 standardBasis := by
  constructor
  · intro i
    exact standardBasis_unit i
  · intro i j h
    exact standardBasis_orthogonal h

/- The individual standard basis vectors are unit vectors. -/
theorem e₁_unit :
    UnitVector e₁ := by
  unfold e₁
  exact basis_unit 0

theorem e₂_unit :
    UnitVector e₂ := by
  unfold e₂
  exact basis_unit 1

theorem e₃_unit :
    UnitVector e₃ := by
  unfold e₃
  exact basis_unit 2

theorem e₄_unit :
    UnitVector e₄ := by
  unfold e₄
  exact basis_unit 3

theorem e₁_e₂_orthonormal_pair :
    OrthonormalPair e₁ e₂ := by
  constructor
  · exact e₁_unit
  constructor
  · exact e₂_unit
  · exact e₁_orthogonal_e₂

end Vec4
