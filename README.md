# Formalizing Euclidean Geometry in Four Dimensions Using Lean

## Introduction


The project formalizes theorems/lemmas by using the Lean proof assistant by formalizing the basic concepts of four dimensional geometry. As the goal is to show how geometric properties can be represented and verified through the Lean proof assistant.

The project defines the vectors in four dimensional space and also formalizes basic concepts of four dimensional space geometry such as dot products, norms, distance, orthogonality, orthonormal basis, as well as coordinate reconstruction. Such concepts wre then used to prove the basic results about the structure of four dimensional space. 

## Project Files

### `MyCoreFile.lean`

Defines the basic defintions/objects used throughout the project:

* Four dimensional vectors 
* Dot product
* Squared norm
* Orthogonality
* Standard basis vectors

Examples:

* Symmetry for the dot product
* Linearity for the dot product
* Nonnegativity for squared norms
* Orthogonality for distinct basis vectors

### `MyDistance.lean`

Shows the squared distance and proves basic geometric properties:

* Distance from a vector between itself
* Nonnegativity of distance
* Symmetry of distance
* Relationship between squared distance and squared norm

### `Orthonormal.lean`

Formalizes orthonormal bases.

Definitions include:

* Unit vectors
* Orthonormal pairs
* Orthonormal bases

Main result:

* The standard basis of ℝ⁴ forms an orthonormal basis.

### `MyLinearCombination.lean`

Studies coordinate reconstruction and basis expansions.

Main result:

* Every vector in ℝ⁴ can be reconstructed from its coordinates from  the standard basis.

## Main Mathematical Results


1. The dot product is symmetric.
2. Squared norms are nonnegative.
3. Distinct standard basis vectors are orthogonal.
4. The standard basis forms an orthonormal basis.
5. Every vector can be expressed as a linear combination of the standard basis vectors.


## Challenges

One of the most challenging aspects of the project was trying to understand the abstract and rigor of pure mathematics. Since I have a weak background in proof based mathematics it was very difficult to verify certain statements and understand the symbolic language that I haven’t really practiced. Statements that would seem obvious to most students who have taken a traditional proofs course were not as simple for me to grasp or understand. However, working through these challenges helped me get exposed to pure math and the level of thinking needed to work on formal verification systems


## Technologies Used

* Lean 4
* Mathlib

## Author

Noah Rainbow

MATH 157 Final Project
