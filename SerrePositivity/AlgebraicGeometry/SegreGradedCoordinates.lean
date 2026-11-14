module

public import SerrePositivity.AlgebraicGeometry.DegreeOneGradedEvaluation
public import SerrePositivity.AlgebraicGeometry.SegreCoordinates
public import Mathlib.RingTheory.GradedAlgebra.TensorProduct
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps

/-!
概要：実際の Segre 座標を左因子の底変換 grading に送り、核の斉次性を得る。
方針：Mathlib の任意の底変換の grading と、homogeneous ideal の comap を使う。
規約：底変換の平坦性を要求しない。右因子の座標の次数はこの左 grading には不要。
使われ方：G3 の Segre の座標環の実際の商と次数分解の入口。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct
variable {R A B ι κ : Type*} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]
variable (G : ℕ → Submodule R A) [GradedRing G]

/-- 左因子の次数を、右因子の環に任意に底変換した次数成分。 -/
def segreLeftTensorGrade (d : ℕ) : Submodule B (B ⊗[R] A) :=
  (G d).baseChange B

instance segreLeftTensorGrade_gradedRing : GradedRing (segreLeftTensorGrade (B := B) G) :=
  inferInstanceAs (GradedRing (fun d ↦ (G d).baseChange B))

/-- 元の R の係数は、底変換した grading の次数零に入る。 -/
theorem segreLeftTensorGrade_algebraMap_zero (r : R) :
    algebraMap R (B ⊗[R] A) r ∈ segreLeftTensorGrade (B := B) G 0 := by
  change algebraMap R B r ⊗ₜ[R] (1 : A) ∈ (G 0).baseChange B
  exact Submodule.tmul_mem_baseChange_of_mem _ (SetLike.one_mem_graded G)

variable (a : ι → A) (b : κ → B) (ha : ∀ i, a i ∈ G 1)

/-- 実際の Segre 座標は、左の次数一座標から底変換 grading への graded な射を定める。 -/
def segreGradedCoordinateMap :
    (MvPolynomial.homogeneousSubmodule (ι × κ) R) →+*ᵍ segreLeftTensorGrade (B := B) G :=
  degreeOneGradedEvaluation (segreLeftTensorGrade (B := B) G)
    (segreLeftTensorGrade_algebraMap_zero G) (fun ij ↦ b ij.2 ⊗ₜ[R] a ij.1)
    (fun ij ↦ Submodule.tmul_mem_baseChange_of_mem _ (ha ij.1))

@[simp]
theorem segreGradedCoordinateMap_toRingHom :
    (segreGradedCoordinateMap G a b ha).toRingHom = (segreCoordinateMap a b).toRingHom := rfl

attribute [local instance] MvPolynomial.gradedAlgebra
include ha

/-- 実際の Segre 座標写像の核は同次イデアル。 -/
theorem segreCoordinateMap_kernel_homogeneous :
    (RingHom.ker (segreCoordinateMap a b).toRingHom).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (ι × κ) R) := by
  have H := ((⊥ : HomogeneousIdeal (segreLeftTensorGrade (B := B) G)).comap
    (segreGradedCoordinateMap G a b ha)).isHomogeneous
  exact H

end SerrePositivity.AlgebraicGeometry
