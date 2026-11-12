module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechGradedLocalization
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.Module.Submodule.RestrictScalars
public import Mathlib.Algebra.Module.Submodule.Range

/-!
概要：斉次局所化の指定部分は、基底環への係数制限と交換する。
方針：分数写像の像と上限の係数制限を比較し、作用の違いを恒等写像でつなぐ。
規約：局所化する環 Q は固定し、B 上と R 上の二つの線形構造を区別する。
使われ方：Rees 環上の標準開の Čech 図式を、元の基底環上の図式と比較する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry

section Module
variable {R B N : Type*} [CommRing R] [CommRing B] [Algebra R B]
variable [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N]

/-- 与えられた R 作用と、B から係数制限した R 作用との恒等同値。 -/
def projectiveModuleScalarRestrictionLinearEquiv :
    N ≃ₗ[R] (ModuleCat.restrictScalars (algebraMap R B)).obj (ModuleCat.of B N) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := (algebraMap_smul B r x).symm

end Module

section Graded
variable {R B Q N : Type*} [CommRing R] [CommRing B] [CommRing Q]
variable [Algebra R B] [Algebra B Q] [Algebra R Q] [IsScalarTower R B Q]
variable [AddCommGroup N] [Module R N] [Module B N] [Module Q N]
variable [IsScalarTower R B N] [IsScalarTower R Q N] [IsScalarTower B Q N]

/-- 斉次分数の線形写像は、係数制限と交換する。 -/
theorem projectiveGradedFraction_restrictScalars (f : Q) (V : ℕ → Submodule B N) (k : ℕ) :
    (projectiveGradedFraction f V k).restrictScalars R =
      projectiveGradedFraction f (fun n ↦ (V n).restrictScalars R) k := by
  rfl

/-- 斉次局所化の部分加群は係数制限と交換する。 -/
theorem projectiveGradedAway_restrictScalars (f : Q) (V : ℕ → Submodule B N) :
    (projectiveGradedAway f V).restrictScalars R =
      projectiveGradedAway f (fun n ↦ (V n).restrictScalars R) := by
  rw [projectiveGradedAway, Submodule.restrictScalars_iSup, projectiveGradedAway]
  congr 1

/-- 斉次局所化の係数制限の比較を、R 加群としての線形同値にする。 -/
def projectiveGradedAwayScalarRestrictionLinearEquiv (f : Q) (V : ℕ → Submodule B N) :=
  (LinearEquiv.ofEq _ _ (projectiveGradedAway_restrictScalars (R := R) f V).symm).trans
    (projectiveModuleScalarRestrictionLinearEquiv
      (R := R) (B := B) (N := projectiveGradedAway f V))

/-- 斉次局所化の係数制限の比較は、周囲の局所化の元を変えない。 -/
theorem projectiveGradedAwayScalarRestrictionLinearEquiv_val
    (f : Q) (V : ℕ → Submodule B N)
    (z : projectiveGradedAway f (fun n ↦ (V n).restrictScalars R)) :
    (projectiveGradedAwayScalarRestrictionLinearEquiv (R := R) f V z).val = z.val := rfl

end Graded
end SerrePositivity.AlgebraicGeometry
