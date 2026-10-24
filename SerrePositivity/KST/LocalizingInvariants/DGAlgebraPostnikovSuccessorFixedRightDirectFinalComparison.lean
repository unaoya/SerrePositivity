module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedRightDirectFinalPathComparison

/-!
概要：source 模型経路の終点を、元の直接 class 模型射の元の Bⱼ 模型への合成へ同定する。
方針：二射影と全経路を保つ実模型の一意性を使う。
規約：元の直接 B 遷移の模型合成を始点に保持。使われ方：右逆三角形の直接側。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} {hn : 0 ≤ n} {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovSuccessorClassInverseData R hn f j)

lemma directSourceFinalModelMap_eq_fixed : d.directSourceFinalModelMap R =
    d.fixedRightDirectModelMap R ≫ d.fixedRightCompletedRelativeToOriginalModel R := by
  let N := d.rightClassifyingLayer R
  let b := d.fixedRightCompletedClass R
  let cL := SquareZeroExtension.relativeComparison_left N b
  let cR := SquareZeroExtension.relativeComparison_right N b
  let cP := SquareZeroExtension.relativeComparison_path N b
  let mL := d.fixedRightDirectModelMap_left R
  let mR := d.fixedRightDirectModelMap_right R
  apply HomotopyPullbackModel.hom_ext R (postnikovPerturbedClass R (B.obj j).obj n hn)
    (SquareZero.zeroSection (postnikov R (B.obj j).obj n)
      (directNativeLayer (n := n) (hn := hn) (B := B) (j := j) R))
  · rw [d.directSourceFinalModelMap_left R]
    simp only [fixedRightCompletedRelativeToOriginalModel,
      Category.assoc, d.fixedRightCompletedToOriginalModel_left R]
    rw [reassoc_of% cL, reassoc_of% mL]
  · rw [d.directSourceFinalModelMap_right R]
    simp only [fixedRightCompletedRelativeToOriginalModel,
      Category.assoc, d.fixedRightCompletedToOriginalModel_right R]
    rw [reassoc_of% cR, reassoc_of% mR]
    rfl
  · rw [d.directSourceFinalModelMap_path_fixed R]
    simp only [fixedRightCompletedRelativeToOriginalModel, Category.assoc,
      d.fixedRightCompletedToOriginalModel_path R]
    rw [reassoc_of% cP]

def directOriginalToFixedModelHomotopy : Path.Witness R (d.directOriginalModelMap R)
    (d.fixedRightDirectModelMap R ≫ d.fixedRightCompletedRelativeToOriginalModel R) where
  hom := (d.directOriginalSourceModelHomotopy R).hom
  source_eq := (d.directOriginalSourceModelHomotopy R).source_eq
  target_eq := (d.directOriginalSourceModelHomotopy R).target_eq.trans
    (d.directSourceFinalModelMap_eq_fixed R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
