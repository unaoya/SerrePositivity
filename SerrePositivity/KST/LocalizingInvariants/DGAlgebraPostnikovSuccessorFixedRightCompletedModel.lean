module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedRightCompletedSquare
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeClassHomotopy

/-!
概要：元の fixed 模型射の接合合成と、直接分母遷移の class 模型射を実経路で比較する。
方針：実二重 class 経路を係数模型射で前合成し、接合合成の厳密な式へ戻す。
規約：元の fixed 模型合成を終点に持つ。使われ方：元の代数 roof の右三角形照合。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} {hn : 0 ≤ n} {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovSuccessorClassInverseData R hn f j)

def fixedRightDirectModelMap := SquareZeroExtension.classModelMap
  (d.rightDenominatorCoefficient R) (d.sourceClass R) _ (d.fixedRightDirectWitness R)

def fixedRightCompletedModelHomotopy : Path.Witness R
    (d.fixedRightDirectModelMap R) (d.sourceToRightCompletedModel R) := by
  let h := SquareZeroExtension.classModelMapHomotopy
    (d.rightDenominatorCoefficient R) (d.sourceClass R) _ (d.fixedRightCompletedSquare R)
  refine ⟨h.hom, h.source_eq, ?_⟩
  exact h.target_eq.trans (d.sourceToRightCompletedModel_eq R).symm

lemma fixedRightCompletedModelHomotopy_left : (d.fixedRightCompletedModelHomotopy R).hom ≫
    Path.map R (SquareZeroExtension.relativeLeft (d.rightClassifyingLayer R) _) =
      SquareZeroExtension.relativeLeft (d.denominatorLayer R) (d.sourceClass R) ≫
        Path.diagonal R (d.classSource R) := by
  exact SquareZeroExtension.classModelMapHomotopy_left
    (d.rightDenominatorCoefficient R) (d.sourceClass R) _ (d.fixedRightCompletedSquare R)

lemma fixedRightCompletedModelHomotopy_right : (d.fixedRightCompletedModelHomotopy R).hom ≫
    Path.map R (SquareZeroExtension.relativeRight (d.rightClassifyingLayer R) _) =
      SquareZeroExtension.relativeRight (d.denominatorLayer R) (d.sourceClass R) ≫
        Path.diagonal R (d.classBase R) := by
  exact SquareZeroExtension.classModelMapHomotopy_right
    (d.rightDenominatorCoefficient R) (d.sourceClass R) _ (d.fixedRightCompletedSquare R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
