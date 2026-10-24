module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedRightImageValue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellComparePathPairs

/-!
概要：元の fixed 模型射の fⱼ 後合成と直接遷移を、三重 cell 源上の実経路で結ぶ。
方針：右像からの二経路と直接側の二経路を、指定した同じ完成射で接続する。
規約：局所化後の射の一致から経路を選ばない。使われ方：τₙ₊₁ の実 roof の右三角形。
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

def fixedTargetModelMap := d.sourceToTargetFixedRelative R ≫ d.targetRelativeComparison R ≫
  d.targetToOriginalModel R

def fixedRightImageToCompletedModelHomotopy : Path.Witness R
    (d.sourceToRightCoefficientModel R ≫ d.rightImageToGammaModel R)
    (d.sourceToRightCompletedModel R ≫ d.fixedRightCompletedRelativeToOriginalModel R) where
  hom := d.sourceToRightCoefficientModel R ≫ (d.rightWModelHomotopy R).hom
  source_eq := (Category.assoc _ _ _).trans (congrArg
    (fun t => d.sourceToRightCoefficientModel R ≫ t) (d.rightWModelHomotopy R).source_eq)
  target_eq := ((Category.assoc _ _ _).trans (congrArg
    (fun t => d.sourceToRightCoefficientModel R ≫ t) (d.rightWModelHomotopy R).target_eq)).trans
      (d.sourceToRightCompletedModel_original R).symm

def fixedRightClassModelPath : Path.Witness R
    (iteratedCellAugmentation R (d.sourceRelativeModel R) 3 ≫
      (d.fixedTargetModelMap R ≫ postnikovClassModelMap R n hn (f.app j).hom))
    (iteratedCellAugmentation R (d.sourceRelativeModel R) 3 ≫ d.directOriginalModelMap R) := by
  let v := (d.rightImageOriginalSourceModelHomotopy R).precomp (d.sourceToRightCoefficientModel R)
  let h := Path.Witness.cellComparePairs R v (d.fixedRightImageToCompletedModelHomotopy R)
    (d.directOriginalToFixedModelHomotopy R) (d.fixedRightCompletedOriginalModelHomotopy R)
  refine ⟨h.hom, ?_, h.target_eq⟩
  have he : d.sourceToRightCoefficientModel R ≫ d.rightImageRelativeToOriginalModel R =
      d.fixedTargetModelMap R ≫ postnikovClassModelMap R n hn (f.app j).hom := by
    exact (d.sourceToRightCoefficientModel_original R).trans (by
      simp only [fixedTargetModelMap, Category.assoc])
  exact h.source_eq.trans (congrArg (fun t =>
    iteratedCellAugmentation R (d.sourceRelativeModel R) 3 ≫ t) he)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
