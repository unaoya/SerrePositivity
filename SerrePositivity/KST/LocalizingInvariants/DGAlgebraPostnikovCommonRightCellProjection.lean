module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassCompatibility
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightTargetFirstPath

/-!
概要：元の Γ の二重 cell 射を一段降ろすと、元の class 模型の cell 射に厳密に戻る。
方針：元の二重 cell 表示と、一段 augmentation の式を合成する。
規約：元の Γ 射そのものの等式。使われ方：直接分母の source 自然性への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c)

lemma postnikovCommonRightImageToSecond_toCell : postnikovCommonRightImageToSecond R f c d ≫
    cellAugmentation R (cellResolution R (postnikovCommonClassBase R f c d)) =
      postnikovCommonClassCompatibilityToCell R f c d := by
  rw [postnikovCommonRightImageToSecond_eq, Category.assoc,
    cellPathNonpositiveToDoubleCell_toCell]
  simp only [postnikovCommonRightToClassifying, postnikovCommonClassCompatibilityToCell,
    postnikovCommonRightGlueToCell, Category.assoc,
    reassoc_of% cellPathNonpositiveToCell_projection]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
