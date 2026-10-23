module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightCellProjection
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightCompletedOriginalModel

/-!
概要：元の直接 B 遷移の source 自然性経路を同じ Γ 上に取り出す。
方針：元の二重 cell 射で前合成し、元の cell 射への厳密な射影式を使う。
規約：元の乗法的 source 経路と一定の底を保持。使われ方：直接模型射の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

def fixedRightDirectSourcePath :=
  (postnikovCellLiftOverNaturalityWitness R (B.obj d.layerInverse.zero.stage).obj (B.obj j).obj
    (d.classBase R) 1 (by omega) (d.lowerBaseInverse R).roof.denominator
    (postnikovCommonRightDenDirectMap R f d.baseInverse d.layerInverse d.target_le)).precomp
    (postnikovCommonRightImageToSecond R f d.baseInverse d.layerInverse)

lemma fixedRightDirectSourcePath_source : (d.fixedRightDirectSourcePath R).hom ≫
    Path.source R (postnikovPerturbedExtension R (B.obj j).obj 1 (by omega)) =
    d.sourceCellMap R ≫ postnikovCellLift R (B.obj d.layerInverse.zero.stage).obj 1 (by omega) ≫
      postnikovPerturbedMap R
        (postnikovCommonRightDenDirectMap R f d.baseInverse d.layerInverse d.target_le)
        1 (by omega) := by
  rw [(d.fixedRightDirectSourcePath R).source_eq]
  simp only [postnikovCellLiftOverSource, Category.assoc]
  rw [reassoc_of% (postnikovCommonRightImageToSecond_toCell R f d.baseInverse d.layerInverse)]
  simp only [sourceCellMap, Category.assoc]

lemma fixedRightDirectSourcePath_target : (d.fixedRightDirectSourcePath R).hom ≫
    Path.target R (postnikovPerturbedExtension R (B.obj j).obj 1 (by omega)) =
      d.fixedRightCompletedNativeSource R := by
  rw [(d.fixedRightDirectSourcePath R).target_eq]
  simp only [postnikovCellLiftOverTarget, fixedRightCompletedNativeSource,
    fixedRightCompletedCellMap, Category.assoc]
  rfl

lemma fixedRightDirectSourcePath_relative : (d.fixedRightDirectSourcePath R).hom ≫
    Path.map R (postnikovPerturbedProjection R (B.obj j).obj 1 (by omega)) =
    (d.classProjection R ≫ postnikovCommonClassRightDenominatorBase R f d.baseInverse
      d.layerInverse d.target_le) ≫ Path.diagonal R (postnikov R (B.obj j).obj 1) := by
  change (postnikovCommonRightImageToSecond R f d.baseInverse d.layerInverse ≫ _) ≫ _ = _
  rw [Category.assoc, postnikovCellLiftOverNaturalityWitness_relative]
  simp only [Category.assoc]
  rw [reassoc_of% (postnikovCommonRightImageToSecond_projection R f d.baseInverse d.layerInverse)]
  rfl

lemma fixedRightDirectSourcePath_class : (d.fixedRightDirectSourcePath R).hom ≫
    Path.map R (postnikovPerturbedClass R (B.obj j).obj 1 (by omega)) =
    postnikovCommonRightImageToSecond R f d.baseInverse d.layerInverse ≫
      (postnikovCellClassOverNaturalityWitness R (B.obj d.layerInverse.zero.stage).obj
        (B.obj j).obj (d.classBase R) 1 (by omega) (d.lowerBaseInverse R).roof.denominator
        (postnikovCommonRightDenDirectMap R f d.baseInverse d.layerInverse d.target_le)).hom := by
  change (postnikovCommonRightImageToSecond R f d.baseInverse d.layerInverse ≫ _) ≫ _ = _
  rw [Category.assoc]
  rfl

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
