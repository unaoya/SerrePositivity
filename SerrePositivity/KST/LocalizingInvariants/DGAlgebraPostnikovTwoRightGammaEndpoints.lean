module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightGammaZeroClass
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightDirectSourcePath

/-!
概要：Γ 上の W source 経路の両端を、元の class 模型で使う cell 射に照合する。
方針：同じ Γ の一重 cell 射と塔の合成式を使い、分母側の元の source を回収する。
規約：source 経路を選び直さない。使われ方：動く底の模型経路の端点同定。
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

lemma postnikovCommonRightGammaToSource_toCell :
    postnikovCommonRightGammaToSource R f c d ≫
      cellPathNonpositiveToCell R (postnikovCommonClassBase R f c d) =
        postnikovCommonClassCompatibilityToCell R f c d := by
  simp only [postnikovCommonRightGammaToSource, postnikovCommonClassCompatibilityToCell,
    postnikovCommonRightGlueToCell,
    PostnikovCommonCore.postnikovCommonRightGammaToSource,
    PostnikovCommonCore.postnikovCommonClassCompatibilityToCell,
    PostnikovCommonCore.postnikovCommonRightGlueToCell, Category.assoc]

lemma postnikovCommonRightGamma_comparison {C : Mon (Complex R)}
    (b : postnikovCommonClassBase R f c d ⟶ C) :
    postnikovCommonRightGammaToSource R f c d ≫ cellPathNonpositiveComparison R b =
      postnikovCommonClassCompatibilityToCell R f c d ≫ cellResolutionMap R b := by
  rw [cellPathNonpositiveComparison_toCell, ← Category.assoc,
    postnikovCommonRightGammaToSource_toCell]

variable {j : ℕ} (hj : j ≤ i)

lemma postnikovCommonRightGammaSourceWitness_source :
    (postnikovCommonRightGammaSourceWitness R f c d hj).hom ≫
      Path.source R (postnikovPerturbedExtension R (B.obj j).obj 1 (by omega)) =
    (postnikovCommonClassCompatibilityToCell R f c d ≫
      cellResolutionMap R (postnikovCommonRightBase R f c d ≫
        postnikovMap R (B.transition hj).hom 1)) ≫
          postnikovCellLift R (B.obj j).obj 1 (by omega) := by
  rw [(postnikovCommonRightGammaSourceWitness R f c d hj).source_eq]
  change postnikovCommonRightGammaToSource R f c d ≫
    (cellPathNonpositiveComparison R (postnikovCommonRightBase R f c d ≫
      postnikovMap R (B.transition hj).hom 1) ≫
        postnikovCellLift R (B.obj j).obj 1 (by decide)) = _
  rw [← Category.assoc, postnikovCommonRightGamma_comparison]

lemma postnikovCommonRightGammaSourceWitness_target :
    (postnikovCommonRightGammaSourceWitness R f c d hj).hom ≫
      Path.target R (postnikovPerturbedExtension R (B.obj j).obj 1 (by omega)) =
    (postnikovCommonClassCompatibilityToCell R f c d ≫
      cellResolutionMap R (postnikovCommonRightDenBase R f c d ≫
        postnikovMap R (B.transition hj).hom 1)) ≫
          postnikovCellLift R (B.obj j).obj 1 (by omega) := by
  rw [(postnikovCommonRightGammaSourceWitness R f c d hj).target_eq]
  change postnikovCommonRightGammaToSource R f c d ≫
    (cellPathNonpositiveComparison R (postnikovCommonRightDenBase R f c d ≫
      postnikovMap R (B.transition hj).hom 1) ≫
        postnikovCellLift R (B.obj j).obj 1 (by decide)) = _
  rw [← Category.assoc, postnikovCommonRightGamma_comparison]

lemma postnikovCommonClassRightDenominatorBase_composite :
    postnikovCommonClassRightDenominatorBase R f c d hj =
      postnikovCommonRightDenBase R f c d ≫ postnikovMap R (B.transition hj).hom 1 := by
  change (postnikovOneRoofRefine R f c d.zero.source_le).roof.denominator ≫
    postnikovMap R (postnikovCommonRightDenDirectMap R f c d hj) 1 =
      ((postnikovOneRoofRefine R f c d.zero.source_le).roof.denominator ≫
        postnikovMap R (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom 1) ≫
          postnikovMap R (B.transition hj).hom 1
  rw [← postnikovCommonRightDenDirect_factorization, postnikovMap_composition]
  exact (Category.assoc _ _ _).symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

lemma rightGammaSourceWitness_target :
    (postnikovCommonRightGammaSourceWitness R f d.baseInverse d.layerInverse d.target_le).hom ≫
      Path.target R (postnikovPerturbedExtension R (B.obj j).obj 1 (by omega)) =
        d.fixedRightCompletedNativeSource R := by
  rw [postnikovCommonRightGammaSourceWitness_target]
  simp only [fixedRightCompletedNativeSource, fixedRightCompletedCellMap, Category.assoc]
  rw [reassoc_of% (postnikovCommonRightImageToSecond_toCell R f d.baseInverse d.layerInverse),
    postnikovCommonClassRightDenominatorBase_composite]
end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
