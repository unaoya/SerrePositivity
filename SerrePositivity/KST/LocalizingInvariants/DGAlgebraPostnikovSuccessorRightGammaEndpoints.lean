module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightGammaZeroClass
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedRightDirectSourcePath

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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} (hn : 0 ≤ n) {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R n)) i m hi)
  (d : PostnikovCommonCore.LayerInverse R hn f c)

lemma postnikovCommonRightGammaToSource_toCell :
    PostnikovCommonCore.postnikovCommonRightGammaToSource R hn f c d ≫
      cellPathNonpositiveToCell R (PostnikovCommonCore.postnikovCommonClassBase R hn f c d) =
        PostnikovCommonCore.postnikovCommonClassCompatibilityToCell R hn f c d := by
  simp only [PostnikovCommonCore.postnikovCommonRightGammaToSource, PostnikovCommonCore.postnikovCommonClassCompatibilityToCell,
    PostnikovCommonCore.postnikovCommonRightGlueToCell, Category.assoc]

lemma postnikovCommonRightGamma_comparison {C : Mon (Complex R)}
    (b : PostnikovCommonCore.postnikovCommonClassBase R hn f c d ⟶ C) :
    PostnikovCommonCore.postnikovCommonRightGammaToSource R hn f c d ≫ cellPathNonpositiveComparison R b =
      PostnikovCommonCore.postnikovCommonClassCompatibilityToCell R hn f c d ≫ cellResolutionMap R b := by
  rw [cellPathNonpositiveComparison_toCell, ← Category.assoc,
    PostnikovCommonCore.postnikovCommonRightGammaToSource_toCell]

variable {j : ℕ} (hj : j ≤ i)

lemma postnikovCommonRightGammaSourceWitness_source :
    (PostnikovCommonCore.postnikovCommonRightGammaSourceWitness R hn f c d hj).hom ≫
      Path.source R (postnikovPerturbedExtension R (B.obj j).obj n hn) =
    (PostnikovCommonCore.postnikovCommonClassCompatibilityToCell R hn f c d ≫
      cellResolutionMap R (PostnikovCommonCore.postnikovCommonRightBase R hn f c d ≫
        postnikovMap R (B.transition hj).hom n)) ≫
          postnikovCellLift R (B.obj j).obj n hn := by
  rw [(PostnikovCommonCore.postnikovCommonRightGammaSourceWitness R hn f c d hj).source_eq]
  rw [← Category.assoc, PostnikovCommonCore.postnikovCommonRightGamma_comparison]

lemma postnikovCommonRightGammaSourceWitness_target :
    (PostnikovCommonCore.postnikovCommonRightGammaSourceWitness R hn f c d hj).hom ≫
      Path.target R (postnikovPerturbedExtension R (B.obj j).obj n hn) =
    (PostnikovCommonCore.postnikovCommonClassCompatibilityToCell R hn f c d ≫
      cellResolutionMap R (PostnikovCommonCore.postnikovCommonRightDenBase R hn f c d ≫
        postnikovMap R (B.transition hj).hom n)) ≫
          postnikovCellLift R (B.obj j).obj n hn := by
  rw [(PostnikovCommonCore.postnikovCommonRightGammaSourceWitness R hn f c d hj).target_eq]
  rw [← Category.assoc, PostnikovCommonCore.postnikovCommonRightGamma_comparison]

lemma postnikovCommonClassRightDenominatorBase_composite :
    PostnikovCommonCore.postnikovCommonClassRightDenominatorBase R hn f c d hj =
      PostnikovCommonCore.postnikovCommonRightDenBase R hn f c d ≫ postnikovMap R (B.transition hj).hom n := by
  rw [PostnikovCommonCore.postnikovCommonClassRightDenominatorBase,
    ← PostnikovCommonCore.postnikovCommonRightDenDirect_factorization, postnikovMap_composition,
    PostnikovCommonCore.postnikovCommonRightDenBase, Category.assoc]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore

namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} {hn : 0 ≤ n} {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovSuccessorClassInverseData R hn f j)

lemma rightGammaSourceWitness_target :
    (PostnikovCommonCore.postnikovCommonRightGammaSourceWitness R hn f d.baseInverse d.layerInverse d.target_le).hom ≫
      Path.target R (postnikovPerturbedExtension R (B.obj j).obj n hn) =
        d.fixedRightCompletedNativeSource R := by
  rw [PostnikovCommonCore.postnikovCommonRightGammaSourceWitness_target]
  simp only [fixedRightCompletedNativeSource, fixedRightCompletedCellMap, Category.assoc]
  rw [reassoc_of% (PostnikovCommonCore.postnikovCommonRightImageToSecond_toCell R hn f d.baseInverse d.layerInverse),
    PostnikovCommonCore.postnikovCommonClassRightDenominatorBase_composite]
end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
