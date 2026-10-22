module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoRoofRightComparison

/-!
概要：元の分子・分母側の二切断射を、元の上段・底・右経路を保つ共通模型へ移す。
方針：元の二つの通常底変更射と、指定経路による実比較の三成分の式を合成する。
規約：二つの合成射の準同型性は未主張。使われ方：右三角形と π₂ 逆の貼合せ。
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

attribute [local instance] roof_nonpositive upper_nonpositive

def postnikovTwoRoofNumeratorToCommon :
    postnikovTwoRoofNumerator R f c ⟶ postnikovTwoRoofRightCommon R f c :=
  postnikovTwoRoofNumeratorMap R f c ≫ postnikovTwoRoofRightFirstComparison R f c

def postnikovTwoRoofDenominatorToCommon :
    postnikovTwoRoofDenominator R f c ⟶ postnikovTwoRoofRightCommon R f c :=
  postnikovTwoRoofDenominatorMap R f c ≫ postnikovTwoRoofRightSecondComparison R f c

lemma postnikovTwoRoofNumeratorToCommon_base :
    postnikovTwoRoofNumeratorToCommon R f c ≫ postnikovTwoRoofRightCommonBase R f c =
      postnikovExtensionBaseChangeBase R (A.obj i).obj 1 c.roof.numerator := by
  rw [postnikovTwoRoofNumeratorToCommon, Category.assoc,
    postnikovTwoRoofRightFirstComparison_base, postnikovTwoRoofNumeratorMap_base]

lemma postnikovTwoRoofDenominatorToCommon_base :
    postnikovTwoRoofDenominatorToCommon R f c ≫ postnikovTwoRoofRightCommonBase R f c =
      postnikovTwoRoofDenominatorBase R f c := by
  rw [postnikovTwoRoofDenominatorToCommon, Category.assoc,
    postnikovTwoRoofRightSecondComparison_base, postnikovTwoRoofDenominatorMap_base]

lemma postnikovTwoRoofNumeratorToCommon_upper :
    postnikovTwoRoofNumeratorToCommon R f c ≫ postnikovTwoRoofRightCommonUpper R f c =
      postnikovExtensionBaseChangeUpper R (A.obj i).obj 1 c.roof.numerator ≫
        postnikovMap R (f.app i).hom 2 := by
  rw [postnikovTwoRoofNumeratorToCommon, Category.assoc,
    postnikovTwoRoofRightFirstComparison_upper, postnikovTwoRoofNumeratorMap_upper]

lemma postnikovTwoRoofDenominatorToCommon_upper :
    postnikovTwoRoofDenominatorToCommon R f c ≫ postnikovTwoRoofRightCommonUpper R f c =
      postnikovTwoRoofDenominatorUpper R f c ≫ postnikovMap R (B.transition hi).hom 2 := by
  rw [postnikovTwoRoofDenominatorToCommon, Category.assoc,
    postnikovTwoRoofRightSecondComparison_upper, postnikovTwoRoofDenominatorMap_upper]

lemma postnikovTwoRoofNumeratorToCommon_trace :
    postnikovTwoRoofNumeratorToCommon R f c ≫ postnikovTwoRoofRightCommonTrace R f c =
      postnikovExtensionBaseChangeBase R (A.obj i).obj 1 c.roof.numerator ≫
        postnikovTwoRoofRightFirst R f c ≫ Path.diagonal R (postnikov R (B.obj i).obj 1) := by
  have ht : postnikovTwoRoofRightFirstComparison R f c ≫ postnikovTwoRoofRightCommonTrace R f c =
      postnikovExtensionBaseChangeBase R (B.obj i).obj 1 (postnikovTwoRoofRightFirst R f c) ≫
        postnikovTwoRoofRightFirst R f c ≫ Path.diagonal R (postnikov R (B.obj i).obj 1) :=
    PathBaseChange.firstNonpositive_trace R _ _
  rw [postnikovTwoRoofNumeratorToCommon, Category.assoc, ht, ← Category.assoc,
    postnikovTwoRoofNumeratorMap_base]

lemma postnikovTwoRoofDenominatorToCommon_trace :
    postnikovTwoRoofDenominatorToCommon R f c ≫ postnikovTwoRoofRightCommonTrace R f c =
      postnikovTwoRoofDenominatorBase R f c ≫ c.rightPath.hom := by
  have ht : postnikovTwoRoofRightSecondComparison R f c ≫ postnikovTwoRoofRightCommonTrace R f c =
      postnikovExtensionBaseChangeBase R (B.obj i).obj 1 (postnikovTwoRoofRightSecond R f c) ≫
        c.rightPath.hom := PathBaseChange.secondNonpositive_trace R _ _ _ _
  rw [postnikovTwoRoofDenominatorToCommon, Category.assoc, ht, ← Category.assoc,
    postnikovTwoRoofDenominatorMap_base]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
