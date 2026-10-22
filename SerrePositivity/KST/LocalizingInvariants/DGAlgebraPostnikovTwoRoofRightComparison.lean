module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoRoofNumerator
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathBaseChangeNonpositive

/-!
概要：元の右経路の両端に沿う二切断モデルを、同じ非正次数の実共通模型へ結ぶ。
方針：元の rightPath と元の二切断の全射遷移を、実経路底変更比較へ渡す。
規約：分子・分母側からの全射の逆は未構成。使われ方：π₂ 係数の逆の貼合せ。
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

local instance roof_nonpositive : c.roof.apex.X.IsStrictlyLE 0 := c.roof_nonpositive
local instance upper_nonpositive : (postnikov R (B.obj i).obj 2).X.IsStrictlyLE 0 :=
  postnikovComplex_nonpositive R (B.obj i).obj 2

def postnikovTwoRoofRightCommon : Mon (Complex R) :=
  PathBaseChange.nonpositiveCommon R (postnikovTwoRoofRightFirst R f c)
    (postnikovTransition R (B.obj i).obj 2 1 (by omega))

def postnikovTwoRoofRightCommonBase : postnikovTwoRoofRightCommon R f c ⟶ c.roof.apex :=
  PathBaseChange.nonpositiveBase R _ _

def postnikovTwoRoofRightCommonUpper :
    postnikovTwoRoofRightCommon R f c ⟶ postnikov R (B.obj i).obj 2 :=
  PathBaseChange.nonpositiveUpper R _ _

def postnikovTwoRoofRightCommonTrace :
    postnikovTwoRoofRightCommon R f c ⟶ Path.algebra R (postnikov R (B.obj i).obj 1) :=
  PathBaseChange.nonpositiveTrace R _ _

def postnikovTwoRoofRightFirstComparison :
    postnikovTwoRoofRightFirstModel R f c ⟶ postnikovTwoRoofRightCommon R f c :=
  PathBaseChange.firstNonpositive R _ _

def postnikovTwoRoofRightSecondComparison :
    postnikovTwoRoofRightSecondModel R f c ⟶ postnikovTwoRoofRightCommon R f c :=
  PathBaseChange.secondNonpositive R _ _ _ (postnikovTwoRoofRightWitness R f c)

lemma postnikovTwoRoofRightFirstComparison_quasiIso :
    QuasiIso (postnikovTwoRoofRightFirstComparison R f c).hom :=
  PathBaseChange.firstNonpositive_quasiIso R _ _

lemma postnikovTwoRoofRightSecondComparison_quasiIso :
    QuasiIso (postnikovTwoRoofRightSecondComparison R f c).hom :=
  PathBaseChange.secondNonpositive_quasiIso R _ _ _ _

lemma postnikovTwoRoofRightCommon_nonpositive :
    (postnikovTwoRoofRightCommon R f c).X.IsStrictlyLE 0 :=
  PathBaseChange.nonpositiveCommon_nonpositive R _ _

lemma postnikovTwoRoofRightFirstComparison_base :
    postnikovTwoRoofRightFirstComparison R f c ≫ postnikovTwoRoofRightCommonBase R f c =
      postnikovExtensionBaseChangeBase R (B.obj i).obj 1 (postnikovTwoRoofRightFirst R f c) :=
  PathBaseChange.firstNonpositive_base R _ _

lemma postnikovTwoRoofRightSecondComparison_base :
    postnikovTwoRoofRightSecondComparison R f c ≫ postnikovTwoRoofRightCommonBase R f c =
      postnikovExtensionBaseChangeBase R (B.obj i).obj 1 (postnikovTwoRoofRightSecond R f c) :=
  PathBaseChange.secondNonpositive_base R _ _ _ _

lemma postnikovTwoRoofRightFirstComparison_upper :
    postnikovTwoRoofRightFirstComparison R f c ≫ postnikovTwoRoofRightCommonUpper R f c =
      postnikovExtensionBaseChangeUpper R (B.obj i).obj 1 (postnikovTwoRoofRightFirst R f c) :=
  PathBaseChange.firstNonpositive_upper R _ _

lemma postnikovTwoRoofRightSecondComparison_upper :
    postnikovTwoRoofRightSecondComparison R f c ≫ postnikovTwoRoofRightCommonUpper R f c =
      postnikovExtensionBaseChangeUpper R (B.obj i).obj 1 (postnikovTwoRoofRightSecond R f c) :=
  PathBaseChange.secondNonpositive_upper R _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
