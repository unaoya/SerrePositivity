module

public import SerrePositivity.InfinityCategories.F2.CoherentCospanCommonCoordinates
public import SerrePositivity.InfinityCategories.F2.CospanRectificationImages

/-!
概要：共通の二脚置換後における native 比較と模型比較の右脚の指定同型を構成する。
方針：同じ右厳密化の指定同型の逆へ、元の native 右脚の値比較を続ける。
規約：元の指定二同型を使用。使われ方：共通の引き戻し全体の同型の貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}} [Quasicategory B]
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z)
local notation "cr" => coherentTransformationTotalMap F Y C.toRight
local notation "cg" => coherentTransformationTotalMap Y Z C.fromRight
local notation "f" => continuousKanReplacement.map (coherentTransformationTotalMap X Z C.fromLeft)
local notation "g" => continuousKanReplacement.map cg
local notation "ng" => coherentTotalMapNativeValueDown Y Z cg
local notation "nr" => coherentTotalMapNativeValueDown F Y cr
local notation "t" => eqToHom (coherentDiagramTotalVertex_object Y)
local notation "v" => eqToHom (coherentDiagramTotalVertex_object Z)
local notation "q" => pullback.snd (intervalReplacementEndpoint f) (intervalReplacementEndpoint g)

/-- 元の右成分の指定比較を、共通の引き戻しの右脚の同型として組み合わせる。 -/
def coherentCospanCommonRightIso :
    FunctorIso (coherentCospanNativeCommonComparison F X Y Z C ≫ q)
      (coherentCospanModelCommonComparison F X Y Z C ≫ q) := by
  let a := FunctorIso.precomp
    (cospanRectificationRightIso ng g t v (coherentTotalNativeKanIso Y Z cg)).symm nr
  let b := functorIsoOfEq ((coherentTotalNativeKanIso F Y cr).postcomp
    (intervalReplacementSection g)) (Category.assoc _ _ _) (Category.assoc _ _ _)
  exact functorIsoOfEq (a ≪≫ b)
    (coherentCospanNativeCommonComparison_right F X Y Z C).symm
    (coherentCospanModelCommonComparison_right F X Y Z C).symm

end SerrePositivity.InfinityCategories.F2
