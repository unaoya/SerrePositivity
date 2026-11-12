module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanCommonInputs
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentNativeKanValueImage
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentNativeKanValueMaps
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoWhiskerCancellation

/-!
概要：左外脚の値比較の第一置換による二段の制限を、元の native 左内脚での制限へ戻す。
方針：前合成の結合則と元の入力射影の式を使い、同じ頂点表示の逆の像を回収する。
規約：元の端点の式と指定値を保持。使われ方：左厳密化の逆補正の第二成分の像。
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
local notation "cf" => coherentTransformationTotalMap X Z C.fromLeft
local notation "nf" => coherentTotalMapNativeValueDown X Z cf
local notation "ng" => coherentTotalMapNativeValueDown Y Z
  (coherentTransformationTotalMap Y Z C.fromRight)
local notation "aN" => coherentCospanConeNativeComparison F X Y Z C ≫
  pullback.fst (intervalReplacementEndpoint nf) ng
local notation "nl" => coherentTotalMapNativeValueDown F X
  (coherentTransformationTotalMap F X C.toLeft)
local notation "w" => eqToHom (Eq.symm (coherentDiagramTotalVertex_object Z))

/-- 同じ左外脚の二段の制限の像は、元の値比較の元の native 左内脚での前合成。 -/
lemma coherentCospanCommonLeftOuterImage :
    HEq ((((coherentTotalNativeKanIso X Z cf).precomp
      (pullback.snd ((intervalEndpointNatTrans 0).app
        (spaceInfinityObject (coherentDiagramTotalVertex Z)).obj) nf)).precomp aN).postcomp w)
      ((coherentTotalMapNativeValueDownIso X Z cf).precomp nl) := by
  exact functorIso_precomp_precomp_postcomp_heq (coherentTotalNativeKanIso X Z cf)
    (coherentTotalMapNativeValueDownIso X Z cf) _ aN nl w
    (coherentTotalNativeKanIso_valueSourceMap X Z cf).symm
    (coherentTotalNativeKanIso_valueTargetMap X Z cf).symm
    (coherentTotalNativeKanIso_valueImage X Z cf)
    (coherentCospanNativeFirstInput F X Y Z C)

end SerrePositivity.InfinityCategories.F2
