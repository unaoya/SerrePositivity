module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanNativeKanPullback
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanModelKanCoordinates

/-!
概要：native 候補と元の Kan 模型比較を、同じ二脚置換後の引き戻しへ送る。
方針：既存の元の比較射へ同じ頂点表示・同じ引き戻し比較を合成する。
規約：元の射を保持。使われ方：全体の指定関手同型を貼り、native 候補へ同値性を反映。
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
local notation "f" => continuousKanReplacement.map (coherentTransformationTotalMap X Z C.fromLeft)
local notation "g" => continuousKanReplacement.map (coherentTransformationTotalMap Y Z C.fromRight)
local instance : KanComplex
    (pullback (intervalReplacementEndpoint f) (intervalReplacementEndpoint g)) :=
  HomotopyLimits.pullback_kanComplex_of_fibration _ _

/-- 元の native 候補から、共通の二脚置換後の引き戻しへの合成比較。 -/
def coherentCospanNativeCommonComparison :
    (spaceInfinityObject (coherentDiagramTotalVertex F)).obj ⟶
      pullback (intervalReplacementEndpoint f) (intervalReplacementEndpoint g) :=
  coherentCospanConeNativeComparison F X Y Z C ≫
    coherentCospanNativeKanPullbackComparison F X Y Z C

/-- 元の Kan 比較から、同じ始域の値と同じ二脚置換後の引き戻しへの合成比較。 -/
def coherentCospanModelCommonComparison :
    (spaceInfinityObject (coherentDiagramTotalVertex F)).obj ⟶
      pullback (intervalReplacementEndpoint f) (intervalReplacementEndpoint g) :=
  eqToHom (coherentDiagramTotalVertex_object F) ≫ coherentCospanConeKanComparison F X Y Z C ≫
    intervalPullbackDoubleReplacementComparison f g

/-- 元の各点の錐が極限なら、filtered な底における同じ模型合成比較は同値。 -/
lemma coherentCospanModelCommonComparison_homotopyEquivalence [IsFilteredInfinity B]
    (hc : ∀ b, IsLimitCone (coherentCospanConePointwiseCone F X Y Z C b)) :
    IsSimplicialHomotopyEquivalence (coherentCospanModelCommonComparison F X Y Z C) :=
  (HomotopyLimits.homotopyEquivalence_of_isIso
    (eqToHom (coherentDiagramTotalVertex_object F))).comp
      ((coherentCospanConeKanComparison_homotopyEquivalence F X Y Z C hc).comp
        (intervalPullbackDoubleReplacementComparison_homotopyEquivalence f g))

end SerrePositivity.InfinityCategories.F2
