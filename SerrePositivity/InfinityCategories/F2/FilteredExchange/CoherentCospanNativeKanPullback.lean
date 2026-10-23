module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentTotalNativeKanIso
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanConeNativeComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CospanRectifiedPullbackComparison

/-!
概要：元の native 値の cospan と元の Kan cospan を同じ二脚置換後の引き戻しへ比較する。
方針：元の値比較の指定同型を厳密化し、頂点表示の三つの同型の同値性を使う。
規約：native 候補の元の二射を保持。使われ方：候補そのものへの弱同値性の移送。
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
local notation "cg" => coherentTransformationTotalMap Y Z C.fromRight
local notation "nf" => coherentTotalMapNativeValueDown X Z cf
local notation "ng" => coherentTotalMapNativeValueDown Y Z cg

/-- 元の native 二射の引き戻しから元の Kan 二射の両脚置換後への実際の比較射。 -/
def coherentCospanNativeKanPullbackComparison : intervalPullback nf ng ⟶
    pullback (intervalReplacementEndpoint (continuousKanReplacement.map cf))
      (intervalReplacementEndpoint (continuousKanReplacement.map cg)) :=
  cospanRectifiedPullbackComparison nf ng
    (continuousKanReplacement.map cf) (continuousKanReplacement.map cg)
    (eqToHom (coherentDiagramTotalVertex_object X))
    (eqToHom (coherentDiagramTotalVertex_object Y))
    (eqToHom (coherentDiagramTotalVertex_object Z))
    (coherentTotalNativeKanIso X Z cf) (coherentTotalNativeKanIso Y Z cg)

/-- 元の値比較から作った同じ引き戻し比較には実際のホモトピー逆が存在する。 -/
lemma coherentCospanNativeKanPullbackComparison_homotopyEquivalence :
    IsSimplicialHomotopyEquivalence (coherentCospanNativeKanPullbackComparison F X Y Z C) := by
  apply cospanRectifiedPullbackComparison_homotopyEquivalence
    nf ng (continuousKanReplacement.map cf) (continuousKanReplacement.map cg)
    (eqToHom (coherentDiagramTotalVertex_object X))
    (eqToHom (coherentDiagramTotalVertex_object Y))
    (eqToHom (coherentDiagramTotalVertex_object Z))
    (coherentTotalNativeKanIso X Z cf) (coherentTotalNativeKanIso Y Z cg)
  all_goals exact HomotopyLimits.homotopyEquivalence_of_isIso _

end SerrePositivity.InfinityCategories.F2
