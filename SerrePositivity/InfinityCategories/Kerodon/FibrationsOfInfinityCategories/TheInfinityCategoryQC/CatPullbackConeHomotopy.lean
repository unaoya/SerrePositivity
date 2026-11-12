module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.CatPullbackCone
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpecifiedConeTransportRestrictions

/-!
概要：引き戻し錐の相対輸送の指定ホモトピーと二つの制限。
方針：選んだ錐と同じ輸送データを使う。
規約：頂点は定値、図式は定値 path の切断の coherent 円柱。
使われ方：元の cospan の二射影と指定 path の比較。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]

/-- 概要：元と置換後の引き戻し錐を結ぶ指定された可逆ホモトピー。
方針：頂点と図式の相対輸送のデータから取り出す。
規約：選択した元の錐との厳密な対応を保つ。
使われ方：二脚と指定可換性の比較。 -/
def catPullbackConeHomotopy (p : A ⟶ C) (q : B ⟶ C) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.catPullbackCone p q).val (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.catPullbackReplacementCone p q).val :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeTransport p q).homotopy
/-- 概要：引き戻し錐の比較ホモトピーは頂点側で定値。
方針：相対輸送の頂点の制限公式を適用する。
規約：全時刻で厳密に固定する。
使われ方：二脚の比較で頂点の自己同値を除く。 -/
lemma catPullbackConeHomotopy_apex (p : A ⟶ C) (q : B ⟶ C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u + 1})
      ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (AsSmall.{u} WalkingCospan))) ▷
      (Δ[1] : SSet.{u + 1})) ≫
        (catPullbackConeHomotopy p q).h =
      fst Δ[0] Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0]
        ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (AsSmall.{u} WalkingCospan))) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.catPullbackReplacementCone p q).val :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeTransport p q).apex
/-- 概要：引き戻し錐の比較は図式側で切断の指定円柱に一致する。
方針：相対輸送の図式の制限公式を適用する。
規約：自然変換を別の代表に置き換えない。
使われ方：二脚の自然性の正方形の計算。 -/
lemma catPullbackConeHomotopy_diagram (p : A ⟶ C) (q : B ⟶ C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u + 1})
      ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (AsSmall.{u} WalkingCospan))) ▷
      (Δ[1] : SSet.{u + 1})) ≫
        (catPullbackConeHomotopy p q).h =
      (β_ ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (AsSmall.{u} WalkingCospan)))
        (Δ[1] : SSet.{u + 1})).hom ≫
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.strictCoherentNatTransMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackReplacementNatTrans p q) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeTransport p q).diagram
/-- 概要：引き戻し錐の全錐の比較ホモトピーは全頂点で可逆。
方針：構成した相対輸送の可逆性を取り出す。
規約：図式上の頂点だけでなく join 全体の頂点を扱う。
使われ方：全錐の同型と極限性の保存。 -/
lemma catPullbackConeHomotopy_vertical_isInvertible (p : A ⟶ C) (q : B ⟶ C)
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u + 1})
      ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (AsSmall.{u} WalkingCospan)))) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (catPullbackConeHomotopy p q) x).toTruncated :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeTransport p q).vertical_isInvertible x

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
