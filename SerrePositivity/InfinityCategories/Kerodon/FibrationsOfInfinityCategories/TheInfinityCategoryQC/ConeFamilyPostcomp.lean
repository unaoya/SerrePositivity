module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ConeFamily
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeVertexFiberLifting

/-!
概要：図式を固定した錐の族の後合成。
方針：錐制限の自然な正方形から頂点 fiber の射を構成する。
規約：元の図式と錐の実際の射を保持する。
使われ方：lax pullback の錐族の成分表示と極限性の判定。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：図式固定の錐の族の後合成。
方針：錐制限の自然性に一般の頂点 fiber の比較を適用する。
規約：像の図式は元の図式と関手の合成そのもの。
使われ方：成分ごとの錐と普遍性の比較。 -/
def coneFamilyPostcomp {J X Y : SSet.{u}} (r : J ⟶ X) (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamily r ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamily (r ≫ f) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeVertexFiberMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction J X) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction J Y)
    ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) J)).map f) ((ihom J).map f)
    ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) J)).naturality f).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex r)

/-- 概要：後合成した錐の族を含めると元の族の後合成。
方針：頂点 fiber の射の包含を計算する。
規約：全次数での射の等式。
使われ方：錐族の引き戻し比較と一意性。 -/
lemma coneFamilyPostcomp_ι {J X Y : SSet.{u}} (r : J ⟶ X) (f : X ⟶ Y) :
    coneFamilyPostcomp r f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction J Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (r ≫ f)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction J X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex r) ≫
        (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) J)).map f := rfl

/-- 概要：後合成は元の錐の頂点を像の錐の頂点へ送る。
方針：fiber の部分型の値を計算する。
規約：元の錐の実際の全単体の族を保つ。
使われ方：極限錐の終対象による判定との接続。 -/
lemma coneFamilyPostcomp_vertex {J X Y : SSet.{u}} (r : J ⟶ X) (f : X ⟶ Y)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone r) :
    (coneFamilyPostcomp r f).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamilyVertexEquiv r c) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamilyVertexEquiv (r ≫ f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone f c) := by
  apply Subtype.ext
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
