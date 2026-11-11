module
public import SerrePositivity.KST.SConstruction.EndpointFixedEdgeSquares
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence

/-! # 四つの元の実三角形からの端点固定辺比較
概要：二組の構造三角形と二つの比較三角形から、二つの指定比較辺を実比較する。
方針：四つの全三角形の合成式を使い、Kan ホモトピー圏で共通始辺を消去する。
規約：四つの実三角形を入力に使い、二辺の類の等式を別途仮定しない。
使われ方：前段比較の構造射像と次段比較の射影の端点固定二次元比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {E : SSet.{u}} [KanComplex E] {a b c d : E _⦋0⦌}
  {original : E.Edge a b} {left : E.Edge b c} {right : E.Edge b d}
  {leftNext : E.Edge a c} {rightNext : E.Edge a d}
  {previous projected : E.Edge c d}
  (leftStructure : SSet.Edge.CompStruct original left leftNext)
  (rightStructure : SSet.Edge.CompStruct original right rightNext)
  (previousComparison : SSet.Edge.CompStruct left previous right)
  (projectedComparison : SSet.Edge.CompStruct leftNext projected rightNext)

include leftStructure rightStructure previousComparison projectedComparison

/-- 四つの元の実三角形から、二つの比較辺の同じ合成類を得る。 -/
lemma fourTriangleComparison_class :
    SSet.HomotopyCategory.homMk projected = SSet.HomotopyCategory.homMk previous := by
  have : IsIso (SSet.HomotopyCategory.homMk leftNext) :=
    IsGroupoid.all_isIso (C := hoFunctor.obj E) (SSet.HomotopyCategory.homMk leftNext)
  apply (cancel_epi (SSet.HomotopyCategory.homMk leftNext)).1
  calc
    _ = SSet.HomotopyCategory.homMk rightNext :=
      SSet.HomotopyCategory.homMk_comp_homMk projectedComparison
    _ = SSet.HomotopyCategory.homMk original ≫ SSet.HomotopyCategory.homMk right :=
      (SSet.HomotopyCategory.homMk_comp_homMk rightStructure).symm
    _ = SSet.HomotopyCategory.homMk original ≫
        (SSet.HomotopyCategory.homMk left ≫ SSet.HomotopyCategory.homMk previous) :=
      congrArg (SSet.HomotopyCategory.homMk original ≫ ·)
        (SSet.HomotopyCategory.homMk_comp_homMk previousComparison).symm
    _ = _ := by
      rw [← Category.assoc, SSet.HomotopyCategory.homMk_comp_homMk leftStructure]

/-- 同じ指定二辺を二面に保つ実比較三角形を、四つの実三角形から構成する。 -/
def fourTriangleComparisonTriangle : SSet.Edge.CompStruct projected (SSet.Edge.id d) previous := by
  apply SSet.Edge.CompStruct.ofTruncated
  apply Nonempty.some
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac
  change SSet.HomotopyCategory.homMk projected ≫
    SSet.HomotopyCategory.homMk (SSet.Edge.id d) = SSet.HomotopyCategory.homMk previous
  rw [SSet.HomotopyCategory.homMk_id, Category.comp_id]
  exact fourTriangleComparison_class leftStructure rightStructure
    previousComparison projectedComparison

/-- 四つの元の実三角形から構成した、両端固定の全実正方形。 -/
def fourTriangleComparisonSquare :=
  endpointFixedEdgeSquare (fourTriangleComparisonTriangle leftStructure rightStructure
    previousComparison projectedComparison)

end SerrePositivity.KST.SConstruction
