module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.EdgeEquiv

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentEdges

/-!
概要：coherent nerve の辺の全単射、恒等辺、合成三角形。
方針：F1 の既存の射データと端点固定の辺の対応を F2 の表示に適用する。
規約：合成は指定した二単体で実現し、全ての合成辺の厳密な一意性は要求しない。
使われ方：Cat_∞ の関手・恒等・合成を元の quasicategory の関手と結ぶ。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe v u
open CategoryTheory
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

variable {C : Type u} [Category.{v} C] [SimplicialCategory C]

/-- 概要：端点付きの射データと coherent nerve の全一単体は全単射に対応する。
方針：F1 の射データの往復対応を逆向きに用いる。
規約：任意の単体的圏で使い、辺を同値類にしない。
使われ方：Cat_∞ の任意の辺を対象二つと実際の関手へ分解する。 -/
def coherentEdgeEquiv : (Σ X Y : C, X ⟶ Y) ≃ (SimplicialNerve C) _⦋1⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowDataEquiv C).symm

/-- 概要：端点を指定した coherent nerve の辺と元の射は全単射に対応する。
方針：F1 の端点の移送を含む辺の全単射を逆向きに用いる。
規約：両端点の表示は F2 の coherentVertex。
使われ方：Cat_∞ の二対象間の関手の具体的な表示。 -/
def coherentFixedEdgeEquiv (X Y : C) :
    (X ⟶ Y) ≃ (SimplicialNerve C).Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentVertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentVertex Y) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeEquiv X Y).symm

/-- 概要：恒等射の coherent な辺は頂点の退化辺。
方針：F1 の端点付き恒等辺の等式を一単体で評価する。
規約：σ₀ は唯一の零単体の退化。
使われ方：Cat_∞ の恒等関手と恒等辺の一致。 -/
lemma coherentEdge_id (X : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdge (𝟙 X) = (SimplicialNerve C).σ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentVertex X) :=
  congrArg SSet.Edge.edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_id X)

/-- 概要：二つの通常の射の合成は coherent nerve の合成三角形を持つ。
方針：F1 の通常の nerve からの標準射による二単体を再利用する。
規約：元の指定射 f、g、f≫g を三辺として厳密に保つ。
使われ方：Cat_∞ の関手の合成を具体的な二単体として扱う。 -/
def coherentCompStruct {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    SSet.Edge.CompStruct (coherentFixedEdgeEquiv X Y f) (coherentFixedEdgeEquiv Y Z g)
      (coherentFixedEdgeEquiv X Z (f ≫ g)) := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct f g

/-- 概要：Cat_∞ の二頂点間の辺と小さい quasicategory 間の関手の全単射。
方針：QCat の通常の射が元の単体集合の射であることを使う。
規約：関手の同型類にせず、端点を指定した native な辺を返す。
使われ方：Cat_∞ 内の引き戻し図式の二本の関手。 -/
def catInfinityEdgeEquiv (X Y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}) :
    (X.obj ⟶ Y.obj) ≃ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u}.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentVertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentVertex Y) :=
  coherentFixedEdgeEquiv X Y

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
