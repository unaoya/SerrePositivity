module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.LeftFiberKan
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.VertexFiberPullback

/-!
概要：anodyne・fibration と頂点 fiber の基礎を読むための入口。
方針：定義を移さず、既存モジュールを public import して所在を示す。
規約：ホーンの向き・型クラス・宣言名は原本のまま保つ。
使われ方：Core の基礎を読む際の目次。Core 集約からも利用できる。

## 定義と読み順

* `InnerFibration`・`KanComplex`：Mathlib の定義。
* `JoinCells`：`rightHornInclusions`・`leftHornInclusions` と左右 anodyne。
* `RightFibration`：左右 fibration、inner fibration との接続、slice 射影。
* `Terminal`：`TrivialKanFibration` と境界充填による判定。
* `VertexFiber`・`VertexFiberPullback`：頂点 fiber と引き戻しとの同型。
* `LeftFiberKan`：左ホーンによる Kan 判定と left fibration の fiber。

cocartesian 辺・cocartesian fibration の定義は、引き続き
`F1/CartesianEdge`・`F1/CartesianFibration` を参照する。
-/
