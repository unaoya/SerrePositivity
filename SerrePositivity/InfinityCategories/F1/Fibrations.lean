module

public import SerrePositivity.InfinityCategories.Core.Fibrations
public import SerrePositivity.InfinityCategories.F1.CartesianFibration
public import SerrePositivity.InfinityCategories.Core.CocartesianCoslice
public import SerrePositivity.InfinityCategories.Core.CocartesianCosliceFiber
public import SerrePositivity.InfinityCategories.Core.CocartesianCosliceLifting
public import SerrePositivity.InfinityCategories.Core.CocartesianEdge
public import SerrePositivity.InfinityCategories.Core.CocartesianEdgePullback
public import SerrePositivity.InfinityCategories.Core.CocartesianFibration
public import SerrePositivity.InfinityCategories.Core.CocartesianFixedVertexTransport
public import SerrePositivity.InfinityCategories.Core.CocartesianHomotopyExtension
public import SerrePositivity.InfinityCategories.Core.CocartesianPathLifting
public import SerrePositivity.InfinityCategories.Core.CocartesianPathSpace
public import SerrePositivity.InfinityCategories.Core.CocartesianPathVertices
public import SerrePositivity.InfinityCategories.Core.CocartesianPrismBoundary
public import SerrePositivity.InfinityCategories.Core.CocartesianPrismExtension
public import SerrePositivity.InfinityCategories.Core.CocartesianTerminalBoundary
public import SerrePositivity.InfinityCategories.Core.RelativeOuterHorn
public import SerrePositivity.InfinityCategories.Core.RelativeOuterHornOp

/-!
概要：cartesian・cocartesian な辺と fibration、相対外側ホーンの基本結果の入口。
方針：Core の充填補題と F1 の辺・fibration の定義を、原本の所在を保ってまとめる。
規約：一単体で表す `IsCocartesianEdge` と、端点付きの辺で表す
`HasCocartesianHornLifting` の公開名・型をそのまま使う。
使われ方：輸送と straightening に進む前に、定義と相対充填の読み順を確認する。

* `Core/Fibrations`：左右 anodyne、左右 fibration、trivial Kan fibration、頂点 fiber。
* `CartesianEdge`・`CartesianFibration`：cartesian・cocartesian な辺と fibration。
* `Core/RelativeOuterHorn`・`RelativeOuterHornOp`：相対外側ホーンの充填。
* `Core/Cocartesian*`：端点付きの辺の充填条件、prism・coslice・固定頂点での輸送。
-/
