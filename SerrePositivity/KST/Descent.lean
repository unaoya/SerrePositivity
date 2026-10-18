module

public import SerrePositivity.KST.Descent.Axioms
public import SerrePositivity.KST.Descent.Transfer
public import SerrePositivity.KST.Descent.RationalFixedPoints
public import SerrePositivity.KST.Descent.PiComparison
public import SerrePositivity.KST.Descent.DiagramTransfer
public import SerrePositivity.KST.Descent.InvariantExactness
public import SerrePositivity.KST.Descent.PresheafAction
public import SerrePositivity.KST.Descent.InvariantsHomology
public import SerrePositivity.KST.Descent.SplitCech
public import SerrePositivity.KST.Descent.NilpotentThickening
public import SerrePositivity.KST.Descent.SchemeFacts
public import SerrePositivity.KST.Descent.ClosedDimension
public import SerrePositivity.KST.Descent.BlowupGeometry
public import SerrePositivity.KST.Descent.MayerVietoris
public import SerrePositivity.KST.Descent.SquareSequence
public import SerrePositivity.KST.Descent.CoincidenceLocus
public import SerrePositivity.KST.Descent.EquivariantMayerVietoris
public import SerrePositivity.KST.Descent.PermutationRepresentation
public import SerrePositivity.KST.Descent.InvariantProducts
public import SerrePositivity.KST.Descent.SplitMayerVietoris
public import SerrePositivity.KST.Descent.Theorem31
public import SerrePositivity.KST.Descent.ReducedClosedSubscheme
public import SerrePositivity.KST.Descent.CoincidenceCenter
public import SerrePositivity.KST.Descent.ClosedCenterSquare
public import SerrePositivity.KST.Descent.AffineReduction
public import SerrePositivity.KST.Descent.ReductionFunctor

/-!
# K-L8：論文 §3 の降下

## 概要
定理 3.1 の全次数 π_* 比較と、その証明に用いる代数的な基礎を集約する。

## 方針
係数つき次数付き前層、導来値域への実現、比較射の retract、
有限平坦 transfer の有理分裂、有理不変部分の完全性・ホモロジー保存を公開する。
底変換後の Čech nerve の分裂と、その前層の像の収縮ホモトピーも公開する。
冪零 thickening、不変性の法則の型、抽象 blowup の幾何データ、
境界を持つ全次数の正方形の長完全列と比較、有限次元での真閉部分の次元低下を公開する。
一致場所の有限和の真閉性、不変部分の全次数完全列、(3.8) の指定対角比較、
軌道正方形の全次数の代数的な貼り合わせを公開する。
被約閉中心と実際の Cartesian 正方形、アフィン Noether の被約化の冪零性、
一般の被約化の普遍性と関手性・群作用の移行を公開する。

## 規約
最小公理 (1)–(8)、Čech 降下、主定理の証明、E の実現は未完成。
通常の不変部分を hG と呼ばず、次数ごとの極限を Tot と呼ばない。

## 使われ方
K0・T2 と L9 の導来値域に接続する L8 専用の入口。
-/
