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
public import SerrePositivity.KST.Descent.NoetherianReduction
public import SerrePositivity.KST.Descent.FiniteTypeReduction
public import SerrePositivity.KST.Descent.DescentNaturality
public import SerrePositivity.KST.Descent.ReductionDescent
public import SerrePositivity.KST.Descent.FiniteCoproduct
public import SerrePositivity.KST.Descent.SectionOrbit
public import SerrePositivity.KST.Descent.ClosedCoproduct
public import SerrePositivity.KST.Descent.SectionCoincidence
public import SerrePositivity.KST.Descent.CoproductRestriction
public import SerrePositivity.KST.Descent.ClosedImmersionSquare
public import SerrePositivity.KST.Descent.OrbitGeometry
public import SerrePositivity.KST.Descent.OrbitAction
public import SerrePositivity.KST.Descent.PullbackAction
public import SerrePositivity.KST.Descent.FiniteTypeAction
public import SerrePositivity.KST.Descent.ClosedPullbackAction
public import SerrePositivity.KST.Descent.SquareAction
public import SerrePositivity.KST.Descent.EquivariantOrbitGeometry
public import SerrePositivity.KST.Descent.SquareSequenceAction
public import SerrePositivity.KST.Descent.SquareMapSequence
public import SerrePositivity.KST.Descent.BlowupSequenceData
public import SerrePositivity.KST.Descent.IdentityCenterSquare
public import SerrePositivity.KST.Descent.EquivariantSquareComparison
public import SerrePositivity.KST.Descent.OrbitComparisonCube
public import SerrePositivity.KST.Descent.OrbitCriterion
public import SerrePositivity.KST.Descent.CopyComparison
public import SerrePositivity.KST.Descent.OrbitCopies
public import SerrePositivity.KST.Descent.CopyEvaluationLimit
public import SerrePositivity.KST.Descent.OrbitCoproduct
public import SerrePositivity.KST.Descent.FixedPullbackComparison
public import SerrePositivity.KST.Descent.OrbitProductComparison
public import SerrePositivity.KST.Descent.FiniteTypeUniversal
public import SerrePositivity.KST.Descent.ExceptionalCopies
public import SerrePositivity.KST.Descent.ExceptionalCopiesAction
public import SerrePositivity.KST.Descent.OrbitDescentStep

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
Noether 基底上の「一般 → 被約」の全次数降下比較の還元も公開する。
切断の有限非交和の有限性・固有性と、被約化への軌道射の G 同変性も公開する。
一致中心の外の切断の像の互いに素と、被約な終域の有限閉被覆の非交和同型も公開する。
有限非交和と開制限の標準比較、および基底の一致中心を引き戻した実際の軌道正方形を公開する。
軌道正方形の四頂点の G 作用と四辺の同変性、前層の指定制限と差の同変性も公開する。
境界の自然性からの同変性、基底の恒等中心正方形への実際の比較立方体、
中項・例外部分の固定比較から指定された全次数 PiDescent を得る軌道判定も公開する。
非交和の指定コピー評価と置換表現、有限型の圏内の軌道の非交和の普遍性、
コピーの有限積保存と中心上の降下からの実際の中項比較も公開する。
例外部分の実際の同変コピー分解を用い、二つの非交和の積保存と中心上の降下から
実際の軌道段階の全次数 PiDescent を導く。

## 規約
最小公理 (1)–(8)、Čech 降下、主定理の証明、E の実現は未完成。
通常の不変部分を hG と呼ばず、次数ごとの極限を Tot と呼ばない。

## 使われ方
K0・T2 と L9 の導来値域に接続する L8 専用の入口。
-/
