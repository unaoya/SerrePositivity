import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.AlgebraicGeometry.ArcRouteB.IntervalSpectrum
import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosed.Basic
import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosed.Etale
import SerrePositivity.CommutativeAlgebra.Ultraproduct.Basic
import SerrePositivity.CommutativeAlgebra.Ultraproduct.Localization
import SerrePositivity.CommutativeAlgebra.ValuationExtension.Aic
import SerrePositivity.CommutativeAlgebra.ValuationInterval.Basic
import SerrePositivity.CommutativeAlgebra.ValuationInterval.Zorn

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "BM18（Bhatt–Mathew, The arc-topology, arXiv 1807.04725v4）" =>
%%%
number := false
tag := "vdescent-bm18"
%%%

BM18 の項目のうち、この経路で本体か Mathlib に対応があるもの。

# §1 Introduction

%%%
number := false
tag := "vdescent-bm18-1"
%%%

:::definition "bm18_1_1"
*BM18 定義 1.1*　v 位相と v 被覆。対応表の状態：一部（component）。

原典 PDF p.2, y=447.9。忠実平坦な付値環拡大によるスキームの射の v 被覆判定と、アフィン有限族の定義を持つ。全スキーム上の Grothendieck 位相の被覆族までの定義は見出していない。

宣言：`SerrePositivity.AlgebraicGeometry.IsSchemeVCover`、`SerrePositivity.AlgebraicGeometry.IsAffineVCoverFamily`

外の文献：RydhII、VHomology

:::

:::definition "bm18_eq_1" (uses := "bm18_1_1")
*BM18 式 (1)*　v 被覆の付値持ち上げ。対応表の状態：一部（special）。

原典 PDF p.2, y=513.6。一射の v 被覆に対する付値環拡大と持ち上げの可換性を合成等式で表している。

宣言：`SerrePositivity.AlgebraicGeometry.IsSchemeVCover`

:::

:::definition "bm18_1_2" (uses := "bm18_eq_1, bm18_1_1")
*BM18 定義 1.2*　arc 位相と arc 被覆。対応表の状態：一部（special）。

原典 PDF p.3, y=125.2。アフィンの射と有限アフィン族を rank ≤ 1 の付値環で判定する。一般の qcqs スキームの射および全スキーム上の arc 位相は型に含まれない。

宣言：`SerrePositivity.AlgebraicGeometry.ArcRouteB.IsArcHom`、`SerrePositivity.AlgebraicGeometry.ArcRouteB.IsArcCoverFamilyCharP`、`SerrePositivity.AlgebraicGeometry.ArcRouteB.isArcHom_pi_iff`

外の文献：Pic、Rydh、RydhII

:::

# §2 The arc-topology

%%%
number := false
tag := "vdescent-bm18-2"
%%%

:::lemma_ "bm18_2_3"
*BM18 補題 2.3*　合成の arc 被覆性からの反映。対応表の状態：一部（special）。

原典 PDF p.9, y=551.8。合成が arc 被覆なら後段も arc 被覆になる。環の射で記述したアフィンの場合。

宣言：`SerrePositivity.AlgebraicGeometry.ArcRouteB.isArcHom_of_refinement`

:::

:::proposition "bm18_2_8"
*BM18 命題 2.8*　付値環の excision datum。対応表の状態：一部（component）。

原典 PDF p.10, y=516.4。q が極大の場合の V、V\_p、V/p、κ(p) の加法群の短完全列から、局所化が素イデアル p を像のイデアルに同型に移すことが従う。一般の q での述語として excision datum を返す型は見出していない。

宣言：`SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationRing_milnorSquare`

:::

:::definition "bm18_2_12"
*BM18 定義 2.12*　submersion の定義。対応表の状態：Mathlib にある。

原典 PDF p.11, y=431.9。スキームの台位相写像に IsQuotientMap を課し、普遍版はすべての引き戻しで同じ性質を課す。原典の qcqs の範囲に制限して一致する。

宣言：`Topology.IsQuotientMap`、`AlgebraicGeometry.topologically`、`CategoryTheory.MorphismProperty.universally`

:::

:::lemma_ "bm18_2_21" (lean := "SerrePositivity.valuationSubringComapHom_faithfullyFlat")
*BM18 補題 2.21*　部分体に引き戻した付値環。対応表の状態：本体にある。

原典 PDF p.14, y=288.5。分数体への部分体の包含を体の単射として扱い、付値部分環の逆像から元の付値環への射の忠実平坦性を与える。逆像は ValuationSubring として型付けされる。

:::

# §3 Studying v-sheaves via valuation rings

%%%
number := false
tag := "vdescent-bm18-3"
%%%

:::definition "bm18_3_2"
*BM18 定義 3.2*　普遍 F 降下。対応表の状態：一部（special）。

原典 PDF p.16, y=428.4。完全なアフィン係数へのすべての底変換後の構造層の増大 Čech 完全性として記述する。任意の F の値の ∞ 圏的比較写像を定義するものではない。

宣言：`SerrePositivity.AlgebraicGeometry.ArcRouteB.PerfectRingCechUniversalExact`、`SerrePositivity.AlgebraicGeometry.ArcRouteB.perfectRingCechUniversalExact_baseChange`

:::

:::lemma_ "bm18_3_4"
*BM18 補題 3.4*　普遍降下の切断・合成・反映・底変換。対応表の状態：一部（special）。

原典 PDF p.16, y=602.4。結論 (4) の完全アフィン係数・構造層の場合。任意の F の普遍降下の合成・反映・切断の全項目を述べる型はない。

宣言：`SerrePositivity.AlgebraicGeometry.ArcRouteB.perfectRingCechUniversalExact_baseChange`

外の文献：EHIK

:::

:::definition "bm18_3_13"
*BM18 構成 3.13*　Stone–Čech コンパクト化。対応表の状態：一部（component）。

原典 PDF p.19, y=325.1。離散空間の Stone–Čech コンパクト化を与える。原典の超フィルターでの表示は、この二つの宣言の型に現れない。

宣言：`StoneCech`、`stoneCechUnit`

外の文献：GJ60

:::

:::definition "bm18_3_15" (lean := "SerrePositivity.RingUltraproduct, SerrePositivity.isLocalization_ringUltraproduct")
*BM18 定義 3.15*　環の超積。対応表の状態：本体にある。

原典 PDF p.20, y=96.3。超フィルター上ほとんど至る所で零となる元による商。指示冪等元による局所化としても得られ、超フィルター集合上の部分積の filtered 余極限と同じ環の超積を表す。

:::

:::lemma_ "bm18_3_25"
*BM18 補題 3.25*　超積による普遍降下の検出。対応表の状態：一部（special）。

原典 PDF p.22, y=96.3。超積全部のテストから積上の完全構造層の普遍 Čech 完全性を得る。任意の finitary F の普遍降下の検出を述べる型はない。

宣言：`SerrePositivity.AlgebraicGeometry.ArcRouteB.perfectRingCechUniversalExact_of_ultraproducts`、`SerrePositivity.isLocalization_ringUltraproduct`

:::

:::definition "bm18_3_26" (lean := "SerrePositivity.IsAbsolutelyIntegrallyClosed, SerrePositivity.valuationSubring_aic")
*BM18 定義 3.26*　絶対整閉環。対応表の状態：本体にある。

原典 PDF p.22, y=314.1。正次数のモニック多項式が根を持つ条件を定める。代数閉体内の付値部分環の絶対整閉性も与える。

:::

:::lemma_ "bm18_3_27" (lean := "SerrePositivity.valuationRing_ultraproduct, SerrePositivity.aic_ultraproduct")
*BM18 補題 3.27*　絶対整閉付値環の超積。対応表の状態：本体にある。

原典 PDF p.22, y=396.5。付値環の超積の付値環性と、絶対整閉整域の超積の絶対整閉性を合わせて結論が従う。

外の文献：BS17、CKmodel、GabberKelly、GooLi

:::

:::lemma_ "bm18_3_28" (lean := "SerrePositivity.exists_valuationSubring_algebraicClosure, SerrePositivity.valuationSubring_aic") (uses := "bm18_2_21")
*BM18 補題 3.28*　絶対整閉付値環への忠実平坦拡大。対応表の状態：本体にある。

原典 PDF p.22, y=568.6。分数体の代数閉包内への付値環の忠実平坦な拡大が存在する。代数閉体内の付値部分環なので絶対整閉性も得る。

:::

:::lemma_ "bm18_3_29" (uses := "bm18_2_21")
*BM18 補題 3.29*　濃度を制限した絶対整閉付値部分環。対応表の状態：一部（component）。

原典 PDF p.23, y=96.3。原典の W と部分体の共通部分から W への忠実平坦性はある。濃度を制御した部分体の選択と A-代数としての因子分解の存在はこの型に含まれない。

宣言：`SerrePositivity.valuationSubringComapHom_faithfullyFlat`

:::

# §4 The main result for arc-descent

%%%
number := false
tag := "vdescent-bm18-4"
%%%

:::lemma_ "bm18_4_4" (uses := "bm18_2_8")
*BM18 補題 4.4*　aic-v-excision の代数への持ち上げ。対応表の状態：一部（special）。

原典 PDF p.26, y=403.4。完全標数 p の付値環と完全な係数 A では同一点の重なりの短完全列が、四つの環の加法群の引き戻しを与える。一般の V-代数や任意の finitary v-sheaf F は扱わない。

宣言：`SerrePositivity.AlgebraicGeometry.ArcRouteB.overlapTensorModuleComplex_shortExact`

:::

:::definition "bm18_4_6" (lean := "SerrePositivity.ValuationIntervalRing, SerrePositivity.AlgebraicGeometry.ArcRouteB.intervalRingSpectrumOrderIso")
*BM18 定義 4.6*　付値環スペクトルの区間。対応表の状態：本体にある。

原典 PDF p.27, y=338.9。区間 \[p,q\] に (V/p)\_q を割り当て、その素スペクトルが同じ順序区間になる。

:::

:::lemma_ "bm18_4_7" (lean := "SerrePositivity.valuationIntervalProperty_of_localExtensions")
*BM18 補題 4.7*　局所延長と貼り合わせによる区間判定。対応表の状態：本体にある。

原典 PDF p.27, y=464.6。上下の局所延長、点、部分区間、重なりの貼り合わせから全区間を得る。原典の隣接点の条件は上下の延長条件から部分区間に制限して従う。

:::

:::proposition "bm18_4_8" (uses := "bs17_4_1, bm18_eq_6, bm18_2_3, bm18_4_4, bm18_4_7")
*BM18 命題 4.8*　aic-v-excision から arc 降下。対応表の状態：一部（special）。

原典 PDF p.28, y=220.5。G-A6-1 の経路 B。絶対整閉付値環上で完全環への arc 被覆を任意の完全アフィン係数へ底変換した構造層の Čech 完全性を示し、最後に完全標数 p のアフィン射・有限族へ戻す。一般の qcqs 基底、cotruncated 対象でコンパクト生成された ∞ 圏値の任意の finitary v-sheaf、任意の aic-v-excisive F の arc-sheaf 性を与える型はない。

宣言：`SerrePositivity.AlgebraicGeometry.ArcRouteB.aicValuationArc_universalExact`、`SerrePositivity.AlgebraicGeometry.ArcRouteB.cechExact_of_arcHom_perfect`、`SerrePositivity.AlgebraicGeometry.ArcRouteB.cech_exact_of_arcCover_perfect`

:::

:::definition "bm18_eq_6" (uses := "bm18_4_8")
*BM18 式 (6)*　重なる区間の比較正方形。対応表の状態：一部（special）。

原典 PDF p.29, y=134.3。同じ端点の局所化・商・交差の係数を比較し、完全な係数で短完全列を得る。この列の核が図式の引き戻しを表す。一般の F に適用した図式ではない。

宣言：`SerrePositivity.AlgebraicGeometry.ArcRouteB.overlapTensorModuleComplex_shortExact`、`SerrePositivity.AlgebraicGeometry.ArcRouteB.intervalTensorLocalizationEquiv`、`SerrePositivity.AlgebraicGeometry.ArcRouteB.intervalTensorQuotientEquiv`、`SerrePositivity.AlgebraicGeometry.ArcRouteB.intervalTensorIntersectionEquiv`

:::

# §5 Examples of arc-sheaves

%%%
number := false
tag := "vdescent-bm18-5"
%%%

:::lemma_ "bm18_5_3" (lean := "SerrePositivity.IsAbsolutelyIntegrallyClosed.henselianLocalRing, SerrePositivity.IsAbsolutelyIntegrallyClosed.residue_isAlgClosed")
*BM18 補題 5.3*　絶対整閉付値環の狭義 Hensel 性。対応表の状態：本体にある。

原典 PDF p.38, y=144.2。付値環の局所性を使い、絶対整閉局所環の Hensel 性と剰余体の代数閉性を合わせて狭義 Hensel 性を得る。

:::

:::theorem "bm18_5_17"
*BM18 定理 5.17*　Universally effective epimorphisms of perfect schemes。対応表の状態：一部（special）。

原典 PDF p.45, y=190.6。完全アフィンの arc 被覆について、Čech 複体の次数零の完全性から環の等化子が得られ、アフィンな試験対象への射についての降下を与える。任意の qcqs 代数空間への射、ならびに普遍有効エピから arc 被覆への逆向きは含まない。

宣言：`SerrePositivity.AlgebraicGeometry.ArcRouteB.cechExact_of_arcHom_perfect`

外の文献：B、RNoeth

:::

