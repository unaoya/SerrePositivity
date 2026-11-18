import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosed.Basic
import SerrePositivity.CommutativeAlgebra.Ultraproduct.Basic
import SerrePositivity.CommutativeAlgebra.Ultraproduct.Localization
import SerrePositivity.CommutativeAlgebra.ValuationExtension.Aic

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "§3 Studying v-sheaves via valuation rings" =>
%%%
number := false
tag := "bm18-3"
%%%

BM18 §3 の項目と、本体の宣言との対応。本文は対応表（`research/bm18-coverage`）の照合の理由で、原典の本文の写しではない。

:::definition "bm18_3_1"
*定義 3.1*　finitary 関手と v 層・arc 層。対応表の状態：なし。

原典 PDF p.16, y=258.3。v-sheaf・ultraproduct・valuation・descent・finitaryの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：Stacks 09MU

:::

:::definition "bm18_3_2" (uses := "bm18_3_1")
*定義 3.2*　普遍 F 降下。対応表の状態：一部（special）。

原典 PDF p.16, y=428.4。完全なアフィン係数へのすべての底変換後の構造層の増大 Čech 完全性として記述する。任意の F の値の ∞ 圏的比較写像を定義するものではない。

宣言：`SerrePositivity.AlgebraicGeometry.ArcRouteB.PerfectRingCechUniversalExact`、`SerrePositivity.AlgebraicGeometry.ArcRouteB.perfectRingCechUniversalExact_baseChange`

:::

:::proposition "bm18_3_3" (uses := "bm18_5_2")
*例 3.3*　エタールコホモロジーの普遍降下。対応表の状態：なし。

原典 PDF p.16, y=506.4。v-sheaf・ultraproduct・valuation・descent・finitaryの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：Gir64、LZ、SGA4

:::

:::lemma_ "bm18_3_4"
*補題 3.4*　普遍降下の切断・合成・反映・底変換。対応表の状態：一部（special）。

原典 PDF p.16, y=602.4。結論 (4) の完全アフィン係数・構造層の場合。任意の F の普遍降下の合成・反映・切断の全項目を述べる型はない。

宣言：`SerrePositivity.AlgebraicGeometry.ArcRouteB.perfectRingCechUniversalExact_baseChange`

外の文献：EHIK

:::

:::definition "bm18_3_5"
*定義 3.5*　余切断対象によるコンパクト生成。対応表の状態：なし。

原典 PDF p.17, y=158.7。v-sheaf・ultraproduct・valuation・descent・finitaryの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：EHIK、HTT

:::

:::proposition "bm18_3_6"
*例 3.6*　余切断対象で生成される圏の例。対応表の状態：なし。

原典 PDF p.17, y=253.0。v-sheaf・ultraproduct・valuation・descent・finitaryの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::lemma_ "bm18_3_7"
*補題 3.7*　全化と filtered 余極限。対応表の状態：なし。

原典 PDF p.17, y=465.4。v-sheaf・ultraproduct・valuation・descent・finitaryの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "bm18_3_8" (uses := "bm18_3_4")
*命題 3.8*　有限表示模型による v 層判定。対応表の状態：なし。

原典 PDF p.17, y=601.4。v-sheaf・ultraproduct・valuation・descent・finitaryの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：Rydh 3.12、Stacks 01YT、Stacks 09MU

:::

:::corollary "bm18_3_9" (uses := "bm18_3_18")
*系 3.9*　finitary v 層の有限表示サイトへの制限。対応表の状態：なし。

原典 PDF p.18, y=431.0。v-sheaf・ultraproduct・valuation・descent・finitaryの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：Jardine、Johnstone

:::

:::proposition "bm18_3_10"
*命題 3.10*　profinite 空間の clopen 基底上の層。対応表の状態：なし。

原典 PDF p.18, y=598.7。v-sheaf・ultraproduct・valuation・descent・finitaryの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：SAG

:::

:::definition "bm18_3_11"
*定義 3.11*　冪集合の上の層。対応表の状態：なし。

原典 PDF p.19, y=226.4。v-sheaf・ultraproduct・valuation・descent・finitaryの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "bm18_3_12"
*例 3.12*　離散の族の積で定める層。対応表の状態：なし。

原典 PDF p.19, y=259.1。v-sheaf・ultraproduct・valuation・descent・finitaryの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::definition "bm18_3_13" (uses := "bm18_3_10, bm18_3_11")
*構成 3.13*　Stone–Čech コンパクト化。対応表の状態：一部（component）。

原典 PDF p.19, y=325.1。離散空間の Stone–Čech コンパクト化を与える。原典の超フィルターでの表示は、この二つの宣言の型に現れない。

宣言：`StoneCech`、`stoneCechUnit`

外の文献：GJ60

:::

:::lemma_ "bm18_3_14"
*補題 3.14*　超フィルターの茎による同値の判定。対応表の状態：なし。

原典 PDF p.19, y=534.5。v-sheaf・ultraproduct・valuation・descent・finitaryの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：HTT

:::

:::definition "bm18_3_15" (lean := "SerrePositivity.RingUltraproduct, SerrePositivity.isLocalization_ringUltraproduct")
*定義 3.15*　環の超積。対応表の状態：本体にある。

原典 PDF p.20, y=96.3。超フィルター上ほとんど至る所で零となる元による商。指示冪等元による局所化としても得られ、超フィルター集合上の部分積の filtered 余極限と同じ環の超積を表す。

:::

:::proposition "bm18_3_16"
*注意 3.16*　積環のスペクトルと超積。対応表の状態：なし。

原典 PDF p.20, y=179.7。v-sheaf・ultraproduct・valuation・descent・finitaryの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::definition "bm18_3_17" (uses := "bm18_3_12")
*構成 3.17*　積環から構成する層。対応表の状態：なし。

原典 PDF p.20, y=314.1。v-sheaf・ultraproduct・valuation・descent・finitaryの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::corollary "bm18_3_18" (uses := "bm18_3_14")
*系 3.18*　超積での関手の同値による積での判定。対応表の状態：なし。

原典 PDF p.20, y=553.1。v-sheaf・ultraproduct・valuation・descent・finitaryの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::corollary "bm18_3_19" (uses := "bm18_3_25")
*系 3.19*　超積から積上の切断の存在。対応表の状態：なし。

原典 PDF p.21, y=96.3。v-sheaf・ultraproduct・valuation・descent・finitaryの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：HTT

:::

:::definition "bm18_3_20"
*定義 3.20*　普遍降下の検出の定義。対応表の状態：なし。

原典 PDF p.21, y=260.1。v-sheaf・ultraproduct・valuation・descent・finitaryの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "bm18_3_21" (uses := "bm18_3_4")
*例 3.21*　普遍降下射による検出。対応表の状態：なし。

原典 PDF p.21, y=314.2。v-sheaf・ultraproduct・valuation・descent・finitaryの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "bm18_3_22"
*例 3.22*　検出する族の合成。対応表の状態：なし。

原典 PDF p.21, y=344.4。v-sheaf・ultraproduct・valuation・descent・finitaryの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "bm18_3_23" (uses := "bm18_3_25")
*例 3.23*　族から積への普遍降下。対応表の状態：なし。

原典 PDF p.21, y=387.9。v-sheaf・ultraproduct・valuation・descent・finitaryの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::lemma_ "bm18_3_24" (uses := "bm18_3_4, bm18_3_7")
*補題 3.24*　逆極限での普遍降下の検出。対応表の状態：なし。

原典 PDF p.21, y=478.0。v-sheaf・ultraproduct・valuation・descent・finitaryの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::lemma_ "bm18_3_25" (uses := "bm18_3_14, bm18_3_17, bm18_3_30, bm18_3_32")
*補題 3.25*　超積による普遍降下の検出。対応表の状態：一部（special）。

原典 PDF p.22, y=96.3。超積全部のテストから積上の完全構造層の普遍 Čech 完全性を得る。任意の finitary F の普遍降下の検出を述べる型はない。

宣言：`SerrePositivity.AlgebraicGeometry.ArcRouteB.perfectRingCechUniversalExact_of_ultraproducts`、`SerrePositivity.isLocalization_ringUltraproduct`

:::

:::definition "bm18_eq_4" (uses := "bm18_3_25")
*式 (4)*　Čech 図式の底変換。対応表の状態：なし。

原典 PDF p.22, y=189.7。v-sheaf・ultraproduct・valuation・descent・finitaryの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::definition "bm18_3_26" (lean := "SerrePositivity.IsAbsolutelyIntegrallyClosed, SerrePositivity.valuationSubring_aic")
*定義 3.26*　絶対整閉環。対応表の状態：本体にある。

原典 PDF p.22, y=314.1。正次数のモニック多項式が根を持つ条件を定める。代数閉体内の付値部分環の絶対整閉性も与える。

:::

:::lemma_ "bm18_3_27" (lean := "SerrePositivity.valuationRing_ultraproduct, SerrePositivity.aic_ultraproduct") (uses := "bm18_3_30")
*補題 3.27*　絶対整閉付値環の超積。対応表の状態：本体にある。

原典 PDF p.22, y=396.5。付値環の超積の付値環性と、絶対整閉整域の超積の絶対整閉性を合わせて結論が従う。

外の文献：BS17、CKmodel、GabberKelly、GooLi

:::

:::lemma_ "bm18_3_28" (lean := "SerrePositivity.exists_valuationSubring_algebraicClosure, SerrePositivity.valuationSubring_aic") (uses := "bm18_2_21")
*補題 3.28*　絶対整閉付値環への忠実平坦拡大。対応表の状態：本体にある。

原典 PDF p.22, y=568.6。分数体の代数閉包内への付値環の忠実平坦な拡大が存在する。代数閉体内の付値部分環なので絶対整閉性も得る。

:::

:::lemma_ "bm18_3_29" (uses := "bm18_2_21")
*補題 3.29*　濃度を制限した絶対整閉付値部分環。対応表の状態：一部（component）。

原典 PDF p.23, y=96.3。原典の W と部分体の共通部分から W への忠実平坦性はある。濃度を制御した部分体の選択と A-代数としての因子分解の存在はこの型に含まれない。

宣言：`SerrePositivity.valuationSubringComapHom_faithfullyFlat`

:::

:::proposition "bm18_3_30" (uses := "bm18_3_25, bm18_3_27, bm18_3_28, bm18_3_29")
*命題 3.30*　付値環の族による普遍降下の検出。対応表の状態：なし。

原典 PDF p.23, y=232.4。v-sheaf・ultraproduct・valuation・descent・finitaryの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "bm18_3_31" (uses := "bm18_2_6, bm18_3_27, bm18_3_29")
*注意 3.31*　付値環を成分にもつ v 被覆。対応表の状態：なし。

原典 PDF p.23, y=481.4。v-sheaf・ultraproduct・valuation・descent・finitaryの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "bm18_3_32" (uses := "bm18_3_18, bm18_3_27, bm18_3_30")
*命題 3.32*　絶対整閉付値環による同値検出。対応表の状態：なし。

原典 PDF p.23, y=604.0。v-sheaf・ultraproduct・valuation・descent・finitaryの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：HTT

:::

