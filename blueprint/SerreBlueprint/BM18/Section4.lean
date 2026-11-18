import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.AlgebraicGeometry.ArcRouteB.IntervalSpectrum
import SerrePositivity.CommutativeAlgebra.ValuationInterval.Basic
import SerrePositivity.CommutativeAlgebra.ValuationInterval.Zorn

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "§4 The main result for arc-descent" =>
%%%
number := false
tag := "bm18-4"
%%%

BM18 §4 の項目と、本体の宣言との対応。本文は対応表（`research/bm18-coverage`）の照合の理由で、原典の本文の写しではない。

:::theorem "bm18_4_1" (uses := "bm18_2_8, bm18_3_1")
*定理 4.1*　arc 降下と excision の同値。対応表の状態：なし。

原典 PDF p.25, y=144.9。arc-cover・valuation interval・excision・Čech・toposの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：HK18

:::

:::definition "bm18_eq_5" (uses := "bm18_4_1")
*式 (5)*　絶対整閉付値環の excision 正方形。対応表の状態：なし。

原典 PDF p.25, y=258.0。arc-cover・valuation interval・excision・Čech・toposの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "bm18_4_2" (uses := "bm18_2_9")
*命題 4.2*　arc 降下から aic-v-excision。対応表の状態：なし。

原典 PDF p.25, y=416.0。arc-cover・valuation interval・excision・Čech・toposの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::lemma_ "bm18_4_3"
*補題 4.3*　絶対整閉付値環の素環拡大と局所化。対応表の状態：なし。

原典 PDF p.25, y=559.5。arc-cover・valuation interval・excision・Čech・toposの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::lemma_ "bm18_4_4" (uses := "bm18_eq_5, bm18_2_8, bm18_3_32, bm18_4_3")
*補題 4.4*　aic-v-excision の代数への持ち上げ。対応表の状態：一部（special）。

原典 PDF p.26, y=403.4。完全標数 p の付値環と完全な係数 A では同一点の重なりの短完全列が、四つの環の加法群の引き戻しを与える。一般の V-代数や任意の finitary v-sheaf F は扱わない。

宣言：`SerrePositivity.AlgebraicGeometry.ArcRouteB.overlapTensorModuleComplex_shortExact`

:::

:::lemma_ "bm18_4_5"
*補題 4.5*　有限表示 v 被覆の有限段への降下。対応表の状態：なし。

原典 PDF p.27, y=162.5。arc-cover・valuation interval・excision・Čech・toposの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：Rydh 3.12、Stacks 09MV

:::

:::definition "bm18_4_6" (lean := "SerrePositivity.ValuationIntervalRing, SerrePositivity.AlgebraicGeometry.ArcRouteB.intervalRingSpectrumOrderIso")
*定義 4.6*　付値環スペクトルの区間。対応表の状態：本体にある。

原典 PDF p.27, y=338.9。区間 \[p,q\] に (V/p)\_q を割り当て、その素スペクトルが同じ順序区間になる。

:::

:::lemma_ "bm18_4_7" (lean := "SerrePositivity.valuationIntervalProperty_of_localExtensions")
*補題 4.7*　局所延長と貼り合わせによる区間判定。対応表の状態：本体にある。

原典 PDF p.27, y=464.6。上下の局所延長、点、部分区間、重なりの貼り合わせから全区間を得る。原典の隣接点の条件は上下の延長条件から部分区間に制限して従う。

:::

:::proposition "bm18_4_8" (uses := "bm18_eq_6, bm18_eq_7, bm18_2_3, bm18_2_5, bm18_3_30, bm18_3_32, bm18_3_7, bm18_4_1, bm18_4_11, bm18_4_2, bm18_4_4, bm18_4_5, bm18_4_7")
*命題 4.8*　aic-v-excision から arc 降下。対応表の状態：一部（special）。

原典 PDF p.28, y=220.5。G-A6-1 の経路 B。絶対整閉付値環上で完全環への arc 被覆を任意の完全アフィン係数へ底変換した構造層の Čech 完全性を示し、最後に完全標数 p のアフィン射・有限族へ戻す。一般の qcqs 基底、cotruncated 対象でコンパクト生成された ∞ 圏値の任意の finitary v-sheaf、任意の aic-v-excisive F の arc-sheaf 性を与える型はない。

宣言：`SerrePositivity.AlgebraicGeometry.ArcRouteB.aicValuationArc_universalExact`、`SerrePositivity.AlgebraicGeometry.ArcRouteB.cechExact_of_arcHom_perfect`、`SerrePositivity.AlgebraicGeometry.ArcRouteB.cech_exact_of_arcCover_perfect`

外の文献：BS17 4.1

:::

:::definition "bm18_eq_6" (uses := "bm18_4_8")
*式 (6)*　重なる区間の比較正方形。対応表の状態：一部（special）。

原典 PDF p.29, y=134.3。同じ端点の局所化・商・交差の係数を比較し、完全な係数で短完全列を得る。この列の核が図式の引き戻しを表す。一般の F に適用した図式ではない。

宣言：`SerrePositivity.AlgebraicGeometry.ArcRouteB.overlapTensorModuleComplex_shortExact`、`SerrePositivity.AlgebraicGeometry.ArcRouteB.intervalTensorLocalizationEquiv`、`SerrePositivity.AlgebraicGeometry.ArcRouteB.intervalTensorQuotientEquiv`、`SerrePositivity.AlgebraicGeometry.ArcRouteB.intervalTensorIntersectionEquiv`

:::

:::definition "bm18_eq_7" (uses := "bm18_4_8")
*式 (7)*　片側の区間を縮める比較正方形。対応表の状態：なし。

原典 PDF p.29, y=235.7。arc-cover・valuation interval・excision・Čech・toposの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::lemma_ "bm18_4_9" (uses := "bm18_4_7")
*補題 4.9*　離散性の区間による判定。対応表の状態：なし。

原典 PDF p.29, y=443.4。arc-cover・valuation interval・excision・Čech・toposの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::lemma_ "bm18_4_10" (uses := "bm18_3_19")
*補題 4.10*　階数一テストによる切断性の判定。対応表の状態：なし。

原典 PDF p.30, y=176.6。arc-cover・valuation interval・excision・Čech・toposの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::corollary "bm18_4_11" (uses := "bm18_3_32, bm18_4_10")
*系 4.11*　階数一テストによる arc 層の同値判定。対応表の状態：なし。

原典 PDF p.30, y=371.4。arc-cover・valuation interval・excision・Čech・toposの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::corollary "bm18_4_12" (uses := "bm18_4_1, bm18_4_10, bm18_4_11")
*系 4.12*　階数一の完備付値環による判定。対応表の状態：なし。

原典 PDF p.30, y=549.9。arc-cover・valuation interval・excision・Čech・toposの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：AHW

:::

:::lemma_ "bm18_4_13" (uses := "bm18_eq_8, bm18_2_7")
*補題 4.13*　整域への Milnor 正方形の底変換。対応表の状態：なし。

原典 PDF p.31, y=326.8。arc-cover・valuation interval・excision・Čech・toposの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::definition "bm18_eq_8" (uses := "bm18_4_13")
*式 (8)*　付値基底へ移す Milnor 正方形。対応表の状態：なし。

原典 PDF p.31, y=344.9。arc-cover・valuation interval・excision・Čech・toposの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::lemma_ "bm18_4_14" (uses := "bm18_eq_8, bm18_4_1, bm18_4_13")
*補題 4.14*　全射の Milnor 正方形と v 層。対応表の状態：なし。

原典 PDF p.31, y=561.6。arc-cover・valuation interval・excision・Čech・toposの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "bm18_4_15" (uses := "bm18_eq_8, bm18_eq_9, bm18_2_7, bm18_4_11, bm18_4_13, bm18_4_14")
*命題 4.15*　arc 層の excision。対応表の状態：なし。

原典 PDF p.32, y=180.6。arc-cover・valuation interval・excision・Čech・toposの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::definition "bm18_eq_9" (uses := "bm18_4_15")
*式 (9)*　切断をもつ補助 Milnor 正方形。対応表の状態：なし。

原典 PDF p.32, y=311.9。arc-cover・valuation interval・excision・Čech・toposの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::definition "bm18_4_16"
*定義 4.16*　濃度を制限した arc トポス。対応表の状態：なし。

原典 PDF p.32, y=479.1。arc-cover・valuation interval・excision・Čech・toposの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "bm18_4_17" (uses := "bm18_1_2, bm18_3_30, bm18_4_16")
*注意 4.17*　被覆に対する濃度上限の独立性。対応表の状態：なし。

原典 PDF p.32, y=604.8。arc-cover・valuation interval・excision・Čech・toposの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "bm18_4_18" (uses := "bm18_4_17")
*注意 4.18*　arc トポスの濃度上限への依存。対応表の状態：なし。

原典 PDF p.33, y=199.5。arc-cover・valuation interval・excision・Čech・toposの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：SAG、SGA4、Waterhouse

:::

:::lemma_ "bm18_4_19"
*補題 4.19*　arc トポスの coherent 性。対応表の状態：なし。

原典 PDF p.33, y=343.8。arc-cover・valuation interval・excision・Čech・toposの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：SAG、SGA4

:::

:::proposition "bm18_4_20" (uses := "bm18_4_19")
*Warning 4.20*　arc 位相の非 subcanonical 性。対応表の状態：なし。

原典 PDF p.33, y=459.5。arc-cover・valuation interval・excision・Čech・toposの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::lemma_ "bm18_4_21"
*補題 4.21*　coherent arc 層の全射の付値判定。対応表の状態：なし。

原典 PDF p.33, y=508.2。arc-cover・valuation interval・excision・Čech・toposの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::lemma_ "bm18_4_22" (uses := "bm18_4_21")
*補題 4.22*　層化の同型の付値判定。対応表の状態：なし。

原典 PDF p.34, y=279.5。arc-cover・valuation interval・excision・Čech・toposの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::lemma_ "bm18_4_23" (uses := "bm18_4_19")
*補題 4.23*　arc 層の押し出しの coherent 性。対応表の状態：なし。

原典 PDF p.34, y=553.5。arc-cover・valuation interval・excision・Čech・toposの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "bm18_4_24" (uses := "bm18_eq_8, bm18_2_7, bm18_4_22, bm18_4_23")
*命題 4.24*　Milnor 正方形の arc 層化。対応表の状態：なし。

原典 PDF p.35, y=323.6。arc-cover・valuation interval・excision・Čech・toposの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::corollary "bm18_4_25" (uses := "bm18_4_24, bm18_5_4")
*系 4.25*　任意の完備な値の圏における excision。対応表の状態：なし。

原典 PDF p.36, y=96.3。arc-cover・valuation interval・excision・Čech・toposの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：CD、SGA4、Stacks 03Q4

:::

