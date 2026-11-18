import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "§2 Subtrusive morphisms" =>
%%%
number := false
tag := "rydh-2"
%%%

Rydh §2 の項目と、本体の宣言との対応。本文は対応表（`research/rydh-coverage`）の照合の理由で、原典の本文の写しではない。

:::proposition "rydh_2_1" (uses := "rydh_1_4")
*命題 2.1*　特殊化の持ち上げと同値な条件。対応表の状態：一部（component）。

原典 PDF p.7, y=480.6。付値持ち上げ条件のもとで (i) の点対の持ち上げと閉制限に対する閉包の包含を与える。(i)–(iv) の一般の同値は扱わない。

宣言：`SerrePositivity.AlgebraicGeometry.IsSchemeVCover.liftsSpecializations`、`SerrePositivity.AlgebraicGeometry.closure_subset_range_comp_of_vCover_closedRestriction`

:::

:::definition "rydh_2_2" (uses := "rydh_2_1")
*定義 2.2*　S-subtrusive と subtrusive。対応表の状態：一部（component）。

原典 PDF p.7, y=686.8。付値持ち上げの仮定から S-subtrusive の点対条件を与える。構成可能位相での商写像というもう一方の条件はこの型にない。

宣言：`SerrePositivity.AlgebraicGeometry.IsSchemeVCover.liftsSpecializations`

:::

:::proposition "rydh_2_3" (uses := "rydh_1_5, rydh_2_2")
*注意 2.3*　spectral 空間と subtrusive 性。対応表の状態：なし。

原典 PDF p.8, y=119.0。subtrusive・submersive・specialization・valuationの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：hochster\_prime\_ideal\_structure、picavet\_submersion

:::

:::proposition "rydh_2_4" (uses := "rydh_1_2, rydh_2_1")
*命題 2.4*　被約化と開被覆による判定。対応表の状態：なし。

原典 PDF p.8, y=337.5。subtrusive・submersive・specialization・valuationの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "rydh_2_5" (uses := "rydh_1_6")
*注意 2.5*　普遍 subtrusive 射の例。対応表の状態：一部（component）。

原典 PDF p.8, y=511.4。固有全射および平坦全射から付値による普遍 subtrusive の判定条件を得る。他の十分条件と反例は含まない。

宣言：`SerrePositivity.AlgebraicGeometry.isSchemeVCover_of_proper_surjective`、`SerrePositivity.AlgebraicGeometry.isSchemeVCover_of_flat_surjective`

外の文献：egaIV

:::

:::proposition "rydh_2_6"
*注意 2.6*　付値環での主イデアル性と平坦性。対応表の状態：Mathlib にある。

原典 PDF p.9, y=119.0。付値環には IsBezout のインスタンスがあり、有限生成イデアルは単項となる。平坦性は torsion 部分加群が零であることと同値で、整域への代数構造では構造射の単射性と同値になる。

宣言：`IsBezout`、`Module.Flat.flat_iff_torsion_eq_bot_of_isBezout`、`Module.isTorsionFree_iff_algebraMap_injective`

外の文献：bourbaki\_alg\_comm\_5\_6

:::

:::proposition "rydh_2_7" (uses := "rydh_2_1, rydh_2_4, rydh_2_5, rydh_2_6, rydh_2_8, rydh_6_1, rydh_6_3")
*命題 2.7*　付値基底上の普遍 subtrusive 性。対応表の状態：なし。

原典 PDF p.9, y=179.2。subtrusive・submersive・specialization・valuationの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：RG71、picavet\_submersion

:::

:::theorem "rydh_2_8" (uses := "rydh_2_7, rydh_6_3")
*定理 2.8*　付値による普遍 subtrusive 性と submersive 性。対応表の状態：なし。

原典 PDF p.9, y=642.9。subtrusive・submersive・specialization・valuationの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：bourbaki\_alg\_comm\_5\_6、egaII、picavet\_submersion

:::

:::corollary "rydh_2_9" (uses := "rydh_2_7, rydh_2_8")
*系 2.9*　普遍 subtrusive 性の付値環拡大による判定。対応表の状態：なし。

原典 PDF p.10, y=497.6。IsSchemeVCover が (ii) の忠実平坦な付値環拡大を定義する。構成可能位相における商写像を含む (i) と (ii) の同値は見出していない。

:::

:::corollary "rydh_2_10" (uses := "rydh_1_6, rydh_2_7, rydh_2_8")
*系 2.10*　局所 Noether 基底の同値な判定。対応表の状態：なし。

原典 PDF p.10, y=682.9。subtrusive・submersive・specialization・valuationの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：kang-oh\_lifting-chains、kollar\_quotients、sga1

:::

:::proposition "rydh_2_11" (uses := "rydh_2_7")
*命題 2.11*　特殊化の鎖の持ち上げ。対応表の状態：なし。

原典 PDF p.11, y=445.8。subtrusive・submersive・specialization・valuationの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：kang-oh\_lifting-chains、picavet\_GGD、voevodsky\_homology

:::

