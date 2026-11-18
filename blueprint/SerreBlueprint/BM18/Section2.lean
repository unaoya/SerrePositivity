import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.CommutativeAlgebra.ValuationExtension.Aic

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "§2 The arc-topology" =>
%%%
number := false
tag := "bm18-2"
%%%

BM18 §2 の項目と、本体の宣言との対応。本文は対応表（`research/bm18-coverage`）の照合の理由で、原典の本文の写しではない。

:::proposition "bm18_2_1" (uses := "bm18_eq_1, bm18_1_1")
*命題 2.1*　v 被覆から arc 被覆。対応表の状態：なし。

原典 PDF p.9, y=213.0。arc-cover・valuation・submersion・constructible・Milnorの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "bm18_2_2"
*注意 2.2*　階数一に切り詰める素理想の記述。対応表の状態：なし。

原典 PDF p.9, y=374.1。arc-cover・valuation・submersion・constructible・Milnorの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：Kaplansky

:::

:::lemma_ "bm18_2_3"
*補題 2.3*　合成の arc 被覆性からの反映。対応表の状態：一部（special）。

原典 PDF p.9, y=551.8。合成が arc 被覆なら後段も arc 被覆になる。環の射で記述したアフィンの場合。

宣言：`SerrePositivity.AlgebraicGeometry.ArcRouteB.isArcHom_of_refinement`

:::

:::lemma_ "bm18_2_4" (uses := "bm18_2_1")
*補題 2.4*　階数一の付値基底における被覆の同値。対応表の状態：なし。

原典 PDF p.9, y=602.1。arc-cover・valuation・submersion・constructible・Milnorの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：Rydh 2.7

:::

:::corollary "bm18_2_5"
*系 2.5*　階数一の付値基底による arc 被覆の判定。対応表の状態：なし。

原典 PDF p.10, y=178.7。arc-cover・valuation・submersion・constructible・Milnorの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：Rydh

:::

:::proposition "bm18_2_6"
*命題 2.6*　Noether 基底での v 被覆と arc 被覆。対応表の状態：なし。

原典 PDF p.10, y=260.0。arc-cover・valuation・submersion・constructible・Milnorの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：Rydh 2.8

:::

:::lemma_ "bm18_2_7" (uses := "bm18_1_11")
*補題 2.7*　excision datum からの arc 被覆。対応表の状態：なし。

原典 PDF p.10, y=329.2。arc-cover・valuation・submersion・constructible・Milnorの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "bm18_2_8"
*命題 2.8*　付値環の excision datum。対応表の状態：一部（component）。

原典 PDF p.10, y=516.4。q が極大の場合の V、V\_p、V/p、κ(p) の加法群の短完全列から、局所化が素イデアル p を像のイデアルに同型に移すことが従う。一般の q での述語として excision datum を返す型は見出していない。

宣言：`SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationRing_milnorSquare`

:::

:::corollary "bm18_2_9"
*系 2.9*　局所化と素商の arc 被覆。対応表の状態：なし。

原典 PDF p.10, y=628.7。arc-cover・valuation・submersion・constructible・Milnorの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "bm18_2_10" (uses := "bm18_2_19, bm18_2_9")
*注意 2.10*　付値環の arc 被覆の別証明。対応表の状態：なし。

原典 PDF p.11, y=125.9。arc-cover・valuation・submersion・constructible・Milnorの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：GooLi、Pic、Rydh 4.3

:::

:::proposition "bm18_2_11"
*命題 2.11*　アフィンの arc 被覆の環論的判定。対応表の状態：なし。

原典 PDF p.11, y=173.3。arc-cover・valuation・submersion・constructible・Milnorの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：Pic、Rydh、Stacks 058I

:::

:::definition "bm18_2_12"
*定義 2.12*　submersion の定義。対応表の状態：Mathlib にある。

原典 PDF p.11, y=431.9。スキームの台位相写像に IsQuotientMap を課し、普遍版はすべての引き戻しで同じ性質を課す。原典の qcqs の範囲に制限して一致する。

宣言：`Topology.IsQuotientMap`、`AlgebraicGeometry.topologically`、`CategoryTheory.MorphismProperty.universally`

:::

:::proposition "bm18_2_13" (uses := "bm18_2_18")
*命題 2.13*　v 被覆の普遍 submersive 性。対応表の状態：なし。

原典 PDF p.11, y=485.6。arc-cover・valuation・submersion・constructible・Milnorの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：Pic、Stacks 00IA、Stacks 0903

:::

:::definition "bm18_2_14"
*定義 2.14*　spectral submersion の定義。対応表の状態：なし。

原典 PDF p.12, y=126.8。arc-cover・valuation・submersion・constructible・Milnorの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "bm18_2_15" (uses := "bm18_2_14")
*注意 2.15*　spectral submersion の簡略条件。対応表の状態：なし。

原典 PDF p.12, y=222.2。arc-cover・valuation・submersion・constructible・Milnorの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "bm18_2_16" (uses := "bm18_2_15, bm18_2_18")
*注意 2.16*　普遍 spectral submersion の局所判定。対応表の状態：なし。

原典 PDF p.12, y=341.4。arc-cover・valuation・submersion・constructible・Milnorの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::lemma_ "bm18_2_17" (uses := "bm18_2_15")
*補題 2.17*　逆極限での spectral submersion。対応表の状態：なし。

原典 PDF p.12, y=511.5。arc-cover・valuation・submersion・constructible・Milnorの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "bm18_2_18" (uses := "bm18_2_17, bm18_2_19, bm18_2_22, bm18_3_13, bm18_3_16, bm18_3_27")
*注意 2.18*　商写像と普遍 spectral submersion の差。対応表の状態：なし。

原典 PDF p.13, y=268.1。arc-cover・valuation・submersion・constructible・Milnorの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：RydhII、SarussiToset

:::

:::proposition "bm18_2_19" (uses := "bm18_2_17")
*命題 2.19*　arc 被覆と普遍 spectral submersion の同値。対応表の状態：なし。

原典 PDF p.14, y=156.4。arc-cover・valuation・submersion・constructible・Milnorの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::corollary "bm18_2_20" (uses := "bm18_2_19, bm18_3_26")
*系 2.20*　逆極限での arc 被覆。対応表の状態：なし。

原典 PDF p.14, y=204.5。arc-cover・valuation・submersion・constructible・Milnorの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::lemma_ "bm18_2_21" (lean := "SerrePositivity.valuationSubringComapHom_faithfullyFlat")
*補題 2.21*　部分体に引き戻した付値環。対応表の状態：本体にある。

原典 PDF p.14, y=288.5。分数体への部分体の包含を体の単射として扱い、付値部分環の逆像から元の付値環への射の忠実平坦性を与える。逆像は ValuationSubring として型付けされる。

:::

:::lemma_ "bm18_2_22" (uses := "bm18_2_1, bm18_2_15, bm18_2_17, bm18_2_19, bm18_2_21, bm18_2_4")
*補題 2.22*　付値環の有限階数近似。対応表の状態：なし。

原典 PDF p.14, y=384.6。arc-cover・valuation・submersion・constructible・Milnorの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：BourbakiCA、Stacks 0903

:::

