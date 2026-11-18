import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.AlgebraicGeometry.ProperInductiveLevel
import SerrePositivity.AlgebraicGeometry.ProperInductiveLevelBaseChange

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "§2 h-Sheaves" =>
%%%
number := false
tag := "bs17-2"
%%%

BS17 §2 の項目と、本体の宣言との対応。本文は対応表（`research/bs17-coverage`）の照合の理由で、原典の本文の写しではない。

:::definition "bs17_2_1"
*定義 2.1*　v 被覆と細分。対応表の状態：一部（component）。

原典 PDF p.4, y=521.1。忠実平坦な付値環拡大による持ち上げの定義を持つ。項目中の細分の定義と、普遍 subtrusive・submersive との比較はこの宣言の結論に含まれない。

宣言：`SerrePositivity.AlgebraicGeometry.IsSchemeVCover`

外の文献：Rydh 2.2、Rydh 2.8、Rydh 2.9

:::

:::proposition "bs17_2_2"
*注意 2.2*　the · name · v-cover · besides · similarity。対応表の状態：なし。

原典 PDF p.4, y=687.5。v-cover・subtrusive・refinement・proper・fppf・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：HuberGeneralization

:::

:::proposition "bs17_2_3"
*例 2.3*　v 被覆の例。対応表の状態：一部（component）。

原典 PDF p.5, y=136.6。平坦全射・固有全射・開被覆の各場合を与える。他の例や反例をまとめて示す型はない。

宣言：`SerrePositivity.AlgebraicGeometry.isSchemeVCover_of_flat_surjective`、`SerrePositivity.AlgebraicGeometry.isSchemeVCover_of_proper_surjective`、`SerrePositivity.AlgebraicGeometry.isSchemeVCover_sigmaDesc_openCover`

外の文献：Rydh 2.5

:::

:::theorem "bs17_2_4"
*定理 2.4*　有限表示 v 被覆の開被覆–固有細分。対応表の状態：なし。

原典 PDF p.5, y=335.5。細分における原典の準コンパクト開被覆と、その後の固有全射の同時分解を確認できない。AffineBaseVCoverRefinement の第一因子は fppf で、AffineOpenVCoverRefinement の結論はアフィンな v 被覆への細分。

外の文献：RG71、Rydh 3.12

:::

:::definition "bs17_2_5" (lean := "SerrePositivity.AlgebraicGeometry.ProperInductiveLevel, SerrePositivity.AlgebraicGeometry.ProperInductiveLevel.baseChange")
*定義 2.5*　固有全射の帰納的レベル。対応表の状態：本体にある。

原典 PDF p.5, y=423.6。レベル零の proper fppf 細分と有限表示 nilimmersion、後続段の中心・中心外同型・再帰・proper fppf 細分を表し、底変換で保存する。nilimmersion は有限表示な全射閉埋め込みで表す。

:::

:::lemma_ "bs17_2_6"
*補題 2.6*　有限の帰納的レベルの存在。対応表の状態：一部（special）。

原典 PDF p.5, y=565.8。有限表示固有全射が有限の帰納的レベルを持つ。基底がアフィン、または Noether の場合を与え、一般の qcqs 基底を一括する型はない。

宣言：`SerrePositivity.AlgebraicGeometry.exists_properInductiveLevel_affineBase`、`SerrePositivity.AlgebraicGeometry.exists_properInductiveLevel_noetherian`

外の文献：RG71、Rydh、Stacks 0815、TT

:::

:::definition "bs17_2_7"
*定義 2.7*　h 位相。対応表の状態：なし。

原典 PDF p.6, y=100.2。v-cover・subtrusive・refinement・proper・fppf・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "bs17_2_8" (uses := "bs17_2_4, bs17_2_6")
*命題 2.8*　presheaf · sets · h-sheaf · and · only。対応表の状態：なし。

原典 PDF p.6, y=169.2。v-cover・subtrusive・refinement・proper・fppf・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：HTT

:::

:::theorem "bs17_2_9"
*定理 2.9*　空間値 h 降下の判定。対応表の状態：なし。

原典 PDF p.7, y=148.9。v-cover・subtrusive・refinement・proper・fppf・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：Stacks 023M、VoevodskyCDStructures

:::

:::lemma_ "bs17_2_10" (uses := "bs17_2_4")
*補題 2.10*　合成と普遍降下。対応表の状態：一部（special）。

原典 PDF p.7, y=615.0。合成での普遍降下から後段へ移す (a) の構造層 Čech 版。元の射に分離・準コンパクト・局所有限表示、合成にアフィン性と局所有限表示を課す。一般の F と (b) の一般形を含まない。

宣言：`SerrePositivity.AlgebraicGeometry.perfectCechUniversalDescent_of_affine_refinement`

外の文献：LiuZhengSixOp

:::

:::corollary "bs17_2_11"
*系 2.11*　sheaf · abelian · groups · assume · for。対応表の状態：なし。

原典 PDF p.8, y=528.7。v-cover・subtrusive・refinement・proper・fppf・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::lemma_ "bs17_2_12" (uses := "bs17_2_4")
*補題 2.12*　アフィン v 被覆の有限表示模型。対応表の状態：一部（special）。

原典 PDF p.9, y=74.4。環の射圏で与えた filtered 余極限の各段が有限表示な affine v-cover。双対の逆極限表示に相当し、基底は素体で、任意の qcqs の S は扱わない。

宣言：`SerrePositivity.AlgebraicGeometry.exists_primeField_vCover_filtered_model`

:::

:::definition "bs17_2_13" (uses := "bs17_2_9")
*定義 2.13*　for · qcqs · base · the · v-topology。対応表の状態：なし。

原典 PDF p.9, y=215.5。v-cover・subtrusive・refinement・proper・fppf・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::corollary "bs17_2_14" (uses := "bs17_2_11, bs17_2_12, bs17_2_9")
*系 2.14*　presheaf · n-truncated · spaces · for · assume。対応表の状態：なし。

原典 PDF p.9, y=264.1。v-cover・subtrusive・refinement・proper・fppf・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：LurieDAGVIII

:::

:::corollary "bs17_2_15" (uses := "bs17_3_18")
*系 2.15*　sheaf · abelian · groups · assume · for。対応表の状態：なし。

原典 PDF p.10, y=107.8。v-cover・subtrusive・refinement・proper・fppf・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

