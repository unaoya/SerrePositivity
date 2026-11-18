import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "§4 h-Descent for vector bundles on perfect schemes" =>
%%%
number := false
tag := "bs17-4"
%%%

BS17 §4 の項目と、本体の宣言との対応。本文は対応表（`research/bs17-coverage`）の照合の理由で、原典の本文の写しではない。

:::theorem "bs17_4_1"
*定理 4.1*　Witt ベクトル束の v コホモロジーと v-stack。対応表の状態：一部（special）。

原典 PDF p.15, y=314.7。4.1(i) の n=1、E=O、完全なアフィン環の有限 v 被覆族に対する増大 Čech 完全性。W\_n（n\>1）・W・任意の有限射影係数、サイト上の RΓ\_v との比較および (ii) の v-stack は型に含まれない。

宣言：`SerrePositivity.AlgebraicGeometry.cech_exact_of_vCover_perfect`、`SerrePositivity.AlgebraicGeometry.perfectAffineVCover_cechExact`

外の文献：Stacks 01XD

:::

:::proposition "bs17_4_2" (uses := "bs17_6_3")
*注意 4.2*　this · the · v-topology · perf · subcanonical。対応表の状態：なし。

原典 PDF p.15, y=403.3。Čech・v-cover・Witt・vector bundle・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "bs17_4_3" (uses := "bs17_4_1")
*注意 4.3*　warn · the · reader · does · not。対応表の状態：なし。

原典 PDF p.15, y=462.1。Čech・v-cover・Witt・vector bundle・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：BST13

:::

:::corollary "bs17_4_4" (uses := "bs17_2_14, bs17_4_1")
*系 4.4*　fix · perfect · qcqs · and · vect。対応表の状態：なし。

原典 PDF p.15, y=606.7。Čech・v-cover・Witt・vector bundle・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::proposition "bs17_4_5"
*命題 4.5*　presheaf · spaces · perf · the · defined。対応表の状態：なし。

原典 PDF p.15, y=686.8。Čech・v-cover・Witt・vector bundle・descentの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

:::

:::lemma_ "bs17_4_6" (uses := "bs17_2_11, bs17_2_14, bs17_3_4, bs17_4_1, bs17_4_5")
*補題 4.6*　完全化した固有変更の fppf コホモロジー。対応表の状態：なし。

原典 PDF p.16, y=327.3。射影模型の完全構造層の Čech 正方形はあるが、原典の RΓ\_fppf の三角との比較および任意のベクトル束係数は型にない。

外の文献：BST13、RG71

:::

