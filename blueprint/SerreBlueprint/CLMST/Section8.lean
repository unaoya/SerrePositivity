import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "§8 Further directions and questions" =>
%%%
number := false
tag := "clmst-8"
%%%

CLMST §8 の項目と、本体の宣言との対応。本文は対応表（`research/clmst-coverage`）の照合の理由で、原典の本文の写しではない。

:::proposition "clmst_8_1" (uses := "clmst_4_0_18, clmst_6_3_2")
*予想 8.1*　Noether–Cohen 正規化とパラメータ選択の独立性予想。対応表の状態：なし。

原典 PDF p.80; layout L4512。原典で未解決の予想「Noether–Cohen 正規化とパラメータ選択の独立性予想」。該当する予想の型・仮定付き入力・証明宣言を確認できない。特殊な既知例を一般の予想の証明とは数えない。

外の文献：GR22 Remark 14.5.69(ii)

:::

:::proposition "clmst_8_2"
*予想 8.2*　局所化に対する perfectoid 不変量の不等式予想。対応表の状態：なし。

原典 PDF p.81; layout L4548。原典で未解決の予想「局所化に対する perfectoid 不変量の不等式予想」。該当する予想の型・仮定付き入力・証明宣言を確認できない。特殊な既知例を一般の予想の証明とは数えない。

:::

:::proposition "clmst_8_3"
*予想 8.3*　忠実平坦局所拡大に対する不等式予想。対応表の状態：なし。

原典 PDF p.81; layout L4555。原典で未解決の予想「忠実平坦局所拡大に対する不等式予想」。該当する予想の型・仮定付き入力・証明宣言を確認できない。特殊な既知例を一般の予想の証明とは数えない。

:::

:::proposition "clmst_8_4"
*予想 8.4*　perfectoid 不変量の半連続性予想。対応表の状態：なし。

原典 PDF p.81; layout L4560。原典で未解決の予想「perfectoid 不変量の半連続性予想」。該当する予想の型・仮定付き入力・証明宣言を確認できない。特殊な既知例を一般の予想の証明とは数えない。

外の文献：DSPY19、Han03、LLX20、Lyu25、PT18、Pol18、Smi16

:::

:::definition "clmst_8_5" (uses := "clmst_6_2_2")
*定義 8.5*　有効 Q Cartier 因子対の perfectoid signature。対応表の状態：なし。

原典 PDF p.82; layout L4579。原典の「有効 Q Cartier 因子対の perfectoid signature」に対応する定義または主張を持つ宣言を確認できない。

外の文献：BST12、MS18、Mur21、Rob22、ST25

:::

