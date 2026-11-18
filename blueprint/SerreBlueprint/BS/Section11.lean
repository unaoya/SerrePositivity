import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "§11 " =>
%%%
number := false
tag := "bs-11"
%%%

BS §11 の項目と、本体の宣言との対応。本文は対応表（`research/bs-coverage`）の照合の理由で、原典の本文の写しではない。

:::theorem "bs_11_1"
*定理 11.1*　The étale cohomological dimension of algebraic étale sheaves。対応表の状態：なし。

原文を再読し、現本体とロックMathlibを節の対象語で再検索したが、同じ対象・指定射の主張を直接与える宣言は未同定。Spec R\[1/p\] の F\_p エタールコホモロジー次元 ≤ 1。本体・drafts・Mathlib に該当なし（HilbertSamuel の Thm 11.1 は Atiyah–Macdonald で無関係）

:::

