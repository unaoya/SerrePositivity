-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "§17 Comparison with AΩ" =>
%%%
number := false
tag := "bs-17"
%%%

BS §17 の項目と、本体の宣言との対応。本文は対応表（`research/bs-coverage`）の照合の理由で、原典の本文の写しではない。

:::definition "bs_17_1"
*記法 17.1*　。対応表の状態：なし。

原文を再読し、現本体とロックMathlibを節の対象語で再検索したが、同じ対象・指定射の主張を直接与える宣言は未同定。A\_inf(O\_C) と q = \[ε\] の記法。A\_inf(R) 自体は E3 で完全 prism として使う（A3・A4）が §17 の設定とは別

:::

:::theorem "bs_17_2"
*定理 17.2*　。対応表の状態：なし。

原文を再読し、現本体とロックMathlibを節の対象語で再検索したが、同じ対象・指定射の主張を直接与える宣言は未同定。AΩ ≃ qΩ ≃ φ\^\*Δ。未形式化

:::

:::proposition "bs_17_3"
*注意 17.3*　。対応表の状態：なし。

原文を再読し、現本体とロックMathlibを節の対象語で再検索したが、同じ対象・指定射の主張を直接与える宣言は未同定。E1 から E∞ への格上げの注意。未形式化

:::

:::lemma_ "bs_17_4"
*補題 17.4*　。対応表の状態：なし。

原文を再読し、現本体とロックMathlibを節の対象語で再検索したが、同じ対象・指定射の主張を直接与える宣言は未同定。導来 d 完備な可換代数の比較補題。未形式化

:::

