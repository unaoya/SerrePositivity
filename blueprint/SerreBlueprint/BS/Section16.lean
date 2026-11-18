import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "§16 " =>
%%%
number := false
tag := "bs-16"
%%%

BS §16 の項目と、本体の宣言との対応。本文は対応表（`research/bs-coverage`）の照合の理由で、原典の本文の写しではない。

:::definition "bs_16_1"
*記法 16.1*　。対応表の状態：なし。

原文を再読し、現本体とロックMathlibを節の対象語で再検索したが、同じ対象・指定射の主張を直接与える宣言は未同定。A = Z\_p\[\[q−1\]\] と \[p\]\_q の記法。未形式化

:::

:::definition "bs_16_2"
*定義 16.2*　q-divided power algebras。対応表の状態：なし。

原文を再読し、現本体とロックMathlibを節の対象語で再検索したが、同じ対象・指定射の主張を直接与える宣言は未同定。q-PD 対の定義。未形式化（q-PD の語は Lean・設計書にない）

:::

:::proposition "bs_16_3"
*注意 16.3*　Characterizing δ-PD pairs。対応表の状態：なし。

原文を再読し、現本体とロックMathlibを節の対象語で再検索したが、同じ対象・指定射の主張を直接与える宣言は未同定。δ-PD 対の特徴づけ（q=1）。近いものに Lemma 2.38 の r=1（Delta/DividedPower/PrincipalDP）があるが、δ-PD 対の一般論はない

:::

:::proposition "bs_16_4"
*注意 16.4*　Relating q-PD pairs to δ-PD pairs。対応表の状態：なし。

原文を再読し、現本体とロックMathlibを節の対象語で再検索したが、同じ対象・指定射の主張を直接与える宣言は未同定。q-PD 対から δ-PD 対へ。未形式化

:::

:::lemma_ "bs_16_5"
*補題 16.5*　Homological properties of q-PD pairs。対応表の状態：なし。

原文を再読し、現本体とロックMathlibを節の対象語で再検索したが、同じ対象・指定射の主張を直接与える宣言は未同定。q-PD 対の完備性・平坦性。未形式化

:::

:::proposition "bs_16_6"
*注意 16.6*　Additivity and multiplicative properties of γ。対応表の状態：なし。

原文を再読し、現本体とロックMathlibを節の対象語で再検索したが、同じ対象・指定射の主張を直接与える宣言は未同定。γ の加法性・乗法性。未形式化

:::

:::lemma_ "bs_16_7"
*補題 16.7*　Existence of higher q-divided powers。対応表の状態：なし。

原文を再読し、現本体とロックMathlibを節の対象語で再検索したが、同じ対象・指定射の主張を直接与える宣言は未同定。高次 q 分冪の存在。未形式化

:::

:::corollary "bs_16_8"
*系 16.8*　Smallest and largest q-PD ideals。対応表の状態：なし。

原文を再読し、現本体とロックMathlibを節の対象語で再検索したが、同じ対象・指定射の主張を直接与える宣言は未同定。最小・最大の q-PD イデアル。未形式化

:::

:::theorem "bs_16_9"
*定理 16.9*　。対応表の状態：なし。

原文を再読し、現本体とロックMathlibを節の対象語で再検索したが、同じ対象・指定射の主張を直接与える宣言は未同定。入力の誤抽出：本文は §7 の引用「\[GR, Theorem 16.9.17\]」の直後にある Thm 7.4 の証明（B4、Surjectivity.lean:506 で sorry なしに証明済み、A5・A8 が使う）。原典の 16.9 は Example 16.9（q-PD 対の例）で、未形式化・E3 に不要。判定は Example 16.9 に対するもの

:::

:::lemma_ "bs_16_10"
*補題 16.10*　Existence of q-PD envelopes。対応表の状態：なし。

原文を再読し、現本体とロックMathlibを節の対象語で再検索したが、同じ対象・指定射の主張を直接与える宣言は未同定。q-PD 包の存在。未形式化

:::

:::lemma_ "bs_16_11"
*補題 16.11*　。対応表の状態：なし。

原文を再読し、現本体とロックMathlibを節の対象語で再検索したが、同じ対象・指定射の主張を直接与える宣言は未同定。pd 包と q-PD 包の比較。未形式化

:::

:::definition "bs_16_12"
*定義 16.12*　The q-crystalline site and its cohomology。対応表の状態：なし。

原文を再読し、現本体とロックMathlibを節の対象語で再検索したが、同じ対象・指定射の主張を直接与える宣言は未同定。q-crystalline site の定義。未形式化

:::

:::definition "bs_16_13"
*構成 16.13*　Computing q-crystalline cohomology via Čech-Alexander complexes。対応表の状態：なし。

原文を再読し、現本体とロックMathlibを節の対象語で再検索したが、同じ対象・指定射の主張を直接与える宣言は未同定。Čech–Alexander による q-crystalline cohomology の計算。未形式化

:::

:::theorem "bs_16_14"
*定理 16.14*　q-crystalline and crystalline cohomology。対応表の状態：なし。

原文を再読し、現本体とロックMathlibを節の対象語で再検索したが、同じ対象・指定射の主張を直接与える宣言は未同定。qΩ ⊗ D/(q−1) ≃ 結晶コホモロジー。未形式化

:::

:::proposition "bs_16_15"
*注意 16.15*　Globalization。対応表の状態：なし。

原文を再読し、現本体とロックMathlibを節の対象語で再検索したが、同じ対象・指定射の主張を直接与える宣言は未同定。大域化。未形式化

:::

:::proposition "bs_16_16"
*注意 16.16*　Computing q-crystalline cohomology via “small” Čech-Alexander complexes。対応表の状態：なし。

原文を再読し、現本体とロックMathlibを節の対象語で再検索したが、同じ対象・指定射の主張を直接与える宣言は未同定。小さい模型による計算。未形式化

:::

:::theorem "bs_16_17"
*定理 16.17*　Invariance under q-PD thickenings of the base。対応表の状態：なし。

原文を再読し、現本体とロックMathlibを節の対象語で再検索したが、同じ対象・指定射の主張を直接与える宣言は未同定。q-PD 厚化の不変性。未形式化

:::

:::theorem "bs_16_18"
*定理 16.18*　q-crystalline and prismatic cohomology。対応表の状態：なし。

原文を再読し、現本体とロックMathlibを節の対象語で再検索したが、同じ対象・指定射の主張を直接与える宣言は未同定。q-crystalline と prismatic の比較。未形式化

:::

:::definition "bs_16_19"
*構成 16.19*　The q-de Rham complex of a framed D-algebra。対応表の状態：なし。

原文を再読し、現本体とロックMathlibを節の対象語で再検索したが、同じ対象・指定射の主張を直接与える宣言は未同定。枠付き代数の q-de Rham 複体。未形式化

:::

:::definition "bs_16_20"
*構成 16.20*　The q-de Rham complex of a framed q-PD pair。対応表の状態：なし。

原文を再読し、現本体とロックMathlibを節の対象語で再検索したが、同じ対象・指定射の主張を直接与える宣言は未同定。枠付き q-PD データの q-de Rham 複体。未形式化

:::

:::lemma_ "bs_16_21"
*補題 16.21*　。対応表の状態：なし。

原文を再読し、現本体とロックMathlibを節の対象語で再検索したが、同じ対象・指定射の主張を直接与える宣言は未同定。γ\_s の q-PD 包への延長。未形式化

:::

:::theorem "bs_16_22"
*定理 16.22*　q-de Rham and q-crystalline comparison。対応表の状態：なし。

原文を再読し、現本体とロックMathlibを節の対象語で再検索したが、同じ対象・指定射の主張を直接与える宣言は未同定。q-de Rham と q-crystalline の比較。未形式化

:::

