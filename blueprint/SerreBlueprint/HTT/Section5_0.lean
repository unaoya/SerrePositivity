-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Yoneda

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HTT 5.0 Presentable and Accessible ∞-Categories（章の導入）" =>
%%%
number := false
tag := "htt-5-0"
%%%

HTT 5.0 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/htt-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

:::proposition "htt_5_0_0_1" (lean := "CategoryTheory.yoneda_preservesLimits, CategoryTheory.Functor.RepresentableBy.toIso, CategoryTheory.Limits.preservesLimits_of_natIso")
*HTT 命題 5.0.0.1*　アーベル群上の連続前層の表現可能性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=332)）。対応表の状態：一部（direction）。

*主張*　アーベル群の圏から集合への反変関手が表現可能であることは、アーベル群の余極限を集合の極限へ送ることと同値である。

KB-W2原文・型再照合：仮定：アーベル群上の集合値前層が表現可能（HTT の必要方向と一致。Lean は同じ宇宙の任意の圏を許す）。結論：表現同型と Hom 関手の極限保存により、元の前層は反対圏の極限、すなわち元の余極限を極限へ送る（一致する方向。十分方向は含まない）。

必要性は表現する Hom の普遍性から分かる。逆向きには、アーベル群の大きい圏を小さい生成対象の情報から扱えることが効く。ここから可提示圏における表現可能性の問題へ進む。

:::

