-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Monoidal.Mod
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.BaseChange
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA 4.2 Left and Right Modules" =>
%%%
number := false
tag := "ha-4-2"
%%%

HA 4.2 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 4.2.1 The ∞-Operad LM\^

%%%
number := false
tag := "ha-4-2-1"
%%%

:::proposition "ha_4_2_1_3" (lean := "CategoryTheory.ModObj")
*HA 注意 4.2.1.3*　The ∞-Operad \$\\mathrm\{LM\}\^\{\\otimes\}\$ (p. 505)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=505)）。対応表の状態：一部（component）。

*主張*　対称モノイダル圏では、$`\mathrm{Assoc}` の射が定める代数 $`A` の左加群は、その射を色付きオペラッド $`\mathrm{LM}` に延ばすことと同値である。

KB-W2型再照合：仮定：通常のモノイダル圏のモノイド対象 A と左作用圏の対象 M（HA の対称モノイダル圏での自己作用を含む）。結論：A⊗M→M と単位律・結合律を持つ左加群を与える（左加群の構造に一致）。colored operad の写像の延長との同値は含まれない。

加群の色の像を $`M` とし、二項演算から作用 $`A\otimes M\to M` を取る。逆に、有限個の $`A` の因子を順に掛けてから $`M` に作用させると全演算を定められる。

:::

:::proposition "ha_4_2_1_5" (lean := "CategoryTheory.ModObj.regular")
*HA 注意 4.2.1.5*　The ∞-Operad \$\\mathrm\{LM\}\^\{\\otimes\}\$ (p. 505)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=505)）。対応表の状態：一部（component）。

*主張*　$`\mathrm{LM}\to\mathrm{Assoc}` は各演算の入力の全順序を記録する射であり、結合代数に適用すると、その代数が自分自身に左から作用する加群を与える。

KB-W2型再照合：仮定：通常のモノイダル圏の内部モノイド A（HA の通常の対称モノイダル圏を含む）。結論：A 自身に元の乗法で左 A-加群構造を与える（LM→Assoc を通じた正則加群の成分に一致）。全順序を忘れない colored operad の写像は含まれない。

加群の色と代数の色を同じ対象 $`A` へ送り、加群作用には代数の乗法を使う。

:::

:::definition "ha_4_2_1_19" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration") (uses := "ha_2_1_2_10, htt_2_4_2_1")
*HA 定義 4.2.1.19*　The ∞-Operad \$\\mathrm\{LM\}\^\{\\otimes\}\$ (p. 508)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=508)）。対応表の状態：本体にある。

*主張*　$`\mathrm{LM}^\otimes` 上のオペラッド・ファイブレーションが余デカルトであるとき、加群の色のファイバーは代数の色のファイバーで左テンソルされているという。

既に与えられたq:C⊗→LM⊗という∞-operad fibrationにCocartesianFibration qを適用すると、原文が追加しているcoCartesian fibration条件とそのまま一致する。通常圏のmonoidal/action構造による代用を取りやめ、同じ単体写像の条件を根拠にする。

演算に沿う余デカルト移送から、代数側の対象と加群側の対象を組み合わせる左作用が得られる。

:::

:::proposition "ha_4_2_1_20" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianFibration_pullback_snd")
*HA 注意 4.2.1.20*　The ∞-Operad \$\\mathrm\{LM\}\^\{\\otimes\}\$ (p. 508)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=508)）。対応表の状態：一部（component）。

*主張*　$`\mathrm{LM}^\otimes` 上の余デカルト・オペラッド・ファイブレーションを代数の色だけに制限すると、$`\mathrm{Assoc}^\otimes` 上の余デカルト・オペラッド・ファイブレーションになる。

KB-W2型再照合：仮定：余デカルトファイブレーションと底変換写像（Lean では Assoc⊗→LM⊗ を明示する）。結論：引き戻した写像は余デカルトファイブレーションとなる（代数色への制限の余デカルト性に一致）。Assoc 上の operadic 構造は型に含まれない。

左テンソル構造の代数側はこの制限でモノイダル ∞ 圏となる。加群の色を含む演算は左作用の側に現れる。

:::

