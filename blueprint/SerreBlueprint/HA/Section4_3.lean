-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.HomotopicalAlgebra.Transfer.Right
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA 4.3 Bimodules" =>
%%%
number := false
tag := "ha-4-3"
%%%

HA 4.3 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 4.3.1 The ∞-Operad BM\^

%%%
number := false
tag := "ha-4-3-1"
%%%

:::definition "ha_4_3_1_17" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration")
*HA 定義 4.3.1.17*　The ∞-Operad \$\\mathrm\{BM\}\^\{\\otimes\}\$ (p. 538)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=538)）。対応表の状態：本体にある。

*主張*　$`\mathrm{BM}^\otimes` 上のオペラッド・ファイブレーションが余デカルトなら、加群の色の圏は左右の代数の色の圏で両側テンソルされているという。

既に与えられたq:C⊗→BM⊗という∞-operad fibrationにCocartesianFibration qを適用すると、原文が追加しているcoCartesian fibration条件とそのまま一致する。通常圏のmonoidal/action構造による代用を取りやめ、同じ単体写像の条件を根拠にする。

多項演算に沿う余デカルト移送が左と右の作用を同時に与える。このデータには、二つの作用を組み合わせる整合性が入る。

:::

# 4.3.3 Limits, Colimits, and Free Bimodules

%%%
number := false
tag := "ha-4-3-3"
%%%

:::proposition "ha_4_3_3_15" (lean := "SerrePositivity.ModelGeneration.rightTransfer, SerrePositivity.ModelGeneration.rightTransfer_weakEquivalences, SerrePositivity.ModelGeneration.rightTransfer_fibrations, SerrePositivity.ModelGeneration.rightTransfer_isRightQuillen")
*HA 命題 4.3.3.15*　Limits, Colimits, and Free Bimodules (p. 554)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=554)）。対応表の状態：一部（stronger-hyp）。

*主張*　組合せ的モノイダルモデル圏で基礎対象が余ファイブラントな二つの結合代数を取ると、双加群の圏には基礎で弱同値とファイブレーションを判定する組合せ的モデル構造が入る。

KB-W2型再照合：仮定：生成されたモデル圏、対象圏への随伴、有限極限・余極限、移送後の small-object 条件と acyclicity（Lean は両側加群の忘却にこれらの入力を要求する）。結論：右随伴で弱同値とファイブレーションを検出するモデル構造を与え、忘却を右 Quillen にする（この成分に一致）。両側加群の具体的 instance、左 Quillen 性と単体両立性は型に含まれない。

忘却関手は左 Quillen かつ右 Quillen となる。基礎に適合する単体構造があれば、双加群のモデル構造も単体的である。

:::

:::proposition "ha_4_3_3_16" (lean := "SerrePositivity.ModelGeneration.rightTransfer, SerrePositivity.ModelGeneration.rightTransfer_weakEquivalences, SerrePositivity.ModelGeneration.rightTransfer_fibrations")
*HA 注意 4.3.3.16*　Limits, Colimits, and Free Bimodules (p. 555)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=555)）。対応表の状態：一部（stronger-hyp）。

*主張*　組合せ的モデル圏上の左 Quillen 自己関手がモナドであるなら、その代数の圏には弱同値とファイブレーションを基礎で判定するモデル構造が入る。

KB-W2型再照合：仮定：生成されたモデル圏、随伴、対象圏の有限極限・余極限、移送後の small-object 条件と acyclicity（Lean はモナドの自由忘却随伴にこれらの入力を要求する）。結論：右随伴で弱同値とファイブレーションを検出するモデル構造を与える（条件付きで一致）。左 Quillen モナドから移送条件を満たす宣言は含まれない。

モナドは合成をテンソルとする自己関手の圏の結合代数である。双加群の場合には、余ファイブラント双加群を局所化した圏から、基礎のモノイダル ∞ 圏の双加群への比較も得られる。

:::

