-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.Objects

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA 3.4 General Features of Module ∞-Categories" =>
%%%
number := false
tag := "ha-3-4"
%%%

HA 3.4 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 3.4.2 Modules over Trivial Algebras

%%%
number := false
tag := "ha-3-4-2"
%%%

:::lemma_ "ha_3_4_2_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.nonempty_cocartesianEdgeLift")
*HA 補題 3.4.2.3*　Modules over Trivial Algebras (p. 418)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=418)）。対応表の状態：一部（stronger-hyp）。

*主張*　底の ∞ オペラッドが単位的で上の ∞ オペラッドが相対単位対象を持つなら、半慣性辺を指定した始域から余デカルト辺に持ち上げられる。

KB-W2型再照合：仮定：単体集合の写像 p が余デカルトファイブレーション（Lean は HA の単位を持つ operadic fibration より強く、全ての底の辺で持ち上げがある場合に限る）。結論：指定の始点から底の辺への余デカルト持ち上げがある（semi-inert 辺に適用した結論は一致）。単位から semi-inert 辺だけの持ち上げを構成する部分は型に含まれない。

射影にはオペラッドのファイブレーションを仮定する。半慣性辺では、入力を使わない出力位置も許され、そこで相対単位対象の存在を使う。

:::

# 3.4.4 Colimits of Modules

%%%
number := false
tag := "ha-3-4-4"
%%%

:::definition "ha_3_4_4_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration, SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber")
*HA 定義 3.4.4.1*　Colimits of Modules (p. 435)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=435)）。対応表の状態：一部（component）。

*主張*　可提示な $`O` モノイダル ∞ 圏とは、余デカルト・ファイブレーションで、各色の圏が可提示であり、演算ごとの移送が各変数で小余極限を保つものである。

原文が与えた同じqについてCocartesianFibration qは条件(1)、各vertexFiber q XのIsPresentableは条件(3)を直接表す。operadicな各変数の小余極限との両立という条件(2)は含まない。

小余極限との両立には、色ごとの余極限の存在と、各多項演算が誘導するファイバーの積からの関手の余極限保存が入る。

:::

