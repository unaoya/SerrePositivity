import Verso
import VersoManual
import VersoBlueprint
import Mathlib.Data.Finset.Sort
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SourceCosliceFilteredColimits
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SourceCosliceProjectionColimits
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftComma
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitCosliceRestriction
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Coslice
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Slice

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA 2.2 Constructions of ∞-Operads" =>
%%%
number := false
tag := "ha-2-2"
%%%

HA 2.2 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 2.2.2 Slicing ∞-Operads

%%%
number := false
tag := "ha-2-2-2"
%%%

:::definition "ha_2_2_2_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverEquiv, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderEquiv")
*HA 定義 2.2.2.1*　Slicing ∞-Operads (p. 200)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=200)）。対応表の状態：一部（special）。

*主張*　$`S` 上の図式 $`p:S\times K\to X` の相対余錐圏・相対錐圏は、$`S` 上の族として $`K` 上の図式を余錐・錐に延長するデータを表現する。

KB-W2型再照合：仮定：単体集合の図式 p : K→X（Lean が強い：HA 2.2.2.2 の底 S が一点の場合）。結論：通常のスライス・余スライスへの写像と、p を延長する join の写像との自然な全単射（HA の絶対の場合の普遍性に一致）。一般の S 上の相対版は型に含まれない。

試験対象 $`Y\to S` を与えると、その上の射は $`Y\times K` 上の指定の制限を持つ $`Y\times K^{\triangleright}` または $`Y\times K^{\triangleleft}` の図式に対応する。余錐または錐の頂点は $`S` から選んだ基底の像に整合する。

:::

:::lemma_ "ha_2_2_2_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnder_quasicategory")
*HA 補題 2.2.2.6*　Slicing ∞-Operads (p. 202)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=202)）。対応表の状態：一部（special）。

*主張*　$`X\to S` が内ファイブレーションなら、指定の相対余錐圏も $`S` 上の内ファイブレーションであり、圏論的ファイブレーションの場合も同じ保存が成り立つ。

KB-W2型再照合：仮定：準圏 X と図式 p : K→X（Lean が強い：底 S が一点）。結論：余スライスが準圏になり、一点への射が inner fibration となる場合に一致。任意の S への射に対する二種類のファイブレーションの主張は型に含まれない。

相対余錐圏への持ち上げをその普遍性で、$`X` に値を取る図式の延長に置き換える。元の持ち上げ性を使って延長を得る。

:::

:::lemma_ "ha_2_2_2_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCosliceRestriction_trivialKanFibration")
*HA 補題 2.2.2.7*　Slicing ∞-Operads (p. 202)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=202)）。対応表の状態：一部（special）。

*主張*　内ファイブレーション $`X\to S` 上で、$`K` の各頂点における余錐が相対余極限なら、余錐図式全体からの下の圏の比較は自明 Kan ファイブレーションである。

KB-W2型再照合：仮定：絶対余極限余錐（Lean が強い：パラメーター K と底 S が一点）。結論：錐頂点を含む図式から元の図式への余スライス制限が自明 Kan ファイブレーション（その場合の比較に一致）。パラメーターを持つ相対版は型に含まれない。

比較の標的では $`K\times Y` 上への制限と、$`S` における $`K\times Y^{\triangleright}` 全体の像を固定して合わせる。点ごとの余極限条件から、この比較の任意の境界に対する持ち上げが得られる。

:::

:::lemma_ "ha_2_2_2_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sourceCoslice_isColimitCone_iff_projection, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sourceCoslice_hasColimit_of_rightCofinal")
*HA 補題 2.2.2.8*　Slicing ∞-Operads (p. 203)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=203)）。対応表の状態：一部（special）。

*主張*　相対余錐圏で、全ての点での指定の底の余錐と評価した余錐が相対余極限として取れるなら、評価で相対余極限となる延長が存在し、それが相対余錐圏での余極限性を判定する。

KB-W2型再照合：仮定：準圏の余スライスの図式、join の右包含の共終性（Lean が強い：底 S が一点、図式形状を準圏とする）。結論：指定余錐の余極限性を元の準圏への射影で判定し、底の存在から余スライスの余極限を得る（この場合の (1) と (2) に一致）。底の任意の射に沿う相対版は型に含まれない。

$`Y` の図式と $`S` 内の延長 $`g:Y^{\triangleright}\to S` を固定する。仮定の一つは各 $`k` で $`p(-,k)\circ g` が相対余極限となること、もう一つは評価した $`Y` の図式が $`g` 上に相対余極限余錐を持つことである。

:::

# 2.2.3 Coproducts of ∞-Operads

%%%
number := false
tag := "ha-2-2-3"
%%%

:::definition "ha_2_2_3_1" (lean := "Finset.orderIsoOfFin")
*HA 記法 2.2.3.1*　Coproducts of ∞-Operads (p. 207)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=207)）。対応表の状態：一部（component）。

*主張*　$`\langle n\rangle` の基点を含む部分集合 $`S` について、基点以外を昇順に並べて同定した代表を $`[S]=\langle |S|-1\rangle` と書く。

KB-W2型再照合：仮定：全順序集合の濃度 k の有限部分集合（Lean は S の非基点部分以外にも適用できる）。結論：Fin k とその部分集合との順序同型（S の非基点部分の整列に一致）。基点を保つ Fin∗ の標準対象と記法は型に含まれない。

非基点の順序を指定するので、代表から $`S` への基点保存全単射は一意である。

:::

# 2.2.4 Monoidal Envelopes

%%%
number := false
tag := "ha-2-2-4"
%%%

:::lemma_ "ha_2_2_4_15" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection_cocartesianFibration") (uses := "ha_2_1_2_10, htt_2_4_2_1, htt_2_4_7_12")
*HA 補題 2.2.4.15*　Monoidal Envelopes (p. 216)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=216)）。対応表の状態：一部（component）。

*主張*　$`C^\otimes` と $`O^\otimes` の矢印圏を始点で引き戻した圏は、終点評価で $`O^\otimes` 上の余デカルト・ファイブレーションとなり、その余デカルト辺は $`C^\otimes` での同値で判定できる。

KB-W2型再照合：仮定：準圏の間の任意の関手 δ（Lean が弱い：operad 構造を要求しない）。結論：δ の oriented fiber product の終点射影が余デカルト・ファイブレーション（(1) の D→O⊗ に一致）。余デカルト辺の判定と Env への制限はこの型に含まれない。

終点評価を包絡 $`\mathrm{Env}_O(C)^\otimes` に制限しても余デカルト・ファイブレーションが得られる。包絡では余デカルト辺の判定は $`C^\otimes` への像が慣性射であることである。

:::

