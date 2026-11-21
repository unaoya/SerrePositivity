-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.CommutativeAlgebra.DeRham.Graded
import SerrePositivity.DifferentialGraded.Algebras.ModelCategory
import SerrePositivity.HomologicalAlgebra.Complexes.Limits.CofibrantTensorQuillen
import SerrePositivity.HomotopicalAlgebra.Complexes.ProjectiveCofibrantUnit
import SerrePositivity.HomotopicalAlgebra.Complexes.ProjectiveModel
import SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraDerivedInfinity
import SerrePositivity.KST.Comparison.DGAlgebra
import SerrePositivity.KST.Comparison.GammaH0Ring

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA 7.1 Structured Ring Spectra" =>
%%%
number := false
tag := "ha-7-1"
%%%

HA 7.1 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 7.1.2 Recognition Principles

%%%
number := false
tag := "ha-7-1-2"
%%%

*08-dgnerve-derived.html — 4. 非可換 dg 代数の導来 ∞ 圏と Morita 不変性（β5）*

\`\`\`text
abbrev dgModuleDerivedInfinityCategory := dgNerve R (SemifreeDGModules R D)
\`\`\`

dg 圏（とくに非可換 dg 代数）$`D` 上の semifree dg 加群の dg nerve として $`D(A)` を定義する（HA §7.1.2 は比較の目標であり、引用はしていない）。

- D(A)・Perf(A) の安定性。Perf(A) は冪等完備（第 6 章の強分裂を使う）。

- 双加群による相対テンソル・Hom を dg 関手として作り、dg nerve に移して ∞ 関手にする。単位・合成・随伴の整合性。

- Morita 不変性：Morita 同値な dg 代数の D・Perf は同値（\`dgMoritaPerfectKernelInfinity\_isQCatEquivalence\` など、Derived/DGModule\*）。

- 単体環は正規化によって dg 代数になり、台の弱同値は D・Perf の同値を与える。

Land–Tamme の ⊙ 構成（K 理論側）では、環や導来環をこの形で扱う（B 案：dg による増強の経路）。

:::proposition "ha_7_1_2_8" (lean := "SerrePositivity.ProjectiveModel.projectiveModelCategory, SerrePositivity.ProjectiveModel.projectiveModelCategory_weakEquivalences, SerrePositivity.ProjectiveModel.projectiveModelCategory_fibrations, SerrePositivity.ProjectiveModel.projectiveModelCategory_cofibrantlyGenerated")
*HA 命題 7.1.2.8*　複体の射影モデル構造（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1209)）。対応表の状態：一部（component）。

*主張*　結合環上の右加群の鎖複体には、擬同型を弱同値、各次数の全射をファイブレーションとする左固有な組合せ的モデル構造がある。

KB-W2原文・型再照合：仮定：任意可換環 R の非有界余鎖複体（Lean が強い：可換環の場合。次数の符号を反転して HA と比較する）。結論：実際の射影モデル構造を構成し、弱同値を擬同型、fibration を各次数全射と同定し、生成族の小対象引数も持つ（モデル構造と W・F の部分に一致）。左固有性と局所可呈示性を合わせた combinatorial 性の宣言は含まれない。ModelCategory は追加仮定でなく構成済み。

余ファイブレーションは全射である擬同型のすべてに対する左持ち上げ類である。弱同値は各次数のホモロジーで同型になることで判定する。

:::

:::proposition "ha_7_1_2_11" (lean := "SerrePositivity.ProjectiveCofibrantUnit.projectiveCofibrant_unit, SerrePositivity.ComplexLimits.tensorLeft_cofibrant_isLeftQuillen")
*HA 命題 7.1.2.11*　射影モデル構造とテンソルの整合性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1212)）。対応表の状態：一部（component）。

*主張*　可換環上の加群の鎖複体は、通常の鎖複体のテンソル積と射影的モデル構造を備えた対称モノイダルモデル圏になる。

KB-W2原文・型再照合：仮定：任意可換環 R の非有界複体と構成済み射影モデル構造（HA と一致）。結論：テンソル単位の cofibrancy と任意 cofibrant X による左テンソルの左 Quillen 性を示す（HA のモノイダル模型の結論の一部に一致）。任意の二つの cofibration の pushout-product 公理全体を登録した宣言は含まれない。

複体のテンソルには全複体と Koszul 符号を用いる。これが射影的モデル構造の押し出し積条件と両立する。

:::

# 7.1.4 Algebras over Commutative Rings

%%%
number := false
tag := "ha-7-1-4"
%%%

:::definition "ha_7_1_4_1" (lean := "SerrePositivity.KST.Comparison.DGAlgebraModel")
*HA 定義 7.1.4.1*　Algebras over Commutative Rings (p. 1220)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1220)）。対応表の状態：本体にある。

*主張*　可換環上の dg 代数は、次数 $`-1` の平方零の微分が符号付き Leibniz 則を満たす次数付き結合代数である。

仮定：任意可換環 R（HA と一致）。結論：R 線形複体に豊穣化した一対象 dg 圏を dg 代数として定義する（HA の単位的次数付き代数・微分・Leibniz 則と一致する一対象圏の表現）。余鎖の +1 微分を用いるため HA の鎖次数とは符号を反転する。

$`x` が次数 $`m` なら $`d(xy)=d(x)y+(-1)^mx d(y)` である。dg 代数の射は、次数付き代数の準同型で微分と可換なものをいう。

:::

:::proposition "ha_7_1_4_2" (lean := "SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraPointEnrichment")
*HA 注意 7.1.4.2*　Algebras over Commutative Rings (p. 1220)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1220)）。対応表の状態：一部（direction）。

*主張*　可換環 $`R` 上の dg 代数の圏は、$`R` 加群の鎖複体のモノイダル圏の結合代数対象の圏と同値である。

KB-W2原文・型再照合：仮定：可換環 R と複体のモノイド対象 B（HA と一致）。結論：同じ複体・単位・乗法を Hom・恒等・合成とする一対象 dg 代数を構成する（HA の同定のこの向きに一致）。逆向きの関手と両合成の自然同型は含まれない。

鎖複体のテンソルからの乗法が鎖写像であるという条件が、符号付き Leibniz 則である。結合と単位はモノイダル圏での代数の公理に対応する。

:::

:::proposition "ha_7_1_4_4" (lean := "SerrePositivity.KST.Comparison.dgAlgebraH0Ring")
*HA 注意 7.1.4.4*　Algebras over Commutative Rings (p. 1221)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1221)）。対応表の状態：一部（component）。

*主張*　dg 代数のホモロジーは次数付き代数をなし、dg 代数の擬同型はそのホモロジー次数付き環で同型となる射である。

KB-W2原文・型再照合：仮定：可換環 R 上の一対象 dg 圏としての dg 代数（HA と一致する dg 模型）。結論：閉零射を境界で割った H⁰ に自己射の合成による環構造を与える（零次の環の部分に一致）。全次数の次数付き R 代数と擬同型による全次数の環同型の判定は含まれない。

サイクルの積はサイクルとなり、片方を境界だけ変えても積のホモロジー類は変わらない。従ってホモロジーの積が定まる。原典中の $`H_*(R)` は直前に定義した $`H_*(A)` と読む。

:::

:::proposition "ha_7_1_4_5" (lean := "SerrePositivity.DGAlgebra.modelCategory, SerrePositivity.DGAlgebra.modelCategory_weakEquivalences, SerrePositivity.DGAlgebra.modelCategory_fibrations")
*HA 命題 7.1.4.5*　Algebras over Commutative Rings (p. 1221)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1221)）。対応表の状態：一部（component）。

*主張*　可換環上の結合 dg 代数には擬同型を弱同値、各次数の全射をファイブレーションとする組合せ的モデル構造が存在し、基礎環が体なら左固有である。

KB-W2原文・型再照合：仮定：任意可換環 R と厳密 dg 代数 Mon(Complex R)（HA と一致する模型）。結論：実モデル構造を構成し、弱同値を底の擬同型、fibration を底の次数別全射と同定する（モデル構造・W・F の部分に一致）。combinatorial 性と体上の左固有性は含まれない。ModelCategory は構成済み。

判定は基礎鎖複体で行う。左固有性を述べる部分では体であることを追加で仮定する。

:::

:::definition "ha_7_1_4_8" (lean := "SerrePositivity.DeRham.GradedCommDGAlgebra")
*HA 定義 7.1.4.8*　Algebras over Commutative Rings (p. 1222)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1222)）。対応表の状態：一部（special）。

*主張*　可換 dg 代数は次数付き可換性 $`xy=(-1)^{mn}yx` を満たす dg 代数である。

KB-W2原文・型再照合：仮定：任意可換環 R と非負余鎖次数（Lean が強い：非負次数に限る）。結論：xy=(-1)\^(ij)yx と微分の Leibniz 則を満たす可換 dg 代数を構造として定義する（この次数範囲の定義に一致）。全整数次数の dg 代数圏の充満部分圏としての束ね方は含まれない。

$`m,n` はそれぞれ $`x,y` の次数である。この性質を満たす dg 代数は、結合 dg 代数の圏の充満部分圏をなす。

:::

