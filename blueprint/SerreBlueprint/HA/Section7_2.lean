-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.AlgebraicTopology.DoldKan.Equivalence
import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
import Mathlib.CategoryTheory.Abelian.LeftDerived
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.GroupTheory.OreLocalization.Basic
import Mathlib.GroupTheory.OreLocalization.OreSet
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.OreLocalization.OreSet
import Mathlib.RingTheory.OreLocalization.Ring

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA 7.2 Properties of Rings and Modules" =>
%%%
number := false
tag := "ha-7-2"
%%%

HA 7.2 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 7.2.1 Free Resolutions and Spectral Sequences

%%%
number := false
tag := "ha-7-2-1"
%%%

:::proposition "ha_7_2_1_3" (lean := "CategoryTheory.Abelian.DoldKan.equivalence")
*HA 例 7.2.1.3*　Free Resolutions and Spectral Sequences (p. 1229)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1229)）。対応表の状態：一部（component）。

*主張*　左 $`R` 加群の単体的対象は、正規化複体の各項が自由なとき $`\{R\}`-自由であり、$`M` の $`\{R\}`-超被覆になるのは、増大正規化複体が $`M` の自由分解になるときである。

KB-W2原文・型再照合：仮定：通常の R 加群のアーベル圏（HA と一致）。結論：単体的対象と非負鎖複体の Dold–Kan 同値を構成する（冒頭の同定に一致）。S-free と各正規化項の自由性、S-hypercovering と増大の完全性の判定は含まれない。

Dold–Kan で単体的対象と非負鎖複体を比較する。増大を $`P_0\to M` として付けると、超被覆の判定は増大複体 $`\cdots\to P_1\to P_0\to M\to0` の完全性になる。

:::

:::proposition "ha_7_2_1_10" (lean := "CategoryTheory.SimplicialObject.Homotopy.toChainHomotopy, CategoryTheory.SimplicialObject.Homotopy.map_homology_eq")
*HA 注意 7.2.1.10*　Free Resolutions and Spectral Sequences (p. 1232)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1232)）。対応表の状態：Mathlib にある。

*主張*　アーベル圏の単体的対象の間の単体ホモトピーは非正規化鎖複体の鎖ホモトピーを与え、両射はホモロジーで一致する。

仮定：アーベル圏の単体対象の射と単体的ホモトピー（HA と一致。構成自体は前加法圏でも成立）。結論：交代面鎖複体の鎖ホモトピーを構成し、各ホモロジー上の写像の一致を示す（HA と一致）。

鎖ホモトピーは、退化写像とホモトピーを与える区間への写像から構成する。原典の途中に正規化の記号が出るが、直前の比較と直後の式では非正規化複体を使う。

:::

:::proposition "ha_7_2_1_12" (lean := "CategoryTheory.Functor.leftDerived, CategoryTheory.ProjectiveResolution.isoLeftDerivedObj")
*HA 例 7.2.1.12*　Free Resolutions and Spectral Sequences (p. 1233)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1233)）。対応表の状態：一部（stronger-hyp）。

*主張*　自由左 $`R` 加群上の加法関手 $`F` の左導来関手 $`L_nF` は、自由分解に $`F` を次数ごとに適用した複体の $`n` 次ホモロジーで計算できる。

KB-W2原文・型再照合：仮定：射影分解を持つ通常のアーベル圏と全対象上に定義された加法関手 F（Lean が強い：自由加群だけでなく全加群上に F を指定する）。結論：左導来関手 LₙF を構成し、任意の射影分解の項別 F のホモロジーと同定する（この仮定での HA の結論に一致）。自由加群だけで定義した F の延長一般は含まれない。

単体的自由加群に移して、単体ホモトピックな射が同じホモロジー写像を与えることを用いる。この不変性によって、分解の選択から加群自身に値を持つ関手へ降りる。

:::

:::proposition "ha_7_2_1_14" (lean := "CategoryTheory.Tor")
*HA 例 7.2.1.14*　Free Resolutions and Spectral Sequences (p. 1234)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1234)）。対応表の状態：一部（special）。

*主張*　右 $`R` 加群 $`M` に対し、左 $`R` 加群の関手 $`M\otimes_R-` の左導来関手を $`\operatorname{Tor}^R_n(M,-)` と書く。

KB-W2原文・型再照合：仮定：通常の可換環 R の加群圏（Lean が強い：可換環の場合。一般のアーベルモノイダル圏にも定義可能）。結論：片側テンソルを第二変数で左導来した Torₙ を定義する（HA と一致する通常の Tor の定義）。一般の非可換環の左右加群版は含まれない。

自由左加群による分解を選び、$`M` とテンソルしてホモロジーを取る。左右の加群の向きを固定しているので、$`R` が非可換でも定義できる。

:::

# 7.2.3 Localizations and Ore Conditions

%%%
number := false
tag := "ha-7-2-3"
%%%

:::definition "ha_7_2_3_1" (lean := "OreLocalization.OreSet, OreLocalization.nonempty_oreSet_iff")
*HA 定義 7.2.3.1*　Localizations and Ore Conditions (p. 1248)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1248)）。対応表の状態：Mathlib にある。

*主張*　左 Ore 条件は、分母の集合が単位と積を含み、任意の $`x\in R,s\in S` に $`tx=ys` となる $`t\in S,y\in R` があり、$`xs=0` ならある $`t\in S` で $`tx=0` となることをいう。

仮定：通常の結合環 R と部分モノイド S（HA の (a) と一致）。結論：共通左分母と右の共通因子を左の共通因子に変える条件を OreSet として定義し、存在量化した条件と同値にする（HA の (b)・(c) と一致。環では差を取ることで零化条件と一般の右消去条件が同じになる）。証人の選択を持つ構造と Nonempty を区別している。

最初の等式は左分母をそろえるために使い、消滅条件は、右から分母を掛けて得た等式を左分母で扱えるようにする。

:::

:::proposition "ha_7_2_3_2" (lean := "OreLocalization.oreSetComm")
*HA 注意 7.2.3.2*　Localizations and Ore Conditions (p. 1248)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1248)）。対応表の状態：一部（special）。

*主張*　分母の集合が環の中心に含まれれば、左 Ore 条件の共通倍と消滅に関する条件は自動的に成り立つ。

KB-W2原文・型再照合：仮定：通常の可換環と任意の部分モノイド（Lean が強い：環全体が可換な場合）。結論：左 Ore 条件の instance を構成する（HA の可換環の場合に一致）。非可換環の中心に含まれる場合の一般化は含まれない。

$`sx=xs` なので共通倍では $`t=s,y=x` を選べる。右から $`s` を掛けて零になる場合も、左から同じ $`s` を掛ければ零になる。

:::

:::proposition "ha_7_2_3_3" (lean := "OreLocalization.OreSet")
*HA 注意 7.2.3.3*　Localizations and Ore Conditions (p. 1248)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1248)）。対応表の状態：Mathlib にある。

*主張*　右 Ore 条件は、反対環での左 Ore 条件である。

仮定：通常の結合環 R とその反対環の部分モノイド（HA と一致）。結論：反対環に OreSet を適用して共通右分母と左因子の消去条件を表す（HA の右 Ore 条件を左 Ore 条件の双対として定義する内容に一致）。

通常の積に戻すと、分母との共通倍の式は $`xt=sy` となり、$`sx=0` からある $`t\in S` に対し $`xt=0` を要求する。

:::

:::definition "ha_7_2_3_4" (lean := "OreLocalization")
*HA 構成 7.2.3.4*　Localizations and Ore Conditions (p. 1248)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1248)）。対応表の状態：Mathlib にある。

*主張*　左 Ore 集合 $`S` による左加群 $`M` の分数 $`s^{-1}x` は、対 $`(s,x)` を共通の左分母のもとで同じ分子になるという関係で割って作る。

仮定：通常の結合環、左 Ore な部分モノイドと左加群（HA と一致。構成自体はモノイドの作用にも適用できる）。結論：分母と分子の共通左倍数による同値関係の商を構成する（HA の左分数加群の台集合に一致）。対の並びは分子・分母の順である。

$`(s,x)\sim(s',x')` は $`as=a's'\in S`、$`ax=a'x'` を満たす $`a,a'\in R` があることをいう。Ore 条件で三つの対の分母を合わせて推移性を得る。標準写像は $`x\mapsto1^{-1}x` である。

:::

:::proposition "ha_7_2_3_5" (lean := "OreLocalization.universalHom, OreLocalization.universalHom_unique, OreLocalization.numerator_isUnit")
*HA 命題 7.2.3.5*　Localizations and Ore Conditions (p. 1249)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1249)）。対応表の状態：一部（component）。

*主張*　Ore の分数加群 $`S^{-1}M` は分母が可逆に作用する左加群への普遍射を持ち、$`M=R` のときは分母を反転する普遍環となる。

KB-W2原文・型再照合：仮定：通常の結合環 R、左 Ore な S と S の像が単元となる環準同型（HA と一致）。結論：Ore 局所化の環構造を用いて各分母の可逆性と環射の一意な延長を与える（結論 (4)–(6) の環の普遍性に一致）。一般の左加群の全ての線形普遍性と R 加群構造の一意性は含まれない。

分数は標準射 $`\phi:M\to S^{-1}M` を用いて $`s(s^{-1}x)=\phi(x)` と特徴付けられる。環の場合は $`\phi` が環準同型となり、$`S` を可逆元に送る任意の環準同型が一意にこの環を経由する。

:::

# 7.2.4 Finiteness Properties of Rings and Modules

%%%
number := false
tag := "ha-7-2-4"
%%%

:::proposition "ha_7_2_4_14" (lean := "Module.finitePresentation_of_finite")
*HA 例 7.2.4.14*　Finiteness Properties of Rings and Modules (p. 1267)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1267)）。対応表の状態：一部（component）。

*主張*　左 Noether 環は左コヒーレントであり、$`\mathbb Z` 上の無限変数多項式環はコヒーレントだが Noether ではない。

KB-W2原文・型再照合：仮定：通常の左 Noetherian 環と有限生成左加群（HA の Noetherian の場合と一致。対象はイデアルより一般）。結論：その加群が有限表示となる（Noetherian⇒coherent の有限生成イデアルへの結論に一致）。無限変数多項式環の coherent 性と非 Noetherian 性の例は含まれない。

左 Noether 環では左イデアルおよび有限生成加群の部分加群が有限生成で、有限表示の関係も有限個にできる。無限変数の例では変数全部が生成するイデアルが有限生成でない。

:::

:::lemma_ "ha_7_2_4_15" (lean := "Module.finitePresentation_of_finite")
*HA 補題 7.2.4.15*　Finiteness Properties of Rings and Modules (p. 1267)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1267)）。対応表の状態：一部（stronger-hyp）。

*主張*　左コヒーレント環では、有限自由加群または有限表示左加群の有限生成部分加群は有限表示であり、有限表示左加群間の射の核と余核も有限表示である。

KB-W2原文・型再照合：仮定：通常の左 Noetherian 環と有限生成加群（Lean が強い：coherent より強い Noetherian 性を要求する）。結論：有限生成部分加群に有限表示性を与える（(1)・(2) のこの仮定での結論に一致）。coherent だけの場合と有限表示間の核・余核の三結論全体は含まれない。

第一の主張は有限自由加群の階数を下げて左イデアルの場合に帰着させる。これを有限表示加群の表示に適用し、核と余核を有限表示の範囲で扱えるようにする。

:::

:::definition "ha_7_2_4_30" (lean := "IsNoetherianRing, Module.finitePresentation_of_finite")
*HA 定義 7.2.4.30*　Finiteness Properties of Rings and Modules (p. 1273)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1273)）。対応表の状態：一部（component）。

*主張*　連結 $`E_k` 環 $`(k\ge2)` が左コヒーレントであるとは、$`\pi_0R` がコヒーレントで各 $`\pi_iR` がその上の有限表示加群であることをいう。

原文が明示する同じ通常可換環π₀RのNoetherian条件はIsNoetherianRingで直接表す。全πᵢの有限表示性とcoherentな環スペクトルという条件全体は含まない。

さらに $`\pi_0R` が Noether 環なら $`R` を Noether と呼ぶ。定義は基礎 $`E_1` 環の左コヒーレント性であり、この範囲では $`\pi_0R` は可換である。

:::

