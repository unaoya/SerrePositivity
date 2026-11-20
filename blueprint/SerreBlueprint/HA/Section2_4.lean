-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.CocartesianInnerHornPullback
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCatSimplicial
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionEquivalence

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA 2.4 Products and Coproducts" =>
%%%
number := false
tag := "ha-2-4"
%%%

HA 2.4 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 2.4.1 Cartesian Symmetric Monoidal Structures

%%%
number := false
tag := "ha-2-4-1"
%%%

*route-6ff-definition.html — 7. $`\mathrm{Cat}_\infty` の対称モノイダル構造*

直積による cartesian 対称モノイダル構造を入れる。手順は (1) $`\mathrm{Cat}_\infty` が有限積を持つことを示し、(2) 有限積を持つ任意の ∞ 圏に対する一般的な構成 $`\mathcal C\mapsto\mathcal C^\times`（HA §2.4.1）を適用する。

*route-6ff-definition.html — 7. $`\mathrm{Cat}_\infty` の対称モノイダル構造 — 7.1 有限積*

$`\mathrm{QCat}^\Delta` で $`\mathcal C\times\mathcal D` は厳密な積（$`\mathrm{Fun}(X,\mathcal C\times\mathcal D)^{\simeq}=\mathrm{Fun}(X,\mathcal C)^{\simeq}\times\mathrm{Fun}(X,\mathcal D)^{\simeq}`）、$`\Delta^0` は厳密な終対象（$`\mathrm{Fun}(X,\Delta^0)^{\simeq}=\ast`）。写像空間の比較定理により、Kan 豊穣な単体的圏の厳密な積・終対象は $`N^{hc}` で ∞ 圏の積・終対象になる（写像空間が積になることが ∞ 圏の積の定義）。

*route-6ff-definition.html — 7. $`\mathrm{Cat}_\infty` の対称モノイダル構造 — 7.2 一般的な構成 $`\mathcal C^\times`*

$`\Gamma^\times` を、対象が組 $`(\langle n\rangle,S)`（$`S\subseteq\langle n\rangle^\circ=\{1,\dots,n\}`）の圏とし、$`\Gamma^\times\to\mathrm{Fin}_*` を射影とする。$`\mathcal C^\times` の $`\langle n\rangle` 上の対象は、関手 $`F\colon\{S\subseteq\langle n\rangle^\circ\}^{\mathrm{op}}\to\mathcal C` で、
$$`F(S)\ \xrightarrow{\ \sim\ }\ \prod_{i\in S}F(\{i\})`
を満たすもの（積の図式）。直観的には「$`n` 個の対象 $`X_1,\dots,X_n` と、その部分積の全ての選択」で、積の選択を全部データとして持つことで選択の問題を消している。単体的集合としては、$`\Delta^k\to N(\mathrm{Fin}_*)` と $`\Delta^k\times_{N(\mathrm{Fin}_*)}N(\Gamma^\times)\to\mathcal C` の組で、積の条件を満たすもの。

*定理*（HA Prop. 2.4.1.5）：$`\mathcal C` が有限積を持てば $`\mathcal C^\times\to N(\mathrm{Fin}_*)` は対称モノイダル ∞ 圏で、$`\otimes=\times`、単位は終対象。

- *cocartesian 持ち上げ*：$`\alpha\colon\langle n\rangle\to\langle m\rangle` の上で $`(X_1,\dots,X_n)` の行き先は $`\bigl(\prod_{\alpha(i)=j}X_i\bigr)_j`。存在は $`\mathcal C` が有限積を持つこと（右 Kan 拡張）から、選択の空間は可縮。

- *Segal 条件*：積の図式の条件から $`\mathcal C^\times_{\langle n\rangle}\simeq\mathcal C^n`。

- *一意性*（HA §2.4.1）：cartesian 構造（単位が終対象で、$`\otimes` が射影とともに積を与える構造）は可縮な選択を除いて一意。

$`\mathcal C=\mathrm{Cat}_\infty` に適用して $`\mathrm{Cat}_\infty^\times` を得る。

*route-6ff-definition.html — 7. $`\mathrm{Cat}_\infty` の対称モノイダル構造 — 7.3 cartesian 構造への lax 関手：六関手の定義への接続*

cartesian 構造には普遍性がある（HA Prop. 2.4.1.7）：∞ operad $`\mathcal O^\otimes` から $`\mathcal C^\times` への lax 関手（operad の写像）は、*lax cartesian 構造*、すなわち関手 $`\tilde F\colon\mathcal O^\otimes\to\mathcal C` で、$`\langle n\rangle` 上の各 $`X\simeq X_1\oplus\cdots\oplus X_n` について inert 射 $`X\to X_i` が $`\tilde F(X)\simeq\prod_i\tilde F(X_i)` を与えるものと同値。

$$`\mathrm{Fun}^{\mathrm{lax}}\bigl(\mathcal O^\otimes,\mathcal C^\times\bigr)\ \simeq\ \mathrm{Fun}^{\text{lax cart}}\bigl(\mathcal O^\otimes,\mathcal C\bigr)`

六関手形式では、lax 対称モノイダル $`D\colon\mathrm{Corr}^\otimes\to\mathrm{Cat}_\infty^\times` は、関手 $`\tilde D\colon\mathrm{Corr}^\otimes\to\mathrm{Cat}_\infty` で $`\tilde D(X_1,\dots,X_n)\simeq\prod_iD(X_i)` となるものと同じ。active 射 $`\langle2\rangle\to\langle1\rangle` の上の射 $`(X,Y)\to X\times Y` は $`D(X)\times D(Y)\simeq\tilde D(X,Y)\to D(X\times Y)`、すなわち外部テンソル積 $`\boxtimes` を与え、これは可逆でない（lax）。$`\mathrm{Cat}_\infty^\times` の構成を細部まで追わなくても、この普遍性で lax 関手を「積を保つ関手」として扱える。

- 段　／　内容　／　入力
- 7.1　／　$`\mathrm{Cat}_\infty` の有限積は $`\mathcal C\times\mathcal D`、終対象は $`\Delta^0`　／　写像空間の比較定理
- 7.2　／　$`\mathcal C^\times` の構成と、それが対称モノイダル　／　$`\Gamma^\times`、積の図式、右 Kan 拡張の可縮性
- 7.3　／　$`\mathcal C^\times` への lax 関手 = lax cartesian 構造　／　HA Prop. 2.4.1.7

*route-6ff-definition.html — 7. $`\mathrm{Cat}_\infty` の対称モノイダル構造 — 7.4 lax 関手への普遍性：何のために要るか、詳しい形*

*なぜ出てくるか*：$`\mathrm{Cat}_\infty^\times` の中身（$`\langle n\rangle` 上の対象は部分集合の半順序集合から $`\mathrm{Cat}_\infty` への積の図式）は複雑で、六関手形式を具体的に書くたびにこの対象への写像を $`\mathrm{Fin}_*` 上で inert の上の cocartesian 辺を保つように作るのは現実的でない。普遍性は*その必要がない*ことを言う：$`\mathrm{Cat}_\infty^\times` への lax 関手は、$`\mathrm{Cat}_\infty` への普通の関手で組を積に送るものと同じ。

- 　／　必要か
- 定義を述べる　／　不要（$`\mathrm{Cat}_\infty^\times` があれば述べられる）
- 定義が何を言っているか分かる　／　ほぼ必要（読み替えがないとデータの中身が見えない）
- 具体例を構成する　／　必要（実際の構成はこの形の関手として行う）

読み替えると六関手形式のデータは：各 $`X` に $`D(X)`、各 span に $`f_!g^*`、組の間の射（$`(X,Y)\to X\times Y` など）に外部テンソル積 $`D(X)\times D(Y)\to D(X\times Y)`、そしてこれら全ての整合性（$`\tilde D` が関手であること）。§4 の (e) の一部にあたる。

*lax 関手の定義との関係*：lax 関手 $`F\colon\mathcal O^\otimes\to\mathcal C^\otimes` は $`N(\mathrm{Fin}_*)` 上の写像で inert の上の cocartesian 辺を保つもの。inert の上の cocartesian 辺は「組から成分を取り出す」射で、これを保つので組を組に送る。active の上の射は多重射 $`(X_1,\dots,X_n)\to Y` で、その像が構造写像（cocartesian とは限らないので lax）。値が $`\mathcal C^\times` なら、active の上の射 $`(Y_1,\dots,Y_n)\to Z` はただの $`\mathcal C` の射 $`\prod_iY_i\to Z` なので、$`F` は多重射を $`\prod_iF(X_i)\to F(Y)` に送る。

*主張*（HA Prop. 2.4.1.7）：射影 $`\pi\colon\mathcal C^\times\to\mathcal C`（$`\langle n\rangle` 上の $`F` を $`F(\{1,\dots,n\})` へ）との合成が同値
$$`\mathrm{Fun}^{\mathrm{lax}}(\mathcal O^\otimes,\mathcal C^\times)\ \xrightarrow{\ \pi\circ-\ \sim\ }\ \mathrm{Fun}^{\text{lax cart}}(\mathcal O^\otimes,\mathcal C)`
を与える。右辺は関手 $`\tilde F\colon\mathcal O^\otimes\to\mathcal C` で、各 $`X=(X_1,\dots,X_n)` について inert 射 $`X\to X_i` の像が $`\tilde F(X)\simeq\prod_i\tilde F(X_i)` を与えるもの。*証明の発想*：$`F(X)(S):=\tilde F(X_S)`（$`X_S` は inert 射 $`\langle n\rangle\to S_+` による像）と置くと、lax cartesian 条件がちょうど $`\mathcal C^\times` の積の図式の条件。

- 例　／　内容
- 1 圏、値 $`(\mathrm{Set},\times)`　／　lax モノイダル関手（$`F(x)\times F(y)\to F(x\otimes y)`、$`\ast\to F(1)`）＝ 組 $`(x_1,\dots,x_n)` を $`\prod F(x_i)` に送る関手
- 可換モノイド（$`\mathcal O^\otimes=N(\mathrm{Fin}_*)`）　／　$`\mathrm{CAlg}(\mathcal C^\times)\simeq\{\tilde F\colon N(\mathrm{Fin}_*)\to\mathcal C:\tilde F(\langle n\rangle)\simeq\tilde F(\langle1\rangle)^n\}`（Segal の $`\Gamma` 空間）。$`\mathcal C=\mathrm{Cat}_\infty` なら補章 5 §1 の「対称モノイダル ∞ 圏 = Segal 条件を満たす $`\mathrm{Fin}_*\to\mathrm{Cat}_\infty`」
- 六関手形式　／　$`\tilde D\colon\mathrm{Corr}(\mathcal C,E)^\otimes\to\mathrm{Cat}_\infty`、$`\tilde D(X_1,\dots,X_n)\simeq\prod_iD(X_i)`。active 射 $`(X,Y)\to X\times Y` の像が $`\boxtimes`

- 　／　定義どおり　／　普遍性で書き換えた形
- データ　／　$`\mathrm{Fin}_*` 上の写像 $`\mathcal O^\otimes\to\mathcal C^\times`　／　普通の関手 $`\tilde F\colon\mathcal O^\otimes\to\mathcal C`
- 条件　／　inert の上の cocartesian 辺を保つ　／　組を積に送る
- lax の構造写像　／　active 射の上の射の像　／　$`\tilde F` を active 射に適用したもの

# 2.4.2 Monoid Objects

%%%
number := false
tag := "ha-2-4-2"
%%%

:::proposition "ha_2_4_2_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCat_sHom_kanComplex")
*HA 注意 2.4.2.7*　Monoid Objects (p. 294)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=294)）。対応表の状態：一部（component）。

*主張*　対称モノイダル ∞ 圏 $`C` は、その反対圏 $`C^{\mathrm{op}}` 上に収縮可能な選択のもとで対称モノイダル構造を定める。

KB-W2型再照合：仮定：小さい準圏と、関手単体集合の core で豊穣化した単体圏（HA の最初の模型と一致）。結論：写像空間が Kan であり、その単体圏の nerve が Cat∞ を与える部分に一致。位相実現の nerve との比較と反対圏の対称モノイダル構造は型に含まれない。

対称モノイダル構造を $`\mathrm{Cat}_\infty` の可換モノイド対象と見なし、反対圏を取る自己同値を合成する。その自己同値は写像対象として用いる単体集合の幾何学的実現と反対の比較を使って構成できる。

:::

# 2.4.3 CoCartesian Symmetric Monoidal Structures

%%%
number := false
tag := "ha-2-4-3"
%%%

*monoidal-prl.html — 1. 対称モノイダル ∞ 圏の定義*

1 圏の対称モノイダル圏は、$`\otimes`・単位・結合子・単位子・対称子と、有限個の整合性図式（五角形・六角形、Mac Lane）で定義される。∞ 圏では図式が「ホモトピーで埋まる」になり、そのホモトピーにも整合性が要って条件が無限に続くので、手では書けない。

*定義*（HA Def. 2.0.0.7）．$`\mathrm{Fin}_*` を有限点付き集合 $`\langle n\rangle=\{\ast,1,\dots,n\}` と点付き写像の圏とする。対称モノイダル ∞ 圏とは、cocartesian fibration $`p\colon\mathcal C^\otimes\to N(\mathrm{Fin}_*)` で Segal 条件
$$`\mathcal C^\otimes_{\langle n\rangle}\ \xrightarrow{\ \sim\ }\ (\mathcal C^\otimes_{\langle1\rangle})^n`
（inert 写像 $`\rho^i\colon\langle n\rangle\to\langle1\rangle` に沿う輸送）を満たすもの。$`\mathcal C:=\mathcal C^\otimes_{\langle1\rangle}` が台。

- データ　／　$`\mathrm{Fin}_*` での表れ
- $`n` 個の対象の組　／　$`\langle n\rangle` 上の fiber
- テンソル積 $`\otimes`　／　$`\langle2\rangle\to\langle1\rangle`（$`1,2\mapsto1`）に沿う輸送
- 単位　／　$`\langle0\rangle\to\langle1\rangle` に沿う輸送
- 結合律・可換律と全ての高次整合性　／　$`\mathrm{Fin}_*` の写像の合成と、輸送の関手性

straightening すると、対称モノイダル ∞ 圏は Segal 条件を満たす関手 $`\mathrm{Fin}_*\to\mathrm{Cat}_\infty`、すなわち $`\mathrm{Cat}_\infty` の中の $`E_\infty` モノイドである。Segal の $`\Gamma` 空間と同じ発想で、整合性の問題を $`\mathrm{Fin}_*` からの関手的な輸送に押し付けている（補章 2 の cocartesian fibration と $`\mathrm{Cat}_\infty` 値関手の対応）。

# 2.4.4 Wreath Products

%%%
number := false
tag := "ha-2-4-4"
%%%

:::lemma_ "ha_2_4_4_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianFibration_innerHorn_preimage_isPrecompositionEquivalence, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence.isQCatEquivalence")
*HA 補題 2.4.4.6*　Wreath Products (p. 307)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=307)）。対応表の状態：一部（stronger-hyp）。

*主張*　$`C\to\Delta^n` の $`i-1` 上のすべての対象が $`i` 上へ余デカルト辺を持つなら、内角 $`\Lambda_i^n` の逆像の $`C` への包含は圏論的同値である。

KB-W2型再照合：仮定：標準単体と内ホーン、および単体への余デカルト・ファイブレーション（Lean が強い：指定の一辺だけでなく、射全体が余デカルト・ファイブレーション）。結論：内ホーン逆像の包含の前合成同値性と準圏間での準圏同値性（この場合に HA と一致）。

$`0<i<n` を仮定する。対象ごとの余デカルト移送が、内角から外れた部分を加えるときに必要な比較を与える。

:::

