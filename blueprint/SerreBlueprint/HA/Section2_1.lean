-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.BaseChange
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftFibrationFiberReflection
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.RelativeFunctor
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA 2.1 Foundations" =>
%%%
number := false
tag := "ha-2-1"
%%%

HA 2.1 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

*monoidal-prl.html — 5. 1 圏との比較*

- 　／　1 圏　／　∞ 圏
- 対称モノイダル構造の定義　／　データ + 有限個の整合性図式（Mac Lane）　／　$`\mathrm{Fin}_*` 上の cocartesian fibration + Segal 条件
- 整合性の扱い　／　五角形・六角形を確かめる　／　$`\mathrm{Fin}_*` の関手性に押し付ける（straightening）
- $`\mathrm{Pr}^L` のテンソル積　／　局所表示可能圏の 2 圏で同様に存在　／　同様だが、$`D(R)` を三角圏ではなく正しく扱える
- 存在の証明　／　表現可能性　／　表現可能性 + Lurie–Simpson による局所化の記述

原典との違い

- HA §4.8.1 は、$`K`-余極限を持つ ∞ 圏の ∞ 圏 $`\mathrm{Cat}_\infty(K)` に、$`K`-余極限を各変数ごとに保つ関手を多重射とする対称モノイダル構造を入れ、$`\mathrm{Pr}^L` をその部分として扱う。§2 の「局所化の直積を局所化する」構成は、presentable の場合の見通しとして書いたもの。

- 対称モノイダル ∞ 圏の定義は HA Def. 2.0.0.7。Segal の $`\Gamma` 空間との類似は HA 第 2 章の導入にもある。

このリポジトリとの対応（既出の宣言のみ）

- このページの既存の章には、対称モノイダル構造・∞ operad・$`\mathrm{CAlg}` の記述はない。§1 の定義に使う cocartesian fibration は第 3 章の \`CocartesianFibrationInfinity B\`（F1/CocartesianFibrationInfinity）、$`\mathrm{Cat}_\infty` は \`CatInfinity\`。

- $`\mathrm{Pr}^L/\mathrm{Pr}^R` は第 6 章の時点で作業中（P-1 b〜g）。

*sixff-foundations.html — ∞-オペラドと対称モノイダル構造*

⊗ の結合性・可換性の無限個の高次ホモトピーも、straightening で一つのファイブレーションに押し込む。

- *対称モノイダル ∞-圏*：余デカルトファイブレーション p: C\^⊗ → Fin\_\*（有限点付き集合）で、⟨n⟩ 上のファイバーが Cⁿ になる（Segal 条件）もの。能動射 ⟨2⟩ → ⟨1⟩ 上の余デカルト持ち上げが ⊗ を与える。Cat\_∞ の中の可換モノイドと言っても同じ。

- *∞-オペラド*：余デカルト持ち上げの存在を inert 射（成分の射影）に限って要求する。多重射が扱える。

- *lax 対称モノイダル関手*：inert 余デカルト射だけを保つ写像。六関手では D(X) × D(Y) → D(X × Y)（外部積 ⊠）が同値である必要がないので、ちょうど lax が必要な一般性。

- *形式化*：Fin\_\* の inert / 能動射の組合せ論は軽い。重いのは straightening と Segal 条件の扱い。

# 2.1.1 From Colored Operads to ∞-Operads

%%%
number := false
tag := "ha-2-1-1"
%%%

*monoidal-prl.html — 1. 対称モノイダル ∞ 圏の定義 — ∞ operad と表現可能性*

cocartesian 持ち上げを inert 写像についてだけ要求したものが ∞ operad で、多重射の空間 $`\mathrm{Mul}(X_1,\dots,X_n;Y)` を持つ。対称モノイダルとは、多重射が表現可能であること：
$$`\mathrm{Mul}(X_1,\dots,X_n;\ Y)\ \simeq\ \mathrm{Map}(X_1\otimes\cdots\otimes X_n,\ Y).`

*route-6ff-definition.html — 10. (e) ∞ operad と lax 関手の正確な定義*

*なぜ要るか*：lax 関手の構造写像 $`F(X)\otimes F(Y)\to F(X\otimes Y)` は可逆とは限らず、$`\mathrm{Fin}_*` 上の写像としては一部の cocartesian 辺しか保たない。どれを保つかを指定するには「一部の射についてだけ cocartesian 持ち上げがある」ものを扱う枠組みが要る。それが ∞ operad。

*route-6ff-definition.html — 10. (e) ∞ operad と lax 関手の正確な定義 — 10.1 $`\mathrm{Fin}_` の二種類の射*

- 種類　／　条件　／　例　／　意味
- inert　／　各 $`j\neq\ast` で $`\alpha^{-1}(j)` がちょうど一点　／　射影 $`\rho^i\colon\langle n\rangle\to\langle1\rangle`　／　成分を選ぶ・捨てる
- active　／　$`\alpha^{-1}(\ast)=\{\ast\}`　／　$`\langle2\rangle\to\langle1\rangle`（$`1,2\mapsto1`）　／　成分をまとめる

全ての射は inert と active の合成に（同型を除き一意に）分解する（要らない成分を捨ててから残りをまとめる）。

*route-6ff-definition.html — 10. (e) ∞ operad と lax 関手の正確な定義 — 10.2 ∞ operad（HA Def. 2.1.1.10）*

内ファイブレーション $`p\colon\mathcal O^\otimes\to N(\mathrm{Fin}_*)` で：

- *inert の cocartesian 持ち上げ*：inert $`\alpha\colon\langle m\rangle\to\langle n\rangle` と $`\langle m\rangle` 上の $`X` に $`p`-cocartesian 辺 $`X\to\alpha_!X` がある。

- *ファイバーの Segal 条件*：$`\rho^i` に沿う輸送が $`\mathcal O^\otimes_{\langle n\rangle}\xrightarrow{\sim}(\mathcal O^\otimes_{\langle1\rangle})^n`。

- *写像空間の Segal 条件*：$`\langle m\rangle` 上の $`Y` と成分への cocartesian 辺 $`Y\to Y_j` について $`\mathrm{Map}^f(X,Y)\xrightarrow{\sim}\prod_j\mathrm{Map}^{\rho^j\circ f}(X,Y_j)`（組への射は各成分への射の組）。

台は $`\mathcal O=\mathcal O^\otimes_{\langle1\rangle}`、$`\langle n\rangle` 上の対象は組 $`(X_1,\dots,X_n)`、多重射の空間は $`\mathrm{Mul}_{\mathcal O}(X_1,\dots,X_n;Y):=\mathrm{Map}^{\mathrm{active}}((X_1,\dots,X_n),Y)`。

*route-6ff-definition.html — 10. (e) ∞ operad と lax 関手の正確な定義 — 10.3 対称モノイダル ∞ 圏との関係*

対称モノイダル ∞ 圏 = ∞ operad で $`p` が cocartesian fibration であるもの（補章 5 の定義と一致：cocartesian fibration なら条件 3 は条件 2 から従う）。違いは active 射の cocartesian 持ち上げの有無で、$`(X,Y)\to X\otimes Y` の存在は $`\mathrm{Mul}(X,Y;-)` が $`X\otimes Y` で表現されること。

# 2.1.2 Maps of ∞-Operads

%%%
number := false
tag := "ha-2-1-2"
%%%

*route-6ff-definition.html — 10. (e) ∞ operad と lax 関手の正確な定義 — 10.4 lax 関手（HA Def. 2.1.2.7）*

∞ operad の写像は $`N(\mathrm{Fin}_*)` 上の写像 $`F\colon\mathcal O^\otimes\to\mathcal O'^\otimes` で、*inert の上の cocartesian 辺を cocartesian 辺に送る*もの（全体を $`\mathrm{Alg}_{\mathcal O}(\mathcal O')`）。inert の cocartesian 辺は「組から成分を取り出す」射なので、これを保つことで組を組 $`(FX_1,\dots,FX_n)` に送る（保たなければ成分が混ざりうる）。active の上の射（多重射）は多重射に送るだけで条件はない。全ての cocartesian 辺を保つものが（強い）対称モノイダル関手。

*route-6ff-definition.html — 10. (e) ∞ operad と lax 関手の正確な定義 — 10.5 lax の構造写像の取り出し方*

- active 射 $`\langle2\rangle\to\langle1\rangle` の上の cocartesian 辺 $`c\colon(X,Y)\to X\otimes Y` を取る。

- $`F(c)\colon(FX,FY)\to F(X\otimes Y)` は active 射の上の辺（cocartesian とは限らない）。

- $`\mathcal O'^\otimes` の cocartesian 辺 $`(FX,FY)\to FX\otimes FY` の普遍性で、$`F(c)` は（可縮な選択を除き一意に）$`FX\otimes FY\to F(X\otimes Y)` を経由する。これが構造写像。単位は $`\langle0\rangle\to\langle1\rangle` の上の $`\ast\to\mathbf 1` から $`\mathbf 1'\to F(\mathbf 1)`。

1 圏の lax モノイダル関手では $`\mu,\eta` と結合性・単位性の図式を確かめたが、∞ 版ではそれらの整合性は全て「$`F` が $`\mathrm{Fin}_*` 上の写像である」ことに含まれる。

- 例　／　内容
- $`E_\infty` 代数　／　可換 operad は $`N(\mathrm{Fin}_*)` 自身。$`\mathrm{Alg}_{N(\mathrm{Fin}_*)}(\mathcal C^\otimes)=\mathrm{CAlg}(\mathcal C)`
- 右随伴　／　対称モノイダルな左随伴の右随伴は自動的に lax（HA Cor. 7.3.2.7）：$`f_*A\otimes f_*B\to f_*(A\otimes B)`
- 六関手形式　／　$`D\colon\mathrm{Corr}(\mathcal C,E)^\otimes\to\mathrm{Cat}_\infty^\times`。構造写像 $`D(X)\times D(Y)\to D(X\times Y)` が $`\boxtimes` で、同値ではない（$`D(X\times Y)` はずっと大きい）ので strong でなく lax でなければならない

- 概念　／　定義　／　要点
- inert / active　／　$`\alpha^{-1}(j)` が一点 / $`\alpha^{-1}(\ast)=\{\ast\}`　／　成分を選ぶ / まとめる
- ∞ operad　／　内ファイブレーション、inert の cocartesian 持ち上げ、二つの Segal 条件　／　多重射の空間 $`\mathrm{Mul}`
- 対称モノイダル ∞ 圏　／　∞ operad で cocartesian fibration　／　多重射が $`\otimes` で表現される
- lax 関手　／　$`\mathrm{Fin}_*` 上の写像で inert の cocartesian 辺を保つ　／　組を組に、多重射を多重射に
- 構造写像　／　active の cocartesian 辺の像を普遍性で分解　／　$`FX\otimes FY\to F(X\otimes Y)`

前提：内ファイブレーション、cocartesian 辺（補章 6）、$`\mathrm{Fin}_*` の組合せ論。定義を述べるだけなら straightening は不要。

:::definition "ha_2_1_2_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting")
*HA 定義 2.1.2.10*　Maps of ∞-Operads (p. 180)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=180)）。対応表の状態：本体にある。

*主張*　∞ オペラッドの射がファイブレーションであるとは、基礎の準圏の写像が圏論的ファイブレーションであることである。

与えられた同じ∞-operad map qにEquivalenceLifting qを適用すると、全ての単射な圏論的同値に対する右持ち上げ性というcategorical fibration条件をそのまま定義する。∞-operadの存在・構成を別途主張するものではない。

判定は圏論的モデル構造で行うので、内角の持ち上げに加えて同値を持ち上げられることを要求する。

:::

:::definition "ha_2_1_2_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration")
*HA 定義 2.1.2.13*　Maps of ∞-Operads (p. 182)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=182)）。対応表の状態：一部（component）。

*主張*　∞ オペラッド上の余デカルト・ファイブレーションで、慣性射による色ごとの分解がファイバーに積分解を与えるものを、$`O` モノイダル ∞ 圏と呼ぶ。

原文が既に与えた同じp:C⊗→O⊗について、CocartesianFibration pは参照先2.1.2.12の仮定であるcoCartesian fibration条件そのものを直接表す。O⊗の∞-operad構造・その存在は含まない。

2.1.2.12 により、余デカルト・ファイブレーション $`C^\otimes\to O^\otimes` の全体が $`\mathrm{Fin}_*` 上の ∞ オペラッドになることと、各 $`T\simeq\bigoplus_i T_i` のファイバーを $`T_i` 上のファイバーの積で表せることは同値である。

:::

:::proposition "ha_2_1_2_17" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianFibration_pullback_snd")
*HA 注意 2.1.2.17*　Maps of ∞-Operads (p. 182)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=182)）。対応表の状態：一部（component）。

*主張*　$`O` モノイダル ∞ 圏を色の ∞ 圏に制限すると、各色上の対象の圏を値とする $`O\to\mathrm{Cat}_\infty` で分類される余デカルト・ファイブレーションが得られる。

KB-W2型再照合：仮定：余デカルト・ファイブレーション p と底への写像 q（Lean は任意の q を許し、HA では h₁ のファイバーの包含）。結論：底変換が余デカルト・ファイブレーションになる部分に一致する。色別の圏の族を分類する関手 χ と operad 上への延長は型に含まれない。

単項部分で得た分類関手はオペラッドの射へ延び、演算ごとの移送も含む。その拡張で全体の $`O` モノイダル圏を同値まで復元できることを、後の結果が示す。

:::

# 2.1.3 Algebra Objects

%%%
number := false
tag := "ha-2-1-3"
%%%

:::definition "ha_2_1_3_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorSpace, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorPredicate_vertex")
*HA 定義 2.1.3.7*　Algebra Objects (p. 185)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=185)）。対応表の状態：一部（component）。

*主張*　同じ $`O^\otimes` 上のモノイダル ∞ 圏の間のモノイダル関手は、すべての相対余デカルト辺を保つオペラッドの射である。

原文で既に∞-operad mapである同じfを入力すると、cocartesianRelativeFunctorPredicate\_vertexは同じfの全p-coCartesian辺の保存というO-monoidal条件を直接判定する。任意の底上写像がoperad mapとなることとAlg内部の全構成はこの引用では含まない。

この条件を満たす関手の充満部分圏を $`\operatorname{Fun}_O^\otimes(C,D)` とする。$`O^\otimes=N(\mathrm{Fin}_*)` の場合には対称モノイダル関手という。

:::

:::proposition "ha_2_1_3_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibration_isQCatEquivalence_iff_fibers")
*HA 注意 2.1.3.8*　Algebra Objects (p. 185)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=185)）。対応表の状態：一部（stronger-hyp）。

*主張*　$`O` モノイダル関手が同値であることは、基礎の圏の間で同値であること、または全ての色のファイバーで同値であることと同値である。

同じ色の∞圏の射影C→O,D→Oにleft fibrationも追加すると、leftFibration\_isQCatEquivalence\_iff\_fibersは同じ基礎関手の(2)⇔(3)を直接返す。全空間の(1)と追加条件のない場合は含まない。

余デカルト移送の保存と色ごとの積分解によって、色での同値から全てのファイバーでの同値が従う。単なるオペラッドの射にまでこの判定を広げることはできない。

:::

