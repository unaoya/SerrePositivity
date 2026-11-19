import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveIdempotence
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveUnitInvertible
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA 4.8 Tensor Products of ∞-Categories" =>
%%%
number := false
tag := "ha-4-8"
%%%

HA 4.8 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 4.8.1 Tensor Products of ∞-Categories

%%%
number := false
tag := "ha-4-8-1"
%%%

*f-06-straightening.html — 9. presentable の状況と $`\mathrm{Pr}^L` のモノイダル構造*

- 項目　／　10-23 時点　／　10-28 時点
- $`\mathrm{Cat}_\infty` の写像空間、引き戻し、lax pullback　／　完成　／　済
- filtered 余極限と有限極限の交換（HTT 5.3.3.3）　／　未完成（仮定として取る定理あり）　／　明記なし
- $`\mathrm{Ind}_\kappa`　／　完成　／　済
- $`\mathrm{Ind}` の安定性　／　未完成　／　ind\_isStable\_unconditional が済
- κ-compact、compact 生成、冪等完備化　／　ほぼ完成・完成　／　済
- accessible　／　完成　／　—
- presentable の定義、Bousfield 局所化　／　作業中　／　IsPresentable、bousfieldReflection が済
- 随伴関手定理　／　作業中　／　第 5 章で使う前提
- $`\mathrm{Pr}^L/\mathrm{Pr}^R`、$`\mathcal P_\Sigma`　／　作業中　／　明記なし
- M3〜M6（安定 presentable）　／　—　／　未着手

随伴関手定理（HTT 5.5.2.9）を述べるには、宇宙、$`\mathcal S` と写像空間の関手性（米田）、前層、$`\kappa`-filtered と $`\kappa`-compact、$`\mathrm{Ind}_\kappa`、accessible、presentable が要る。証明にはさらに表現可能性の判定（HTT 5.5.2.2、5.5.2.7）が要り、各点の普遍射による随伴の判定に帰着する。

$`\mathrm{Pr}^L` のモノイダル構造は直積ではない

- $`\mathrm{Pr}^L` は $`\widehat{\mathrm{Cat}}_\infty` の部分圏だが、載せるのは Lurie テンソル積：$`\mathrm{Fun}^L(\mathcal C\otimes\mathcal D,\mathcal E)\simeq` 各変数ごとに余極限を保つ $`\mathcal C\times\mathcal D\to\mathcal E`。単位は $`\mathcal S`。例：$`\mathcal P(A)\otimes\mathcal P(B)\simeq\mathcal P(A\times B)`、$`\mathrm{Mod}_R\otimes\mathrm{Mod}_S\simeq\mathrm{Mod}_{R\otimes S}`。

- $`\mathcal C\times\mathcal D` は $`\mathrm{Pr}^L` の中では双積で、テンソル積とは別（加群の $`\oplus` と $`\otimes` の関係）。

- 多重射は共通：$`\mathrm{Pr}^{L,\otimes}` は直積 ∞ operad $`\mathrm{Cat}_\infty^\times` の充満でない部分 ∞ operad。表現する対象が変わる。包含は lax 対称モノイダルで strong ではない（HA §4.8.1）。

- 六関手形式の定義（Mann、Scholze）は $`\mathrm{Cat}_\infty` の直積構造で足りる。直積構造は HA 2.4.1 の組合せ的な構成で作れ、Cat∞ 値の straightening は要らない。Lurie テンソル積は $`\mathrm{CAlg}(\mathrm{Pr}^L)`、係数の変更、Künneth 型の主張などで要り、presentable の理論の上に立つ。

*monoidal-prl.html — 2. $`\mathrm{Pr}^L` のテンソル積*

$`\mathrm{Pr}^L` の多重射を
$$`\mathrm{Mul}(\mathcal C_1,\dots,\mathcal C_n;\ \mathcal D)\ :=\ \mathrm{Fun}^{L,\dots,L}(\mathcal C_1\times\cdots\times\mathcal C_n,\ \mathcal D)`
（各変数ごとに余極限を保つ関手）と定めると、$`\mathrm{Cat}_\infty` の直積構造の部分 operad として $`\mathrm{Pr}^L` の ∞ operad が得られる。対称モノイダルであることは、次を満たす $`\mathcal C\otimes\mathcal D` の存在である。
$$`\mathrm{Fun}^L(\mathcal C\otimes\mathcal D,\ \mathcal E)\ \simeq\ \mathrm{Fun}^{L,L}(\mathcal C\times\mathcal D,\ \mathcal E).`
ベクトル空間のテンソル積が双線形写像を表現するのと同じ形で、「線形」が「余極限を保つ」に置き換わる。0 項では $`\mathrm{Fun}^L(\mathcal S,\mathcal E)\simeq\mathcal E` なので単位は $`\mathcal S`。

*monoidal-prl.html — 2. $`\mathrm{Pr}^L` のテンソル積 — 構成*

- *前層圏どうし*：§4 の普遍性（補章 4）を各変数と $`A\times B` に使って
  $$`\mathrm{Fun}^{L,L}(\mathcal P(A)\times\mathcal P(B),\mathcal E)\simeq\mathrm{Fun}(A\times B,\mathcal E)\simeq\mathrm{Fun}^L(\mathcal P(A\times B),\mathcal E),`
  よって $`\mathcal P(A)\otimes\mathcal P(B)\simeq\mathcal P(A\times B)`。

- *局所化*：Lurie–Simpson（補章 4 §6）で $`\mathcal C\simeq S^{-1}\mathcal P(A)`、$`\mathcal D\simeq T^{-1}\mathcal P(B)` と書くと
  $$`\mathcal C\otimes\mathcal D\ \simeq\ (S\boxtimes B\ \cup\ A\boxtimes T)^{-1}\,\mathcal P(A\times B).`
  各変数ごとに余極限を保ち $`S`、$`T` を可逆にする関手は、$`s\boxtimes y(b)` と $`y(a)\boxtimes t` を可逆にする $`\mathcal P(A\times B)` からの余極限保存関手と同じだから。テンソル積は局所化の直積をさらに局所化したもの。

- *別の公式*：$`\mathcal C\otimes\mathcal D\simeq\mathrm{Fun}^R(\mathcal C^{\mathrm{op}},\mathcal D)`（HA Prop. 4.8.1.17）。$`\mathcal C=\mathcal P(A)` なら $`\mathrm{Fun}(A^{\mathrm{op}},\mathcal D)`（$`\mathcal D` 値の前層）。

*monoidal-prl.html — 2. $`\mathrm{Pr}^L` のテンソル積 — 例*

- テンソル積　／　結果
- $`\mathcal P(A)\otimes\mathcal P(B)`　／　$`\mathcal P(A\times B)`
- $`\mathrm{Sp}\otimes\mathcal C`　／　$`\mathrm{Sp}(\mathcal C)`（安定化）
- $`\mathrm{Mod}_R\otimes\mathrm{Mod}_S`　／　$`\mathrm{Mod}_{R\otimes S}`
- $`\mathrm{QCoh}(X)\otimes\mathrm{QCoh}(Y)`　／　$`\mathrm{QCoh}(X\times Y)`（perfect stack など適切な条件下、Ben-Zvi–Francis–Nadler）

*monoidal-prl.html — 2. $`\mathrm{Pr}^L` のテンソル積 — 基本的な性質*

- 性質　／　内容
- 単位　／　$`\mathcal S`
- 閉構造　／　内部 Hom は $`\mathrm{Fun}^L(\mathcal C,\mathcal D)`
- 余極限　／　$`\mathcal C\otimes-` は $`\mathrm{Pr}^L` の余極限を保つ（閉構造から）
- 極限　／　一般には保たない。$`\mathcal C` が双対化可能（たとえばコンパクト生成）なら保つ
- 双対　／　コンパクト生成な $`\mathcal C` の双対は $`\mathrm{Ind}((\mathcal C^\omega)^{\mathrm{op}})`

$`\mathrm{Pr}^L` の極限は $`\mathrm{Cat}_\infty` で計算でき、降下は極限で書かれる。そのため「貼り合わせた圏のテンソル積は、テンソル積の貼り合わせか」（Künneth 型の問題）は極限保存の問題になり、双対化可能性で解決される。

# 4.8.2 Smash Products of Spectra

%%%
number := false
tag := "ha-4-8-2"
%%%

:::proposition "ha_4_8_2_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveSubcategory.unitOnLocalizationIso, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveSubcategory.reflectedUnitIso, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveSubcategory.idempotentIso")
*HA 例 4.8.2.3*　Smash Products of Spectra (p. 717)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=717)）。対応表の状態：一部（direction）。

*主張*　合成を積とする自己関手のモノイダル ∞ 圏で、冪等対象は単位 $`\mathrm{id}\to L` を備えた局所化関手に対応する。

KB-W2型再照合：仮定：準圏の頂点述語で切り出した全充満部分準圏への反射的包含と随伴を指定する（Lean が強い：この反射的局所化の場合）。結論：局所化自己関手 L の単位の左右 whisker は関手のホモトピー圏で可逆となり、L²≃L を得る（この仮定での HA の結論の一部に一致）。任意の単位付き自己関手の条件から反射的局所化を回復する逆向きは含まれない。

単位を $`L` の左または右から合成して得る二つの $`L\to L^2` がともに同値となることが条件である。局所化ではこれらが、対象を再び局所化しても変わらないことを表す。

:::

# 4.8.3 Algebras and their Module Categories

%%%
number := false
tag := "ha-4-8-3"
%%%

:::definition "ha_4_8_3_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration")
*HA 定義 4.8.3.1*　Algebras and their Module Categories (p. 724)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=724)）。対応表の状態：一部（component）。

*主張*　$`O` モノイダル ∞ 圏の余デカルト $`S` 族は、$`O^\otimes\times S` 上の余デカルト・ファイブレーションで、各 $`s` での制限が余デカルト・オペラッド・ファイブレーションである。

同じq:C⊗→O⊗×SにCocartesianFibration qを課すのは原文冒頭の全体のcoCartesian条件そのものである。各sで∞-operad fibrationとなる条件とfamily全体の構成は含まない。

固定した $`s` では $`O` モノイダル構造を得る。$`O^\otimes` を結合オペラッドにするとモノイダル ∞ 圏の族となる。

:::

