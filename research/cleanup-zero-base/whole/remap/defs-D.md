# 概念の定義書：D 安定 ∞ 圏と導来 ∞ 圏

小概念は out/remap-*.csv（B・D・F の担当分）の new_subconcept と一致する。ほかの大分類の担当が同じ概念へ送る小概念はここには入っていない。

## D 安定 ∞ 圏と導来 ∞ 圏/Verdier 列

**入るもの**：安定 ∞ 圏の Verdier 列と Verdier 商：列である条件（充満忠実・核・商の普遍性）、coherent な四角形による提示、dg 神経の Verdier 商の分数計算（分母の圏）、cell 分解した dg 商の神経と核。

**入らないもの**：
- 三角圏の Verdier 商は「B/三角圏と t 構造」、Perf の Verdier 商は「B/導来圏と Perf（dg 加群）」へ。
- dg 商そのものと、その H⁰ と Verdier 商の比較は「B/dg 商と cell 分解」へ。
- 零対象・cofiber の一般論は「D/安定 ∞ 圏」へ。
- 準圏の局所化の分数計算（分母付き span の一般論）は「C/局所化（Dwyer–Kan）」へ。
- Tamme 商と差の関手、局所化不変量の定義は「H/lax 引き戻しと局所化不変量」へ。冪等完備化は「C/冪等完備（∞ 圏）」へ。

**小概念**：
- Verdier 列（安定 ∞ 圏）
- Verdier 図式（coherent な四角形による提示）
- dg Verdier 商の分母の圏のフィルター性（分母図式の錐とホーン） — 印：補助

**文献**：小概念の reference に記載なし。

## D 安定 ∞ 圏と導来 ∞ 圏/coherent bar 構成

**入るもの**：dg 神経に値をもつ coherent な図式から Maurer–Cartan 元で作る右 dg 加群（coherent bar 構成）と、それがホモトピー余極限を与えること：正規化、余錐と普遍性、strict な図式の bar 複体との比較、コンパクト性。

**入らないもの**：
- 複体の strict な図式の ∞ 局所化と D(A) の比較は「D/導来 ∞ 圏」へ。
- 一般の ∞ 圏の余極限・余錐は「C/極限と余極限」へ。
- 複体の重みつき end/coend・bar 重みによるホモトピー極限の模型は「B/複体」へ。
- dg 商の収縮元 ε と整合する dg 関手は「B/dg 商と cell 分解」へ。Kan ホモトピー群のチャートは「C/Kan 複体とホモトピー群」へ。
- 非連結 K の段の構成は「H/非連結 K」へ。

**小概念**：
- coherent bar 構成の κ コンパクト性と懸垂作用 — 印：補助
- coherent bar 構成（dg 加群の図式のホモトピー余極限）
- coherent bar 構成と strict な図式の bar 複体の比較（次元フィルター） — 印：補助
- coherent bar 構成の余錐の持ち上げ（join の添字と座標） — 印：補助

**文献**：
- HA 1.3.1（dg 神経）・HTT 4.2.4 に対応する余極限の計算

## D 安定 ∞ 圏と導来 ∞ 圏/dg の貼り合わせ

**入るもの**：双加群に沿う dg 圏の貼り合わせ圏そのもの（対象、Hom 複体、cone とシフト、因子の部分圏、comma 表示、dg 関手の comma 圏）、dg 代数の Milnor 四角形、貼り合わせの dg 神経と ∞ 圏の lax 引き戻しの比較定理。

**入らないもの**：
- ∞ 圏の lax 引き戻しの定義、Cat^perf、差の関手と Tamme 商、Land–Tamme の ⊙ の dg 模型（dgHomGluing*・DGOdotInput）は「H/lax 引き戻しと局所化不変量」へ。
- 双加群そのものとテンソルは「B/双加群とテンソル」へ。
- dg 前三角性の定義は「B/dg 加群」へ（貼り合わせが前三角であるという主張はここ）。
- dg 代数のホモトピー引き戻しの模型・path 対象は「B/dg 代数のホモトピー論」へ。
- 安定 ∞ 圏の半直交分解の一般論は「D/安定 ∞ 圏」へ。

**小概念**：
- Milnor 四角形
- 貼り合わせの comma 表示と代表加群
- dg 貼り合わせ圏（対象と Hom 複体）
- 因子の部分圏と引き戻し部分圏
- 貼り合わせの dg 神経と lax 引き戻しの比較
- 貼り合わせの cone とシフト
- Hom 複体と lax 写像空間の比較：合成対応と入力 fiber — 印：補助
- Hom 複体と lax 写像空間の比較：単位補正・正規化の三角形と cube の族 — 印：補助
- dg 関手の comma 圏

**文献**：
- Kuznetsov–Lunts の gluing、Land–Tamme の lax 引き戻しの dg 模型
- 半直交分解
- Land–Tamme（lax pullback）

## D 安定 ∞ 圏と導来 ∞ 圏/安定 ∞ 圏

**入るもの**：点付き・安定 ∞ 圏の一般論（HA §1.1）：零対象、零角の四角形と fiber・cofiber 列、suspension と loop、安定性の定義と判定、完全関手、ホモトピー圏の三角構造、安定部分圏と半直交分解、安定 ∞ 圏の ∞ 圏。

**入らないもの**：
- 零対象を使わない一般の四角形・pullback・pushout（頂点や辺の取り出しも）は「C/極限と余極限」へ。
- Verdier 列・Verdier 商は「D/Verdier 列」へ。
- 複体や dg 加群の dg 神経での具体的な fiber・cofiber 四角形、dg 神経の安定性は「D/導来 ∞ 圏」へ。
- 三角圏の一般論は「B/三角圏と t 構造」へ。
- 点つき空間の loop・fiber・cofiber は「C/基点付き空間」へ。スペクトルは G へ。
- Cat^perf・局所化不変量の定義は「H/lax 引き戻しと局所化不変量」へ。S• 構成の間の完全関手は「H/S 構成と K スペクトル」へ。

**小概念**：
- cofiber 列とホモトピー圏の三角構造
- suspension と loop
- 安定 ∞ 圏の定義と安定 ∞ 圏の ∞ 圏
- 安定性の判定（pullback と pushout の一致） — 印：補助
- 安定部分圏の閉包と半直交分解
- 完全関手
- 零対象と零角の四角形（点付き ∞ 圏）

**文献**：
- HA §1.1.2（Theorem 1.1.2.14）
- HA §1.1.2
- HA Definition 1.1.1.9、§1.1.4
- HA 1.4.2.15 と記載（Proposition 1.1.3.4 周辺）
- HA §1.1.3、Lemma 1.1.3.3 周辺
- HA §1.1.4
- HA §1.1.1（Definition 1.1.1.1–1.1.1.6）

## D 安定 ∞ 圏と導来 ∞ 圏/導来 ∞ 圏

**入るもの**：dg 神経による導来圏の ∞ 圏の模型：semifree 複体の dg 神経 D(R)、dg 圏上の加群の導来 ∞ 圏、Perf の ∞ 圏模型、複体の dg 神経 N_dg(Ch) の中の写像空間・fiber 四角形・cofiber 四角形、複体の strict な図式の ∞ 局所化（相対圏）と D(A) の比較、ホモトピー圏と通常の導来圏の比較。

**入らないもの**：
- dg 神経の一般の構成（任意の dg 圏の単体・Hom 空間）は「C/dg 神経」へ。
- 三角圏としての D(D)・Perf は「B/導来圏と Perf（dg 加群）」へ。厳密な水準の加群・分解は「B/dg 加群」へ。
- dg 加群の図式のホモトピー余極限の計算（coherent bar）は「D/coherent bar 構成」へ。
- 安定性の一般論は「D/安定 ∞ 圏」へ。
- dg 関手の comma 圏と貼り合わせは「D/dg の貼り合わせ」へ。
- K 理論の入力としての小さい Perf は「H/S 構成の入力（安定モデル・小さい Perf）」へ。E 代数上の加群の導来 ∞ 圏は「F/E∞ 代数の圏（CAlg と加群）」へ。
- pinched Hom の一般論は「C/写像空間」へ。

**小概念**：
- Perf の ∞ 圏模型（射影的 perfect dg 加群の dg 神経）
- N_dg(Ch) の写像空間と錐の計算（正規化テンソルの要素圏） — 印：補助
- 複体の dg 神経での fiber 四角形と cofiber 四角形
- dg 圏上の加群の導来 ∞ 圏
- 複体の semifree 分解（導来 ∞ 圏の頂点として）
- 複体の pinched 写像空間模型
- 複体の導来 ∞ 圏（semifree 複体の dg 神経）
- kernel の作用の ∞ 圏版（相対 K-flat 加群の dg 神経）（「B/双加群とテンソル」の今の小概念「kernel の導来作用と ∞ 圏版」から定義ごとに分かれて来る分）

**文献**：
- HA §1.3.2（Proposition 1.3.2.10）
- HA §1.3.5 の dg 圏版（Keller の導来圏）
- HA Definition 1.3.5.8、§1.3.2
