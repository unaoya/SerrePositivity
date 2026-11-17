# Codex 作業指示書 BS-W9：E3 を消す設計（A0〜A9・∞ 層の一般論・drafts の骨組み）のレビュー

作成：2026-11-02（BS 作業チャット）。宛先：Codex。**読んで報告するだけの作業**で、Lean のビルドもコードの修正もしない。
基準コミット：main `1d98cf0e2`（設計書と骨組みはこの時点のもの）。

## 0. 前提と方針

- 対象は `formalization-plans/bhatt-scholze/` の設計書と `formalization-plans/bhatt-scholze/drafts/` の骨組み（Lean、ビルドしていない）、
  および `exposition/ja/bs/` のノート。原典は `paper/refs/BS-prisms-author.pdf`（Bhatt–Scholze, Prisms and prismatic cohomology, 著者版）。
- **やってよいこと**：読む、原典と突き合わせる、紙で確かめる、報告ファイルを書く。
- **やってはいけないこと**：`lake build`・`lake env lean` などビルドの一切、`SerrePositivity/`・`exposition/`・`drafts/`・設計書の編集、
  新しいファイルの作成（報告ファイル一本を除く）、`git add -A`・`git commit -a`。
- 報告ファイル：`formalization-plans/bhatt-scholze/reports/review-codex-w9.md`（新規、日本語）。コミットは
  `git add -- formalization-plans/bhatt-scholze/reports/review-codex-w9.md && git commit -m "docs(bs): Codex review W9 (part N)"` の形で、報告ファイルだけ。
- この設計の立場（ユーザーの決定、2026-11-02）：**定義は原典どおり**（site・RΓ・envelope の普遍性・Def 8.2 の定義域など。計算用の模型を定義に
  すり替えない）、**定理は E3 に要る特別な場合だけ証明してよい**、避けられない差は D 番号で明示して相談する。レビューもこの立場で行う：
  「原典と違う定義になっていないか」「D 番号なしに差が入っていないか」「特別な場合への制限が E3 の経路を壊していないか」。
- 言葉：E3 = 唯一の perfectoid 側の引用 `BhattScholze.Inputs.exists_perfectoidizationInterfaceE3`（`SerrePositivity/BhattScholze/Inputs/PerfectoidizationInterface.lean:52`）。
  界面の型は `SerrePositivity/BhattScholze/Perfectoidization/Derived/Interface.lean`（D(R) 版）と `SerrePositivity/EInfinity/Perfectoidization/Interface.lean`（CAlg 版）。
  A0〜A9 は E3 を原典の経路で消す作業単位（A0 site、A1 HT 比較、A2 導来 Δ、A3 semiperfectoid、A4 Def 8.2、A5 Prop 8.5、A6 arc 降下と excision、
  A7 Prop 8.13・Cor 8.14、A8 §10、A9 組み立て）。S1〜S8 は ∞ 層の一般論。G-Ak-n は各単位が要る一般補題。D 番号は原典との差（全章で通し番号）。

## 1. 読む順と対象

まず全体像：
1. `formalization-plans/bhatt-scholze/design/design-status.md`（単位の一覧、要確認の分類、決定の所在、調整役の返答）。
2. `formalization-plans/bhatt-scholze/drafts/README.md`（骨組みの規約と置き場所）。
3. `exposition/ja/bs/index.html` と各章（`04-site`・`05-hodge-tate`・`07-semiperfectoid`・`08-perfection`・`10-almost`）の「原典の項目一覧」「原典との差の評価」。

次に単位ごとに「設計書 → 原典の該当ページ → 骨組み」の順で：

| 段 | 設計書 | 原典（著者版のページ） | 骨組み（drafts/） |
| --- | --- | --- | --- |
| I | `infinity-sheaves-design.md`（S1〜S7） | §4 脚注 10、Not 4.16 | `Sheaves/{SheafCondition,GlobalSections,CechConerveLimit,CAlgValued}.lean` |
| I | `a0-design.md` | §3（Def 2.42、Lemma 3.7、Cor 3.12、Prop 3.13）、§4.1・4.3 | `A0/{PrismaticSite,PrismaticEnvelope,CechAlexander}.lean` |
| I | `a1-design.md`（§9 の A1-5 を含む） | §4.2、§5、§6（pp.45–54） | `A1/{HodgeTateMap,HodgeTateComparison,DeRhamComparisonPoly}.lean`、`Shared/{CosimplicialCupProduct,CosimplicialBockstein,DeRhamPolynomial,CosimplicialEInfinity}.lean` |
| I | `a2-design.md` | §7.2 Construction 7.6（pp.56–57） | `A2/*.lean`、`DerivedGeneral/{Truncation,CompletionFunctor}.lean` |
| I | `a3-design.md` | §7（pp.55–62） | `A3/{DiscreteCase,LciAndQuasiregular}.lean` |
| II | `a4-design.md` | §8.1 前半（pp.63–64） | `A4/{Perfectoidization,InterfaceFields}.lean`、`Shared/EInfinityPowerOperation.lean` |
| II | `a5-design.md` | §8.1 後半（pp.64–66）、Rem 4.6、Lemma 4.8 | `A5/*.lean`、`Shared/Descendable.lean` |
| II | `a6-design.md` | §8.2（pp.67–69） | `A6/*.lean`、`Sheaves/SpaceValued.lean` |
| II | `a7-design.md` | Prop 8.13、Cor 8.14（pp.69–70） | `A7/*.lean` |
| III | `a8-design.md` | §10（pp.78–83） | `A8/*.lean` |
| III | `a9-design.md` | — | `A9/Assembly.lean` |

段 I・II・III の終わりが「止めて報告」の点（§4）。

## 2. レビューの観点

各単位について次の六点を見る。見つけたことは §5 の形式で報告ファイルに書く。

- **A. 原典との忠実性**：定義（site、位相、O_Δ、RΓ、envelope、Def 8.2、arc 被覆、descendable、J-almost など）が原典の定義と同じか。
  違うなら D 番号で設計書に記録されているか。設計書の D 表にない差（暗黙の差）がないか。「特別な場合の定理」への制限が、下流（E3 の欄）で
  要る一般性を失っていないか（例：S 離散への制限 D45 と、A7 で animated が要ること D60 の整合）。
- **B. 数学的な正しさ**：設計書の「証明の筋」（各 §3）が原典の証明と一致するか、省略・飛躍・循環がないか。特に各設計書の「紙で確かめる項目」
  （各 §8 など）を**実際に紙で確かめ**、確かめられたもの・反例や疑義があるものを分けて報告する。単位間の依存が循環していないか
  （例：A5-2 が A7 の Prop 8.13 を使わないこと、A8 が A5〜A7 を使う向き、A1-5 が A1-4 の装置だけで閉じること）。
- **C. 単位間の整合**：同じ対象の名前・仮定（離散／animated、p 完備／非完備、κ の取り方、基底 prism の種類）が設計書と骨組みで一致しているか。
  E3 の欄の型（Interface.lean の `PerfectoidizationInterfaceCAlg` の八欄）と、それを供給する骨組みの主張（`e3Perfd`・`e3Unit`・`e3H0RingData`・
  `e3Universal`・`e3LimitCone`・`e3LimitCone_isLimit`・`e3Integral`・`e3Excision`）の型が合うか。D41（非完備 S は S^∧ 経由）が全欄で一貫しているか。
- **D. 一般論の切り出し**：G-Ak-n と S1〜S8 が過不足なく挙がっているか（同じ補題が別名で重複していないか、使っているのに表にない一般論がないか）。
  置き場所（調整役の決定 M12〜M15 など）と内容が合うか。
- **E. 骨組みの形**：Lean の主張の型が、将来の中身に対して妥当か（宇宙、暗黙の仮定、`True` の置き場が「主張を書くべき箇所」になっていないか、
  `sorry` の理由が書かれているか、import 予定のモジュールが設計と合うか）。docstring の「概要／方針／規約／使われ方」が設計書と矛盾しないか。
  **修正はしない**。指摘だけ。
- **F. ノートとの整合**：`exposition/ja/bs/` の項目一覧・差の評価が設計書の最新の決定と合うか（例：第 8 章の Prop 8.10 の行、第 10 章の Thm 10.9 の行）。

## 3. 特に見てほしい論点

設計の中で判断が入った箇所。それぞれ「妥当」「疑義（理由）」「代案」のいずれかで答えてほしい。

1. **β と D-S1**（infinity-sheaves-design §0・§2）：RΓ := Γ(F^♯) を全前層に定義する β、Čech 層（HTT 6.2.2.6）と hypersheaf のずれ。離散な層で
   ずれが消えるという説明は正しいか。A5・A6 で使う層（O_Δ、arc の O、F_T）はすべてその範囲か。
2. **κ の切り落とし**（II-a、D16、D47）：site を κ-small にし、E3 の Type u の添字圏との一致を弱始対象の Čech 余脈体（S3）で取る。S3 の補題
   （弱終対象の Čech 余脈体の Tot が任意の前層の極限を計算する）の主張と、Perfd_{S/} の余積が (T₁ ⊗̂_S T₂)_perfd であることの確認（a5-design §8 の 1）。
3. **A0 の cechKernel と envelope**（a0-design §5.1）：Prop 3.13 の envelope を普遍性で定義し変数の場合だけ存在を示す。Čech–Alexander の核を
   導来 p 完備化の H⁰ で取る理由。Lemma 3.7(2) の自由加群の場合。
4. **A1 の結晶の黒箱**（a1-design §3・§9、D25・D68・D69）：黒箱を Thm 5.2 β の de Rham 形一つにし、HT（Cor 5.5）を Cartier で導く案。
   Thm 6.4 の多項式・mod p の場合を Prop 6.2 の経路（A_0、Construction 6.1、Lemma 4.20）で帰着する案。Frobenius 捻りと底変換の両立（a1 §9.5 の 1）。
5. **A2 の P_Σ と HT filtration**（a2-design、D31〜D35）：Δ を多項式代数からの sifted 余極限保存延長で定義し、HT filtration を τ^{≤i} の Kan 延長で、
   gr を (∧^i L)^∧ の**定義**にする（D33）。これが原典の Construction 7.6 の読みとして妥当か。
6. **A3 の Lemma 7.7(1) の特別な場合**（D36）と **D37・D38**（Prop 7.2 不要、Prop 7.11 に揃えない）：A5・A8 で Prop 7.2 や Prop 7.11 が暗黙に要らないか。
7. **A4 の Lemma 8.4**：P⁰（Lur11 Rem 2.2.7）の使い方（levelwise Frobenius が Tot の P⁰ を誘導すること、Δ_perf/p で P⁰ 可逆）。
   H⁰(Δ_perf) の完全 δ 環性の議論（A3 の (1′) の仮定が満たされるか）。
8. **A5 の Prop 8.5 の四段**（a5-design §3）：(1) ω 段の S̃ の性質 (i)〜(iv)、(2) filtered 余極限（Tot と完備化の順序）、(3) Lemma 8.6 による
   両辺の降下（右辺の左随伴の始性と極限の交換）、(4) semiperfectoid の場合（**G-A5-17**：原典 Prop 7.10 の証明の「余接複体が変わらないので
   Δ も変わらない」の導来版。HT filtration と両立する比較写像の構成が本当に取れるか）。Lemma 8.6 の証明（n = 1 への帰着、(p, φ^{-1}(d)) の底変換、
   一変数 Cartier の形式性、dg 加群の計算 (∗)）。
9. **A6 の arc site と S8**（a6-design §2.4・§3.2・§9・§10）：affine（affCompl_κ ⊃ affPerfd_κ）で閉じる確認表 §9、集合の層の等式の「ほどき」
   （§3.2 の 3）、空間の層への持ち上げに S8 が要るという判断（E 値の Tot で直接ほどく代案が本当に無いか）、Prop 8.10 の tilt の帰着
   （R^♭[1/d] の項の完備化、付値環の tilt・untilt）。三つの引用（BS17 Thm 4.1、BM18 Thm 1.7、BS17 Lemma 6.2/6.3）の主張の形が原典の引用と合うか。
10. **A7 の D60**：Def 8.2 を animated の定義域に戻す必要（Cor 8.14 の X = S_perfd ⊗̂^L_S S_perfd）、Prop 8.13 の相対テンソル版の導出、
    Cor 8.14 の一意性の議論（X → X_perfd と Prop 8.13 の同値の合成が乗法になること）。
11. **A8 の D63**：Thm 10.9 の J-almost 連結性を原典 (1)(2) だけで示す簡略化が正しいか（Galois 構造を使わずに済む理由、J-almost ⇔ 生成元ごと、
    S′ の構成と Cor 8.12 の前提）。Thm 10.11 の帰納（層別の底変換、整閉包 S′ の近似、D64）。Lemma 10.12 の筋（noetherian 近似、全商環、広げ）。
12. **A9**：八欄の供給と `nonempty_e3_of_cAlg` だけで E3 が消える構造になっているか。残る引用の一覧（a9-design §3）に漏れがないか。

## 4. 止めて報告する点

段 I（S1〜S7、A0、A1（A1-5 含む）、A2、A3）を読み終えたら、報告ファイルに「第 1 部」を書いてコミットし、**止める**。
続行の指示を受けてから段 II（A4〜A7）、同様に段 III（A8、A9、横断的な事項、§3 の 12 点の総括）。各部で §3 の該当する論点に答える。
致命的な問題（E3 の経路が閉じない、定義が原典と違うのに D 番号がない、循環）を見つけたら、その段の途中でも止めて報告する。

## 5. 報告の形式

報告ファイルは次の構成（各部ごとに追記）：

1. **総括**（5〜10 行）：この部の範囲で、E3 の経路は閉じているか、致命的な問題の有無、主な疑義。
2. **指摘一覧**（表）：番号 ｜ 単位 ｜ 重さ（致命／要修正／要確認／軽微）｜ 場所（ファイル:行、または設計書の §）｜ 指摘（一文）｜ 理由（原典のページや計算）｜ 提案。
   - 致命：E3 の経路が閉じない、定義が原典と違う（D 番号なし）、証明の筋に循環や誤り。
   - 要修正：設計書や骨組みの記述の誤り・不整合で、直せば済むもの。
   - 要確認：紙で確かめたが決着しなかったもの、原典の読みが分かれるもの。
   - 軽微：記法・名前・docstring の不一致。
3. **紙で確かめた項目**：各設計書の「紙で確かめる項目」ごとに、確かめた結果（○／×／未）と要点（×なら反例や抜け）。
4. **§3 の論点への回答**：番号ごとに「妥当」「疑義」「代案」と理由。
5. **ユーザーに決めてもらう事項**：レビューの結果、設計の変更を要する判断があれば、選択肢と推奨を添えて箇条書き。
6. **確認済み（問題なし）の一覧**：読んで問題がなかった単位・項目。短く。

提案は文章で書く（diff や Lean の修正案を書いてもよいが、ファイルには適用しない）。原典を引くときはページ番号と項目番号（Prop 8.5 など）を添える。

## 6. 受入条件

- 報告ファイル以外に差分がない（`git status --short` で確認）。
- 各部のコミットが報告ファイルだけを含む。
- §3 の 12 点すべてに回答がある（第 3 部の終わりまでに）。
- 「紙で確かめる項目」の全件に結果が付いている。
