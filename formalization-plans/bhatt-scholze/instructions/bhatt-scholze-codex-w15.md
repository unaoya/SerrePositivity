# Codex 作業指示書 BS-W15：§2・§3・§7 の古典的な残り（⑤c）

作成：2026-11-10（段階 II の調整役）。宛先：⑤c BS 実装の Codex（新しいレーン。worktree `../SerrePositivity-bs-classical`、枝 `math/bs-classical`）。検収：調整役。決定：ユーザー（11-10、「∞ 圏の前にできる §2・§3・§7 の残りを新しいレーンで」）。

## 0. 目標と範囲

Prisms の地図（`research/bs-coverage/items.csv`、https://claude.ai/artifact/YWUyntvwsGb2aX39kZnMyT）で、目標に必要なのに本体の形で足りていない項目のうち、**∞ 圏（D(A) の ∞ 圏としての操作、CAlg、animated ring、∞ 層）なしで示せるもの**を本体に入れる。順序は、⑤b（結晶サイト）が先に使うものから。

| 部品 | 原典 | 内容 | 使う所 |
| --- | --- | --- | --- |
| **K1** | Lemma 2.36、Lemma 2.38、Cor 2.39 | 多変数・r 元の場合：Z_p{x₁..x_r, φ(x)/p} の p ねじれなし、正則列の divided power 包絡の離散性・p ねじれなし・δ 構造・底変換（今は r = 1 だけ。課題 T2-1） | ⑤b の結晶サイト（`drafts/A1/CrystallineSite`・`DeRhamComparisonPoly` の sorry） |
| **K2** | Ex 2.21、Ex 3.4 | 普遍的な distinguished な環 Z_(p){d, δ(d)⁻¹} と、その (p,d) 完備化の向き付き prism（正則性、完備性、p ∈ (d, φ(d))、有界性、Frobenius の平坦性） | A1-4（`drafts/A1/HodgeTateComparison` の `universalOrientedPrism`） |
| **K3** | Def 2.42、Rem 2.37 | 完全に正則な関係（Koszul ホモロジーの形、D20）と、導来 pushout の離散性の代わり（Koszul 正則性、r 元） | A0 の envelope の存在の仮定 |
| **K4** | Lemma 3.7 (2)(3)、Cor 3.12、Prop 3.13 (2)、Ex 3.14 の一般形 | 有界 prism の完全平坦性の一般形、prism のサイト（平坦位相、押し出し）と O_Δ が高次コホモロジーの消える層であること（Čech 複体の完全性として）、envelope の底変換と一般の滑らかな場合 | drafts の A0（BaseChange・PrismaticEnvelope・FlatDescent・PrismaticSite）。Čech–Alexander で RΓ_Δ を計算する部分（G10 待ち）は除く |
| **K5** | Lemma 7.7、Lemma 7.8、Ex 7.9 の envelope の側 | 離散な場合の δ 構造、冪等なレトラクトからの始対象、lci の場合の envelope の計算（p 反転の議論 G-A3-7 を含む）。RΓ_Δ との同一視は G10 の後なので drafts に残す | drafts の A3（DiscreteCase、LciAndQuasiregular の envelope の部分） |

範囲の外：qrsp の定義（Not 7.1。原典どおり余接複体で定義するので animated を待つ）、Constr 7.6・Prop 7.10（導来プリズム・コホモロジー）、Čech–Alexander による RΓ_Δ の計算。

## 1. 段と止めて報告する点

| 段 | 内容 | 止めて報告 |
| --- | --- | --- |
| 段 0 | 1. K1〜K5 の各項目について、本体の既存の宣言（`Delta/`・`Prism/`・`Prismatic/`・`Andre/`。`Prismatic/` の envelope・PrismOver・Čech–Alexander の模型は ⑤b が D68 で作った）と drafts の型を洗い、何が既にあり何を新しく書くかを決める。2. 主張の型の案（drafts の型があればそれ）と置き場所。3. 規模の見込み。4. ⑤b の枝（`math/bs-d68`）の進行中の差分と重ならないかの確認 | **停止点 0**：調整役が確かめる |
| 段 1 | K1 | 停止点 1：取り込む（⑤b に知らせる） |
| 段 2 | K2・K3 | 停止点 2 |
| 段 3 | K4 | 停止点 3 |
| 段 4 | K5 | 停止点 4：BS-W15 の区切り |

- 停止点 0 は承認を待つ。段 1〜4 は BS-W12 §3 と同じ条件（対象のビルドと監査が通り、sorry・公理 0、既存の宣言を変えていない）なら、報告してそのまま次へ進んでよい。取り込みは調整役が停止点ごとに行う。
- drafts の型を変える必要があれば止める。

## 2. 規則

- BS-W11 §6・BS-W12 §4 と同じ：新しい数学は**新規ファイルだけ**（既存のファイルと宣言は変えない）、本体に sorry を残さない、閉じられない宣言は drafts に残す、E3 非依存、入口と監査への登録は調整役、docstring は日本語の 概要／方針／規約／使われ方 と原典の番号（`（BS 著者版 Lemma 2.38 の r 元の場合）` など）、小さなビルドだけ。
- **持ち分**：drafts の `A0/`（Čech–Alexander の `CechAlexander.lean` を除く）と `A3/` は ⑤c が書き換えてよい（⑤a の BS-W14 の段 2 はこの二つを触らない）。ほかの drafts は読むだけ。drafts の中で CAlg_R に触れる所を書き換えるときは、界面 `EInfinityTheory`（`calg-interface-design.md`、D71）を通す形にする。CAlg_R の模型の中身に新しく触れない。
- 置き場所：δ 環と divided power は `BhattScholze/Delta/` の下（既存の `Delta/DividedPower/` の隣に新しいファイル）、prism は `BhattScholze/Prism/`、サイトと envelope は `BhattScholze/Prismatic/`（⑤b の既存ファイルの隣に新しいファイル）、§7 は `BhattScholze/Semiperfectoid/` の隣。一般性のある可換環論（Koszul 正則性など）は `CommutativeAlgebra/` の新しい下位ディレクトリ。
- 原典どおりの定義（`bs-faithful-definitions`）：定義は原典の形で置き、特別な場合に限るのは定理だけ。
- KL-W1 の段 3 が近く main に入り、`InfinityCategories/` のモジュールの場所と名前空間が変わる。取り込まれたら調整役が改名表と書き換えの手順を知らせる。
- ビルドの鍵は `zsh scripts/refactor/with_build_lock.sh --wait 1800 -- …`（`source ~/.zshenv`）。
- 報告は `formalization-plans/bhatt-scholze/reports/report-codex-w15.md`。

## 3. 追記（2026-11-10、調整役）：停止点 0 の承認

**承認**：段 0 の報告（`report-codex-w15.md`）。K1〜K5 の既存宣言の洗い出し、型案、置き場所、規模（合わせて約 5,000〜10,000 行）は報告のとおりでよい。段 1 に進んでよい。段 1〜4 は §1 の条件で、報告してそのまま次へ進んでよい。検収事項は次のとおりに決める。

1. **K1**：⑤b の既存の特殊な場合（`crystallineAffineFrobeniusDivision_primeRegular` ほか）を再利用し、一般の r 元へ広げる案でよい。順序（自由変数の未完備版 → 一般の r 元 → 底変換・完備な模型への適用）も報告のとおり。停止点 1 で取り込み、⑤b に知らせる。
2. **K2 の Frobenius の平坦性（D74）**：本体は**原典どおりの形**（U/p 上の Frobenius が d 完全平坦、`IsCompletelyFlat (Ideal.span {d̄}) …`）で置く。U は変数が無限個の非 Noether 環で、普通の平坦性（drafts の `FrobeniusFlatModP`）は原典より強く、成り立つかも自明でない。drafts の A1 の型（`universalOrientedPrism_frobenius_flat`）は ⑤c では変えない。Construction 6.1 が完全平坦性で足りるかは、A1 の drafts を界面に書き換える段（⑤b の停止点 3 の後、⑤a）で一緒に確かめ、要れば A1 の型を原典の形に直す。
3. **K4**：Lemma 3.7 (2) の入力を Mathlib の通常の導来圏 `DerivedCategory (ModuleCat A)`（またはその鎖複体の模型）で述べる案、Cor 3.12 の層の性質を「完全忠実平坦な射の増大つき完備 Čech 余脈体の交代余面複体が全次数で完全」という古典的な形で示し、∞ 層と RΓ への接続を drafts に残す案、Ex 3.14 は変数版の型を保ち一般化を別の定理にする案、いずれもよい。Ex 3.14 の一般の存在が重いと分かったら、そこで止めて報告する（目標に要るのがどの場合かを調整役が確かめる）。
4. **K5 の G-A3-7 の切り出し**：比較先を通常の p 完備なフィルター付き環 C に一般化した古典的な部分を本体に置き、実際の Δ̄ がそのフィルトレーションと評価を持つことは drafts に残す案でよい。`exists_lciEnvelope` の一般の型を Δ の離散性なしで閉じる経路も、それで進めてよい。

## 4. 追記（2026-11-10 夜、調整役）：Ex 3.14 は変数の場合だけ（D21 のとおり）

段 3 の中断の報告（c43e8f48d）を受けて。§0 の表の K4 の「Ex 3.14 の一般形」は調整役の誤りだった。設計の決定 **D21**（`a0-design.md` §4）は、Prop 3.13 の存在を Ex 3.14 の**変数の場合**（多項式代数からの全射の核で、変数の取り替えの後は変数の部分集合）に絞っており、それは本体（`exists_prismaticEnvelope_of_variables`）にある。

1. Ex 3.14 の一般の存在（滑らかな全射の核の局所完全正則列による表示、δ 除算包の完全平坦性と貼り合わせ）は**作らない**。
2. 段 3 は、残りの Lemma 3.7 (2)(3)、Cor 3.12、Prop 3.13 (2)（変数の場合の底変換、drafts `prismaticEnvelope_baseChange_of_variables` の型）へ進む。今回の共通部品（通常のテンソル積の δ 構造と δ 射の一意延長）はそのまま使ってよい。
3. A3（Ex 7.9）で要る別の場合（f_1, …, f_r の正則列）は K5 で扱う（D21 の注記どおり）。

## 5. 追記（2026-11-11、調整役）：W15 の後の予定（ユーザー決定）

Prisms の地図で「本体に部品」の項目のうち、∞ 圏を待たずに組み立てられて担当がいなかったものを、W15 の段 4（K5）の後に ⑤c に頼む（BS-W17 として、段 4 の終わるころに調整役が指示書を書く）。

1. **Thm 4.11 の帰着**：一般の有界な向き付き基底への帰着（Prop 6.2・Thm 6.3、drafts の A1-4、`A1/HodgeTateComparison`）。結晶基底の場合（BS-D68）と普遍的な向き付き prism（K2）を使う。Construction 6.1 が Frobenius の平坦性を使うので、D74（d 完全平坦）で足りるかを最初に確かめる。
2. **Construction 4.17**：Čech–Alexander の対象が弱終対象であること。
3. **Rem 4.19 の底変換との両立**。

`A1/HodgeTateComparison.lean` は、そのとき ⑤c の持ち分にする（⑤a の A1 の二本の書き換えは `CrystallineInput`・`HodgeTateMap` だけ）。

## 6. 追記（2026-11-11、調整役）：Ex 7.9 の存在補題に原典どおり有界性を足す（D76）

drafts `A3/LciAndQuasiregular.lean` の `exists_lciEnvelope (hf : IsKoszulRegularModGenerator P f)` は有界性を仮定していないが、原典 Ex 7.9 は冒頭で「R の p 冪ねじれが有界」と仮定している。原典で envelope B = A{f/d}^∧ が離散になるのは Δ_R/A との同一視による（その同一視に有界性を使う）。有界性なしで古典的な envelope が存在するという主張は原典になく、成り立つかも自明でない（普遍の場合からの底変換で離散性を保つには、普遍の envelope が底の上で完全平坦である必要があるが、Prop 3.13 (1) が与えるのは A₀ の上の平坦性だけ）。この補題の利用者は drafts にも本体にもない。E3 の経路で要るのは T の場合と普遍の場合で、どちらも有界（a3-design §2.2）。

**決定（D76）**：`exists_lciEnvelope` の型に、原典どおり `(hR : BoundedPTorsion p (lciQuotient P f))` を足す。⑤c は A3 の drafts の持ち分なので、この型の変更を行ってよい（指示書 §1 の「型を drafts から変える必要があれば止める」の例外として、調整役が承認した）。証明は原典の筋（有界性を使い、`completedBaseChange_bounded_torsion_pure` へつなぐ）でよい。
