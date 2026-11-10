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
- 報告は `formalization-plans/bhatt-scholze/report-codex-w15.md`。
