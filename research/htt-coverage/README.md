# Higher Topos Theory の項目と Lean の宣言の対応表

作成：2026-11-07（段階 II の調整役）。Kerodon の対応表（`research/kerodon-coverage/`）と同じ形で、Lurie『Higher Topos Theory』（以下 HTT）の項目を Lean の宣言に対応させる。実作業は Codex（`codex-review.md`）、検収と地図（HTML）は調整役。

## 範囲

**本全体**。全章の Section・Subsection の見出しと全項目を一行ずつ作り、全項目を照合する。

| 順 | 章 | 理由 |
| --- | --- | --- |
| 1 | 第 1・2・4・5 章 | Lean の HTT の引用 2,374 件はこの四章（第 1 章 1,203、第 4 章 688、第 5 章 333、第 2 章 150）。多いのは §4.2.4（591）・§1.2.13（450）・§1.1.5（272）・§1.2.8（243）・§1.2.12（155）・§2.1.2（108）・§5.5.4（103） |
| 2 | 第 6 章（∞ トポス） | 計画が §6.2.2（層化）・§6.2.3・§6.4・§6.5（超完備性）を引く（BS の層） |
| 3 | 第 3 章・第 7 章・付録 | 計画の引用は第 3 章の 8 件だけ。付録 A（モデル圏）は、主経路でモデル圏を使わない方針（Kerodon §6）に照らして扱う |

**Kerodon との重なり**：HTT の第 1〜5 章の多くは Kerodon と同じ内容で、Lean の docstring も両方を並べて引くことが多い（例「HTT 1.1.5.10、Kerodon 2.4.5.8」）。`kerodon` 列に対応する Kerodon の番号を書き、Kerodon の確認の行（`research/kerodon-coverage/review/ch<N>.csv`）を参照する。ただし主張の比較は HTT の本文で行う（仮定の置き方が違うことがある）。

## ファイル

- `citations.csv`：Lean の docstring の HTT の引用（番号つき、2,374 件、11-07 の main で採取）。列は `file,line,kind,number,section,directory`。番号のない「HTT」は含めない。
- `plan-citations.csv`：計画（`formalization-plans/`、archive を除く）と `research/k-coverage/` の HTT の引用（223 件）。どの項目が段階 II で要るかの印。
- `toc.md`・`items.csv`：Codex が段 0 で作る（`codex-review.md` §2）。
- `review/`：Codex の確認の結果（章ごとの `ch<N>.csv`、`check/` に証拠）。

## items.csv の列

`number,kind,title,section,status,declarations,reason,confidence,lean_citations,plan_citations,kerodon,goal`

- `status`：Kerodon と同じ語彙。`own`（SerrePositivity にある）・`mathlib`（Mathlib にある）・`both`・`partial`（特別な場合・片方向・仮定が強いなど一部だけ）・`none`。
- `declarations`：`完全な名前 @ path:line` を ` | ` で区切る。
- `reason`：Kerodon の確認の基準（`research/kerodon-coverage/codex-review.md` §7.1）の形。`仮定：…（HTT と一致／Lean が強い：…／Lean が弱い：…）。結論：…（…）。`
- `lean_citations`・`plan_citations`：その番号の引用の件数（上の二つの CSV から）。
- `kerodon`：同じ内容の Kerodon の番号（docstring に並んで引かれている、または本文で同じと確かめたもの）。
- `goal`：段階 II で要るか。`BS`（BS の設計が引く）・`inf`（∞ 基盤の部品）・`K`（K 側、後回し）・`-`。`plan_citations` の引用元のファイルで決める。

## 原典

HTT は Lurie のページの最新版（`https://www.math.ias.edu/~lurie/papers/HTT.pdf`）を使う。リポジトリには置かない（`paper/refs/` と同じ扱い）。取得した版の日付と SHA-256 を `toc.md` の冒頭に書く。
