# 指示書 KB-W1：Kerodon の対応表の partial・none の一括見直し（B6、紙）

作成：2026-11-17（調整役）。決定：ユーザー（11-17「8 に B6 の指示を出してください」）。レーン：⑧（worktree `../SerrePositivity-cited`、枝 `research/cited-coverage`。`pwd` を確かめてから始める。始める前に `git merge main`）。

## 0. 目的

Kerodon の対応表（`research/kerodon-coverage/review/ch1.csv`〜`ch10.csv`、全 3,553 項目）の **partial 1,574 行と none 1,417 行**を、一つの基準で一度に見直す。11-07〜11-10 の確認は章ごとに担当が分かれ（-a2・-b・-c）、抜き取りで none ↔ partial の判定に 10〜20% の揺れが出た（`codex-review.md` §8）。§8.2 の 4 で「最後に一つの Codex が全章の partial・none を §8.1 の基準で一度に見直す」と決めていたもの（一括レーンの B6）。結果はブループリントの Kerodon の部と文献の属性（`@[kerodon …]` は own・both だけ、partial は `partial :=` の種類）にそのまま使い、ユーザーの Kerodon の内容の確認の材料にもなる。

## 1. 基準（`codex-review.md` §8.1 のとおり）

- **partial** と数えるのは、Lean の宣言から原文の主張の一部が**直接**導ける場合だけ。`partial_kind` 列に `special`（仮定の特殊化：対象・圏・次元を限る）・`direction`（iff・同値の片側）・`stronger-hyp`（より強い仮定で同じ結論）・`component`（結論の一部・構成の一部の成分）のどれかを書く。
- **none**：証明の部品・補題にあたる主張、似た構成、別の射・別の対象の類似の主張、原文の主張を導くのに追加の議論が要るもの（`reason` に候補を書いてよい）。
- 宣言がビルドしない場所（`SerrePositivity/Archive/`）にあるものは own・partial にしない（AR-W1、9.1.1.20 の例）。モデル圏を仮定に持つ宣言の扱いは §6 のとおり。

## 2. やること

1. **partial の全行**：§8.1 の四つのどれかに当たるか、宣言の型（仮定と結論）を原文の主張と並べて判定し直す。当たれば `partial_kind` を埋める（空の行が多い）。当たらなければ none に直し、理由を書く。
2. **none の全行**：KL-W1・B3・B3′・OE-W1（11-11〜11-17）で本体に入った・動いた宣言も含めて探し直す（`research/coverage-location-refresh/`、`evidence/consolidation/organize-einfinity-w1/module-map.json`）。own・partial に当たる宣言が見つかれば状態を直し、宣言（`名前 @ パス:行`）と理由を書く。
3. own・both・mathlib の行は**変えない**。明らかな誤りを見つけたら `review/check/b6-own-issues.md` に書くだけにする。
4. 章ごとに `review/check/b6-ch<N>.md` に変更の一覧（番号、旧状態 → 新状態、partial_kind、理由の要約）と集計。

## 3. 順と報告

- 第 1 章から第 10 章の順。**章ごとにコミット**し、2 章ごとに止まらずに途中報告する。全章が終わったら止まる。
- 報告は `report-clmst-coverage.md` に節「KB-W1」を続け、先頭の現在地を更新。「一覧：済み n／全体 10（章）」。

## 4. 規則

- 紙だけ。Lean の変更・ビルドはしない。宣言の存在と型はソースを読んで確かめる（kernel の確認ではないことを README に書く）。鍵は使わない。
- 対応表の書式（列・区切り・改行）を変えない。書き換えるのは該当行の `status_new`・`declarations_new`・`reason`・`partial_kind` だけ（`partial_kind` の列がない章は列を足してよい、その旨を b6 の記録に）。
- 証拠（大きい抽出結果）は git の外 `~/serre-evidence/cited/kerodon-b6/`、目録だけをコミット。
- 状態を変えた行が地図・ブループリントに反映されるのは、調整役の取り込みの後（`scripts/docs/coverage_map.py refresh`・`blueprint/scripts/gen_kerodon.py`）。
