# 指示書 KB-W2・BT-W1：HA・HTT の見直しと、BS の対応表の書式（紙）

作成：2026-11-17（調整役）。決定：ユーザー（11-17「1, 2 をやりましょう」）。レーン：⑧（worktree `../SerrePositivity-cited`、`pwd` を確かめ、始める前に `git merge main`）。紙だけ、Lean の変更・ビルドなし、鍵は使わない。証拠は git の外 `~/serre-evidence/cited/<段>/`、目録だけコミット。報告は `report-clmst-coverage.md` に節を続け、現在地を更新。段ごとにコミットし、二つとも終わったら止まる。

## 段 1　KB-W2：HA・HTT の対応表の見直し

対象：`research/ha-coverage/review/ch*.csv`（2,866 項目：none 2,324・partial 465・own 38・mathlib 39）と `research/htt-coverage/review/ch*.csv`（1,730 項目：none 1,197・partial 291・own 192・mathlib 50）。どちらも partial の行には `partial_kind` が付いている（11-11 の確認は `research/kerodon-coverage/codex-review.md` §8.1 の基準の後）。

1. **none の全行を探し直す**：11-11 以降に入った・動いた宣言を含めて（KL-W1・B3・B3′・OE-W1、`evidence/consolidation/organize-einfinity-w1/module-map.json`、`research/coverage-location-refresh/`）。own・partial に当たれば状態・宣言（`名前 @ パス:行`）・理由・`partial_kind` を直す。
2. **partial の全行を §8.1 で確かめ直す**：Lean の宣言から原文の主張の一部が**直接**導けるか、`partial_kind` が正しいか。当たらなければ none に直し、理由を書く。より強く原文どおりなら own に。
3. own・mathlib の行は変えない（誤りの候補は `review/check/kb2-own-issues.md` に書くだけ）。Archive の宣言・BS の drafts の宣言は own・partial にしない。
4. 章ごとに `review/check/kb2-<HA|HTT>-ch<N>.md`（番号、旧 → 新、partial_kind、理由の要約、集計）。順は HA（第 0 章から）→ HTT（第 1 章から）。**HTT 第 6 章は最後に**（③-a の 5∞-1 の層の一般論＝HTT 6.2 がまだ main に入っていない。入っていれば `git merge main` してから、入っていなければ「③-a の取り込み待ち」と記録して残りを済ませる）。
5. 表の書式（列・区切り・改行）を変えない。

## 段 2　BT-W1：BS の対応表を他の表と同じ書式に

対象：`research/bs-coverage/items.csv`（211 項目）。今は `status` が独自の語（`proved`・`proved_special`・`parts_in_body`・`drafts`・`e3_input`・`design_only`・`none`）で、`declarations` などと一緒に items.csv にある。

1. **`research/bs-coverage/review/ch<N>.csv` を作る**（節ごと、BS の §1〜§18）。列は HA・HTT と同じ `number,status,declarations,reason,axioms,check,partial_kind`。
2. 状態の語を他の表に揃える。行ごとに宣言の型を原典の主張と並べて判定する（語の機械的な置き換えにしない）：
   - 原典どおり、sorry なし → `own`（Mathlib にあれば `mathlib`・`both`）
   - 主張の一部が宣言から直接導ける → `partial`（`partial_kind` を §8.1 の四つから）。今の `proved_special` の多くは `special` のはず
   - 宣言はあるが本論文の E3 の sorry に依存 → `interface`（本論文の表と同じ語。CLMST の表の 4.0.4 などと同じ扱い）
   - 証明の部品だけが本体にある（今の `parts_in_body`）、drafts にだけある、設計だけ → `none`（理由にその旨と所在を書く。drafts の宣言は own・partial にしない）
3. **宣言の所在を今の本体で確かめる**（`research/bs-coverage/check_locations.py`、11-12 以降の HT04・B3′・OE-W1 の移動を含む）。
4. `items.csv` は目録（番号・種類・題・`title_ja`・`goal`・`design`）として残し、`status`・`declarations`・`note`・`confidence` は review が正本になる旨を README に書く（二重管理にしない。items.csv の該当列は空にしてよい。`exposition/ja/bs/build_items.py` は凍結中の解説の道具で、今は動かさない）。
5. README に集計（旧状態 → 新状態の表）と、BS の整理のレーンの段 0 に渡す所見（drafts と本体の食い違い、同じ主張の並行版など）を書く。
