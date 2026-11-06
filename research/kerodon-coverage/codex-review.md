# Codex への依頼：Kerodon の項目と Lean の宣言の対応表の確認

作成：2026-11-07（段階 II の調整役）。宛先：Codex（新しいチャット）。読み取りの確認作業で、新しい数学は書かない。

## 0. 背景

`research/kerodon-coverage/items.csv` は、Kerodon（https://kerodon.net、11-06 取得）の本文 Ch 1〜10 の番号つきの項目 3,553 個について、SerrePositivity と Mathlib に対応する宣言があるかを判定した表である。対象は Definition・Theorem・Proposition・Lemma・Corollary・Construction・Variant・Notation の全部と、Lean が番号で引いている Example・Remark など。

- 列：`number`（Kerodon の番号）、`kind`、`status`、`declarations`（`宣言名 @ path:line` を ` | ` で区切る）、`note`、`confidence`、`lean_citations`（Lean の docstring がその番号を引いている件数）、`subsection_tag`。
- `status` の意味：
  - `own`：SerrePositivity にある
  - `mathlib`：Mathlib にある
  - `both`：両方にある
  - `partial`：特別な場合だけ、片方の向きだけ、など
  - `none`：見つからない
- 作り方：Claude のエージェントが、宣言名の索引と grep で探し、宣言の主張と docstring を読んで判定した。「なし」とした Definition・Theorem・Proposition は、別のエージェントがもう一度探した。**Lean を動かしての確認はしていない**。確度は `confidence`（high・med・low）。
- 集計は `items-summary.md`、各塊の所見は `items-remarks.md`、Subsection 単位の先行の調査は `README.md`・`coverage-ch*.md`。

## 1. 確認してほしいこと

対象は `review-targets.csv` の 417 項目。`reason` 列が選んだ理由である（重なりあり）。

| 理由 | 中身 | 件数 | 見ること |
| --- | --- | --- | --- |
| A | `none` 以外で確度が `low` | 196 | 宣言が実在し、主張が Kerodon の項目と合っているか |
| B | `none` 以外の Theorem の全部 | 72 | 同上。特に `own`・`both` の主要な定理が本当にその主張か（仮定が強すぎないか、特別な場合だけでないか） |
| C | Ch 1〜7 で `none` の Theorem・Definition | 122 | 本当にないか。言い換え・双対・特別な場合の版・Mathlib の命名で探す |
| D | `own`・`both`・`mathlib` からの抜き取り（20 件に 1 件） | 38 | 表全体の正確さの見積もり |

確かめ方：

1. 宣言は `#check @名前` と `#print axioms 名前` で引く（scratch のファイルを一つ作り、`lake env lean` で流す。import は宣言のファイルのモジュール）。主張の型を Kerodon の項目の主張と比べる。Kerodon の本文は `https://kerodon.net/tag/<Tag>`（Subsection の Tag は `subsection_tag` 列）。
2. `#print axioms` に `sorryAx` や標準 3 公理以外が出たら記録する。
3. `[ModelCategory SSet]` のように、主張の仮定に、後で満たせないかもしれない型クラスが入っていないかも見る。
4. C は、見つかれば宣言名と場所を書く。見つからなければ「確認済み・なし」と書く。

## 2. 返してほしいもの

`research/kerodon-coverage/codex-review-result.csv` に、確認した 417 項目を一行ずつ書く。列は次のとおり。

- `number`
- `verdict`：`ok`（表のとおり）、`fix`（訂正）、`unsure` のいずれか
- `status_new`：訂正後の status
- `declarations_new`
- `reason`：短く、日本語
- `axioms`：`#print axioms` の結果が標準 3 公理以外なら、その中身

末尾の要約は `codex-review-result.md` に書く。中身は次のとおり。

- 理由（A〜D）ごとの ok・fix・unsure の件数
- D の結果から見た、表全体の正確さの見積もり
- よくある誤りの型
- 主張がずれている宣言の例

## 3. 規則

- 読み取りの確認だけ。`SerrePositivity/` の Lean のファイルは編集しない。書いてよいのは `research/kerodon-coverage/` の上の 2 ファイルと、確認用の scratch のファイルだけ（scratch は作業後に消すか、`research/kerodon-coverage/scratch/` に置いてコミットしない）。
- worktree は main から切った作業用のものを使う（例 `../SerrePositivity-kerodon-review`、枝 `research/kerodon-review`）。main の作業木では作業しない。
- ビルドは小さなものだけ。`lake env lean` の前に、import するモジュールを `lake build <module>` で用意する（Lake のキャッシュが効く。`source ~/.zshenv`）。全体のビルドや verify はしない。始める前に `ps -axo command= | grep '[l]ake build'` で他の大きなビルドがないことを確かめ、`scripts/refactor/with_build_lock.sh --wait 0 -- lake build …` を通す。
- 終わったら枝にコミットして報告する。main への取り込みは調整役が行う。
