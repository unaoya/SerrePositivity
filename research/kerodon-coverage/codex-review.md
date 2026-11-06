# Codex への依頼：Kerodon の項目と Lean の宣言の対応表の確認

作成：2026-11-07（段階 II の調整役）。宛先：Codex（新しいチャット）。読み取りの確認作業で、新しい数学は書かない。**全項目を確認する（11-07、ユーザー）**。

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

## 1. 確認してほしいこと（全 3,553 項目）

`items.csv` の**全項目**を確認する。`review-targets.csv` の 417 項目（`reason` A〜D）は、誤りが多そうな所の印として**先に**見る。

| 段 | 対象 | やること |
| --- | --- | --- |
| 段 1（機械的、全件） | `declarations` 列に書かれた宣言のすべて | スクリプトで `#check @名前` と `#print axioms 名前` を流し、宣言が実在するか、標準 3 公理以外（`sorryAx` など）を使っていないかを一括で記録する。宣言名の解決（名前空間・Mathlib の名前）に失敗したものは段 2 で手で直す |
| 段 2（主張の照合） | `status` が `own`・`both`・`mathlib`・`partial` の 1,606 項目 | 宣言の型を Kerodon の項目の主張と比べ、判定が正しいかを決める（仮定が強すぎないか、特別な場合だけでないか、`partial` の欠けの記述が正しいか） |
| 段 3（「なし」の確認） | `status` が `none` の 1,947 項目 | 本当にないかを探す（言い換え・双対・特別な場合の版・Mathlib の命名・SerrePositivity の命名）。見つかれば宣言名と場所、見つからなければ「確認済み・なし」 |

確かめ方：

1. 段 1 の Lean のファイルは、宣言のファイルのモジュールを import して、宣言ごとに `#check` と `#print axioms` を並べる。宣言の数が多いので、モジュールの塊ごとに分けて `lake env lean` で流す。出力を解析するスクリプトも残す。
2. Kerodon の本文は `https://kerodon.net/tag/<Tag>`（Subsection の Tag は `subsection_tag` 列）。
3. `[ModelCategory SSet]` のように、主張の仮定に後で満たせないかもしれない型クラスが入っていないかも見る。
4. 章ごとに進める（Ch 1 → Ch 10）。一つの章が終わるたびに枝にコミットして、短く報告する。

## 2. 返してほしいもの

章ごとに `research/kerodon-coverage/review/ch<N>.csv` を作り、その章の全項目を一行ずつ書く。章ごとのファイルにするのは、Codex を並行で走らせても衝突しないようにするため。列は次のとおり。

- `number`
- `verdict`：`ok`（表のとおり）、`fix`（訂正）、`unsure` のいずれか
- `status_new`：訂正後の status
- `declarations_new`
- `reason`：短く、日本語
- `axioms`：`#print axioms` の結果が標準 3 公理以外なら、その中身
- `check`：段 1 の結果。`found`・`not_found`・`renamed`

段 1 のスクリプトと生の出力は `research/kerodon-coverage/review/check/` に置く。全章が終わったら、要約を `research/kerodon-coverage/review/summary.md` に書く。中身は次のとおり。

- 章ごと・status ごとの ok・fix・unsure の件数
- 理由 A〜D の項目での誤りの率（元の表の確度の見積もり）
- よくある誤りの型
- 主張がずれている宣言の例

## 2.1 並行で走らせる場合

調整役の指示で Codex を複数走らせるときは、章の範囲を分ける（例：Ch 1〜3、Ch 4〜6、Ch 7〜10）。worktree と枝はチャットごとに一つずつ切る（`../SerrePositivity-kerodon-review-a` と `research/kerodon-review-a` など）。書くのは自分の章の `review/ch<N>.csv` だけにする。段 1 のスクリプトは最初のチャットが作ってコミットし、ほかのチャットはそれを取り込んで使う。

## 3. 規則

- 読み取りの確認だけ。`SerrePositivity/` の Lean のファイルは編集しない。書いてよいのは `research/kerodon-coverage/review/` の下だけ（段 1 の確認用の Lean のファイルも `review/check/` に置く。`SerrePositivity/` の下には置かない）。
- worktree は main から切った作業用のものを使う（例 `../SerrePositivity-kerodon-review`、枝 `research/kerodon-review`）。main の作業木では作業しない。
- ビルドは小さなものだけ。`lake env lean` の前に、import するモジュールを `lake build <module>` で用意する（Lake のキャッシュが効く。`source ~/.zshenv`）。全体のビルドや verify はしない。始める前に `ps -axo command= | grep '[l]ake build'` で他の大きなビルドがないことを確かめ、`scripts/refactor/with_build_lock.sh --wait 0 -- lake build …` を通す。
- 終わったら枝にコミットして報告する。main への取り込みは調整役が行う。
