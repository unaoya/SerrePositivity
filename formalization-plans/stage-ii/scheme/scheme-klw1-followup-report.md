# ⑥ KL-W1 追従報告

2026-11-12。修正版 `8267bf808` の共有採取器で、検証済み本体 68 本の新規 collect と rewrite が成功した。`review.json` は `{}`、書き換えは **0 本・0 行**。main `0f30e1f6c`（指定の `23f47736c` 以降）を `math/scheme` に取り込んだ。対象と直接 importer のビルドは成功した（4,332 jobs）。停止点 2e の検収とは別の改名追従である。

## 1. 対象と道具

[対象一覧](scheme-klw1-followup-files.json) は前回の検証済み本体 **68 本**のまま。数学の基点は `69ace8712`、追従前 HEAD は `3a7f198f3`。前回以降に追加した検証済み Lean はない。全 68 本が `git show 69ace8712:<path>` とバイト単位で一致することを収集前に確認した。

未検証の 49 本（`scheme-drafts/` の 48 本と `AlgebraicGeometry/ProjectiveCechFrobenius.lean`）は対象外。作業木に保存し、main の取り込み前後でソースハッシュが変わっていないことも確認した。検証するときに旧名のエラーが出た場合は、改名表で直す。

道具は指定された共有パスのものを使用した。

`/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout/scripts/refactor/klw1_namespace.py`

採取器のコミットは `8267bf808`。Python・Lean ヘルパー・その Python 依存二本・両改名表のハッシュが収集前後で一致した。68 capture に計 155,744 件の参照と 959 件の command 記録があり、全 capture の `elaboration.configured` が真で、共通の Lean 採取器ハッシュは次のとおり。

```text
67ef69cc1b87f500d832146e75870ae1997ea95a4e05ee264ce5d3ef4a13e43a
```

## 2. collect・rewrite・review

従前の部分採取は使わず、新しい `scheme-drafts/klw1-followup-1112-fixed/before_index/` へ採取した。collect は共有鍵 `--wait 3600` を通した単独実行（1,700 秒上限）で成功し、終了コードは 0。完成した `files.json` が一覧と一致すること、68 capture の source が実ソースと一致することを確認した。

rewrite と差分確認は鍵の外で実行した。

```sh
klw1=/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout
files=formalization-plans/stage-ii/scheme/scheme-klw1-followup-files.json
base=formalization-plans/stage-ii/scheme-drafts/klw1-followup-1112-fixed
python3 "$klw1/scripts/refactor/klw1_namespace.py" collect \
  --root "$PWD" --files "$files" --output "$base/before_index"
python3 "$klw1/scripts/refactor/klw1_namespace.py" rewrite \
  --root "$PWD" --files "$files" --index "$base/before_index" \
  --plan "$klw1/scripts/refactor/targets/kl-namespace-map.json" \
  --output "$base/preview"
```

| 確認項目 | 結果 |
|---|---|
| 完全な採取 | 68 / 68 本、collect 終了コード 0 |
| rewrite | 終了コード 0 |
| `review.json` | `{}`、保留 0 |
| 書き換えたファイル | 0 本 |
| 書き換えた行数 | 追加 0・削除 0 |
| 取り込み後のソース | 全 68 本がプレビューと一致 |
| 下書き | 除外した 49 本のソースハッシュを保存・照合済み |

ソース差分 0 は意味参照を採取して得た結果であり、単なる import 行の検索結果ではない。プレビューから反映すべき編集はない。

## 3. main の取り込みと対象ビルド

main `0f30e1f6c7c2c4e7684c8217ffe1010ff36b8e4b` を衝突なく取り込んだ。merge コミットは **`2ed2c017c`**。指定の `23f47736c` が取り込み先の祖先であることを確認した。main の作業木では編集・ビルドしていない。

対象ビルドは共有鍵 `--wait 3600` の整理券一つで待った後、単独の `lake build` に一覧の 68 モジュールを指定して実行した。直接 importer `SerrePositivity.AlgebraicGeometry` もこの一覧に含む。ビルド完了で鍵を返却済み。全ルートのビルドは行っていない。

ビルド結果：**成功、4,332 jobs、終了コード 0**。

## 4. 証拠と数学の状態

作業木の `formalization-plans/stage-ii/scheme-drafts/klw1-followup-1112-fixed/` に、`provenance-before.json`、`collect.log`、完全な `before_index/`、`preview/` と空の `review.json`、`preview-summary.json`、`merge-before.json`、対象ビルドの `build.py` と `build.log`、総合の `verification.json` を保存した。旧失敗の記録は `3a7f198f3` に残っている。

追従前の検証は数学 `69ace8712` に対する対象・直接 importer のビルド成功（4,332 jobs）、監査 **7,204 宣言・標準三公理のみ**。この監査は追従前の結果であり、追従後に再実行したものではない。今回の追従では数学の宣言は変更していない。2e の残り（§9 の未完の比較など）は引き続き残っており、停止点 2e の完成は主張しない。
