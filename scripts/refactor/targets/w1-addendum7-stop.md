# IF-W0-3 §10.7 取り込み後の停止報告

改訂版 §7-1 は未完了。コミットはしていない。

## 取り込み

専用 worktree `SerrePositivity-ifw0-3`、ブランチ `infra/if-w0-3` で
`git merge --ff-only main` を実行し、終了コード 0。
`502e78840` から `10b90008e` へ fast-forward した。
指定された `208f148bc` と §10.7 を含む。main の作業木で変更・ビルドはしていない。
この範囲では InfinityCategories・KST・scripts/refactor の追跡ファイルの差分はない。

## 停止理由

§10.7-3 は、prune 後の 15 本に入らない C の残り 8 本を W2c に回す。
その 8 本には `Derived.FirstTriangleIndex` が含まれる。
一方、§10.7-4 はその prune と下流補充を今回の JSON に入れる指定である。

現行の対象 JSON は `move`・`split`・`archive` のみを認め、
`imports` は move の移し先、または split の両側のヘッダーだけを指定できる。
`module == dest` も拒否する。このため、FirstTriangleIndex を移動せずに
import だけ縮める項目を現在の書式では表せない。
根拠：`validate_targets.py` 21–28 行、77 行、82 行。

FirstTriangleIndex は既存の 49 move 下書きにも入っていない。
勝手に W1 の move を追加したり、同一モジュールへの move で代用したりせず、
IF-W0-1 §0 の「指示書と現状が食い違うとき」に従って停止した。

## 件数の内訳

以前の証拠 `.lake/verify/ifw0-3-addendum6/roof/post-prune-seed-closure.json`
と `pure-moves-draft.json` の照合結果：

| 集合 | 本数 | 既存 move と重複 | 新規 |
| --- | ---: | ---: | ---: |
| 3 入口が必要とする集合 | 15 | 4 | 11 |
| 必要集合の外に残る C | 8 | 2 | 6 |
| C 全体 | 23 | 6 | 17 |

残り 8 本のうち既存 move があるのは `ConeEdgeCompatibility` と
`RightFibrationReflection`。§10.7-2 の既存優先なら、この 2 本は W1 に残る。
「重複 6 本」は C 全体について正しい数値であり、15 本との重複は 4 本である。
これは新しい閉包計測ではなく、承認済みの証拠の集合の照合である。

## 判断案

FirstTriangleIndex の移動は W2c のまま、W1 では import の縮小と
JoinFirstTriangle への直接 import 補充だけを記録できるよう、
対象 JSON に移動なしの import 更新を表す方法を追加する案を提案する。
別案は、FirstTriangleIndex の move も W1 に追加すること。
いずれも本報告の時点では実装していない。

## 実行・状態

- 生成補題の修正、分割再試行、最終 JSON 検査、W1 判定、全体 verify は未実施。
- 今回の新規ファイルは本報告のみ。前回までの所有範囲内の変更は保持した。
- `git status --porcelain --untracked-files=all -- SerrePositivity SerrePositivity.lean` は空。
- `git diff --check` は終了コード 0。
- ビルド・監査は実行していないため、今回それらの成功／失敗の判定はない。
- git merge のコマンド実行時間は約 0.06 秒。全体の所要時間は計測していない。
