# IF-W0-3 §10.15 準備完了・停止報告（2026-10-31）

> **2026-10-31 §10.16：R75の29本＋検査1本の削除と参照元の処置が承認済み。26本の除外は解除。最新の対象・処置は [R75一覧](r75.md)、実行順は [束の手順書](batch-w1w2a.md)。以下の除外・処置待ちは§10.15時点の履歴。準備ファイルを保存し、DG-W1通知を待つ。**

§10.16 の準備再検査：R75チェッカー PASS、approved=29、eligible=29、excluded=0、applied=false。生成監査・削除する検査・SpherePowersへの承認済み処置を区別し、未知の実importerでSTOPする回帰試験4件を追加。Python試験は **161件PASS、5.194秒、exit 0**。`git diff --check` と全ログのエラー検索も成功。実Leanソース・監査の編集は0。SpherePowersを集合へ加えた計画値は下流20,220、snapshot前2,970／後2,982。main取り込み後に再計算する。

準備用スクリプト・試験と記録を `git commit --only` で保存する。以下の「未コミット」は前回§10.15時点の履歴。

`git show main:formalization-plans/infinity-codex-w0-3.md` で §10.15（e8b31f000）を読み、ビルドなしの準備を完了した。worktree `SerrePositivity-ifw0-3`、ブランチ `infra/if-w0-3`。**main merge・.lake/build複製・snapshot・束適用・Leanビルド・verify は実行していない。** 本番の開始通知を待って停止する。

## 1. 指定の3コミット

全て `git commit --only` で所有ファイルを列挙。事前の150試験PASSは承認済み。数学ソースを含まない。

| 区分 | SHA | ファイル数 |
| --- | --- | ---: |
| 道具 | b0491d1fafe7a60599f45ab7cc526b4180c0ea0a | 4 |
| 試験 | 67c6ea7cbf37958bd28c5f62722affc86a1ee88a | 3 |
| 記録 | 21258b0d9b2fc2e948a8be5649449d6bf99cb59c | 4 |

追加のR79/R75準備・手順書は未コミットでレビューに残した。

## 2. R79 dry-run

道具：`scripts/refactor/rewrite_r79_docs.py`（既定dry-run、文書別apply、DGは探索対象外）。コマンド：

```sh
python3 -B scripts/refactor/rewrite_r79_docs.py --dry-run --output /tmp/ifw03-r79.json
```

終了コード0、status=PASS。結果を [r79-dry-run.json](r79-dry-run.json) に保存。

| 種類 | 期待 | 実測 |
| --- | ---: | ---: |
| planの参照ラベル | 618 | 618 |
| plan本文（StageTwo、別指定分） | 1 | 1 |
| inventoryの参照ラベル | 618 | 618 |
| inventory本文 | 16 | 16 |
| ArrowFactorization系の対象ファイル | 3 | 3 |

変更予定は635ファイル（HA610・CT24・Spectra1）、1253箇所。ArrowFactorization・ArrowFactorizationCategory・ArrowFactorizationTransportは内数。DGの旧参照521＋9=530本は数を確認したが書き換え対象外。R75の29候補との重複は0なので、この削除によってR79期待件数は変わらない。

archive/k-theory-v1.md:22594 に `## 396. 任意モデル源への一般化（中断）（2026-10-17）` が存在。生成アンカーは `396-任意モデル源への一般化中断2026-10-17`。[GitHub公式の見出しリンク規則](https://docs.github.com/en/get-started/writing-on-github/getting-started-with-writing-and-formatting-on-github/basic-writing-and-formatting-syntax#section-links) に従い、小文字化・空白のハイフン化・句読点除去・重複処理を行う。相対パスの深さを保持し、inventoryの #mNNNN / #layout-execution も保持する。

書き換え位置が module docstring の外なら STOP。StageTwo以外の未承認の本文plan参照、期待件数との差、既存のplanアンカーなども STOP。元ファイルは一切変更していない。

## 3. R75：29候補中、3本が importer 0、26本を除外

[全29本と参照元](r75.md)、[全行のJSON](r75-candidates.json)、[削除可能な3本](r75-delete.txt)。コマンド：

```sh
python3 -B scripts/refactor/check_r75.py --output scripts/refactor/targets/r75-candidates.json
```

終了コード0は調査の完了を表す。29本全てが削除可能という意味ではない。

- CategoryTheory/Presentation 15本＋Quiver 2本＋トップ階層8本：全25本に `scripts/audit/shared.lean` の直接import。
- `Presentation.RetractWordPullback` は `scripts/check_word_source_operators.lean:1` からもimport。
- `Spectra/SymmetricSequence/AdjacentBraid` は `SpherePowers.lean:3` からimport（mainを読み取りでも同じ）。
- importer 0かつ現役の完全パス参照0：`Spectra/SymmetricSequence/{TensorPowers,TensorPermutations,AdjacentTranspositions}` の3本。
- 監査の禁止リスト・manifest・個別チェックの名前参照も記録。HA READMEに拡張子なしの案内3件（AnchoredChain、ArrowContext、Presentation/RetractWords）と短い宣言名の言及がある。Monoidal READMEの同名リンクはMonoidalの正規ファイルを指し、Spectraの殻とは区別した。

§10.15-3 の指定どおり、importer のある26本を削除可能一覧から外した。import・README・監査を勝手に直していない。29本全てを削除するには、この参照元の処置の判断が必要。DG-W1後のmainで再検査する。

## 4. 束の手順書

[batch-w1w2a.md](batch-w1w2a.md) に次を記載した。

- 通知後のmain取り込み・排他確認・キャッシュ複製。
- 全適用前のbefore snapshot、適用順 R75 → R79 → W1 → W2a、文書別のR79 2コミット、split/move/reimport のコマンド。
- R79だけのコメント差をsplit入力に反映する際の厳密一致検査、旧planの自動consumer追加を捨てること、窓間のimport改名の合成。
- 対象集合の定義と、実適用後にbefore/afterの両方の逆閉包を含める規則。現在の計画値は下流20,128、snapshot前2,969／後2,981（main後に再計算）。
- 原因モジュールが全ログから特定できない場合だけ二分。中核への補充はSTOP。
- **停止点1：適用後／停止点2：下流ビルド・保存検査後／停止点3：verify後**。各停止で報告し、続行指示を待つ。

## 5. 検証と現在の差分

`python3 -B -m unittest discover -s scripts/refactor -p 'test_*.py'`：**157件PASS、7.814秒、exit 0**。新規7件はR79の相対パス・アンカー・コード不変・本文例外・コメント境界・CRLF・文書別の合成を検査。実Leanは呼ばず、既存Lean統合試験のmain関数も実行していない。ログ全体をエラー語で検索し、想定外のエラー0。

新規：rewrite_r79_docs.py、test_rewrite_r79_docs.py、check_r75.py、targets/{r79-dry-run.json,r75-candidates.json,r75-delete.txt,r75.md,batch-module-sets.json,batch-w1w2a.md,batch-preparation-2026-10-31.md}。更新：targets/w2a.md の最新状態への案内。全て所有範囲内。数学 .lean の差分・追加は0。

**待機**：DG-W1 のmain取り込み通知。R75の除外26本は、既存の参照元への処置を判断してもらうまで復活させない。
