# ⑥ KL-W1 追従：collect の途中報告

2026-11-12。**追従は未完。main `19f081dcb` 以降の取り込みは、まだ行っていない。** 未検証の下書きを含む collect が停止したため、指定どおり書き換えずに報告する。

## 0. 追従前の検証の区切り

数学 `69ace8712`、記録 `44651feab`。局所化と指定次数の Frobenius、半線形な Čech H の入口の三本をコミットした。対象と直接 importer `SerrePositivity.AlgebraicGeometry` のビルドは成功（4,332 jobs）、別実行の標準監査は **7,204 宣言・標準三公理のみ**。共有鍵 `--wait 3600` を各実行の間だけ持った。

`ProjectiveCechFrobenius.lean` は通常の係数作用と Frobenius による制限作用の型合わせが未完なので、入口から外し、未コミットのまま保存した。Frobenius の自然性などの未検証下書きも保存している。停止点 2e ではない。

## 1. 対象一覧

正本の配布ファイル：

`/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout/formalization-plans/stage-ii/kerodon-layout-stop-3/scheme-files.json`

[枝側の対象一覧](scheme-klw1-followup-files.json) は配布の 112 本に、10:21 以後の追加・編集がある次の 5 本を足した **117 本**。うち 48 本は `scheme-drafts/` の下にある。検証済みかどうかで対象を黙って絞っていない。

- `SerrePositivity/AlgebraicGeometry/ProjectiveCechFrobenius.lean`
- `SerrePositivity/AlgebraicGeometry/ProjectiveCechSemilinearMap.lean`
- `SerrePositivity/AlgebraicGeometry/ProjectiveGradedFrobenius.lean`
- `SerrePositivity/AlgebraicGeometry/ProjectiveLocalizedFrobenius.lean`
- `formalization-plans/stage-ii/scheme-drafts/ProjectiveFrobeniusNaturality.lean`

## 2. 実行した collect と停止箇所

main の取り込み前、HEAD `44651feab` の枝で、共有鍵を通して次を実行した（内部の Lean 実行を含む一回の収集）。

```sh
klw1=/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout
files="$PWD/formalization-plans/stage-ii/scheme-klw1-followup-files.json"
before_index="$PWD/formalization-plans/stage-ii/scheme-drafts/klw1-followup-1112/before_index"
python3 "$klw1/scripts/refactor/klw1_namespace.py" collect \
  --root "$PWD" --files "$files" --output "$before_index"
```

117 本中 **13 本の capture を保存**した後、未検証の `SerrePositivity/AlgebraicGeometry/ProjectiveCechFrobenius.lean` で終了した。Lean の終了コード 1、collect の終了コード 2。失敗した一本に続く 103 本は未収集。保存したソースのハッシュは 117 本すべて収集開始前と同じである。

主なエラー：

```text
ProjectiveCechFrobenius.lean:57:10:
  synthesized type class instance is not definitionally equal ...
  synthesized: ((projectiveNatGradedModuleChartDiagram G (↑p * d)).obj T).isModule
  inferred: Module.compHom ... (frobenius R p)
ProjectiveCechFrobenius.lean:48:4: unknown free variable ...
ProjectiveCechFrobenius.lean:91:5: Unknown identifier
  projectiveNatGradedChartFrobeniusNatTrans
```

これは改名で生じたエラーではなく、もともと未検証の下書きに残していた問題である。収集器は各ソースを elaboration し、エラーがあれば index の完成前に終了するため、現行の道具では「未検証の下書きも含む全 117 本」の index を作れていない。成功扱いの空の参照データを作ったり、失敗ファイルを除外したりはしていない。

## 3. 書き換え・review・ビルドの状態

| 項目 | 状態 |
|---|---|
| before_index | 13 本の capture がある部分出力。全体の `files.json` は未生成。 |
| rewrite のプレビュー | 未実行。完全な index がないため作っていない。 |
| `review.json` の保留 | **未判定**。`review.json` 自体が未生成であり、「保留 0」とは報告しない。 |
| 書き換えたファイル・行 | 0 本・0 行。 |
| main `19f081dcb` 以降の取り込み | 未実行。 |
| 追従後の対象・直接 importer のビルド | 未実行。追従前の結果は §0。 |

補助の静的調査では、対象からたどったローカル import 閉包 752 本に、改名表の移動対象の import は 0 件。ただしこれは意味参照の collect の代わりではない。また、古い下書き `scheme-drafts/ProjectiveNatCechCoefficientMapNaturality-grading-transport.lean:3` に、存在しない `SerrePositivity.AlgebraicGeometry.ProjectiveNatCoefficientMapNaturality` の import がある。現行の収集器で処理を進めた場合、この未検証ファイルも elaboration できない。

## 4. 保存した証拠と必要な接続

作業木内の `formalization-plans/stage-ii/scheme-drafts/klw1-followup-1112/` に以下を保存した。

- `collect.log`：実行と上のエラー。
- `before_index/`：13 本の実際の capture（未完成の部分出力）。
- `collect-failure.json`：成功・失敗・未実行の対象、終了コード、道具と改名表のハッシュ。
- `manifest-provenance.json`：配布元と追加した 5 本。
- `source-hashes-before-collect.json`：117 本の同じソースの確認。
- `static-import-closure.json`：補助の静的閉包。

KL-W1 の道具側で、elaboration error がある下書きの参照収集／保留をどう扱うかが必要である。処理できる入口が用意されたら、同じ全対象で collect・プレビュー・review をやり直し、その後 main を取り込み、対象と直接 importer をビルドする。曖昧な参照を推測で書き換えない。
