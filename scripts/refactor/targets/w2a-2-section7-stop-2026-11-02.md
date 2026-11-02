# IF-W2a-2 §7：保存比較による停止（2026-11-02）

main `68486e16e` の §7 を `git show` で読み、承認された 2 案を試した。新たな main merge は行っていない。

## 個別比較

| 宣言 | 型 | 本体（def のみ） | 結果 |
|---|---|---|---|
| `codomainMap_id` | 一致 | — | PASS |
| `domainMap_id` | 一致 | — | PASS |
| `simplicialLevelModelCategory` | 一致 | 不一致（両案とも） | FAIL |
| `simplicialLevelModelCategory_generated` | 一致 | — | PASS |

`simplicialLevelModelCategory` の本体ハッシュ：before `6511626150952382968`、`circle.{u}` 案・関数 `.{u, u + 1, u}` 案とも `5132274096363497318`。型は3環境とも `14415208476746953958`。

## 実行結果

- `RelativeBoundaryFunctor` 158・169 行を `CategoryTheory.Functor.map_id` に変更。
- `SimplicialLevel` の2呼出しで、まず `PointedSimplicialSet.circle.{u}` を使用。内部 round 2 は 28.766 秒、Built 7、exit 1。指定2モジュールは通ったが、その下流 `FunctorialExtension:68` に同型の `Functor.map_id` の失敗が1本現れた。
- 追加修飾に進む前に、指定2モジュールを snapshot 比較。FAIL（9宣言）。
- §7 に従って2呼出しを `levelModelCategoryOfMonoidalGenerators.{u, u + 1, u}` と `_generated.{u, u + 1, u}` に変更。`circle` は元の表記に戻した。SimplicialLevel の単独ビルドは PASS（5.824 秒）、再 snapshot 9.638 秒、比較 0.086 秒。FAIL（同じ9宣言）。
- 保存一致条件を満たさないため、追加修飾・内部全体比較・外部92ファイルの復帰・下流ビルド・全体保存比較・層検査・verify を停止。**新規コミットなし**。

## 残った9宣言

| 宣言 | 不一致 |
|---|---|
| `SerrePositivity.Reedy.FactorizationProblem.codomainMap_fst` | type |
| `SerrePositivity.Reedy.FactorizationProblem.codomainMap_snd` | type |
| `SerrePositivity.Reedy.FactorizationProblem.inl_domainMap` | type |
| `SerrePositivity.Reedy.FactorizationProblem.inr_domainMap` | type |
| `SerrePositivity.SimplicialModelInputs.simplicialLevelI` | body |
| `SerrePositivity.SimplicialModelInputs.simplicialLevelJ` | body |
| `SerrePositivity.SimplicialModelInputs.simplicialLevelModelCategory` | body |
| `SerrePositivity.SimplicialModelInputs.simplicialLevelModelCategory_fibrations` | type |
| `SerrePositivity.SimplicialModelInputs.simplicialLevelModelCategory_weakEquivalences` | type |

4件の RelativeBoundaryFunctor の補題と `simplicialLevelI/J` 等は今回直接修正していない。`used_constants` の差分では、前者に limit/colimit 関連の参照の変化、fibrations/weakEquivalences の型に colimit instance の経路の変化がある。`simplicialLevelModelCategory` の集合差は生成証明名 `_proof_7` → `simplicialLevelI._proof_1` だが、それだけがハッシュ不一致の原因とは未確定。比較規則を変更したり pp 一致を新たに認定したりはしていない。

## 再開時の状態

- HEAD は `ecc0be826` のまま。今回の未コミットの Lean 編集は指定の2ファイル・4箇所。現在は関数の宇宙を明示した案。
- `FunctorialExtension:68` の2箇所の完全修飾は**未適用**。before/after の検証も未実施。
- 保留92ファイルはすべて `deferred-imports.json` の old_sha256 と一致していることを再確認した。一括 reset/commit しない。
- 共有鍵のもとで実行し、キャッシュの3変数を有効化した。停止後に鍵を解放し、この再開で作った未使用の scratch worktree を削除した。
- 詳細のハッシュ・差分は隣の `w2a-2-section7-comparison.json`。ログは `/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ifw0-3/.lake/verify/ifw2a2-batch/section7` と `/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ifw0-3/.lake/verify/ifw2a2-batch/internal-round2`。全ログの error／PANIC を確認し、比較の exit 1 と不一致を保持した。

停止根拠：§7「一致しなければ止める」。保存比較の不一致として報告し、指示を待つ。
