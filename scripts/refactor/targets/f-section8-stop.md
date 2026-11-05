# IF-F §8：内部 round 5 の再発停止

実装 HEAD `f908c70db`。**停止点 4 には未到達**。main の変更・ビルド、他レーンの枝の変更はしていない。

## 停止理由

`LoopCylinderConstantParameter.lean:50:35` の `change` 内で、`paramCurry` の証明引数 `hf`（`_`）を推論できない。round 4 の後に利用側の `paramCurry` と `loopSpace` を新名へ揃えたが、round 5 でも同じ箇所・同じ目標で再発した。`rw` より前の引数推論なので、§8-3 の旧名展開の例外には含めず、継承する W2b §16(a)「補充したモジュールが次の round でも同じ型で落ちる」を適用して止めた。

定義元 `LoopOfCylinder.lean` には旧 `Spectra.PointedMapping.paramCurry` と旧 `Spectra.loopSpace` が残る。これを新名へ揃える **1 本・2 参照**の案を `f-section8-hf-proposal.patch` に保存した。**未適用・未ビルド**。原因の候補であり、解消は未検証。既存の証明 `circleCylinderDesc_point` の明示引数はそのまま保持し、新しい証明ステップは加えない。

## 内部検証

| round | 失敗モジュール | 未検証の根 / 103 | 秒 |
|---|---:|---:|---:|
| 1 | 42 | 40 | 363.181 |
| 2 | 30 | 32 | 653.957 |
| 3 | 24 | 26 | 260.197 |
| 4 | 19 | 23 | 484.378 |
| 5 | 18 | 20 | 452.281 |

内部対象 745 本の最小 103 根について、失敗モジュールに依存する根を未検証として数えた。根が減っても、再発停止は独立して適用する。旧名展開の再発 `FreeStandardContraction` は §8 の例外として区別した。全エラーの位置・種別は JSON に記録。

round 5 の失敗 18 本：

- `SerrePositivity.KST.Comparison.FreeStandardContraction`
- `SerrePositivity.KST.Fibration.WeakMarkedSpanCartesianLift`
- `SerrePositivity.KST.LocalizingInvariants.LaxCounitRightHom`
- `SerrePositivity.KST.LocalizingInvariants.SquareFramePathExtension`
- `SerrePositivity.KST.LocalizingInvariants.TammeMarkedSpanCartesianLift`
- `SerrePositivity.KST.SConstruction.CoaugmentedPointedFunctor`
- `SerrePositivity.KST.SConstruction.CubeDeletionExpression`
- `SerrePositivity.KST.SConstruction.CubeDeletionNormalComposition`
- `SerrePositivity.KST.SConstruction.LoopCylinderConstantParameter`
- `SerrePositivity.KST.SConstruction.TerminalLoopPathFiber`
- `SerrePositivity.KST.SConstruction.TerminalPathEvaluation`
- `SerrePositivity.KST.Spectra.FilteredPointedHomotopy`
- `SerrePositivity.KST.Spectra.Limits.SpectrumBinaryProductSequence`
- `SerrePositivity.KST.Spectra.LoopMappingOperations`
- `SerrePositivity.KST.Spectra.PathNaturality`
- `SerrePositivity.KST.Spectra.PointedHomotopyGroupDiagram`
- `SerrePositivity.KST.Spectra.RawSpectrumCotensorSourceNaturality`
- `SerrePositivity.KST.Spectra.ThreeEdgeTransportSquare`

## 適用・保存状態

- 承認された 6 本・10 参照の patch と、tactic 引数の予防書き換え（576 本・1,393 参照）を `0b4ac3145`「完全修飾（旧名の展開）」でコミット。以後の名前解決・scope・生成 alias 補充は `86d2c12c7`、`74fd12350`、`f908c70db` に分離。
- 移動対象 730 本、ソース宣言 3,871、生成宣言を含む alias 7,526。現在の利用者側変更は 931 本。改名表は未確定の停止状態に更新した。
- 変更前の有効 snapshot は重複を除き 1666 本。現時点で変更済みの Lean ソース（新規 helper を除く）の before 不足は 0。広い追加 capture は中断状態を保持し、全体 PASS と扱っていない。
- 停止を認識した時点で進行中だった、変更前 baseline の追加 2 本の snapshot のみ完了。round 6 の補充・内部ビルドは実行していない。
- snapshot の名前照合を高速化した runner は、元 runner と単一モジュールの出力全体の一致を確認。比較器の名前照合も元実装と出力全体が一致。型・本文のハッシュ方式と比較条件は不変。ただし、この診断比較を全保存比較の PASS と扱わない。
- 停止時の層検査 `PASS`、直接禁止辺 0。例外追加なし。
- 下流 10,519 本（helper 込み 10,520 本、23 根）、全保存比較、監査追従、verify は未実施。

## verify summary

```json
{
  "status": "NOT_RUN",
  "summary": null,
  "VERIFY_JOBS": 6,
  "VERIFY_MEMORY_GB": 40,
  "reason": "internal/downstream/preservation prerequisites not met"
}
```

## 再開に必要な判断

この `hf` 推論失敗に関する再発停止を解除し、定義元 2 参照の完全修飾案から再開する承認が必要。解除後は候補の小さなビルドで原因を確かめ、残る失敗を判断表内で補充して内部検証を再実行する。内部 PASS 後の順序は §8 のとおり（下流 → 保存比較 → 層 → 監査 → verify → 停止点 4）。既存の条件付き事前承認は維持する。

証跡は `.lake/verify/if-f2/`。round 6 の未適用候補は同ディレクトリの `unapplied-supplement-round-06.json`。候補を既適用として扱わない。改名表の行先は変更していない。
