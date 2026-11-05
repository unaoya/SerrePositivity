# IF-F §7：F-2 内部 round 2 の再発停止

- base `640288f33`、実装 `c1779328e`、補充 `6caa532d9`。main は変更・ビルドしていない。
- **停止点 4 には未到達**。IF-F §4 が継承する IF-W2b §16(a) による停止。
- 規定：「補充したモジュールが次の round でも同じ型で落ちる」。旧 alias の `rw` 展開が補充後にも残ったため、追加の補充はしていない。

| round | 失敗モジュール | 未検証の根 / 全根 | 秒 |
|---|---:|---:|---:|
| 1 | 42 | 40 / 103 | 363.181 |
| 2 | 30 | 32 / 103 | 653.957 |

未検証の根は、内部対象 745 本のうち import の推移閉包で他の対象に含まれない 103 根について、失敗依存先に遮られる根を数えた。round は最後まで終了し、追加の round は未実行。根の数が減っても、§16(a) の再発停止は独立して適用する。

同じ旧 alias 展開で再発した 6 本：

- `SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams`
- `SerrePositivity.KST.LocalizingInvariants.MarkedSpanFamilyFiber`
- `SerrePositivity.KST.LocalizingInvariants.FinalHornArrowSquares`
- `SerrePositivity.KST.Fibration.KanEnrichedOppositePointHom`
- `SerrePositivity.KST.SConstruction.IdentityPushoutShapes`
- `SerrePositivity.KST.SConstruction.CofiberCompletion`

上の 6 本の `rw` 内に残った 10 参照だけを新名で完全修飾する案を `f-section7-unfold-proposal.patch` に保存した。**未適用・未ビルド**。全失敗モジュール・各エラー・再発/新規の区分は `f-section7-stop.json`。名前の修飾以外の数学的変更は案に含めない。

適用と確認：

- 移動対象 730 モジュール、ソース宣言 3,871（private 157）。生成宣言を含む deprecated alias 7,526。名前対応表は `f-namespace-map.json` と逆対応表。**未確定**の状態を明記。
- 利用者側の変更は main に存在する 28 モジュール。BS・G2・KST の別枝は変更していない。
- before v3b は最初の 745 本と追加利用者 15 本が PASS。初回適用後の小さなビルド（small round 2）は PASS。補充後の内部 round 2 は上記の FAIL。内部の保存比較は未実行。
- 停止時点の `layer_check --enforce W2b` 相当 PASS、直接禁止辺 0。例外追加なし。
- 重複した `doubleMappingCylinder_hom_ext` の旧名は Desc 側の alias、Map 側の自己参照 2 か所は新名に追従。

下流・Archive：

- 生の逆閉包は 11,539 本。うち Archive は 1,020 本で、ルート/監査閉包との交差は 0。W2b §1 と Archive README の「追跡するがビルドしない」を適用した稼働範囲は 10,519 本、追加 helper を含むと 10,520 本。
- 追加 before の試行で誤って Archive をビルド対象に含め、変更前の base で 22 本の既存失敗を記録した。Archive の修正・検査の例外追加はしない。非 Archive の追加 baseline ビルドは PASS。広い追加 snapshot は内部診断を優先して中断し、部分記録を保持。

verify summary：

```json
{
  "status": "NOT_RUN",
  "summary": null,
  "VERIFY_JOBS": 6,
  "VERIFY_MEMORY_GB": 40,
  "reason": "conditional preapproval prerequisites not met"
}
```

再開する場合：未適用案の確認と再発停止の解除 → 新たな補充対象の before 記録を追加 → 小さなビルド → 残る内部失敗の名前解決を判断表内で補充 → 内部 PASS → 下流 → 名前対応つき保存比較 → 層検査 → 監査追従 → verify → 停止点 4。再発した場合は再び停止する。

全ログ・snapshot・runner は `.lake/verify/if-f2/`。下流の稼働対象と根の一覧は `f-namespace-active-build-plan.json`。再開時はこの根を使う（古い一時 downstream runner の raw 80 根は Archive を含むため使用しない）。一時 baseline worktree は `/private/tmp/SerrePositivity-if-f2-baseline`（base のソース不変）。
