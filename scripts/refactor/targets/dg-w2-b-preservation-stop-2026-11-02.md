# DG-W2(b) §14 再開後の停止報告（2026-11-02）

> 過去の停止・準備時点の記録です。その後の解消と停止点 2 の結果は [§16 の完了報告](dg-w2-b-universe-replay-2026-11-02.md) を参照。

**名前の修飾は保存比較 PASS、内部ビルドも PASS。ただし D3・D4 全対象の保存比較が FAIL のため、§13-2・§14 に従って停止した。停止点 2 の受入には未到達。** 比較規則の緩和・宣言の追加修正は行っていない。外部 import の付け替え、下流ビルド、layers.json、verify は未実施。共有鍵は解放済み。

## 今回の適用とコミット

作業木は `../SerrePositivity-dgw1`、ブランチ `infra/dg-w2`。main `8e456c782` の §14 は git show で読み、今回 main の merge はしていない。main の作業木での作業・ビルドもしていない。

`3a08fb3c7 fix(dg): qualify names shadowed by consolidated imports` を作成した。`Functor/ModuleShiftOpposite.lean` の `op → Opposite.op` と、修飾箇所の一覧・前回停止報告を含む。前回の 14 はエラー件数で、修飾対象は **19 行・36 出現**。同じ型の隠蔽としてすべて従来の解決先へ完全修飾した。修飾を取り除くと変更前の文字列と完全一致し、追加・削除・並べ替えはない。

[修飾箇所の一覧](dg-w2-b-name-qualifications.md)と [JSON](dg-w2-b-name-qualifications.json) にファイル・行・旧名・新名を記録した。列番号は修飾前のもの。対象行は 19、20、23、25、30、31、39、41、45、46、50、52、53、60、62、66、69、71、78。

修正モジュール単独のビルドは終了 0（8.592 秒）、after snapshot は終了 0（14.460 秒）、before／after 比較は **6 宣言、差分 0、終了 0**（0.065 秒）。型・本体ハッシュ・公理・属性が一致した。

前回の D3 `0fe63746a`、D4 `f7933ec9d`、D5 `3a9f78a1a` はそのまま。

## 内部ビルド

Lake キャッシュの 3 変数が入った新しい zsh を使い、with_build_lock.sh で排他した。指定対象は統合先 78＋移動先 33 の **111 モジュール**。新規成功数には上流依存も含むため、111 に対する成功割合ではない。

| 段階 | 終了 | 秒 | 新規成功 | 結果 |
| --- | ---: | ---: | ---: | --- |
| 修飾後の内部ビルド | 1 | 359.631 | 161 | Boundary の heartbeat 上限 1 件 |
| section 内の上限調整後 | 0 | 196.489 | 8 | 全 111 対象 PASS、3,963 ジョブ |
| 全 111 対象の after snapshot | 0 | 57.094 | — | 2 群とも PASS |
| snapshot の統合 | 0 | 2.559 | — | 対象・source の被覆を照合 |
| 全対象の保存比較 | 1 | 6.345 | — | 2,585 差分、STOP |

最初の追加失敗は次の 1 件だけだった。

```text
error: SerrePositivity/DifferentialGraded/Resolution/Cells/Boundary.lean:671:0: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
```

生成された `BoundaryInterchange` section の冒頭に `set_option maxHeartbeats 800000` を 1 行追加した。宣言・証明は変更していない。これで内部ビルドは通った。この変更は **未コミット**で保持する。保存比較では、当該 `replaceMiddle_tail_anticommute` の型ハッシュにも差があるため、その保存を確認済みとは扱っていない。

## 全対象の保存比較

既存の compare_snapshots.py を変更せず、同じ DAG ハッシュ方式・空の name-map と、D3・D4 の旧→新 module-map で比較した。before は 1,012 モジュール、after は 111 モジュール。修飾した ModuleShiftOpposite 自体はこの 111 とは別に上記の単独比較で一致を確認している。

| 項目 | before | after |
| --- | ---: | ---: |
| 採取行 | 11,589 | 9,516 |
| 比較行（補助宣言を親へまとめた後） | 5,294 | 5,540 |
| transient 名 | 508 | 405 |

差分は **76 モジュール・1,681 の (宣言名, 移動後モジュール) に対する 2,585 項目**。

| 差分 | 件数 |
| --- | ---: |
| added | 246 |
| type | 716 |
| body | 908 |
| auxiliaries | 715 |
| removed／kind／axioms／attributes | 0 |

### 読み取りだけの診断

以下は原因調査のための分類で、保存判定を緩和する規則として適用していない。

1. **追加 246 件のうち 242 件は before 原本にも同じ名前・移動先対応の行がある。** 親への束ね方や transient 判定の差が関係する候補。残る 4 件は `DGCellAttachment.Family.appendMap.eq_1`・`eq_2`・`eq_def`（Cells.Boundary）と `Morita.kernelDerivedTensorOnBimoduleCompositionIso.congr_simp`（Morita.CoherenceCompositionKernel）。全 246 件の同一性を確認したわけではない。
2. **型 716 件・本体 908 件の使用定数集合を比較**した。型 700／本体 895 件は差が `_proof_*` の名前だけ。型 15／本体 9 件は使用定数集合が同じだがハッシュが異なる。残る型 1 件・本体 4 件には別の定数差がある。これらはフィールドごとの件数で、宣言数ではない。
3. 型の別の定数差の例は `BalancedTensor.rightTensor_intervalProjection_quasiIso`。`CategoryTheory.Abelian.hasBinaryBiproducts` から `ModuleCat.instHasBinaryBiproducts` へ選択が変わっている。
4. 本体の別の定数差 4 件は match 補助定数の参照差を含む。例えば `DGCellAttachment.Family.includeDoubleFace` は `includeDoubleFace.match_1` から `negateDoubleFace.match_1` へ変わっている。ほかは `DGQuotient.includeDoubleFace`、`FreeDGCategory.pathEvaluation`、`FreeDGCategory.pathMap`。
5. `_proof_*` の例は `BalancedTensor.BalancedFamily` の本体。before の `objectFamily._proof_*` から after の `rightAction._proof_*` へ使用定数が変わっている。型・本体ハッシュの一致や定義的等価性は未証明なので、この分類だけで除外していない。

D3 の move 対象にも次の 3 差分がある（統合による上流の影響を含む）。

| 宣言（KST.SConstruction 名前空間） | 移動先 SharedFunctoriality 以下 | 差分 |
| --- | --- | --- |
| dgFunctorGraphComposition_input_left | DGGraphCompositionInputLeft | type |
| dgFunctorGraphParameter_app | DGFunctorGraphParameter | type |
| dgModuleExtensionCompositionTensorIso | DGModuleExtensionComposition | body |

## 停止状態と記録

未コミット変更は `Resolution/Cells/Boundary.lean` の heartbeat 設定 1 行と、この停止報告。`git diff --check` は終了 0。比較・採取・verify 等の既存の道具は変更していない。

`.lake/verify/dg-w2-b-s14/` に今回の全記録を保存した。前回の `.lake/verify/dg-w2-b/` は上書きしていない。

- `before.json`・`after.json`・`comparison.json`・`state.json`：op 修飾単体の PASS
- `locations.json`：修飾 36 出現
- `internal-state.json`・`internal-build.log`：heartbeat 上限の失敗
- `heartbeat-adjustment.json`・`internal-r2-state.json`・`internal-build-r2.log`：上限調整と内部ビルド PASS
- `before-preserve.json`・`after-preserve.json`・`module-map.json`・`preservation.json`：全対象の保存比較 FAIL
- `after-shards/manifest.json`：after 採取の実コマンド・結果
- `preservation-analysis.json`：全差分のモジュール別集計・使用定数の差・追加行の照合

外部 import・監査一覧の書き換え、ルートと監査対象の下流ビルド、layers.json の DG 規則・PerfectComplex 3 辺、VERIFY_JOBS=3 の verify は未実施。今回の verify summary は存在しない。適用途中の状態なので完成版として main に取り込む段階ではない。
