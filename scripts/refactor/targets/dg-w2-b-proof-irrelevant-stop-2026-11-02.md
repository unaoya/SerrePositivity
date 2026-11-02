# DG-W2(b)：新しい保存規則と pp 比較の STOP（2026-11-02）

> 過去の停止・準備時点の記録です。その後の解消と停止点 2 の結果は [§16 の完了報告](dg-w2-b-universe-replay-2026-11-02.md) を参照。

## 結論

**STOP**。新規則の snapshot 比較に残った差分を §10.34 で調べたところ、13 宣言で universe パラメータの順序が異なる。表示だけの相違ではなく、同じ明示的 universe 引数を指定した場合の型の相違を確認した。現在の一致規則に含めず、外からの import と監査の一覧の付け替え以降は実施していない。

`sequentialCoproductMap.{0, 1, 2}` の明示的な `#check`：

```text
before: {C : Type 1} → [CategoryTheory.Category.{2, 1} C] → ...
after:  {C : Type 2} → [CategoryTheory.Category.{1, 2} C] → ...
```

この検査は両側とも終了 0。元の記録は `before-universe-check.lean/.log` と `after-universe-check.lean/.log`。本文や universe 宣言を直す処置、順序を無視する比較規則の追加はしていない。

## 実行と保存比較

- main の 2aa4f330e までを取り込み、merge commit は `1ff0ac691`。衝突なし。
- scratch の HEAD は `887896bba` のまま。コピーしたのは `scripts/refactor/decl_snapshot.lean` と `compare_snapshots.py` の 2 ファイルだけ。DG の Lean ソースには変更なし。
- 両側の採取は既定の `--proof-irrelevant`。アルゴリズム識別子は `normalized Expr DAG mixHash proof-irrelevant v2`。
- 既存 snapshot_batch.py が旧アルゴリズム名だけを受理するため、/tmp の実行器で期待値の文字列だけを新識別子に置換して実行した。リポジトリの既存道具は編集していない。
- fresh shell、Lake キャッシュの設定、`with_build_lock.sh` による排他で全 Lean 検査を直列実行。
- 内部 111 本 PASS、op 修飾、heartbeat の既報を維持。今回ソースを直す追加コミットはない。

| 側 | 対象モジュール | 生の宣言数 | 秒 | 結果 |
|---|---:|---:|---:|---|
| before | 1013 | 11595 | 246.038 | PASS |
| after | 112 | 9523 | 86.408 | PASS |

統合・移動の元 1,012 本／先 111 本に、op 修飾済みの ModuleShiftOpposite 1 本をそれぞれ加えた。対応表は D3＋D4 のものを使用。

比較は **FAIL、418 件**（追加 246・本体 106・型 43・補助群 23）。正規化後は before 5,299／after 5,545。削除・kind・axioms・attributes の独立した差分項目は 0。旧規則の 2,585 件を上書きせず、別の検査結果として保存した。

## pp の個別調査

追加扱い以外の差分は 163 宣言。各宣言で `#print`、`pp.explicit false` の `#check`、`pp.explicit true` の `#check` を両側から取得した。最終採取は両側とも終了 0、診断エラーなし。

- 通常の #print と #check が一致：145 宣言（105 は明示表示も一致、40 は明示表示に差）。これは pp の照合結果であり、補助群全体を含めた保存 PASS を意味しない。
- 本体の通常表示に生成された `_proof_*` 参照名の差：5 宣言。型の通常・明示表示は一致。
- universe パラメータの順序の差：13 宣言（定義 8、定理 5）。これを STOP の根拠とする。

### universe 順序が異なる 13 宣言

共通の名前空間 `SerrePositivity.DifferentialGraded.` を省略する。

| 宣言 | before | after |
|---|---|---|
| `ResolutionBimodule.canonicalComparisonComposeIso` | `u, v, w, z, v', w', z'` | `u, v, w, v', w', z', z` |
| `ResolutionBimodule.changeComposeIso` | `u, v, w, z, v', w', z', v'', w'', z''` | `u, v, w, v', w', z', z, v'', w'', z''` |
| `sequentialCoproductCoconeOfZero` | `u, v, w` | `u, w, v` |
| `sequentialCoproductCokernel` | `u, v, w` | `u, w, v` |
| `sequentialCoproductDesc` | `u, v, w` | `u, w, v` |
| `sequentialCoproductMap` | `u, v, w` | `u, w, v` |
| `sequentialCoproductMap_desc` | `u, v, w` | `u, w, v` |
| `sequentialCoproductMap_mono_of_moduleCat_functor` | `u, v, w` | `u, w, v` |
| `sequentialCoproductMap_sigmaComparison` | `u, v, w, v_1, u_1` | `u, w, v, v_1, u_1` |
| `sequentialCoproductProjection` | `u, v, w` | `u, w, v` |
| `sequentialCoproductShift` | `u, v, w` | `u, w, v` |
| `sequentialCoproductShift_projection_succ` | `u, v, w` | `u, w, v` |
| `sequentialCoproductShift_projection_zero` | `u, v, w` | `u, w, v` |

### 生成された証明参照名が異なる 5 宣言

- `SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData.evaluationPrefixAction`

```diff
--- before
+++ after
@@ -33,2 +33,2 @@
     (CochainComplex.HomComplex.Cochain.ofHom (P.evaluationOriginalAction x (C.source i) y))
-    SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData.evaluationPrefixAction._proof_1
+    SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData.pathEvaluation._proof_9
```

- `SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData.primitiveAction`

```diff
--- before
+++ after
@@ -30,2 +30,2 @@
       (CategoryTheory.eComp (SerrePositivity.DifferentialGraded.Complex A) (F.obj (C.source i)) (F.obj (C.target i)) y))
-    SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData.primitiveAction._proof_11
+    SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData.primitiveAction._proof_1
```

- `SerrePositivity.DifferentialGraded.DGQuotient.contractionAction`

```diff
--- before
+++ after
@@ -28,2 +28,2 @@
         y))
-    SerrePositivity.DifferentialGraded.DGQuotient.contractionAction._proof_11
+    SerrePositivity.DifferentialGraded.DGQuotient.contractionAction._proof_2
```

- `SerrePositivity.DifferentialGraded.DGQuotient.contractionCochain`

```diff
--- before
+++ after
@@ -18,2 +18,2 @@
       (C.homotopy b))
-    SerrePositivity.DifferentialGraded.DGQuotient.contractionCochain._proof_3
+    SerrePositivity.DifferentialGraded.DGQuotient.contractionCochain._proof_1
```

- `SerrePositivity.DifferentialGraded.DGQuotient.evaluationPrefixAction`

```diff
--- before
+++ after
@@ -32,2 +32,2 @@
       (SerrePositivity.DifferentialGraded.DGQuotient.evaluationOriginalAction A C b x y))
-    SerrePositivity.DifferentialGraded.DGQuotient.evaluationPrefixAction._proof_1
+    SerrePositivity.DifferentialGraded.DGQuotient.contractionAction._proof_2
```

### 追加扱い 246 件の生データ照合

- 240 件：before の生データに同名で存在し、module 対応後の kind・型／本体ハッシュ・公理・属性が一致。親への束ね方の差として記録。
- 2 件：before に同名が存在するが型ハッシュが異なる。
- 4 件：before snapshot の生データに同名がない生成補助宣言。

| 宣言 | 生データ照合 |
|---|---|
| `SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData.cochain.eq_1` | raw_hash_difference |
| `SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData.primitiveAction.eq_1` | raw_hash_difference |
| `SerrePositivity.DifferentialGraded.DGCellAttachment.Family.appendMap.eq_1` | absent_from_before_snapshot |
| `SerrePositivity.DifferentialGraded.DGCellAttachment.Family.appendMap.eq_2` | absent_from_before_snapshot |
| `SerrePositivity.DifferentialGraded.DGCellAttachment.Family.appendMap.eq_def` | absent_from_before_snapshot |
| `SerrePositivity.DifferentialGraded.Morita.kernelDerivedTensorOnBimoduleCompositionIso.congr_simp` | absent_from_before_snapshot |

13 宣言の STOP 条件が成立したため、残る生成補助・親への束ね方を新たな規則で一致扱いする作業は行っていない。追加全 246 件の照合表は `added-review.json` に保存。

## 163 宣言の pp 一覧

`同一` は空白折り返しだけを正規化した pp の一致を表す。明示表示を除外したハッシュを書き換えるなどの処置はしていない。

| 宣言 | 差分項目 | 通常 print | 通常 check | 明示 check | 分類 |
|---|---|---|---|---|---|
| `SerrePositivity.DifferentialGraded.BalancedTensor.Fubini.columnCurry` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.BalancedTensor.balancedFamilyMk` | body,type | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.BalancedTensor.balancedFamily_element` | type | 同一 | 同一 | 差あり | pp_identical |
| `SerrePositivity.DifferentialGraded.BalancedTensor.paramFamilyMk` | body,type | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.BalancedTensor.rightParamMap_element` | type | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.BalancedTensor.rightTensor_intervalProjection_quasiIso` | type | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.BalancedTensor.swapFamily` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.BalancedTensor.uncurryModuleMapFamily` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.BalancedTensor.unswapFamily` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.BalancedTensor.yonedaEvaluation_element` | type | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.Bimodule.ClosedMapFamily` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.Bimodule.closedFamilyTrans` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.Bimodule.closedFamilyTrans_app` | type | 同一 | 同一 | 差あり | pp_identical |
| `SerrePositivity.DifferentialGraded.Bimodule.closedMapFamilyComp` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.Bimodule.closedMapFamilyEquiv` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.Bimodule.closedMapFamilyId` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.Bimodule.closedTransApp` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.Bimodule.diagonalRestrictionMap` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.Bimodule.isoFamilyHom` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.Bimodule.isoFamilyHom_app` | type | 同一 | 同一 | 差あり | pp_identical |
| `SerrePositivity.DifferentialGraded.Bimodule.isoFamilyInv` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.Bimodule.isoFamilyInv_app` | type | 同一 | 同一 | 差あり | pp_identical |
| `SerrePositivity.DifferentialGraded.Bimodule.isoFamily_hom_inv_app` | type | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.Bimodule.isoFamily_inv_hom_app` | type | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.Bimodule.ofParamTrans` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.Bimodule.paramFamilyTrans` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.Bimodule.paramRightAt` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.Bimodule.paramValue` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.Bimodule.param_square_of_values` | type | 同一 | 同一 | 差あり | pp_identical |
| `SerrePositivity.DifferentialGraded.BimoduleCategory.evaluation` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.BimoduleCategory.homEquiv` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.BimoduleCategory.homEquiv_app` | type | 同一 | 同一 | 差あり | pp_identical |
| `SerrePositivity.DifferentialGraded.BimoduleCategory.homEquiv_comp_app` | type | 同一 | 同一 | 差あり | pp_identical |
| `SerrePositivity.DifferentialGraded.BimoduleCategory.isoOfFamily` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.BimoduleCategory.middleLeftRestrictionMap` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionMap` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionMap_component` | type | 同一 | 同一 | 差あり | pp_identical |
| `SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionMap_naturality` | type | 同一 | 同一 | 差あり | pp_identical |
| `SerrePositivity.DifferentialGraded.BimoduleParamTrans` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.BimoduleSemifreeResolution.obj` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.BimoduleTensor.associatorHom_app` | type | 同一 | 同一 | 差あり | pp_identical |
| `SerrePositivity.DifferentialGraded.BimoduleTensor.associatorHom_π` | type | 同一 | 同一 | 差あり | pp_identical |
| `SerrePositivity.DifferentialGraded.BimoduleTensor.associatorInv_app` | type | 同一 | 同一 | 差あり | pp_identical |
| `SerrePositivity.DifferentialGraded.BimoduleTensor.associatorInv_π` | type | 同一 | 同一 | 差あり | pp_identical |
| `SerrePositivity.DifferentialGraded.BimoduleTensor.associator_firstParam` | type | 同一 | 同一 | 差あり | pp_identical |
| `SerrePositivity.DifferentialGraded.BimoduleTensor.associator_hom_inv_app` | type | 同一 | 同一 | 差あり | pp_identical |
| `SerrePositivity.DifferentialGraded.BimoduleTensor.associator_inv_hom_app` | type | 同一 | 同一 | 差あり | pp_identical |
| `SerrePositivity.DifferentialGraded.BimoduleTensor.associator_lastParam` | type | 同一 | 同一 | 差あり | pp_identical |
| `SerrePositivity.DifferentialGraded.BimoduleTensor.associator_middleParam` | type | 同一 | 同一 | 差あり | pp_identical |
| `SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.BimoduleTensor.middleRestrictionComparisonMap` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.BimoduleTensorModule.map` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.BimoduleTensorModule.objectPreimage` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.DGCategoryCellResolution.stage` | auxiliaries | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.DGCategoryCellResolution.stageComparison` | auxiliaries | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.DGCellAttachment.Family` | auxiliaries | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData` | auxiliaries | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData.boundaryOriginalAction` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData.cochain` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData.evaluationOriginalAction` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData.evaluationPrefixAction` | body | 差あり | 同一 | 同一 | generated_proof_reference |
| `SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData.extension` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData.pathEvaluation` | auxiliaries | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData.pathEvaluationTail` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData.primitiveAction` | body | 差あり | 同一 | 同一 | generated_proof_reference |
| `SerrePositivity.DifferentialGraded.DGCellAttachment.Family.appendMap` | auxiliaries | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.DGCellAttachment.Family.includeDoubleFace` | auxiliaries | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.DGCellAttachment.Family.prependMap` | auxiliaries | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replaceFace` | auxiliaries | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.DGCellAttachment.Family.term` | auxiliaries | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.DGGeneratedHomSymbol` | auxiliaries | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.DGGeneratedHomWord` | auxiliaries | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.DGGeneratedHomWord.encode` | auxiliaries | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.DGGeneratedHomWord.evaluate` | auxiliaries | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.DGQuotient.appendMap` | auxiliaries | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.DGQuotient.contractionAction` | body | 差あり | 同一 | 同一 | generated_proof_reference |
| `SerrePositivity.DifferentialGraded.DGQuotient.contractionCochain` | body | 差あり | 同一 | 同一 | generated_proof_reference |
| `SerrePositivity.DifferentialGraded.DGQuotient.evaluationOriginalAction` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.DGQuotient.evaluationPrefixAction` | body | 差あり | 同一 | 同一 | generated_proof_reference |
| `SerrePositivity.DifferentialGraded.DGQuotient.graphCompletedPerfectComparisonFunctorCommShift` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.DGQuotient.graphCompletedPerfectComparisonInverseCommShift` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.DGQuotient.graphPairLocalMoritaSquareTriangle` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.DGQuotient.graphQuotientPerfectHomotopyFunctorCommShift` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.DGQuotient.graphQuotientPerfectHomotopySquareTriangle` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.DGQuotient.includeDoubleFace` | auxiliaries | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.DGQuotient.localScalarTriaExtensionCommShift` | body | 同一 | 同一 | 差あり | pp_identical |
| `SerrePositivity.DifferentialGraded.DGQuotient.localScalarTriaSquareTriangle` | body | 同一 | 同一 | 差あり | pp_identical |
| `SerrePositivity.DifferentialGraded.DGQuotient.mainKernelCompletedQuotientFunctorCommShift` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.DGQuotient.mainKernelLocalPerfectSquareTriangle` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.DGQuotient.mainKernelMoritaLocalPerfectSquareTriangle` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.DGQuotient.pathEvaluation` | auxiliaries | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.DGQuotient.pathEvaluationTail` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.DGQuotient.pathTensorRightDG` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.DGQuotient.prependMap` | auxiliaries | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.DGQuotient.quotientScalarRepresentableIso` | body | 同一 | 同一 | 差あり | pp_identical |
| `SerrePositivity.DifferentialGraded.DGQuotient.quotientScalarTriaFunctorCommShift` | body | 同一 | 同一 | 差あり | pp_identical |
| `SerrePositivity.DifferentialGraded.DGQuotient.scalarCompletedTriaFunctorCommShift` | body | 同一 | 同一 | 差あり | pp_identical |
| `SerrePositivity.DifferentialGraded.DGQuotient.sourceScalarLocalQuotientSquare` | body | 同一 | 同一 | 差あり | pp_identical |
| `SerrePositivity.DifferentialGraded.FixedObjectAugmentation` | auxiliaries | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.FixedObjectAugmentation.Map` | auxiliaries | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.FixedObjectAugmentation.Map.attachedSourceFunctor` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.FixedObjectAugmentation.Map.augmentationThenFunctor` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.FixedObjectAugmentation.Map.comparisonThenAugmentation` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.FixedObjectAugmentation.Objects` | auxiliaries | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.FixedObjectAugmentation.cellGenerator` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.FreeDGCategory.appendPath` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.FreeDGCategory.wordTensor` | auxiliaries | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.KFlatDGResolution.comparisonLeftModuleDerivedEquivalence` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.KFlatDGResolution.comparisonRightModuleDerivedEquivalence` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.Morita.kernelClosedFamilyNatTrans` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.Morita.kernelTensorMap_app` | type | 同一 | 同一 | 差あり | pp_identical |
| `SerrePositivity.DifferentialGraded.Morita.scalarKernelMap` | body | 同一 | 同一 | 差あり | pp_identical |
| `SerrePositivity.DifferentialGraded.ResolutionBimodule.canonicalComparisonComposeIso` | body | 差あり | 差あり | 差あり | universe_parameter_order |
| `SerrePositivity.DifferentialGraded.ResolutionBimodule.changeComposeIso` | body | 差あり | 差あり | 差あり | universe_parameter_order |
| `SerrePositivity.DifferentialGraded.bimoduleCanonicalSemifreeResolution` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.dgHomMapShortComplex` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.endomorphismDerivedTensorBaseChange` | body | 同一 | 同一 | 差あり | pp_identical |
| `SerrePositivity.DifferentialGraded.endomorphismEvaluationFamily` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.endomorphismModuleEvaluationFamily` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.endomorphismRegularModuleIso` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.moduleCompactComparison` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.moduleCompactHomLinearEquiv` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.moduleFiniteCellFamilyZero` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.moduleFiniteCellStage` | auxiliaries | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.moduleHomEvaluateAt` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.moduleRepresentableDerivedCoyoneda` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.moduleRepresentableDerivedHomEquiv` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.moduleRepresentableDerivedHomLinearEquiv` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.moduleRepresentableDerivedHomologyEquiv` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.moduleRepresentableDerivedHomologyLinearEquiv` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.moduleRepresentableHomologyPreNatIso` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.moduleSequentialConeDesc` | body,type | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.moduleSequentialConeDesc_quasiIso` | type | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.moduleSequentialShortComplex` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.normalizedDGModuleFunctorShiftIso` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.perfectEndomorphismEnhancementScalarTensorComparison` | body | 同一 | 同一 | 差あり | pp_identical |
| `SerrePositivity.DifferentialGraded.perfectEndomorphismEnhancementScalarTensorTriangleSquareIso` | body | 同一 | 同一 | 差あり | pp_identical |
| `SerrePositivity.DifferentialGraded.perfectEndomorphismTensorBaseChange` | body | 同一 | 同一 | 差あり | pp_identical |
| `SerrePositivity.DifferentialGraded.perfectEndomorphismTensorScalarEvaluationIso` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.scalarPerfectClosedExtension` | body | 同一 | 同一 | 差あり | pp_identical |
| `SerrePositivity.DifferentialGraded.scalarPerfectDG` | body | 同一 | 同一 | 差あり | pp_identical |
| `SerrePositivity.DifferentialGraded.sequentialCoproductCoconeOfZero` | body,type | 差あり | 差あり | 差あり | universe_parameter_order |
| `SerrePositivity.DifferentialGraded.sequentialCoproductCokernel` | body,type | 差あり | 差あり | 差あり | universe_parameter_order |
| `SerrePositivity.DifferentialGraded.sequentialCoproductDesc` | body,type | 差あり | 差あり | 差あり | universe_parameter_order |
| `SerrePositivity.DifferentialGraded.sequentialCoproductMap` | body,type | 差あり | 差あり | 差あり | universe_parameter_order |
| `SerrePositivity.DifferentialGraded.sequentialCoproductMap_desc` | type | 差あり | 差あり | 差あり | universe_parameter_order |
| `SerrePositivity.DifferentialGraded.sequentialCoproductMap_moduleCat_injective` | type | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.sequentialCoproductMap_moduleCat_mono` | type | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.DifferentialGraded.sequentialCoproductMap_mono_of_moduleCat_functor` | type | 差あり | 差あり | 差あり | universe_parameter_order |
| `SerrePositivity.DifferentialGraded.sequentialCoproductMap_sigmaComparison` | type | 差あり | 差あり | 差あり | universe_parameter_order |
| `SerrePositivity.DifferentialGraded.sequentialCoproductProjection` | body,type | 差あり | 差あり | 差あり | universe_parameter_order |
| `SerrePositivity.DifferentialGraded.sequentialCoproductShift` | body,type | 差あり | 差あり | 差あり | universe_parameter_order |
| `SerrePositivity.DifferentialGraded.sequentialCoproductShift_projection_succ` | type | 差あり | 差あり | 差あり | universe_parameter_order |
| `SerrePositivity.DifferentialGraded.sequentialCoproductShift_projection_zero` | type | 差あり | 差あり | 差あり | universe_parameter_order |
| `SerrePositivity.DifferentialGraded.sourceScalarRepresentableIso` | body | 同一 | 同一 | 差あり | pp_identical |
| `SerrePositivity.DifferentialGraded.sourceScalarTriaFunctorCommShift` | body | 同一 | 同一 | 差あり | pp_identical |
| `SerrePositivity.DifferentialGraded.sourceScalarVerdierFactors` | body | 同一 | 同一 | 差あり | pp_identical |
| `SerrePositivity.DifferentialGraded.sourceScalarVerdierFunctor` | body | 同一 | 同一 | 差あり | pp_identical |
| `SerrePositivity.DifferentialGraded.sourceScalarVerdierFunctorCommShift` | body | 同一 | 同一 | 差あり | pp_identical |
| `SerrePositivity.DifferentialGraded.sourceScalarVerdierLifting` | body | 同一 | 同一 | 差あり | pp_identical |
| `SerrePositivity.DifferentialGraded.triaToPerfectCommShift` | body | 同一 | 同一 | 同一 | pp_identical |
| `SerrePositivity.KST.SConstruction.dgFunctorGraphComposition_input_left` | type | 同一 | 同一 | 差あり | pp_identical |
| `SerrePositivity.KST.SConstruction.dgFunctorGraphParameter_app` | type | 同一 | 同一 | 差あり | pp_identical |

## 記録と再開点

すべての記録を `.lake/verify/dg-w2-b-v2/` に保存（作業原本 `/tmp/dgw2b-v2/`）。`comparison.json`、`pp-summary.json`、`pp-parsed.json`、両側の shard と manifest、pp の Lean 入力と出力、`universe-check-state.json`、`stop-summary.json` を含む。

外からの import・監査一覧の付け替え、下流ビルド、layers.json の DG 規則、verify は未実施。verify 再開時の設定は指定どおり `VERIFY_JOBS=6 VERIFY_MEMORY_GB=45`。scratch は再調査に必要なので保持する。今回の STOP は停止点 2 の完了報告ではない。
