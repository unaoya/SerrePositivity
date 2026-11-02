# DG の層規則案（§11.3）

main `40ec57e06` のソースで、設定だけを変えた 2 回の read-only report を比較した。設定ファイルと出力は /tmp に置いた。両実行とも REPORT、対象は同じ 33,191 モジュール・113,048 辺。

```sh
python3 -B ../SerrePositivity/scripts/refactor/layer_check.py --report --root ../SerrePositivity --output /tmp/dg11-prep/main-report.json
python3 -B ../SerrePositivity/scripts/refactor/layer_check.py --report --root ../SerrePositivity --config /tmp/dg11-prep/layers.json --output /tmp/dg11-prep/proposed-report.json
```

現行設定は DG を層に分類せず、DG 発の直接違反は 0 件。提案設定では DG を rank −1（∞ の土台より下）に分類し、DG・HomologicalAlgebra・CategoryTheory・Mathlib だけを直接 import 可とする。現状の生の直接違反は **18 件**（KST 13、IC/Derived 1、Asymptotic 1、PerfectComplex 3）。このうち §9-2 の 3 辺を個別に許すと **15 件**。これは D3 前の値。

既存チェッカの `allowed_until_move` は W2a/W2b の禁止閉包の参照先 prefix にのみ作用し、`restricted_imports` の直接違反を除去しない。そのため、同じ 3 つを `exceptions` にも正確な from/to の組で記す。raw の `direct_violations` は例外込みの 18 を表示する。現在の `--enforce` は core だけを検査する。DG は core に入れると自層が禁止閉包に当たるため core に加えず、DG の受入時は direct_violations の DG 行から有効な例外を引いて検査する。例外の期限 W2b は現行スキーマの上限で、移動が済み次第外す。

main 取り込みにより、旧 ProjectiveBounds は KoszulLength、旧 HomotopyCategory は Perfect.HomotopyCategory になった。D4 で import 元が Perfect.Basic または Perfect.Ring.FiniteProjectiveComparison に変わったら exceptions の from も同時に更新する。D3/D4 適用前のパッチ案を以下に示す。

| 現在の DG 側 | 参照先 | 扱い |
| --- | --- | --- |
| `Functor.ClosedConjugationPasting` | `KST.SConstruction.DGFunctorHomConjugation` | D3 で解消予定 |
| `Functor.ClosedConjugationTensorComposition` | `KST.SConstruction.DGClosedIsoConjugationLaws` | D3 で解消予定 |
| `Functor.InducedClosedConjugate` | `KST.SConstruction.DGClosedComparisonIso` | D3 で解消予定 |
| `Functor.InducedClosedConjugate` | `KST.SConstruction.DGClosedIsoConjugation` | D3 で解消予定 |
| `Functor.InducedClosedParameter` | `KST.SConstruction.DGFunctorHomPrecomposition` | D3 で解消予定 |
| `Functor.InducedClosedParameter` | `KST.SConstruction.DGParameterConjugation` | D3 で解消予定 |
| `Functor.InducedClosedTransport` | `KST.SConstruction.DGClosedIsoConjugationLaws` | D3 で解消予定 |
| `Functor.ModuleExtensionConjugation` | `KST.SConstruction.DGConjugationNaturality` | D3 で解消予定 |
| `Functor.ModuleExtensionConjugation` | `KST.SConstruction.DGModuleExtensionComposition` | D3 で解消予定 |
| `Module.ExtensionRepresentableClosedNaturality` | `KST.SConstruction.DGFunctorClosedNaturality` | D3 で解消予定 |
| `Module.ExtensionRepresentableClosedNaturality` | `KST.SConstruction.DGGraphCompositionInputLeft` | D3 で解消予定 |
| `Module.ExtensionRepresentableComposition` | `KST.SConstruction.DGModuleExtensionEvaluationTransport` | D3 で解消予定 |
| `Module.ExtensionRepresentableComposition` | `KST.SConstruction.DGModuleExtensionInputTransport` | D3 で解消予定 |
| `Perfect.FiniteProjectiveImage` | `PerfectComplex.KoszulLength` | 一時許容 |
| `Perfect.StrictComplexEnhancement` | `PerfectComplex.Perfect.HomotopyCategory` | 一時許容 |
| `Perfect.StrictComplexOperations` | `PerfectComplex.BiproductPerfect` | 一時許容 |
| `Presentation.GeneratedHomFunctorLift` | `InfinityCategories.Derived.DGObjectImage` | D3 で解消予定 |
| `Verdier.OrderSquare` | `Asymptotic.PaperRankQuotient` | D3 で解消予定 |

```diff
--- a/scripts/refactor/layers.json
+++ b/scripts/refactor/layers.json
@@ -98,6 +98,13 @@
       "rank": 10,
       "prefixes": [
         "SerrePositivity.InfinityCategories.Derived"
+      ]
+    },
+    {
+      "name": "DG",
+      "rank": -1,
+      "prefixes": [
+        "SerrePositivity.DifferentialGraded"
       ]
     }
   ],
@@ -141,7 +148,10 @@
   },
   "allowed_until_move": [
     "SerrePositivity.Spectra.PointedSimplicialSet",
-    "SerrePositivity.Spectra.Pointed"
+    "SerrePositivity.Spectra.Pointed",
+    "SerrePositivity.PerfectComplex.KoszulLength",
+    "SerrePositivity.PerfectComplex.BiproductPerfect",
+    "SerrePositivity.PerfectComplex.Perfect.HomotopyCategory"
   ],
   "restricted_imports": {
     "Core": {
@@ -162,9 +172,38 @@
       "external_prefixes": [
         "Mathlib"
       ]
+    },
+    "DG": {
+      "layers": [
+        "DG"
+      ],
+      "external_prefixes": [
+        "SerrePositivity.HomologicalAlgebra",
+        "SerrePositivity.CategoryTheory",
+        "Mathlib"
+      ]
     }
   },
-  "exceptions": [],
+  "exceptions": [
+    {
+      "from": "SerrePositivity.DifferentialGraded.Perfect.FiniteProjectiveImage",
+      "to": "SerrePositivity.PerfectComplex.KoszulLength",
+      "reason": "DG-W2 §9-2、論文側の配置確定まで。移動時に再照合。",
+      "expires": "W2b"
+    },
+    {
+      "from": "SerrePositivity.DifferentialGraded.Perfect.StrictComplexOperations",
+      "to": "SerrePositivity.PerfectComplex.BiproductPerfect",
+      "reason": "DG-W2 §9-2、論文側の配置確定まで。移動時に再照合。",
+      "expires": "W2b"
+    },
+    {
+      "from": "SerrePositivity.DifferentialGraded.Perfect.StrictComplexEnhancement",
+      "to": "SerrePositivity.PerfectComplex.Perfect.HomotopyCategory",
+      "reason": "DG-W2 §9-2、論文側の配置確定まで。移動時に再照合。",
+      "expires": "W2b"
+    }
+  ],
   "prefix_matching": {
     "rule": "m == p or m.startswith(p + \".\")",
     "layer_precedence": "longest matching prefix",
```
