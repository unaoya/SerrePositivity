> **§10.7/10.8反映：必要15本をW1へ、Stable側はStable.Roof。FirstTriangleIndexの移動・pruneはW2cへ。最新の採用一覧・判定は [w1.md](w1.md)。以下は調査時の証拠。**

# IF-W0-3 roof の分析（§10.6）

基準 main `502e78840`。専用 worktree の一時試験と復元まで完了した roof の分析。改訂版 §7-1 全体の結果は [w1.md](w1.md) を参照。roof の3入口は判断待ちで JSON の外に置く。

## 集合と語彙判定

Derived 内だけを辿った集合は 379 本。そのうち C は **23 本**、除外は **356 本**。旧判定 C=14 から9本増えた。識別子の DG/dg 接頭辞、または Cochain・HomologicalComplex・ChainComplex・ModuleCat・CommRing・Bimodule の完全一致だけを印とした。コメントと文字列は除き、import と namespace の識別子は含める。Edge、Subcomplex、FullSubcomplex、Simplex、単独 Complex/Module は印にしない。これは指定された語彙判定であり、除外356本すべてに数学的な DG 依存が本質的だと判定したものではない。

除外の全件・一致した識別子・行は [w1-roof-excluded.md](w1-roof-excluded.md)。機械記録は `../../../.lake/verify/ifw0-3-addendum6/roof/roof-cluster.json`。

## C からの漏れ

| 元 | 直接 import | uses_modules と処置 |
| --- | --- | --- |
| FirstTriangleIndex | Derived.SpanJoinCells | そのモジュールの定数を使う宣言なし。prune・保存検査・下流ビルド・復元 PASS。Mathlib.Order.Fin.Basic のみへ縮小。 |
| RoofPinchedSlicePostcomp | Derived.RoofSliceTransport | そのモジュールの定数を使う宣言なし。prune・保存検査・下流ビルド・復元 PASS。Core.PinchedSlice、Derived.PinchedEndpointTransport、Derived.SliceOverEqualityTransport の3 import。 |
| SpanUnknownIndex | Derived.SpanSuffixIndex | spanVertex_cases と spanUnknown_cases が使う。単純除去しない。 |

`uses_modules` の証拠は `roof/leak-uses.json`。対象の元ソースがスナップショットと完全一致することを照合した。型だけでなく証明項の定数も調べている。

prune と下流補充を反映した後に残る漏れ：

- `Derived.SpanUnknownIndex` → `Derived.SpanSuffixIndex`

## 実試験と下流補充

両試験とも `python3 -B scripts/refactor/prune_imports.py <対象> --snapshot <変更前 snapshot> --output <計画 JSON>` を実行。元ファイルの宣言を保つ inclusion-minimal な import 集合を採用し、影響範囲の下流ビルド後に元ソースを復元した。ログは全体を `rg -n "^error:"` で検索した。下流の初回・中間ビルドには次表の失敗があり、修復後の最終ビルドが成功した。

| 対象 | 下流対象本数 | 最終下流ビルド秒 | 復元ビルド秒 | 結果 |
| --- | ---: | ---: | ---: | --- |
| FirstTriangleIndex | 4090 | 6255.712 | 7.325 | PASS・復元済み |
| RoofPinchedSlicePostcomp | 1522 | 2140.809 | 125.060 | PASS・復元済み |

### 追加した直接 import

| 下流モジュール | 追加 import |
| --- | --- |
| `Derived.DGModuleAllResolvedExact` | `Derived.DGModuleStability` |
| `Derived.DGModuleResolvedFunctorExact` | `Derived.DGModuleStability` |
| `Derived.DGPinchedCompositionFamilyGeneral` | `DGNerve.Functor` |
| `Derived.JoinFirstTriangle` | `Derived.SpanJoinCells` |
| `Derived.RightKanSliceRoof` | `Core.InnerPullback`、`F1.Fibrations.CartesianFibration` |
| `Derived.TerminalConeSectionEdges` | `Derived.DGRoofSliceVertices` |
| `Stable.LoopEquivalenceCofiberExists` | `Stable.CofiberPushoutComparison` |

各補充先について、元の状態のビルドと snapshot → 直接 import の追加 → ビルドと snapshot → 型・属性・公理等の保存比較を行った。補充先の変更も試験後に復元済み。

### 検出した下流エラー

| 対象 | 試行 | 終了コード | エラー先頭3行 |
| --- | --- | ---: | --- |
| FirstTriangleIndex | downstream-build-0-try0 | -2 | error: SerrePositivity/InfinityCategories/Derived/JoinFirstTriangle.lean:15:5: unknown namespace CategoryTheory<br>error: SerrePositivity/InfinityCategories/Derived/JoinFirstTriangle.lean:16:12: unknown namespace Simplicial<br>error: SerrePositivity/InfinityCategories/Derived/JoinFirstTriangle.lean:22:13: expected token |
| RoofPinchedSlicePostcomp | downstream-build-0-try0 | -2 | error: SerrePositivity/InfinityCategories/Derived/DGPinchedCompositionFamilyGeneral.lean:25:68: Unknown constant SerrePositivity.InfinityCategories.dgNerve.map<br>error: SerrePositivity/InfinityCategories/Derived/DGPinchedCompositionFamilyGeneral.lean:35:74: Unknown constant SerrePositivity.InfinityCategories.dgNerve.map<br>error: SerrePositivity/InfinityCategories/Derived/DGPinchedCompositionFamilyGeneral.lean:38:63: Unknown constant SerrePositivity.InfinityCategories.dgNerve.map |
| RoofPinchedSlicePostcomp | downstream-build-0-try1 | -2 | error: SerrePositivity/InfinityCategories/Derived/DGModuleAllResolvedExact.lean:34:10: failed to synthesize instance of type class<br>  IsStable (dgNerve R (RightModule R E))<br> |
| RoofPinchedSlicePostcomp | downstream-build-0-try2 | -2 | error: SerrePositivity/InfinityCategories/Derived/RightKanSliceRoof.lean:31:37: failed to synthesize instance of type class<br>  RightFibration (sliceOverProjection (SSet.yonedaEquiv.symm b))<br> |
| RoofPinchedSlicePostcomp | downstream-build-0-try3 | -2 | error: SerrePositivity/InfinityCategories/Derived/TerminalConeSectionEdges.lean:22:11: Unknown identifier roofPointSliceVertexEdge<br>error: SerrePositivity/InfinityCategories/Derived/TerminalConeSectionEdges.lean:24:13: Unknown identifier roofPointSliceVertexEdge<br>error: SerrePositivity/InfinityCategories/Derived/TerminalConeSectionEdges.lean:26:13: Unknown identifier roofPointSliceVertexEdge |
| RoofPinchedSlicePostcomp | downstream-build-0-try4 | -2 | error: SerrePositivity/InfinityCategories/Derived/DGModuleResolvedFunctorExact.lean:35:10: failed to synthesize instance of type class<br>  IsStable (dgNerve R (RightModule R E))<br> |
| RoofPinchedSlicePostcomp | downstream-build-0-try5 | -2 | error: SerrePositivity/InfinityCategories/Stable/LoopEquivalenceCofiberExists.lean:41:24: Unknown identifier squareBottomEdge_transpose<br>error: SerrePositivity/InfinityCategories/Stable/LoopEquivalenceCofiberExists.lean:29:34: unsolved goals<br>X : SSet |

非零の下流試行は、失敗を検出した時点で当該 Lake を停止して補充へ進んだため、通常は -2。理由は縮小した public import の再公開から定義・インスタンスが失われたこと。候補 import の個別除去で意図的に失敗した試行も記録に残し、最終成功と混同していない。全コマンド・各段秒数・保存比較は2本の `roof/*-prune.json` とそこに記載した `prune-*/results.json`。

## 閉包に基づく移し先の案

C 内の相互依存も推移的に辿り、C の外に必要な層から最も低い配置を選んだ。49本の純粋 move と同時実施した場合を主表とする。単にファイルの語彙が純粋なだけでは下層に置かない。

| C のモジュール | 閉包総数（自己除外） | 配置案 | 既存 W1 move と重なる場合 |
| --- | ---: | --- | --- |
| `Derived.ConeEdgeCompatibility` | 21 | `Core.Roof.ConeEdgeCompatibility` | `Core.ConeEdgeCompatibility` |
| `Derived.CosliceBoundaryFromJoinFaces` | 22 | `Core.Roof.CosliceBoundaryFromJoinFaces` | — |
| `Derived.FirstTriangleIndex` | 1 | `Core.Roof.FirstTriangleIndex` | — |
| `Derived.FunctorRightConstantSquare` | 117 | `F1B.Roof.FunctorRightConstantSquare` | `F1B.FunctorRightConstantSquare` |
| `Derived.FunctorSliceEvaluationComponents` | 697 | `Stable.Verdier.Fractions.FunctorSliceEvaluationComponents` | — |
| `Derived.FunctorSliceTerminal` | 670 | `Stable.Verdier.Fractions.FunctorSliceTerminal` | — |
| `Derived.HomotopyPostcomposition` | 271 | `F1B.Roof.HomotopyPostcomposition` | — |
| `Derived.HomotopyPostcompositionEvaluation` | 274 | `Stable.Verdier.Fractions.HomotopyPostcompositionEvaluation` | — |
| `Derived.PinchedEndpointTransport` | 46 | `Core.Roof.PinchedEndpointTransport` | — |
| `Derived.PinchedFamilyComposition` | 138 | `F1B.Roof.PinchedFamilyComposition` | `F1B.PinchedFamilyComposition` |
| `Derived.PrismFunctorSquare` | 133 | `F1B.Roof.PrismFunctorSquare` | `F1B.PrismFunctorSquare` |
| `Derived.RebaseCocone` | 22 | `Core.Roof.RebaseCocone` | — |
| `Derived.RightFibrationReflection` | 75 | `Core.Roof.RightFibrationReflection` | `Core.RightFibrationReflection` |
| `Derived.RightFibrationTerminalRepresentation` | 630 | `F1B.Roof.RightFibrationTerminalRepresentation` | — |
| `Derived.RoofPinchedSlicePostcomp` | 57 | `Core.Roof.RoofPinchedSlicePostcomp` | — |
| `Derived.RoofTargetFunctor` | 129 | `F1B.Roof.RoofTargetFunctor` | — |
| `Derived.SliceEvaluationHomotopy` | 691 | `Stable.Verdier.Fractions.SliceEvaluationHomotopy` | — |
| `Derived.SliceEvaluationPinched` | 706 | `Stable.Verdier.Fractions.SliceEvaluationPinched` | — |
| `Derived.SliceOverEqualityTransport` | 6 | `Core.Roof.SliceOverEqualityTransport` | — |
| `Derived.SlicePrismFamilyComposition` | 137 | `F1B.Roof.SlicePrismFamilyComposition` | `F1B.SlicePrismFamilyComposition` |
| `Derived.SpanIndexGeometry` | 60 | 保留：C の外への禁止依存が残る | — |
| `Derived.SpanUnknownIndex` | 59 | 保留：C の外への禁止依存が残る | — |
| `Derived.SquareLegCompatibility` | 27 | `Core.Roof.SquareLegCompatibility` | — |

配置別本数：Core.Roof 9、F1B.Roof 7、Stable.Verdier.Fractions 5、保留 2。既存 move との重なりは 6 本で、重複した移動項目は作らない。49 move なしの比較と各層での禁止依存・経路は `roof/closure-placement.json`。

## 使っている漏れを切る案

`SpanSuffixIndex` の6宣言のうち、`spanSuffixFaces` と `mem_spanSuffixFaces` の2宣言を `Core.Roof.SpanSuffixFaces` へ出す案。`SpanUnknownIndex` の2補題と `SpanIndexGeometry` の本文はこの2宣言を使っている。残る4宣言は元に残す。とくに `spanSuffixFaces_covers` の型は `DGNerve.SelectedFaces.CoversVertices` を参照するため、6宣言を無条件で Core へ動かさない。分割時には必要な Mathlib の Finset import を直接指定して prune・保存比較・下流ビルドを行う。この追加 split は案であり、実行も JSON 登録もまだ行っていない。

## prune 後に入口から必要になる部分集合

規則で定めた C=23 は上記のまま保持する。一方、実際の2本の prune と下流補充の後で3入口から Derived 内だけを辿り直すと **15 本**になる。そのうち元の C は 15 本、語彙で除外した側は 0 本。これは C の定義の差し替えではなく、入口に必要な範囲を縮める追加計測。

下表は元の三案比較と揃えて、3入口とも F1B へ下ろすと仮定した S(v) の大きさ。Stable 配置を提案したものまで F1B へ移す勧告ではない。

| 入口の参照先 | prune 後の pull-down 本数（F1B 仮定） | DG・KST・モデル圏の汚染本数 |
| --- | ---: | ---: |
| `Derived.SliceEvaluationPinched` | 40 | 0 |
| `Derived.RightFibrationTerminalRepresentation` | 5 | 0 |
| `Derived.RoofTargetFunctor` | 4 | 0 |

元の C のうち `SpanUnknownIndex` と `SpanIndexGeometry` はこの15本には含まれない。従って、それらに残る漏れと追加 split 案は C 全体を移す場合の課題であり、prune 後の3入口に必要な部分集合の障害とは区別する。

全リストは `roof/post-prune-seed-closure.json`。roof 3入口を含む塊を W1 に入れるか W2c/R52 に回すかは、以上をもとに判断を依頼する。これらの roof 移動を実施済みとして W1 の終了条件を判定しない。
