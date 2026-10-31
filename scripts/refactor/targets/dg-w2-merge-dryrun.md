# DG-W2(a) 草案と検証記録

基点：`3af962416`、ブランチ：`infra/dg-w2`。DG-W1 の worktree を継続使用。
main の新しいコミットは取り込まず、計画文書は `git show main:formalization-plans/dg-codex-w2.md` で読んだ。
(a) の道具・試験・草案だけを作成し、(b) の移動・分割・統合は一切適用していない。
既存ファイルは変更していない（README の追記も今回の「新しいファイルだけ」に従い実施しない）。

## 対応表と所有範囲

**対応表 981 → 980**。`Morita/ScalarExtensionKernelOutputComponents.lean` は main の作業木だけにある未追跡の作業途中ファイルなので、§5-0 に従い除外した。他の 980 本は `git ls-files` と現存ファイルを照合済み。
78 統合先の連結順・仮名は対応表を維持。D3 は move 33 件（SConstruction A 17・B 9、共有関手性 3、ObjectImage 1、Asymptotic 3）と split 2 件。
群 B の 9 本は `DGFunctorGraph{Composition,Parameter,Units}`・`DGGraphCompositionInputLeft`・`DGModuleExtension{Composition,EvaluationTransport,Identity,InputTransport}`・`DGConjugationNaturality`。最後のものは加群延長共役の共通の自然性として分類した。

実装・試験・dry-run の作業時間：約 27 分（新規ファイル作成開始 17:08 から 17:35 頃、JST。事前の計画確認を除く）。

## 実行した試験

- `python3 -B -m unittest discover -s scripts/refactor -p 'test_*.py'`：終了 0、66 件（65 成功、環境変数未指定の Lean 試験 1 件 skip）、24.194 秒。
- 作業前の同じ HEAD の通常試験：30 件 PASS。計画にある 145 件は、この基点の試験数とは異なる。未通知の main は merge していない。
- `DG_W2_LEAN_TEST=1 PYTHONPATH=scripts/refactor python3 -B -m unittest test_merge_modules.LeanMergeTest`：終了 0、1 件 PASS、91.422 秒。`with_build_lock.sh --wait 0` 経由で実行し、鍵を取得できた。実ビルドは `Mathlib.Data.Nat.Basic` を import する一時ソース 2 本と、その統合先だけ。前後の `decl_snapshot.lean` と `compare_snapshots.py` による保存検査は一致。一時ソース・index エントリ・生成物・鍵は掃除済み。一度成功した後はこの Lean 試験を再実行せず、通常試験では opt-in にしている。
- `zsh -n scripts/refactor/with_build_lock.sh` と `zsh -n scripts/refactor/warm_build_dir.sh`：終了 0。
- `python3 -B scripts/refactor/merge_modules.py scripts/refactor/targets/dg-w2-merge-plan.json --area SerrePositivity.DifferentialGraded --check --report scripts/refactor/targets/dg-w2-merge-dryrun.md --max-lines 1500`：終了 0（警告あり）。下の詳細表はこの dry-run に基づく。
- 排他試験：直列実行、使用中の即時保留、古い鍵、終了コード透過、中断時の子プロセス終了と鍵の掃除。
- 複製試験：小さな一時ディレクトリだけで実 rsync、削除同期、packages 保持、23/24 の消失ログ（標準・macOS 書式）、50 件以上・別の場所・別種エラーの拒否、複製元の稼働確認、`--yes` 待機、manifest 不一致、no-build の未知エラー。実 worktree のキャッシュ複製はしていない。
- 新規実装中に直した点：複合 namespace を部分ごとに閉じる Lean の構文、模擬 rsync が rsync 自身から再帰呼出しされない PATH の設定。既存の道具への修正は 0。

## 大きさ・警告の集計

生成行数は最小 163、中央値 1066、平均 1054.3、最大 1605。500 行以下 7、501–1,000 行 27、1,001–1,500 行 32、1,500 行超 12 件。元ファイルの行数の合計と、見出し・section・統合先 docstring を含む生成行数を区別する。上限を超える群をこちらで再分割してはいない。

| 1,500 行超の統合先（DG からの相対名） | 生成行数 |
| --- | ---: |
| `Tensor.ScalarExtension1` | 1521 |
| `Quotient.DerivedComparison1` | 1570 |
| `Quotient.DerivedComparison3` | 1545 |
| `Tensor.Enriched` | 1582 |
| `Tensor.Bimodule1` | 1581 |
| `Tensor.Associator1` | 1605 |
| `Tensor.Associator3` | 1515 |
| `Resolution.Cells.Path` | 1523 |
| `Morita.CoherenceCompositionKernel` | 1501 |
| `Morita.CoherenceAssociator` | 1530 |
| `Perfect.Ring2` | 1584 |
| `Morita.CriterionPerfTriangulated` | 1538 |

警告は 989 件：無名 section の閉じ補完 971 件、`set_option` の値の差 6 件（4 統合先）、上限超過 12 件。
同名 private の衝突 0、public section のない元 0、閉じていない名前付き scope 0、連結順の矛盾 0。
option の差は `Tensor/ScalarExtension1`・`Tensor/ScalarExtension2`・`Quotient/Scalar`・`Resolution/Cells/Append2`。元ごとの section に閉じて保持する。

## 外部 import の比較

| 区分 | InfinityCategories | KST | EInfinity | ルート | 合計 |
| --- | ---: | ---: | ---: | ---: | ---: |
| 10-30 調査：全対応表の統合元 | 684 | 441 | 51 | 12 | 1,188 |
| 現 HEAD：全対応表の統合元 | 686 | 445 | 51 | 0 | 1,182 |
| 現 HEAD：新入口を含む DG 全体 | 686 | 445 | 51 | 1 | 1,183 |
| 今回の 980 本の統合元だけ | 177 | 164 | 1 | 0 | 342 |

差分は DG-W1 D2 で説明できる：ルートの直接 import 12 本が新入口へ置換されたため対応表の元への辺は −12。
一方、対応表外だった殻 `Complexes/Monoidal` の外部利用者 6 本（IC 2・KST 4）が、対応表内の `Complexes/HomComplex` へ置換されて +6。
したがって比較対象を同じ全対応表にすると **1,188 − 12 + 6 = 1,182**。新入口へのルート 1 辺を含めた DG 全体は 1,183。
Paper・Asymptotic 等から DG への直接辺は現 HEAD では 0（間接依存は下流逆閉包に含める）。Archive と scripts はこの外部辺の表から除外し、import 書換候補としては検査している。

## (b) 前に確定する事項

- `Verdier/OrderSquare` は D3 の Asymptotic への move と D4 の統合元の両方に載る。草案は両要求を明示し、(b) 前に移動後の構成を調整する。混在草案の `--apply` は拒否するため、意図せず両方を適用しない。
- `strictlyPerfectComplex`・`PerfectHomotopy` の定義への依存はそのまま残る（計画 §7-1）。`strictlyPerfectComplex_biprod` が使う `cochainBiprodXIsoProd` の配置も、分割を適用する前に確認する。
- 統合先の仮名と 12 件の上限超過を Claude が確定・調整する。宣言の本文を変える圧縮はしていない。
- 下流の見積もりは現存する本番ソースの import グラフの逆閉包。統合元と D3 の移動元/先・split 元/先・import 書換元を起点にし、Archive と監査スクリプトを除く。削除前のソース単位なので、実際の統合後の lake の再ビルド本数と同一ではない。

## 新しい道具の使い方

```sh
python3 -B scripts/refactor/merge_modules.py PLAN.json --area SerrePositivity.DifferentialGraded --check --max-lines 1500 --report REPORT.md
# --area と --rewrite-scope（リポジトリ相対パスの正規表現）は複数指定可。
# --apply は merge のみの計画に使い、変更済みのソース/利用元には適用しない。
python3 -B scripts/refactor/merge_modules.py --snapshot-before before.json --snapshot-after after.json
zsh scripts/refactor/with_build_lock.sh --wait 0 -- lake build MODULE
zsh scripts/refactor/warm_build_dir.sh --from ../SerrePositivity --yes
```

`with_build_lock.sh` は `${TMPDIR:-/tmp}/serre-lake-build.lock/owner.json` に PID・worktree・開始時刻・コマンドを記録する。無指定なら無期限待機、タイムアウトは 75、子の終了コードは透過。鍵を使わない lake build は警告だけ。
`warm_build_dir.sh` は manifest 一致と複製元の lake プロセスの cwd を確認し、一回だけ `rsync -a --delete` する。`--yes` は稼働中の複製元の終了を待つ指定。消失だけの 23/24 は、`build/lib/lean` 以下の指定出力が 1–49 件の場合だけ受入。それ以外は停止する。`build/ir/*.c` は §4 の指定範囲外として受け入れない。最後は `--no-build` の診断先頭 20 行と未ビルド起点数を出す。
保存検査では宣言名を照合し、型・本体・公理・属性の正規化・生成補題の扱いを既存の比較道具に委譲する。既存の比較規則を書き換えたり独自に緩和したりしない。

---

# モジュール統合 dry-run

統合先 78、元 980 本。move/split 草案 35 件は未適用。
生成行数：最小 163、中央値 1066、平均 1054.3、最大 1605。

| 統合先 | 元本数 | 元行数 | 生成行数 | import 和 | 外部 importer | 警告数 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `SerrePositivity.DifferentialGraded.Endomorphism.Basic` | 11 | 658 | 728 | 15 | 25 | 9 |
| `SerrePositivity.DifferentialGraded.Tensor.Parameter` | 14 | 1234 | 1307 | 13 | 40 | 14 |
| `SerrePositivity.DifferentialGraded.Tensor.BalancedElements` | 20 | 1353 | 1445 | 13 | 43 | 20 |
| `SerrePositivity.DifferentialGraded.Tensor.ScalarExtension1` | 15 | 1441 | 1521 | 18 | 23 | 18 |
| `SerrePositivity.DifferentialGraded.Tensor.ScalarExtension2` | 9 | 945 | 995 | 4 | 11 | 10 |
| `SerrePositivity.DifferentialGraded.Quotient.Path1` | 13 | 619 | 690 | 13 | 24 | 13 |
| `SerrePositivity.DifferentialGraded.Quotient.Path2` | 19 | 1165 | 1241 | 13 | 17 | 19 |
| `SerrePositivity.DifferentialGraded.Quotient.Erasure` | 15 | 719 | 796 | 10 | 24 | 14 |
| `SerrePositivity.DifferentialGraded.Quotient.Scalar` | 10 | 605 | 658 | 6 | 14 | 11 |
| `SerrePositivity.DifferentialGraded.Quotient.Append` | 19 | 932 | 1009 | 9 | 17 | 19 |
| `SerrePositivity.DifferentialGraded.Quotient.Composition` | 17 | 852 | 927 | 12 | 17 | 17 |
| `SerrePositivity.DifferentialGraded.Quotient.DerivedComparison1` | 15 | 1492 | 1570 | 11 | 27 | 15 |
| `SerrePositivity.DifferentialGraded.Quotient.DerivedComparison2` | 4 | 473 | 509 | 10 | 6 | 4 |
| `SerrePositivity.DifferentialGraded.Quotient.DerivedComparison3` | 15 | 1475 | 1545 | 27 | 23 | 16 |
| `SerrePositivity.DifferentialGraded.Quotient.DerivedComparison4` | 3 | 363 | 397 | 14 | 6 | 3 |
| `SerrePositivity.DifferentialGraded.Quotient.DerivedComparison5` | 13 | 1395 | 1455 | 12 | 9 | 13 |
| `SerrePositivity.DifferentialGraded.Bimodule.Basic` | 15 | 834 | 913 | 10 | 39 | 14 |
| `SerrePositivity.DifferentialGraded.Bimodule.Value` | 16 | 1127 | 1206 | 11 | 47 | 16 |
| `SerrePositivity.DifferentialGraded.Perfect.RepresentableHomology` | 8 | 686 | 740 | 17 | 18 | 8 |
| `SerrePositivity.DifferentialGraded.Perfect.Compact1` | 11 | 877 | 940 | 17 | 36 | 11 |
| `SerrePositivity.DifferentialGraded.Perfect.Compact2` | 15 | 1375 | 1454 | 15 | 26 | 15 |
| `SerrePositivity.DifferentialGraded.Presentation.Category` | 9 | 422 | 486 | 13 | 11 | 9 |
| `SerrePositivity.DifferentialGraded.Presentation.GeneratedHom1` | 21 | 1328 | 1446 | 13 | 10 | 20 |
| `SerrePositivity.DifferentialGraded.Presentation.GeneratedHom2` | 10 | 706 | 773 | 9 | 8 | 9 |
| `SerrePositivity.DifferentialGraded.Bimodule.Tensor` | 10 | 692 | 749 | 7 | 16 | 10 |
| `SerrePositivity.DifferentialGraded.Bimodule.Right` | 17 | 1354 | 1430 | 15 | 24 | 17 |
| `SerrePositivity.DifferentialGraded.Tensor.Enriched` | 22 | 1485 | 1582 | 30 | 44 | 23 |
| `SerrePositivity.DifferentialGraded.Tensor.Bimodule1` | 23 | 1493 | 1581 | 11 | 56 | 24 |
| `SerrePositivity.DifferentialGraded.Tensor.Bimodule2` | 11 | 580 | 635 | 14 | 22 | 11 |
| `SerrePositivity.DifferentialGraded.Tensor.Fubini` | 8 | 802 | 850 | 8 | 15 | 8 |
| `SerrePositivity.DifferentialGraded.Tensor.Associator1` | 27 | 1489 | 1605 | 10 | 33 | 28 |
| `SerrePositivity.DifferentialGraded.Tensor.Associator2` | 10 | 606 | 653 | 8 | 23 | 10 |
| `SerrePositivity.DifferentialGraded.Tensor.Associator3` | 19 | 1434 | 1515 | 5 | 12 | 20 |
| `SerrePositivity.DifferentialGraded.Tensor.Triple` | 15 | 957 | 1026 | 7 | 38 | 15 |
| `SerrePositivity.DifferentialGraded.Tensor.Graded` | 12 | 858 | 922 | 16 | 36 | 12 |
| `SerrePositivity.DifferentialGraded.Tensor.Compose` | 10 | 763 | 817 | 12 | 18 | 10 |
| `SerrePositivity.DifferentialGraded.Resolution.Basic` | 8 | 621 | 674 | 6 | 15 | 8 |
| `SerrePositivity.DifferentialGraded.Resolution.Free.Evaluation` | 14 | 1103 | 1178 | 9 | 12 | 14 |
| `SerrePositivity.DifferentialGraded.Resolution.Cells.Boundary` | 17 | 1296 | 1380 | 16 | 19 | 17 |
| `SerrePositivity.DifferentialGraded.Resolution.Cells.Append1` | 15 | 948 | 1019 | 7 | 18 | 15 |
| `SerrePositivity.DifferentialGraded.Resolution.Cells.Append2` | 14 | 1027 | 1091 | 8 | 10 | 16 |
| `SerrePositivity.DifferentialGraded.Resolution.Cells.Length` | 11 | 947 | 1009 | 11 | 8 | 11 |
| `SerrePositivity.DifferentialGraded.Resolution.Cells.Path` | 20 | 1435 | 1523 | 13 | 10 | 21 |
| `SerrePositivity.DifferentialGraded.Resolution.FixedObject` | 7 | 550 | 598 | 5 | 12 | 7 |
| `SerrePositivity.DifferentialGraded.Resolution.Cell` | 13 | 1144 | 1208 | 9 | 22 | 13 |
| `SerrePositivity.DifferentialGraded.Resolution.Composition` | 8 | 542 | 594 | 8 | 10 | 8 |
| `SerrePositivity.DifferentialGraded.Morita.Kernel` | 10 | 1094 | 1157 | 9 | 31 | 10 |
| `SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionKernel` | 15 | 1426 | 1501 | 6 | 22 | 16 |
| `SerrePositivity.DifferentialGraded.Morita.CoherenceAssociator` | 15 | 1455 | 1530 | 4 | 14 | 16 |
| `SerrePositivity.DifferentialGraded.Perfect.Basic` | 13 | 1016 | 1088 | 24 | 38 | 13 |
| `SerrePositivity.DifferentialGraded.Perfect.Ring2` | 22 | 1484 | 1584 | 20 | 14 | 23 |
| `SerrePositivity.DifferentialGraded.Perfect.EnhancementOperations` | 8 | 732 | 781 | 10 | 21 | 8 |
| `SerrePositivity.DifferentialGraded.Verdier.Derived` | 14 | 1218 | 1301 | 25 | 27 | 13 |
| `SerrePositivity.DifferentialGraded.Endomorphism.Module` | 10 | 1059 | 1116 | 11 | 13 | 10 |
| `SerrePositivity.DifferentialGraded.Endomorphism.Derived1` | 7 | 717 | 766 | 9 | 12 | 7 |
| `SerrePositivity.DifferentialGraded.Endomorphism.Derived2` | 10 | 743 | 801 | 8 | 14 | 10 |
| `SerrePositivity.DifferentialGraded.Endomorphism.Scalar1` | 17 | 1323 | 1405 | 10 | 17 | 17 |
| `SerrePositivity.DifferentialGraded.Endomorphism.Scalar2` | 10 | 1020 | 1072 | 10 | 6 | 10 |
| `SerrePositivity.DifferentialGraded.Endomorphism.Scalar3` | 16 | 1231 | 1313 | 12 | 13 | 16 |
| `SerrePositivity.DifferentialGraded.Endomorphism.Shift` | 15 | 1190 | 1265 | 13 | 21 | 15 |
| `SerrePositivity.DifferentialGraded.Endomorphism.Perfect` | 17 | 1189 | 1269 | 11 | 14 | 17 |
| `SerrePositivity.DifferentialGraded.Endomorphism.Enhancement` | 13 | 945 | 980 | 17 | 3 | 13 |
| `SerrePositivity.DifferentialGraded.Morita.Perfect` | 13 | 1303 | 1373 | 16 | 28 | 12 |
| `SerrePositivity.DifferentialGraded.Morita.ScalarExtension1` | 14 | 1403 | 1474 | 16 | 10 | 14 |
| `SerrePositivity.DifferentialGraded.Morita.ScalarExtension2` | 12 | 1392 | 1452 | 10 | 4 | 12 |
| `SerrePositivity.DifferentialGraded.Morita.CriterionDerivedCoproducts` | 7 | 535 | 583 | 8 | 6 | 7 |
| `SerrePositivity.DifferentialGraded.Bimodule.DiagonalRestriction` | 4 | 402 | 434 | 5 | 12 | 4 |
| `SerrePositivity.DifferentialGraded.Tensor.LeftUnitRestriction` | 4 | 405 | 435 | 11 | 6 | 4 |
| `SerrePositivity.DifferentialGraded.Tensor.ResolvedRestriction` | 4 | 420 | 456 | 8 | 7 | 4 |
| `SerrePositivity.DifferentialGraded.Verdier.Scalar` | 10 | 1071 | 1131 | 17 | 8 | 10 |
| `SerrePositivity.DifferentialGraded.Morita.CriterionPerfTriangulated` | 16 | 1459 | 1538 | 11 | 15 | 17 |
| `SerrePositivity.DifferentialGraded.Morita.Adjunction1` | 14 | 1325 | 1399 | 7 | 18 | 14 |
| `SerrePositivity.DifferentialGraded.Morita.Adjunction2` | 7 | 698 | 745 | 6 | 8 | 7 |
| `SerrePositivity.DifferentialGraded.Morita.QuasiEquivalenceGraph` | 10 | 918 | 976 | 8 | 16 | 10 |
| `SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonGraphSquare` | 1 | 138 | 163 | 3 | 3 | 1 |
| `SerrePositivity.DifferentialGraded.Verdier.Comparison` | 3 | 459 | 491 | 5 | 6 | 3 |
| `SerrePositivity.DifferentialGraded.Verdier.Karoubi` | 10 | 1002 | 1060 | 6 | 6 | 10 |
| `SerrePositivity.DifferentialGraded.Verdier.Kernel` | 11 | 1141 | 1204 | 6 | 8 | 11 |

## 警告

### `SerrePositivity.DifferentialGraded.Endomorphism.Basic`

- SerrePositivity.DifferentialGraded.Endomorphism.Basic: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.LocalizationHomNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.GradedSplitRelations: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ZeroHomComponents: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.CompactHomDetectsIso: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.GradedSplitOfElements: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.GradedSplitImage: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ModuleConeImage: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ModuleShiftImage: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Tensor.Parameter`

- SerrePositivity.DifferentialGraded.Tensor.Actions: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.Balanced: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.Maps: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.Functor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.Elements: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.Ring: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.Yoneda: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.Parameter: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ParameterLeftAction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ParameterLeft: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ParameterRightAction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ParameterRight: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ParameterBalancedElements: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ParameterBalancedConstructor: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Tensor.BalancedElements`

- SerrePositivity.DifferentialGraded.Tensor.LeftYoneda: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.LeftUnitSigns: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ChangeLeft: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ElementsExt: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ElementMap: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.HomElements: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.RightParameter: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ModuleParameter: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.YonedaNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.RestrictBalanced: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.DegreeElementsExt: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ParameterEvaluation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ParameterTensorFamilies: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.TensorModuleIso: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.BalancedUnitElements: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.BalancedFamilyElements: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.BalancedReindex: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.SwapFamilies: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.Swap: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.SwapNaturality: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Tensor.ScalarExtension1`

- SerrePositivity.DifferentialGraded.Tensor.RestrictionComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.RestrictionComparisonCoherence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionColimits: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionCoherence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ScalarExtension: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionHom: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionModule: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionCochain: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionDiagrams: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionModuleMaps: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ScalarRestrictionHom: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ScalarRestrictionCategory: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ScalarRestrictionModule: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ScalarRestrictionNaturality: close 1 anonymous section(s)
- set_option backward.isDefEq.respectTransparency: false, true (isolated by source section)
- set_option backward.isDefEq.respectTransparency.types: false, true (isolated by source section)
- max-lines: 1521 > 1500

### `SerrePositivity.DifferentialGraded.Tensor.ScalarExtension2`

- SerrePositivity.DifferentialGraded.Tensor.ScalarRestrictionModuleMaps: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionAdjunction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionActions: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionPresentation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionBalanced: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionBalancedNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionLeftMaps: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionRing: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionCoendCoherence: close 1 anonymous section(s)
- set_option backward.isDefEq.respectTransparency: false, true (isolated by source section)

### `SerrePositivity.DifferentialGraded.Quotient.Path1`

- SerrePositivity.DifferentialGraded.Quotient.Paths: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.PathUniversal: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.PathPrefix: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.PathCochainExt: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.PathCochainDesc: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.PathComposition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.PrependUnit: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.PrependAssociativity: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.EpsilonAppend: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.EpsilonCochainExt: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.EpsilonDifferential: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.EpsilonTensor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.EpsilonHomogeneousExt: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Quotient.Path2`

- SerrePositivity.DifferentialGraded.Quotient.PathGeneration: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.ScalarExtension: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.EpsilonContraction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.ContractedFunctor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.ContractionCochain: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.ContractionAction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.PathEvaluation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.PathEvaluationPrepend: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.PathEvaluationAppend: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.EvaluationPrefix: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.InternalEvaluation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.InternalEvaluationPrefix: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.InternalEvaluationPrepend: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.InternalEvaluationComposition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.HomogeneousNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.PathEvaluationDifferential: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.EvaluationErasure: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.Evaluation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.EvaluationComposition: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Quotient.Erasure`

- SerrePositivity.DifferentialGraded.Quotient.ErasureFaces: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.ErasureRows: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.ErasureOperator: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.ErasureInterchange: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.ErasureFaceEquations: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.ErasureRowRecursion: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.ErasureTailComposition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.ErasureMiddleInterchange: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.ErasureHead: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.ErasureHeadNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.ErasureHeadCochainNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.ErasureTensorRight: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.ErasureTensorTransport: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.ErasureFirstEvaluation: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Quotient.Scalar`

- SerrePositivity.DifferentialGraded.Quotient.AppendPrepend: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.InternalComposition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.InternalUnit: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.TensorPathCochainExt: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.TensorRightPathCochainExt: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.TensorTwoPathCochainExt: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.ScalarExtensionPaths: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.ScalarExtensionEpsilon: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.ScalarExtensionComposition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.ScalarExtensionErasure: close 1 anonymous section(s)
- set_option backward.isDefEq.respectTransparency: false, true (isolated by source section)

### `SerrePositivity.DifferentialGraded.Quotient.Append`

- SerrePositivity.DifferentialGraded.Quotient.PrependTailNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.PrependHomNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.PrependFirstNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.PrependErasureNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.PrependErasureRows: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.PrependErasure: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.AppendRight: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.AppendRightUnit: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.AppendRightPrepend: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.AppendErasureHead: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.PrefixErasure: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.PrefixGeneration: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.InternalRightUnit: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.CompositionPrefix: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.CompositionPrepend: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.AppendLiftCochain: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.AppendErasureRecursion: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.AppendErasure: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.AppendRightAssociativity: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Quotient.Composition`

- SerrePositivity.DifferentialGraded.Quotient.CompositionErasure: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.InternalAssociativity: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.ErasureFirstTailInterchange: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.ErasureAdjacentInterchange: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DoubleFaces: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DoubleFaceSum: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.ErasureSquare: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.Differential: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.EpsilonElement: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.PrependDifferential: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.CompositionDifferential: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.CompositionEvaluation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.CompositionComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.Identity: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.RightIdentity: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.Associativity: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.Category: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Quotient.DerivedComparison1`

- SerrePositivity.DifferentialGraded.Quotient.Extension: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.Reconstruction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.Universal: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.ParameterExtension: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.ParameterPostcomposition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonFiltration: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonFiltrationZero: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonFiltrationColimit: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonFunctoriality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonColimitQuasiIso: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonGradedProjection: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonGraded: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonFiltrationAction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonLengthAction: close 1 anonymous section(s)
- max-lines: 1570 > 1500

### `SerrePositivity.DifferentialGraded.Quotient.DerivedComparison2`

- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonLengthModule: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonModuleColimit: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonConeDiagram: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonConeColimit: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Quotient.DerivedComparison3`

- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonCells: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonFlatness: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonContraction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonZeroModule: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonGenerators: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonExtension: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonRestriction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonTriangulated: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonPathFlatness: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonPathModule: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonLocalObjects: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonHomPresheaf: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonGradedTensor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonGradedModule: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonLocalHom: close 1 anonymous section(s)
- max-lines: 1545 > 1500

### `SerrePositivity.DifferentialGraded.Quotient.DerivedComparison4`

- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonLayerModule: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonLayerTriangle: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonFreeExtension: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Quotient.DerivedComparison5`

- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonAdjointUnit: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonFreeGeneration: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonLayerGeneration: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonUnitCone: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonFiniteRoof: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonRepresentableHom: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonHomNormalization: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonDerivedLift: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonFullFaithful: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonEquivalence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonPerfect: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonExtensionCoherence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonCanonical: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Bimodule.Basic`

- SerrePositivity.DifferentialGraded.Bimodule.Basic: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.Ext: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.Action: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.ActionElement: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.Identity: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.Transpose: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.OfActions: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.ClosedTransforms: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.ClosedIso: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.ClosedComponents: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.ClosedMapFamily: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.Category: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.Evaluation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.Isomorphism: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Bimodule.Value`

- SerrePositivity.DifferentialGraded.Bimodule.LeftEvaluation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.ValueExt: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.ValueActions: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.ValueIdentity: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.ValueIsomorphism: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.QuasiIso: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.MiddleRestriction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.MiddleRestrictionMaps: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.MiddleLeftRestrictionCoherence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.MiddleRightRestrictionCoherence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.IdentityTranspose: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.ParameterEvaluation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.ParameterSquare: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.ParameterFamily: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.RightRestrictionLeftEvaluation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.ResolvedRestrictionAugmentation: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Perfect.RepresentableHomology`

- SerrePositivity.DifferentialGraded.Perfect.FiniteCell: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.SmallStages: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.SmallStageCover: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.RepresentableHomology: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.RepresentableHomologyLinear: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.RepresentableHomologyNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.RepresentableHomologyNaturalIso: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.RepresentableCoproductSupport: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Perfect.Compact1`

- SerrePositivity.DifferentialGraded.Perfect.Compact: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.CompactComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.CompactRetracts: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.CompactShift: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.CompactTriangles: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.Enhancement: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.EnhancementLinear: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.PerfectCompact: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.Generators: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.EssentiallySmall: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.SmallEnhancement: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Perfect.Compact2`

- SerrePositivity.DifferentialGraded.Perfect.RingTriangleFiniteModel: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.RingRetractFiniteRepresentative: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.RingPerfectRepresentatives: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.CompactConverseTelescope: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.CompactConverseFactor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.CompactConverseExtensions: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.CompactConverseResolutionStages: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.CompactConverseSequential: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.CompactConverseSequentialCone: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.CompactConverse: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.SmallEnhancementTriangulated: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.EnhancementIdempotents: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.RingPerfectEquivalence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.RingPerfectCoherence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.RingKaroubiFactors: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Presentation.Category`

- SerrePositivity.DifferentialGraded.Presentation.ComplexCode: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Presentation.ComplexFromSurjections: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Presentation.CategoryCode: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Presentation.CategoryData: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Presentation.CategoryReindex: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Presentation.CategoryReindexInverse: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Presentation.CategoryReindexIdentity: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Presentation.CategoryFromHomSurjections: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Presentation.ZeroComplexCode: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Presentation.GeneratedHom1`

- SerrePositivity.DifferentialGraded.Presentation.GeneratedHomWords: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Presentation.GeneratedHomSpan: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Presentation.GeneratedHomComplex: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Presentation.GeneratedHomUnit: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Presentation.GeneratedHomComposition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Presentation.GeneratedHomCategory: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Presentation.GeneratedHomFunctorLift: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Presentation.GeneratedHomWordCardinality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Presentation.GeneratedHomFreeCover: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Presentation.GeneratedHomCode: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Presentation.GeneratedHomCodeFaithful: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Presentation.GeneratedHomCodeFunctorLift: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Presentation.GeneratedHomCochainLift: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Presentation.GeneratedHomClosedLift: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Presentation.QuotientGeneratorImage: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Presentation.GeneratedHomSourceContainment: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Presentation.GeneratedHomSourceGenerators: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Presentation.GeneratedHomAugmentedCoefficients: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Presentation.GeneratedHomAugmentedCode: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Presentation.GeneratedHomAugmentedClosedFamily: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Presentation.GeneratedHom2`

- SerrePositivity.DifferentialGraded.Presentation.CategorySigma: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Presentation.CategorySigmaDesc: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Presentation.CategorySigmaInclusion: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Presentation.CategorySigmaComponents: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Presentation.GeneratedHomSphereArrowLift: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Presentation.GeneratedHomSphereExtensionComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Presentation.GeneratedHomSphereMatrixLift: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Presentation.GeneratedHomAugmentedSphereFamily: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Presentation.GeneratedHomClosedFamilyRepresentables: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Bimodule.Tensor`

- SerrePositivity.DifferentialGraded.Bimodule.TensorFunctor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.UncurryHom: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.UncurryRestriction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.CochainComposition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.UncurryComposition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.Uncurry: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.TensorComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.TensorModuleMaps: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.TensorModuleFunctor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.TensorModuleComparison: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Bimodule.Right`

- SerrePositivity.DifferentialGraded.Bimodule.UncurryNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.TensorModuleFull: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.UncurryClosedFunctor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.RightModuleComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.RightRestriction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.RightRestrictionNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.SemifreeResolution: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.SemifreeRetarget: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.MiddleRestrictionUncurry: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.PairedRestriction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.PairedRestrictionCoherence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.ExplicitRightModuleFunctor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.RestrictedRepresentableAction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.RestrictedRepresentable: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.RestrictedFree: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.RelativeKFlat: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.CylinderKFlat: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Tensor.Enriched`

- SerrePositivity.DifferentialGraded.Tensor.HomUnits: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.HomComposition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.HomAdjunctionFamilies: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.HomAdjunction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.HomAdjunctionLaws: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.KFlat: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.KFlatComplex: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.KFlatColimits: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.Enriched: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.EnrichedHomAdjunction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.EnrichedHomPoints: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.EnrichedHomElements: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.EnrichedHomLeft: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.EnrichedHomTarget: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.EnrichedHomSource: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.Interchange: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.LeftColimits: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.BoundedAbove: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.YonedaEnriched: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.YonedaRepresentative: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.FreeEvaluation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.SphereFreeKFlat: close 1 anonymous section(s)
- max-lines: 1582 > 1500

### `SerrePositivity.DifferentialGraded.Tensor.Bimodule1`

- SerrePositivity.DifferentialGraded.Tensor.BimoduleActions: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.Bimodule: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.BimoduleElements: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.BimoduleValueMaps: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.BimoduleValueElements: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.BimoduleMapComponent: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.BimoduleMapLeftAction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.BimoduleMapElementValues: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.BimoduleValueHom: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.BimoduleRightElements: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.BimoduleMapRightAction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.BimoduleMapNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.BimoduleMapFamilies: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.BimoduleFunctor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.BimoduleParameterValues: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.BimoduleParameterElements: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.BimoduleParameterLeft: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.BimoduleParameterRight: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.BimoduleParameters: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.BimoduleMiddleComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.BimoduleMiddleActions: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.BimoduleMiddleMap: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.BimoduleMiddleNaturality: close 1 anonymous section(s)
- max-lines: 1581 > 1500

### `SerrePositivity.DifferentialGraded.Tensor.Bimodule2`

- SerrePositivity.DifferentialGraded.Tensor.Cone: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.QuasiIsoLeft: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.KFlatCriterion: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.Shift: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.LeftKFlatResolution: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.KFlatComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ProjectiveLeftQuasiIso: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.BimoduleQuasiIso: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.BimoduleKFlatQuasiIso: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.BimoduleRestrictionKFlat: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.BimoduleSemifreeKFlat: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Tensor.Fubini`

- SerrePositivity.DifferentialGraded.Tensor.RightUnit: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.FubiniData: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.FubiniFamilies: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.FubiniRightAction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.FubiniColumns: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.FubiniRightFamilies: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.FubiniRightRestriction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.Fubini: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Tensor.Associator1`

- SerrePositivity.DifferentialGraded.Tensor.TripleFunctors: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorValues: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorGenerators: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorCochainExt: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorElements: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorDegreeExt: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorLeftAction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorLeftMaps: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorRightAction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorRightMaps: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorParameterExt: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorCochainAction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorActionDegree: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorComponent: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorValueHom: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorLeftActionMap: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorRightTransport: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorRightComponentCompatibility: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorRightValueHomNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorRightNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorComponentTransport: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorComponentCompatibility: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorValueHomNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorLeftNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorBimodule: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorTransforms: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorIso: close 1 anonymous section(s)
- max-lines: 1605 > 1500

### `SerrePositivity.DifferentialGraded.Tensor.Associator2`

- SerrePositivity.DifferentialGraded.Tensor.ProjectiveComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ProjectiveKFlat: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.PentagonLongElements: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.PentagonShortElements: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.Pentagon: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorMapElements: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorMapNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorParameterValues: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorParameters: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Tensor.Associator3`

- SerrePositivity.DifferentialGraded.Tensor.OuterUnitRestriction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.RightRestrictionValueHom: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.MiddleRestrictionValueHom: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorLeftRestriction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorRightRestrictionElements: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorRightRestrictionPathElements: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorRightRestrictionComponents: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorRightRestrictionValues: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorRightRestriction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorMiddleRestrictionElements: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorMiddleRestrictionPaths: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorMiddleRestrictionComponents: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorMiddleRestrictionValues: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorMiddleRestriction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorSecondMiddleRestrictionElements: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorSecondMiddleRestrictionPaths: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorSecondMiddleRestrictionComponents: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorSecondMiddleRestrictionValues: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorSecondMiddleRestriction: close 1 anonymous section(s)
- max-lines: 1515 > 1500

### `SerrePositivity.DifferentialGraded.Tensor.Triple`

- SerrePositivity.DifferentialGraded.Tensor.AssociatorValueEvaluation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.AssociatorIsoElements: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.QuadElements: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.QuadCochainExt: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.TripleMapElements: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.TripleMapComponents: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.TripleParameterFirst: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.TripleParameterRest: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.LeftDiagonalValues: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.LeftDiagonalHom: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.LeftDiagonalUnit: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.LeftUnit: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.UnitBimoduleIso: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.UnitMapNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.UnitFunctors: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Tensor.Graded`

- SerrePositivity.DifferentialGraded.Tensor.TriangleGenerators: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.Triangle: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ModuleCylinderKFlat: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.GradedSplitElements: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.GradedSplitLaws: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.GradedSplit: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.Semifree: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.Homotopy: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.LeftNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ObjectwiseKFlat: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.RestrictionSemifree: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.RestrictionComparisonNaturality: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Tensor.Compose`

- SerrePositivity.DifferentialGraded.Tensor.TensorModuleNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.RestrictionCylinder: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.BimoduleCylinder: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.RightUnitAssociativity: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.RightUnitAssociativityBimodule: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ComposeLeftRestriction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ComposeRightRestrictionValue: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ComposeRightRestrictionActions: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ComposeRightRestriction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ComposeRightRestrictionNaturality: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Resolution.Basic`

- SerrePositivity.DifferentialGraded.Resolution.Basic: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.CycleCover: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.CycleCoverFunctor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Initial: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.InitialComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.BoundaryCells: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.BoundarySequence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.CycleCoverComparisonLaws: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Resolution.Free.Evaluation`

- SerrePositivity.DifferentialGraded.Resolution.Free.Words: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Free.Hom: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Free.Maps: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Free.Composition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Free.Units: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Free.Evaluation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Free.EvaluationComposition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Free.AppendRight: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Free.AppendRecursion: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Free.PrefixAssociativity: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Free.Associativity: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Free.Category: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Free.Reconstruction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Free.Universal: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Resolution.Cells.Boundary`

- SerrePositivity.DifferentialGraded.Resolution.Cells.Paths: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.PathEquations: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.PathComposition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.PathAction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.GeneratorAppend: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.BoundaryCochain: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.BoundaryFaces: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.BoundaryOperator: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.BoundaryInterchange: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.BoundaryHead: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.BoundaryNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.BoundaryHeadInterchange: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.DoubleFaces: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.DoubleFaceSum: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.PrimitiveData: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.PrimitiveAction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.BoundarySquare: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Resolution.Cells.Append1`

- SerrePositivity.DifferentialGraded.Resolution.Cells.Differential: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.PathCochainDesc: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.InternalComposition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.Prefix: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.PrefixGeneration: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.AppendRecursion: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.AppendPrepend: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.AppendRightPrepend: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.InternalUnits: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.CompositionPrefix: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.CompositionPrepend: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.PrependBoundaryRows: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.TensorPathCochainExt: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.TensorRightPathCochainExt: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.TensorTwoPathCochainExt: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Resolution.Cells.Append2`

- SerrePositivity.DifferentialGraded.Resolution.Cells.PrependBoundary: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.PrependDifferential: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.InternalBoundaryHead: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.AppendBoundaryHead: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.AppendRightAssociativity: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.BoundaryRowRecursion: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.PrefixBoundary: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.AppendLiftCochain: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.AppendBoundaryRecursion: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.AppendBoundary: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.CompositionBoundary: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.CompositionDifferential: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.CompositionEvaluation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.CompositionComparison: close 1 anonymous section(s)
- set_option backward.isDefEq.respectTransparency: false, true (isolated by source section)
- set_option backward.isDefEq.respectTransparency.types: false, true (isolated by source section)

### `SerrePositivity.DifferentialGraded.Resolution.Cells.Length`

- SerrePositivity.DifferentialGraded.Resolution.Cells.Identity: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.RightIdentity: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.InternalAssociativity: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.Associativity: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.Category: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.LengthBoundary: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.LengthFiltration: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.LengthTransition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.LengthGraded: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.LengthSplit: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.LengthColimit: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Resolution.Cells.Path`

- SerrePositivity.DifferentialGraded.Resolution.Cells.GeneratorBoundary: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.GeneratorDisk: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.PathGeneration: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.PathEvaluation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.PathEvaluationPrepend: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.PathEvaluationAppend: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.InternalEvaluation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.InternalEvaluationComposition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.BoundaryActionEvaluation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.EvaluationPrefix: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.InternalEvaluationPrefix: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.PathEvaluationDifferential: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.EvaluationReplacement: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.Evaluation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.EvaluationComposition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.Extension: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.Augmentation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.RestrictionData: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.Reconstruction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Cells.Universal: close 1 anonymous section(s)
- max-lines: 1523 > 1500

### `SerrePositivity.DifferentialGraded.Resolution.FixedObject`

- SerrePositivity.DifferentialGraded.Resolution.Bimodule: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Coherence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.FixedObjectAugmentation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.FixedObjectCategory: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.FixedObjectMap: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.FixedObjectMapExtension: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.FixedObjectGenerators: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Resolution.Cell`

- SerrePositivity.DifferentialGraded.Resolution.CellSequence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.CellComposition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.CellUnits: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.CellAssociativity: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.CellCategory: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.InitialStageComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.FixedObjectMapAugmentation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.FixedObjectMapLaws: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.FixedObjectAttachmentExt: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.FixedObjectAttachmentLaws: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.CellComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.CellComparisonLaws: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.CellComparisonQuasiEquivalence: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Resolution.Composition`

- SerrePositivity.DifferentialGraded.Resolution.CanonicalZigzag: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.Restriction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.DerivedEquivalence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.BimoduleDerivedEquivalence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.CompositionComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.CompositionChange: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.DiagonalComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Resolution.MiddleCompositionComparison: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Morita.Kernel`

- SerrePositivity.DifferentialGraded.Morita.KernelBasic: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.KernelTensor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CriterionPerfHomInduction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.ScalarExtensionTensorModels: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.ScalarExtensionTensorNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.KernelResolution: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.KernelNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.KernelDerivedFunctor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.KernelComparisonNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.KernelComparisonComponents: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionKernel`

- SerrePositivity.DifferentialGraded.Morita.CoherenceIdentity: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionFamilies: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionLocalization: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionValueNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.KernelAugmentation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.KernelResolutionModel: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.KernelAugmentationNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CoherenceProjectiveExt: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionClosed: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionKFlat: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionKFlatNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionAugmentation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionDerivedNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionNaturalIso: close 1 anonymous section(s)
- max-lines: 1501 > 1500

### `SerrePositivity.DifferentialGraded.Morita.CoherenceAssociator`

- SerrePositivity.DifferentialGraded.Morita.CoherenceComposition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionWhisker: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CoherenceIdentityAugmentation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CoherenceUnitClosed: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CoherenceUnitDerived: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CoherenceUnitMain: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CoherenceAssociatorClosed: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CoherenceAssociatorAugmentation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CoherenceAssociatorKFlat: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CoherenceAssociatorModels: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CoherenceAssociatorPaths: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CoherenceAssociatorNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CoherenceAssociatorRightNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CoherenceAssociatorMain: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CoherenceLeftUnitMain: close 1 anonymous section(s)
- max-lines: 1530 > 1500

### `SerrePositivity.DifferentialGraded.Perfect.Basic`

- SerrePositivity.DifferentialGraded.Perfect.FiniteCellProjective: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.Basic: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.Shift: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.KaroubiCriterion: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.Triangulated: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.UniversalProperty: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.KaroubiEquivalence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.FiniteProjectiveImage: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.RingSingle: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.RingSingleShift: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.RingExtensions: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.RingShiftComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.RingHomotopyDerivedComparison: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Perfect.Ring2`

- SerrePositivity.DifferentialGraded.Perfect.StrictComplexEnhancement: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.StrictComplexEnhancementLinear: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.StrictComplexProjective: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.StrictComplexDerived: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.StrictComplexDerivedLinear: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.StrictComplexOperations: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.RingBounded: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.RingFiniteCell: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.RingEnhancement: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.RingFiniteCellImage: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.RingPerfectComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.RingPerfectTriangulated: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.RingRetract: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.RingRetractTopHomology: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.RingKaroubi: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.RingFiniteHomologyCover: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.RingTopTruncation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.RingHomologyCoverCone: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.RingDerivedFiniteCover: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.RingRetractTriangle: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.RingRetractRangeReduction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.RingRetractSingle: close 1 anonymous section(s)
- max-lines: 1584 > 1500

### `SerrePositivity.DifferentialGraded.Perfect.EnhancementOperations`

- SerrePositivity.DifferentialGraded.Perfect.EnhancementOperations: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.EnhancementShiftComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.EnhancementShift: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.EnhancementTriangulated: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.EnhancementCone: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.EnhancementDerivedComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.EnhancementShiftEvaluation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Perfect.EnhancementConeComparison: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Verdier.Derived`

- SerrePositivity.DifferentialGraded.Verdier.ShiftReflection: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.KaroubiTransport: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.ShiftedHomComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.TriangulatedHomComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.AdjunctionComparisonShift: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.DerivedCoproductComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.Tria: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.NullObjects: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.FiniteCellHomotopy: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.DerivedGeneratorInduction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.DerivedGraphComposition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.GraphRestrictionShift: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.GraphCompositionShift: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Endomorphism.Module`

- SerrePositivity.DifferentialGraded.Endomorphism.HomBimodule: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.Evaluation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.EvaluationAdjunction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.LargeHomBimodule: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ModuleComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ModuleFunctorMaps: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ModuleTensorElements: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ModuleEvaluation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ModuleInsertion: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ModuleAdjunction: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Endomorphism.Derived1`

- SerrePositivity.DifferentialGraded.Endomorphism.DerivedHom: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.DerivedTensor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.DerivedTensorNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.DerivedTensorEvaluation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.DerivedEvaluation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.DerivedScalarTensor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.DerivedLocalizingGeneration: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Endomorphism.Derived2`

- SerrePositivity.DifferentialGraded.Endomorphism.ActualScalarEnd: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ActualScalarEvaluation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.HomotopyAdjunction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ProjectiveCriterion: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.TensorProjective: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.DerivedHomEquiv: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.DerivedProjectiveHomNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.DerivedHomNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.DerivedAdjunction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.DerivedGenerators: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Endomorphism.Scalar1`

- SerrePositivity.DifferentialGraded.Endomorphism.IsoLocus: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ScalarEvaluation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ScalarHomFactors: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ScalarEvaluationActual: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ScalarRepresentable: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ScalarModuleHomNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ScalarModuleHom: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ScalarModuleDGFunctor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ScalarYonedaHom: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ScalarYonedaIso: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ScalarClosedMap: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ScalarHomNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ScalarHomRetracts: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ScalarModuleHomotopy: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ScalarHomElements: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ScalarHomHomotopyRetracts: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ScalarHomElementComponents: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Endomorphism.Scalar2`

- SerrePositivity.DifferentialGraded.Endomorphism.ScalarHomShift: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ScalarHomCone: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ScalarPerfectHom: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ScalarProjectiveImage: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ScalarShiftCoherence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ScalarShiftAddition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ScalarHomotopyShift: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ScalarConeTriangles: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ScalarModuleShiftImage: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ScalarPerfectImage: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Endomorphism.Scalar3`

- SerrePositivity.DifferentialGraded.Endomorphism.ThickHomComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.PerfectImage: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.HomotopyImage: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.HomotopyShiftCoherence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ProjectiveImage: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ProjectiveHomotopyComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.QuasiFullyFaithful: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ShiftConeComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.PerfectDGComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ScalarPerfectEnhancement: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ScalarDerivedProjectiveComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ScalarDerivedPerfect: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ScalarEnhancementClosed: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ScalarEnhancementDerivedComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ScalarEnhancementShift: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ScalarPerfectShiftTriangles: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Endomorphism.Shift`

- SerrePositivity.DifferentialGraded.Endomorphism.ScalarGradedSplit: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ScalarModuleConeImage: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ShiftNormalization: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ShiftNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ShiftZeroCoherence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ShiftAdditionElements: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ShiftAddCoherence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ShortExactComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ScalarHomShortExact: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.EnhancementComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.GeneratorHomIso: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.HomMapNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.HomComparisonRetracts: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.HomComparisonShift: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.HomComparisonCone: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Endomorphism.Perfect`

- SerrePositivity.DifferentialGraded.Endomorphism.ConeConnectingComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ConeTriangleComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.DerivedHomHomotopyComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.DerivedShiftCoherence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.DerivedTriangleComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.DerivedTensorTriangles: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.CompactGenerator: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.EssentialImageRetracts: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.EssentialImageShift: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.EssentialImageTriangles: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.PerfectEquivalence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.PerfectShiftTriangles: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.PerfectTensor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.PerfectTensorDG: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.PerfectAdjunction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.PerfectScalarTensor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.CompactUnitCounit: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Endomorphism.Enhancement`

- SerrePositivity.DifferentialGraded.Endomorphism.EnhancementAdjunction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.EnhancementShiftTriangles: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.EnhancementHomotopyAdjunction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.EnhancementTensorComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.EnhancementTensorTriangles: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.CoproductHomComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.HomPreservesCoproducts: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.DerivedUnitAll: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.DerivedEquivalence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.DerivedEquivalenceTriangles: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.DerivedEquivalenceCompactGenerator: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.ScalarReconstructionTriangles: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Endomorphism.Compatibility: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Morita.Perfect`

- SerrePositivity.DifferentialGraded.Morita.AdjunctionHom: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.AdjunctionBrownSeed: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.AdjunctionBrownRelations: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.AdjunctionBrownSuccessor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.PerfectFunctoriality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.PerfectKernelImage: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.PerfectKernelColumns: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.PerfectKernelEvaluation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.PerfectKernelEvaluationNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.PerfectKernelComposition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.PerfectDerivedKernelCoherence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.PerfectDerivedKernelComposition: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Morita.ScalarExtension1`

- SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernel: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelTensor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelAction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelFunctor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelProduct: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelBalanced: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelBalancedModule: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelBalancedNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelHomotopy: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelLocalization: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelLocalizationAugmentation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelMapNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelDerivedComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelHomotopyNaturality: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Morita.ScalarExtension2`

- SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelOutputModels: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelEvaluationModels: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelDerivedNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelBaseChangeNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.ScalarExtensionPerfect: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.ScalarExtensionPerfectSquares: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelPerfectSquare: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelPerfectNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelLocalizedSquare: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelLocalizedComposition: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.ScalarExtensionOutputEvaluation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelOutputEvaluation: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Morita.CriterionDerivedCoproducts`

- SerrePositivity.DifferentialGraded.Morita.AdjunctionKernelColimits: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.AdjunctionKernelCoproducts: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CriterionDerivedCoproducts: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CriterionDerivedGeneration: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CriterionDerivedHomCoproducts: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CriterionDerivedHomTriangles: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CriterionDerivedHomLocus: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Bimodule.DiagonalRestriction`

- SerrePositivity.DifferentialGraded.Bimodule.DiagonalRestriction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.DiagonalRestrictionCoherence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.PairedRestrictionPresentation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Bimodule.MiddleRestrictionPresentation: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Tensor.LeftUnitRestriction`

- SerrePositivity.DifferentialGraded.Tensor.LeftUnitRestriction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.LeftUnitRestrictionAugmentation: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.RightUnitRestriction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.FunctorExtensionProjection: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Tensor.ResolvedRestriction`

- SerrePositivity.DifferentialGraded.Tensor.RestrictionComparisonYoneda: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.FunctorRestrictionQuasiIso: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ResolvedRestrictionCoherence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Tensor.ResolvedRestrictionIdentity: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Verdier.Scalar`

- SerrePositivity.DifferentialGraded.Verdier.ScalarGraphRestriction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.ProjectiveResolutionComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.KernelActionTriangles: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.PerfectKernelVerdier: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.RetractSquare: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.ScalarExtensionSquare: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.ScalarExtensionTria: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.ScalarSourceVerdier: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.ScalarGraphDerivedComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.ScalarQuotientSourceSquare: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Morita.CriterionPerfTriangulated`

- SerrePositivity.DifferentialGraded.Morita.CriterionPerfTriangulated: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CriterionPerfGeneration: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CriterionPerfEquivalence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CriterionPerfHomComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CriterionPerfHomComparisonZero: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CriterionPerfConditions: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CriterionPerfFullyFaithful: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CriterionPerfHomComparisonDegrees: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CriterionPerfYonedaAction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CriterionPerfYonedaHomology: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CriterionPerfResolvedHomShift: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CriterionPerfDGFunctorShift: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CriterionPerfResolvedHom: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CriterionPerfResolvedAction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CriterionPerfTensorHomComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CriterionPerfFullHomCriterion: close 1 anonymous section(s)
- max-lines: 1538 > 1500

### `SerrePositivity.DifferentialGraded.Morita.Adjunction1`

- SerrePositivity.DifferentialGraded.Morita.CriterionPerf: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CriterionPerfRelativeFullyFaithful: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CriterionPerfGeneratorHomComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.AdjunctionKernelSuccessor: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.AdjunctionKernelSequence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.AdjunctionKernelTelescope: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.AdjunctionKernelGeneratorHom: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.AdjunctionHomTriangles: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.AdjunctionHomClosure: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.AdjunctionHomGeneration: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.AdjunctionDerived: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CriterionDerivedFullyFaithful: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CriterionDerivedEquivalence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CriterionDerivedConditions: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Morita.Adjunction2`

- SerrePositivity.DifferentialGraded.Morita.AdjunctionSquare: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.AdjunctionCoherence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.AdjunctionScalarExtension: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CoherencePerfectUnit: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.CoherencePerfectAssociator: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.Criterion: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.AdjunctionPerfectInverse: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Morita.QuasiEquivalenceGraph`

- SerrePositivity.DifferentialGraded.Morita.QuasiEquivalenceTriangles: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.PerfectQuasiEquivalence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.PerfectQuasiEquivalenceTriangles: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.PerfectEnhancementComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.QuasiEquivalenceGraph: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.QuasiEquivalenceGraphNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.QuasiEquivalenceGraphAction: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.QuasiEquivalenceProducts: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.QuasiEquivalenceDerivedGraph: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Morita.QuasiEquivalenceEndomorphismComparison: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonGraphSquare`

- SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonGraphSquare: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Verdier.Comparison`

- SerrePositivity.DifferentialGraded.Verdier.ComparisonLinear: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.OrderSquare: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.SupportSquare: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Verdier.Karoubi`

- SerrePositivity.DifferentialGraded.Verdier.KaroubiFunctorSquare: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.KaroubiSquareShift: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.KaroubiMapShift: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.ScalarKaroubiShift: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.GraphPerfectSquare: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.GraphKernelSquare: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.PerfectNullComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.PerfectQuotientEquivalence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.ScalarCompletionSquare: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.CompletionSquareShift: close 1 anonymous section(s)

### `SerrePositivity.DifferentialGraded.Verdier.Kernel`

- SerrePositivity.DifferentialGraded.Verdier.ScalarDirectCompletion: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.KernelLocalPerfectSquare: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.KernelQuotientNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.KernelComparisonNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.KernelCompositionDescent: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.KernelCompositionComparison: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.KernelCompositionNaturality: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.MoritaPairEquivalence: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.GraphPairMorita: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.DerivedKernelGraphSquare: close 1 anonymous section(s)
- SerrePositivity.DifferentialGraded.Verdier.ConjugatedCompositionNaturality: close 1 anonymous section(s)


## 対象領域の外からの import 辺（Archive・scripts を除く現行ソース）

- EInfinity: 51
- InfinityCategories: 686
- KST: 445
- SerrePositivity: 1

合計 1183 辺。

## 下流見積もり

統合元・D3 移動元/先・import 書換利用元の逆閉包：7222 本（現存本番ソース、Archive を除く）。単独 1.0–1.5 秒/本なら 120.4–180.6 分。監査時間は別。
import のみの書換候補 516 ファイル。

## move/split 草案

- move: `SerrePositivity.KST.SConstruction.DGClosedComparisonIso` → `SerrePositivity.DifferentialGraded.Functor.DGClosedComparisonIso`。群 A（17 本）：閉共役・Hom end・Param・Enrichment。
- move: `SerrePositivity.KST.SConstruction.DGClosedIsoConjugation` → `SerrePositivity.DifferentialGraded.Functor.DGClosedIsoConjugation`。群 A（17 本）：閉共役・Hom end・Param・Enrichment。
- move: `SerrePositivity.KST.SConstruction.DGClosedIsoConjugationLaws` → `SerrePositivity.DifferentialGraded.Functor.DGClosedIsoConjugationLaws`。群 A（17 本）：閉共役・Hom end・Param・Enrichment。
- move: `SerrePositivity.KST.SConstruction.DGConjugationNaturality` → `SerrePositivity.DifferentialGraded.SharedFunctoriality.DGConjugationNaturality`。群 B（9 本）：graph・加群延長と、その共役の自然性。
- move: `SerrePositivity.KST.SConstruction.DGFunctorClosedComparison` → `SerrePositivity.DifferentialGraded.Functor.DGFunctorClosedComparison`。群 A（17 本）：閉共役・Hom end・Param・Enrichment。
- move: `SerrePositivity.KST.SConstruction.DGFunctorClosedNaturality` → `SerrePositivity.DifferentialGraded.Functor.DGFunctorClosedNaturality`。群 A（17 本）：閉共役・Hom end・Param・Enrichment。
- move: `SerrePositivity.KST.SConstruction.DGFunctorCoherence` → `SerrePositivity.DifferentialGraded.Functor.DGFunctorCoherence`。群 A（17 本）：閉共役・Hom end・Param・Enrichment。
- move: `SerrePositivity.KST.SConstruction.DGFunctorEnrichment` → `SerrePositivity.DifferentialGraded.Functor.DGFunctorEnrichment`。群 A（17 本）：閉共役・Hom end・Param・Enrichment。
- move: `SerrePositivity.KST.SConstruction.DGFunctorGraphComposition` → `SerrePositivity.DifferentialGraded.SharedFunctoriality.DGFunctorGraphComposition`。群 B（9 本）：graph・加群延長と、その共役の自然性。
- move: `SerrePositivity.KST.SConstruction.DGFunctorGraphParameter` → `SerrePositivity.DifferentialGraded.SharedFunctoriality.DGFunctorGraphParameter`。群 B（9 本）：graph・加群延長と、その共役の自然性。
- move: `SerrePositivity.KST.SConstruction.DGFunctorGraphUnits` → `SerrePositivity.DifferentialGraded.SharedFunctoriality.DGFunctorGraphUnits`。群 B（9 本）：graph・加群延長と、その共役の自然性。
- move: `SerrePositivity.KST.SConstruction.DGFunctorHomConjugation` → `SerrePositivity.DifferentialGraded.Functor.DGFunctorHomConjugation`。群 A（17 本）：閉共役・Hom end・Param・Enrichment。
- move: `SerrePositivity.KST.SConstruction.DGFunctorHomEnd` → `SerrePositivity.DifferentialGraded.Functor.DGFunctorHomEnd`。群 A（17 本）：閉共役・Hom end・Param・Enrichment。
- move: `SerrePositivity.KST.SConstruction.DGFunctorHomIdentity` → `SerrePositivity.DifferentialGraded.Functor.DGFunctorHomIdentity`。群 A（17 本）：閉共役・Hom end・Param・Enrichment。
- move: `SerrePositivity.KST.SConstruction.DGFunctorHomPostcomposition` → `SerrePositivity.DifferentialGraded.Functor.DGFunctorHomPostcomposition`。群 A（17 本）：閉共役・Hom end・Param・Enrichment。
- move: `SerrePositivity.KST.SConstruction.DGFunctorHomPrecomposition` → `SerrePositivity.DifferentialGraded.Functor.DGFunctorHomPrecomposition`。群 A（17 本）：閉共役・Hom end・Param・Enrichment。
- move: `SerrePositivity.KST.SConstruction.DGFunctorHomUniversal` → `SerrePositivity.DifferentialGraded.Functor.DGFunctorHomUniversal`。群 A（17 本）：閉共役・Hom end・Param・Enrichment。
- move: `SerrePositivity.KST.SConstruction.DGFunctorHomWhiskering` → `SerrePositivity.DifferentialGraded.Functor.DGFunctorHomWhiskering`。群 A（17 本）：閉共役・Hom end・Param・Enrichment。
- move: `SerrePositivity.KST.SConstruction.DGFunctorParamComposition` → `SerrePositivity.DifferentialGraded.Functor.DGFunctorParamComposition`。群 A（17 本）：閉共役・Hom end・Param・Enrichment。
- move: `SerrePositivity.KST.SConstruction.DGFunctorParamNaturality` → `SerrePositivity.DifferentialGraded.Functor.DGFunctorParamNaturality`。群 A（17 本）：閉共役・Hom end・Param・Enrichment。
- move: `SerrePositivity.KST.SConstruction.DGGraphCompositionInputLeft` → `SerrePositivity.DifferentialGraded.SharedFunctoriality.DGGraphCompositionInputLeft`。群 B（9 本）：graph・加群延長と、その共役の自然性。
- move: `SerrePositivity.KST.SConstruction.DGModuleExtensionComposition` → `SerrePositivity.DifferentialGraded.SharedFunctoriality.DGModuleExtensionComposition`。群 B（9 本）：graph・加群延長と、その共役の自然性。
- move: `SerrePositivity.KST.SConstruction.DGModuleExtensionEvaluationTransport` → `SerrePositivity.DifferentialGraded.SharedFunctoriality.DGModuleExtensionEvaluationTransport`。群 B（9 本）：graph・加群延長と、その共役の自然性。
- move: `SerrePositivity.KST.SConstruction.DGModuleExtensionIdentity` → `SerrePositivity.DifferentialGraded.SharedFunctoriality.DGModuleExtensionIdentity`。群 B（9 本）：graph・加群延長と、その共役の自然性。
- move: `SerrePositivity.KST.SConstruction.DGModuleExtensionInputTransport` → `SerrePositivity.DifferentialGraded.SharedFunctoriality.DGModuleExtensionInputTransport`。群 B（9 本）：graph・加群延長と、その共役の自然性。
- move: `SerrePositivity.KST.SConstruction.DGParameterConjugation` → `SerrePositivity.DifferentialGraded.Functor.DGParameterConjugation`。群 A（17 本）：閉共役・Hom end・Param・Enrichment。
- move: `SerrePositivity.DifferentialGraded.Functor.ModuleExtensionConjugation` → `SerrePositivity.DifferentialGraded.SharedFunctoriality.ModuleExtensionConjugation`。Tensor より上の共有関手性へ。名前空間は保存。
- move: `SerrePositivity.DifferentialGraded.Module.ExtensionRepresentableClosedNaturality` → `SerrePositivity.DifferentialGraded.SharedFunctoriality.ExtensionRepresentableClosedNaturality`。Tensor より上の共有関手性へ。名前空間は保存。
- move: `SerrePositivity.DifferentialGraded.Module.ExtensionRepresentableComposition` → `SerrePositivity.DifferentialGraded.SharedFunctoriality.ExtensionRepresentableComposition`。Tensor より上の共有関手性へ。名前空間は保存。
- move: `SerrePositivity.InfinityCategories.Derived.DGObjectImage` → `SerrePositivity.DifferentialGraded.Category.ObjectImage`。一般の DG 対象の像を DG へ。
- move: `SerrePositivity.DifferentialGraded.Verdier.OrderSquare` → `SerrePositivity.Asymptotic.DGVerdier.OrderSquare`。論文固有の依存を上の層へ。Verdier/U17 の該当 import も (b) で追従。
- move: `SerrePositivity.DifferentialGraded.Verdier.ChecksOrderSquare` → `SerrePositivity.Asymptotic.DGVerdier.ChecksOrderSquare`。論文固有の依存を上の層へ。Verdier/U17 の該当 import も (b) で追従。
- move: `SerrePositivity.DifferentialGraded.Verdier.ChecksU17Integration` → `SerrePositivity.Asymptotic.DGVerdier.ChecksU17Integration`。論文固有の依存を上の層へ。Verdier/U17 の該当 import も (b) で追従。
- split: `SerrePositivity.PerfectComplex.ProjectiveBounds` → `SerrePositivity.HomologicalAlgebra.FiniteProjectiveRetract`。有限射影の一般補題。型・本文・名前空間を保存。
- split: `SerrePositivity.PerfectComplex.BiproductPerfect` → `SerrePositivity.HomologicalAlgebra.StrictlyPerfectBiproduct`。strictlyPerfectComplex・PerfectHomotopy の定義への依存は未決 §7-1 として残す。補助定義 cochainBiprodXIsoProd への依存も (b) の分割案で確認する。
