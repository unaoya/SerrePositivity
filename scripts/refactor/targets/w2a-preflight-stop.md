# IF-W0-3 W2a 作成中の停止報告

基準 `cdbefbde9`、専用 worktree `../SerrePositivity-ifw0-3`、ブランチ `infra/if-w0-3`。

**§7-2 は未達。w2a.json・w2a.md は未作成。** W1 はユーザーの判断に従い「verify 待ち・PASS を条件に仮承認」とし、W2a の読解と前提検査へ進んだ。全体 verify は実行していない。main の取り込み・監査の修正・コミットも行っていない。

## 停止理由

HA の指定12本を読解し、現在の分割パーサーで宣言を抽出したところ、次の3本で既存の未対応構文を検出した。ビルド・snapshot 後に `split_module.py --dry-run` でも再現した。3件とも終了コード1で、ソースへの適用前に停止する。

| 対象 | 拒否される既存構文 | 位置 |
| --- | --- | --- |
| Simplicial.Generators | `attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType` | 26行 |
| Generated.Basic | `attribute [instance] CofibrantlyGenerated.smallObjectI CofibrantlyGenerated.smallObjectJ` | 54行 |
| HomotopyFunctionComplex.DiagonalFrame | 無名の `local instance : ModelCategory (SimplexCategory ⥤ C)` | 82行 |

これは対象 Lean コードのコンパイル失敗ではなく、既存道具の対応範囲による拒否。`scripts/refactor/README.md:140` は「未対応の構文や複雑な局所スコープ、snapshot に現れない通常の private 宣言は自動分割せず拒否する」としている。既存パーサー部分は今回変更していない。共通前提の停止規則に従い、構文対応を拡張せず報告する。

対応を広げる場合は、属性コマンドを対象宣言の側に保持すること、`include hgen` のスコープを維持すること、無名 local instance を snapshot の生成名と対応させて片側へ帰属させることが必要。既存の名前を推測して JSON に入れたり、local instance を両側に複製したりしていない。

## 完了した確認

| 確認 | 結果 | 秒 |
| --- | --- | ---: |
| W1 68件の累積検査とグラフ取得（validate API） | PASS | 33.763 |
| HA 12本のみの `lake build` | 終了コード0、2,230 jobs | 2.917 |
| HA 12本の宣言 snapshot | 終了コード0、159定数（補助宣言を含む） | 22.796 |
| Generators の dry-run | 未対応構文による停止・終了コード1 | 0.405 |
| Basic の dry-run | 未対応構文による停止・終了コード1 | 0.397 |
| DiagonalFrame の dry-run | 未対応構文による停止・終了コード1 | 0.396 |

HL の ModelCategory を含むファイルは 42 本。R27 は 27 辺・参照先 21 本で、計画の数と一致する。R27 の汎用17本は参照先、Spectrum5本は利用元であり、同一集合の分割ではない（R2-A 詳細の説明に従う）。

HA の `Generated.FunctorClosure`・`Transfer.FullyFaithfulLifting`・`HomotopyFunctionComplex.BoundaryOne` は一般論のみで、ModelCategory を仮定する節がない。これらは空の split を作らず、後の窓での純粋部分の移動候補として扱う案。残るファイルの分割・prune・保存比較は未実施。

全ログをエラー語で検索した。既存HAのビルド・snapshotには該当診断なし。dry-run 3ログに上記の STOP 各1件。結果と全コマンドは `.lake/verify/ifw0-3-w2a/stop.json`、宣言一覧は `ha-before.json`、抽出結果は `ha-inventory.json`。

## 再現コマンドと診断

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 -B scripts/refactor/split_module.py SerrePositivity.HomotopicalAlgebra.Simplicial.Generators SerrePositivity.InfinityCategories.ModelBridge.HA.Generators --moved SerrePositivity.SimplicialModel.simplicialSet_isCofibrant --snapshot /Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ifw0-3/.lake/verify/ifw0-3-w2a/ha-before.json --dry-run
```

```text
split_module: STOP: /Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ifw0-3/SerrePositivity/HomotopicalAlgebra/Simplicial/Generators.lean:26: unsupported top-level syntax: attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType
```

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 -B scripts/refactor/split_module.py SerrePositivity.HomotopicalAlgebra.Generated.Basic SerrePositivity.InfinityCategories.ModelBridge.HA.Basic --moved SerrePositivity.ModelGeneration.CofibrantlyGenerated SerrePositivity.ModelGeneration.cofibrations_eq_generated SerrePositivity.ModelGeneration.trivialCofibrations_eq_generated SerrePositivity.ModelGeneration.hasFunctorialFactorization_cofibration_trivialFibration SerrePositivity.ModelGeneration.hasFunctorialFactorization_trivialCofibration_fibration --snapshot /Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ifw0-3/.lake/verify/ifw0-3-w2a/ha-before.json --dry-run
```

```text
split_module: STOP: /Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ifw0-3/SerrePositivity/HomotopicalAlgebra/Generated/Basic.lean:54: unsupported top-level syntax: attribute [instance] CofibrantlyGenerated.smallObjectI CofibrantlyGenerated.smallObjectJ
```

```sh
/opt/homebrew/opt/python@3.14/bin/python3.14 -B scripts/refactor/split_module.py SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalFrame SerrePositivity.InfinityCategories.ModelBridge.HA.DiagonalFrame --moved SerrePositivity.HomotopyFunctionComplex.DiagonalFrame.resolution SerrePositivity.HomotopyFunctionComplex.DiagonalFrame.resolutionObj SerrePositivity.HomotopyFunctionComplex.DiagonalFrame.resolutionAugmentation SerrePositivity.HomotopyFunctionComplex.DiagonalFrame.resolutionAugmentation_weakEquivalence SerrePositivity.HomotopyFunctionComplex.DiagonalFrame.resolutionObj_homotopicallyConstant --snapshot /Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ifw0-3/.lake/verify/ifw0-3-w2a/ha-before.json --dry-run
```

```text
split_module: STOP: /Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ifw0-3/SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/DiagonalFrame.lean:82: unsupported top-level syntax: local instance : ModelCategory (SimplexCategory ⥤ C) := Reedy.simplexModelCategory C
```

## 今回の変更

- `scripts/refactor/targets/w1.md`：冒頭の承認状態を「verify 待ち」に更新。
- `scripts/refactor/targets/w2a-preflight-stop.md`：本報告。

その他は `.lake/verify/ifw0-3-w2a/` の計測記録だけ。数学の `.lean`・監査・既存道具は今回変更していない。既存の `scripts/refactor/decl_snapshot.lean` 差分は前回までに承認された作業のもの。
