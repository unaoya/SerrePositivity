# IF-W0-3 W2a 再開時の停止報告（8e6e75d8e）

W1 の全体 verify は PASS・gate:true となり、続行条件を満たした。§4.2 を再開する前提検査として、前回報告済みの HA 3本の split dry-run を再確認したところ、同じ未対応構文で停止した。**§7-2 は未達。w2a.json・w2a.md は未作成。**

基準 `8e6e75d8e5f161eb01dd5f5cbbd2b1f544aa0bf5`。専用 worktree・ブランチ infra/if-w0-3 で実行。前回基準 cdbefbde9 から今回HEADまで、対象3ソース・split_module.py・lean_source.py のコミット差分がないことを確認した。前回のHA snapshotを利用。数学のLean・道具を変更せず、apply・prune・追加ビルドは行っていない。

| 対象 | 終了コード | 秒 |
| --- | ---: | ---: |
| SerrePositivity.HomotopicalAlgebra.Simplicial.Generators | 1 | 0.686 |
| SerrePositivity.HomotopicalAlgebra.Generated.Basic | 1 | 0.565 |
| SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalFrame | 1 | 0.562 |

## SerrePositivity.HomotopicalAlgebra.Simplicial.Generators

```text
split_module: STOP: /Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ifw0-3/SerrePositivity/HomotopicalAlgebra/Simplicial/Generators.lean:26: unsupported top-level syntax: attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType
```

## SerrePositivity.HomotopicalAlgebra.Generated.Basic

```text
split_module: STOP: /Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ifw0-3/SerrePositivity/HomotopicalAlgebra/Generated/Basic.lean:54: unsupported top-level syntax: attribute [instance] CofibrantlyGenerated.smallObjectI CofibrantlyGenerated.smallObjectJ
```

## SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalFrame

```text
split_module: STOP: /Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ifw0-3/SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/DiagonalFrame.lean:82: unsupported top-level syntax: local instance : ModelCategory (SimplexCategory ⥤ C) := Reedy.simplexModelCategory C
```

全ログを確認し、各ログは上記STOP1行のみ。対象コードのコンパイルエラーではなく、既存の保守的パーサーが未対応構文を拒否したもの。前回と同じ制約のため、共通前提に従い対応を広げず停止する。

必要な判断は、attributeコマンド（local instance / instance）の帰属、include hgen のスコープ、無名local instanceのsnapshot生成名との対応を分割道具で扱う方針を認めるかどうか。推測した宣言名や未検証splitをJSONへ入れていない。

完全なコマンド・終了コード・時間は `.lake/verify/ifw0-3-resume-8e6e75d8e/w2a-recheck.json`。前回の読解・HA12本のビルドとsnapshot・HL42本/R27の計測は `w2a-preflight-stop.md`。今回の変更は本報告とw1.mdへの停止位置の追記のみ。全体verifyの追加実行・コミットなし。
