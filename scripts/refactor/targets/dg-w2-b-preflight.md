# DG-W2(b) 宣言単位の事前検査

基準は `887896bba`（`a26eb3351` と文書移動 `d219b6eb1` を取り込み済み）。Lean の基準内容は `4010216e9` と同一。いずれも衝突なし。作業木は `SerrePositivity-dgw1`、ブランチ `infra/dg-w2`。

- D3 は 33 move、split 0。D4 は承認済みの本名 78 統合先、979 元。対応表 981 → 980 は未追跡 WIP の除外、980 → 979 は OrderSquare を move のみにした差。
- 生成行数の最大は 1,605、上限 1,700 超は 0。匿名 section の補完 970 と option の差 6 は承認済みの扱い。循環 0。
- 下流の逆閉包は main 取り込み後 6,940 本。単独 1.0–1.5 秒/本なら 115.7–173.5 分。監査時間は別。
- Lake の 3 変数を確認し、共有鍵の下で事前ビルド。19,722 ジョブ、新規 4、本体復元を含め 53.436 秒、終了 0。warm_build_dir.sh は未使用。
- DAG before snapshot は DG 内全体と直接利用者の 2,259 モジュール、21,497 宣言行。988.712 秒、終了 0。木に展開すると 1 GB を超える項も DAG のまま採取。
- 推移的 import で到達する利用は 24,678 モジュール対。移動・統合・集約修正後に失われる宣言参照は **0**、DG に残る KST・IC・Asymptotic の宣言依存は **0**。事前の `downstream_imports` は空。
- 入口・Checks の 312 モジュールを検査。DG 内へ移す 30 本はすべて DG 入口から到達。OrderSquare の移動後、DG の入口と Verdier.U17 の集約 import から外す。ルートは移動先を直接 import して公開範囲を保つ。ルート自身は import のみで宣言・#check はない。
- 統合先・移動先の上流で、内部検証に先立ち必要となる DG 外の import 書換は 0。

## 生成補題の帰属確認

一括環境で検出した 4 対は変更前から import 閉包外だった。単独環境で 4 モジュールを再採取し、各宣言の種類・型・本体ハッシュ・公理・属性の一致を確認して `uses_modules` を照合した。元の snapshot と単独再採取の原本は両方保持し、不要な import は加えない。

| 利用元 | 帰属が変わる生成補題 |
| --- | --- |
| Category.TensorInclusions | dgTensorElement.congr_simp |
| Category.TensorMixed | dgTensorElement.congr_simp |
| Resolution.Cells.PrefixGeneration | generatorInclusion.eq_1 |
| KST.SConstruction.DGTensorLeftUnitElements | BalancedTensor.element.congr_simp |

## DG-W3 と重なる 3 元

ModuleExtensionConjugation、ExtensionRepresentableClosedNaturality、ExtensionRepresentableComposition は HEAD と a26eb3351 で内容が一致。D3 で SharedFunctoriality へ移すので DG-W3 の元から外し、611 → 608 本とする。命名案 9 件は承認済みのまま。

詳細な宣言ごとの推移的利用、入口閉包、snapshot 原本、コマンドとログは実行記録 `dg-w2-b` に保存。実行中の記録場所は `/tmp/dgw2b/`、停止報告時に `.lake/verify/dg-w2-b/` に保存する。主なファイルは `preflight.json`、`single-owner-review.json`、`before-shards/manifest.json`、`before-single/manifest.json`、`dryrun.md`、`layers-before.json`。
