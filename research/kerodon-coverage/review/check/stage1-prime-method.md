# 段1′：名前の自動補正

`resolve_names.py` は段1の2,108種類の記載と結果を入力にする。
既に型・公理検査が通った394件は保持し、not_found 1,602件、unresolved_reference 111件に加え、
同じ名前空間不足に起因するcheck_failed 1件を候補検査の対象にする。
数学的な主張との一致は、補正後も段2で確認する。

## 候補を作る規則

1. 出典のLeanを読み、入れ子コメントと文字列を除去する。改行位置は保持する。
2. namespace・section・endのスタックを追い、section内のopenはsection終了時に外す。
   open … inは次の宣言だけに適用し、同じ行のopen … in lemmaにも対応する。
   namespace _root_.Xは絶対名として扱う。open scopedは名前空間の候補には使わない。
3. 引用行のスコープを使い、同じ末尾名の宣言が近傍12行にある場合は最寄り宣言のスコープも使う。
   引用行から離れた別namespaceの同名宣言は、その候補の根拠にしない。
4. 原記載の名前と、スコープ・openを補った接尾名を候補にする。
   近傍宣言がある場合、原記載と一致する最長の修飾接尾名を保持する。
   例：SimplicialObject.δを、同じファイルにあるCosimplicialObject.δに縮めない。
5. 文書で使われているパス省略IC/はSerrePositivity/InfinityCategories/、
   HomotopicalAlgebra/はSerrePositivity/HomotopicalAlgebra/に展開する。
   `.lake/packages/mathlib/`という接頭辞も除去する。
6. 説明文、匿名instanceの型、複数名のスラッシュ略記、記法は単一の定数名に推測で縮めない。
   パスを一意に確定できないもの、候補を作れないものはmanualに残す。

これはPythonによる限定したスコープ解析であり、Leanの全構文の再実装ではない。
未対応の記載や複雑な表現、近傍のprivate宣言は、推測で承認せず段2へ回す。

## kernelによる採用条件

引用元のモジュールだけをimportし、候補ごとに#check @名前と#print axioms 名前を実行する。
その前に、source ~/.zshenv後、with_build_lock.sh --wait 0経由のlake build <module>を行う。
待機条件は依頼書§4と同じ。全体ビルドやverifyは行わない。

- 候補が全て検査され、型と公理を確認できた完全名がちょうど一つ：renamed。
- 二つ以上の完全名が通る：ambiguous。手作業で確認する。
- 一つも通らない・候補を作れない：manual。
- 未実行や出力不明の候補が残る：pending。一意に決まったとは扱わない。
- 元のfound 394件：foundのまま保持。

Leanのフロントエンドには`-DmaxErrors=0`を渡す。set_optionだけでは多数の未知名による
フロントエンドの打ち切りを防げないことを試走で確認した。
候補ごとの診断位置と生成したコマンド行番号で、型・公理・失敗を対応付ける。
標準3公理以外も記録する。名前が一意に解決しても数学的な対応の承認にはならない。

## 実行

worktreeのルートで実行する。HEAD・入力・検査スクリプトを変更したら新しいrun-dirでprepareする。

```sh
python3 -B research/kerodon-coverage/review/check/resolve_names.py prepare --run-dir runs/stage1-prime-01
python3 -B research/kerodon-coverage/review/check/resolve_names.py run --run-dir runs/stage1-prime-01
python3 -B research/kerodon-coverage/review/check/resolve_names.py parse --run-dir runs/stage1-prime-01
```

runはchecked済みのジョブを飛ばす。既存の失敗・中断ジョブの生出力を上書きしない。
限定検査はrun --module <module>（複数指定可）または--limit <件数>で行える。
中断後にHEADが変わった場合は、元の記録を保持して新しい計画で必要なmoduleだけを実行する。

出力：resolution-results.csvは原記載ごとの結果、declarations_newは採用した引用、
successful_jsonは成功候補の一覧。original_idは段1のreferences.csvと結び付く。
verified-candidates.csvには成功した候補の型と公理を保存する。
summary.jsonは補正前後の件数、manual・ambiguous・pending、追加公理の件数を記録する。
manifest.jsonは入力・スクリプト・ソースのhash、Git HEAD、候補計画のhashを持つ。

モジュールごとの生成Leanと生出力はruns/*/modules/に保存し、.gitignoreで除外する。
既に枝で追跡されている古い生出力は削除・追跡解除しない。
mainへの受け渡しにはスクリプト、報告、runごとのresolution-results.csv・verified-candidates.csv・
summary.json・manifest.jsonを用い、生出力や大量の失敗候補を含む中間計画は取り込まない。

## 検証

スコープ、入れ子コメント、文字列、open … in、sectionの終了、絶対namespace、
行位置のずれ、修飾名の保持、候補の曖昧性・未実行を扱う15件の回帰テスト。
試走ではSimplicialObject、PiZeroConstant、F2.Presentable.Accessibleの3モジュールで
335候補を検査し、18記載を一意に補正できた。引用元が重なる別記載もそれぞれ記録する。
この試走の数字は全件結果ではない。

```sh
python3 -B -m unittest discover -s research/kerodon-coverage/review/check -p 'test_resolve_names.py' -v
```
