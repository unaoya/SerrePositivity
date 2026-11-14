# B3′ の改名への追従（準備版）

B3′ の本体の適用・最終検証・main への取り込みは別に記録する。この資料は原環境での採取とプレビュー作成に使う。各表の branch/HEAD は `lanes.json` に記録した。

- `module-map.json`：全体移動70本の旧モジュール→新モジュール。
- `public-owner-map.json`：公開ソース宣言1,936行。名前を変えずに所有モジュールだけを変えるものも含む。移動後のネイティブな宣言の存在を全件確認した。
- `namespace-rewrite-map.json`：上の70移動と、実際の移動先が存在する2,580行の所有元付き書換表。元のopenの解決先を保ち、移動した定数を完全名へ書き換える。
- `compiler-inventory-review.json`：同じ生成された式補題が別々のネイティブ環境で作られる4行。通常のソース宣言の対応とは区別し、所有元を推測した自動書換を登録していない。
- `redirects-and-deletions.json`：承認済みのInputs/Perfectoidization wrapperの削除と呼出し先。これは同じ型の宣言の改名ではない。旧wrapperだけが要求した有限表示性が定義の引数から落ちないよう、必要なら元の引数列を定義の頭に明示する。B3′ではこの方法でFiniteとConeの型を保存した。
- `*-files.json`：短い名前を調べるための採取候補。修正が確定したファイル数ではない。draftsは別の文字列の影響表へ分けた。

## 原環境での採取と一行の書換コマンド

`bulk`は検収された一括枝の作業木の絶対パス、`lane`は5a/5d/3a/3b/6/kerodon、`follow`は新しい一時ディレクトリの絶対パスとする。`files`と`plan`はこの資料を置くディレクトリのファイルへ設定する。

```sh
files="$bulk/formalization-plans/stage-ii/bulk-b3prime/B4/$lane-files.json"
plan="$bulk/formalization-plans/stage-ii/bulk-b3prime/B4/namespace-rewrite-map.json"
python3 "$bulk/scripts/refactor/bulk_namespace.py" collect --root "$PWD" --files "$files" --output "$follow/before"
python3 "$bulk/scripts/refactor/bulk_namespace.py" rewrite --root "$PWD" --files "$files" --index "$follow/before" --plan "$plan" --output "$follow/preview"
```

collectはビルド対象が検証済みの元環境で、通常の共有鍵（--wait 3600、各レーンのclass）を取って行う。rewriteは鍵を使わず、mainを取り込む前の同じ元ソースに対して行う。採取器はLakeの設定を引き継ぐ。`preview/review.json`の保留を確認してからmainを取り込み、プレビューとの差分を自分の変更へ反映する。取り込みで同じファイルに増分があった場合は、その増分を保って反映する。

importされるモジュールの名前と、宣言が実際に属する名前空間は別の表で扱う。モジュール名を新しいopenとして追加しない。保留のある構文は原環境の参照と移動後の実際の宣言で確認する。

旧wrapperをimportする新規ファイルは、代替の`SerrePositivity.BhattScholze.Perfectoidization.Interface.IntegralExistence`へ個別に追従する。移動元のIntegralExistenceも同じ先へ移るため、この削除による多対一のimport変更は、通常の一対一の移動表とは別に扱う。

最終反映後は各レーンの対象ビルドを行い、元HEAD・修正数・保留・結果を報告する。
