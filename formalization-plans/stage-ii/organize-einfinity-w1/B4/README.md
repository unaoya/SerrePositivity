# OE-W1 の改名への追従資料（段1検収済み）

段1は完了。対象1,661本、v3b全1,071本・未説明0、引用／タグ63件・欠落／余分0、root、全audit-targets、正式106監査は成功。同じHEAD `76dfccc3a` の通常verifyで106監査すべて成功し、別実行のsorry閉包も終了0・PASSとなったため、11-17の調整役指定の合成判定で **verify PASS** とする。機械のgateは時間枠で止まったnon-gateのまま残す。主張・証明の変更やD81で止めた経路の再開を含めない。数学ソースは `6678d6a9a`、証拠保存は `10338c2be`、停止点報告は枝先。

## 表と所有元

- `../module-map.json`：段1の588本のモジュール対応。456本を移動し、132本は恒等。
- `../namespace-rewrite-map.json`：原環境の実際のnative所有元から作った、既存の書換器用の表。public 3,282名とprivate user name 75名の改名候補を含む。旧BEのroot全体を置換する表ではなく、99ファイルの所有宣言だけをStoppedRoutes.ISW2Totへ運ぶ。
- `../stage1-modules.csv`：588本の元ソースSHA、元／先のファイルとnamespace、根拠、原行数。
- `../preparation/native-owners-before.json.gz`：原環境の588本・4,160宣言の実所有元。private 157を含む。
- `../preparation/native-owner-destinations-proposed.json.gz`：上の全宣言の移送先候補。これは初期の候補表であり、実測を置き換えない。移送後raw kernel名も取得済みで、実際の対応は下の `public-owner-map.csv` と `actual-owner-pairs.json.gz` を用いる。
- `../branch-impact.json`：他のレーンのHEADと、dirty／untracked Leanを読取専用で照合した文字列影響。draftsも含む。最終の現存四枝の候補は枝・pathの組で8件（異なるpathは6本）だが、後から足した差分や短名の全束縛を検証済みという意味ではない。

モジュール名と宣言のnamespaceは同じとは限らない。特にAnodyne二本は、一般のFrameHomからKerodonの3.1と4.6へ別々に置く。namespace名からimport元を推測せず、最終のnative所有元表を用いる。今回、同じ型の別名wrapperを削除する操作はない。

## レーン側の原環境での採取とプレビュー

自分の枝の検証済みをコミットし、未検証の下書きは作業木に保持してよい。mainのこの整理を取り込む**前**に、自分の枝で追加・変更したLean（draftsを除く）をJSON配列`files`へ置く。draftsの文字列影響は別に記録する。`bulk`は検収済みの整理枝の作業木、`follow`は新しい一時ディレクトリの絶対パス。

```sh
plan="$bulk/formalization-plans/stage-ii/organize-einfinity-w1/namespace-rewrite-map.json"
zsh scripts/refactor/with_build_lock.sh --class impl --wait 3600 -- \
  python3 "$bulk/scripts/refactor/bulk_namespace.py" collect \
  --root "$PWD" --files "$files" --output "$follow/before"
python3 "$bulk/scripts/refactor/bulk_namespace.py" rewrite \
  --root "$PWD" --files "$files" --index "$follow/before" \
  --plan "$plan" --output "$follow/preview"
```

collectは元のソースがビルド済みの原環境で行う。昼は3〜5分に収まるファイルの組へ分け、同じworktreeの整理券を重ねない。rewriteは同じソースへのプレビューだけを作り、共有鍵を使わない。元のcompilerの束縛とsource SHAを保持し、mainの取り込み後のソースへ古い索引を流用しない。

`review.json`が空であること、型・証明には移動した名前の参照以外の差分がないことを確認してからmainを取り込み、ローカルな差分を保って反映する。保留があるときは適用せず、元の束縛と新しい実在宣言を照合する。openが同じ名前で残り、そのopenで使う全宣言も同じ完全名で残る場合は、元のopenを保持する既存の方針を使う。namespaceを分けたため使う宣言の一部だけが移る場合は、その実際の参照を明示する。

反映後は変更したモジュールと直接のimporterを対象ビルドし、小さい監査を行う。元HEAD・採取対象・書換ファイル数／行数・保留・対象ビルドと監査の結果・コミットを報告する。

## 目録と到達点

- `research/einfinity-general/README.md`：一般部品489本。移送後の実所有元と実在する公開宣言のヘッダーによる目録。
- `research/is-w2-be-route/README.md`：D81で止めたBE99本。IS-W2は12/25、R03d／R03hとTot比較は未完、R06〜R10は未着手。
- `research/g12-monad-route/README.md`：HA Monads179本の既存目録。今回移動しない。

今回の移送後もEInfinity監査は、元の3,887モジュールをmodule-mapで運んだ集合を保持する。一般部品357本がEInfinity接頭辞の外へ出ることを理由に公理監査の対象から落とさない。これらの最終結果と、基準側の層の未登録348本・既存違反86件を区別した照合はreport-organize-einfinity.mdへ記録する。

`../preparation/compiler-child-parent-review.json`には、直接のソース宣言を持たない179件の生成された等式・合同補題を記録した。ファイルのnamespaceとは別に改名される親へ追従するものが2件ある。移送後の実providerと分割読取りの文脈差は `native-provider-context-review.json` と全captureで照合した。ソースを持たない補題をsource-owned APIのimport登録へ自動転用しない。

## Mathlib の HomotopicalAlgebra の open（11-17 追記、検証済み）

この整理で `SerrePositivity.HomotopicalAlgebra` が新しく可視になる import 文脈がある。元のコンパイラの記録で `open HomotopicalAlgebra` が Mathlib の global な名前空間一つへ解決していたときは、`open _root_.HomotopicalAlgebra` と明示して元の解決を保存する。project 側へ解決していた open を Mathlib 側へ変えない。既に `_root_.` があるものも変更しない。元の定数参照における同じ global prefix の明記も、元の解決情報で認証した位置だけを絶対名にする。

plain な共有書換器は、宣言のnamespaceを変えない呼び出し側でこの open をそのままにすることがある。module の対応表を反映しただけで終えず、元の採取の open operand と対象ビルドを確認する。現在の他レーンの保守的な文字列候補は③-aのKanPushoutCocones.leanとDiscreteAnodyneExtensions.leanの二本。これは二本とも実際に失敗するという判定ではない。元の意味参照とビルドで確かめる。

## 移送後の実所有元による照合（11-17）

`public-owner-map.csv` は比較範囲1,071モジュールの公開10,244宣言について、前後で実際に観測した完全名とimport所有元を対応させたもの。生成補題も、この1,071本を同時に読んだ環境での実providerのまま載せる。ソースを持たない生成補題のproviderはimportの組合せで変わることがあるため、その行を新しいソースAPIのimport登録の根拠にはせず、親宣言の定義元も確認する。ソース宣言だけの候補表やファイルのnamespaceから所有元を推測した表ではない。private 232件を含む全10,476件の対応は `../preparation/actual-owner-pairs.json.gz`、前後の実データは `native-owners-before-augmented.json.gz` と `native-owners-after.json.gz` にある。欠落0・余分0であるが、型・証明項の保存結果は別のv3bで判定する。

引用metadataの七欄と重複度は、元61件＋計画したpartial二件＝63件に完全一致。結果は `../preparation/citation-comparison-final-rules.json`。verifyの最終判定は `../preparation/composite-verification.json` と報告§18を参照する。

## 検収結果（11-17）

数学ソースの移動・参照は `6678d6a9a`。同一HEAD `76dfccc3a` の全106監査成功とsorry閉包単独PASSを、調整役の明示指示により合成して **verify PASS** とする。機械のgateはnon-gateのままで、summaryやrunnerを生成・書換えしていない。

二つのログは `../preparation/normal-60min-controller.log.gz` と `../preparation/sorry-alone-success.log.gz`。106監査の実行・入力の対応、sorryの終了0、合成判定は `normal-106-audits-success-evidence.json.gz`、`sorry-alone-success.json`、`composite-verification.json` に保存した。所在と外部原資料は `../evidence/README.md` を参照する。今回だけ証拠本体の枝への保存が承認され、次回以降はgit外の証拠への目録のみを残す。

最後の文字列照合はmath/inf-supply 2、math/scheme 1、fix/audit-reimport 4、research/cited-coverage 1の計8件（異なるpathは6本）。削除・改名された旧枝は `branch-impact.json` に明示した。他のレーンは編集していない。mainの取り込みと今夜のroot・全監査は調整役が行う。段2は分類表だけで未適用。`/private/tmp/oe-w1-*` は削除しない。
