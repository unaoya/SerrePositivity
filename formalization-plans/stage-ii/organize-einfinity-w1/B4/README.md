# OE-W1 の改名への追従資料（準備中）

これは段1の準備資料。移動の適用・移送後の対象ビルド・v3b・引用／Tag・root・正式全監査・verifyは未検収であり、まだ最終の取り込み用の表ではない。完成後の報告コミットで検証済みの版を指定する。主張・証明の変更や、D81で止めた経路の再開を含めない。

## 表と所有元

- `../module-map.json`：段1の588本のモジュール対応。456本を移動し、132本は恒等。
- `../namespace-rewrite-map.json`：原環境の実際のnative所有元から作った、既存の書換器用の表。public 3,282名とprivate user name 75名の改名候補を含む。旧BEのroot全体を置換する表ではなく、99ファイルの所有宣言だけをStoppedRoutes.ISW2Totへ運ぶ。
- `../stage1-modules.csv`：588本の元ソースSHA、元／先のファイルとnamespace、根拠、原行数。
- `../preparation/native-owners-before.json.gz`：原環境の588本・4,160宣言の実所有元。private 157を含む。
- `../preparation/native-owner-destinations-proposed.json.gz`：上の全宣言の移送先候補。**privateの移送後raw kernel名を観測済みとはしていない**。最終の公開宣言／import所有元表は、対象ビルド後の実native表で確かめてから加える。
- `../branch-impact.json`：他のレーンのHEADと、dirty／untracked Leanを読取専用で照合した文字列影響。draftsも含む。現在の5枝は0本だが、後から足した差分や短名の全束縛を検証済みという意味ではない。

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

- `research/einfinity-general/README.md`：一般部品489本。現段階は原環境の実在する公開宣言と型の抜粋による目録案。
- `research/is-w2-be-route/README.md`：D81で止めたBE99本。IS-W2は12/25、R03d／R03hとTot比較は未完、R06〜R10は未着手。
- `research/g12-monad-route/README.md`：HA Monads179本の既存目録。今回移動しない。

今回の移送後もEInfinity監査は、元の3,887モジュールをmodule-mapで運んだ集合を保持する。一般部品357本がEInfinity接頭辞の外へ出ることを理由に公理監査の対象から落とさない。これらの最終結果と、基準側の層の未登録348本・既存違反86件を区別した照合はreport-organize-einfinity.mdへ記録する。

`preparation/compiler-child-parent-review.json`には、直接のソース宣言を持たない179件の生成された等式・合同補題を記録した。ファイルのnamespaceとは別に改名される親へ追従するものが2件ある。これらの実providerを移送後のnativeで確認するまでは、source-owned API用のimport所有元として自動登録しない。
