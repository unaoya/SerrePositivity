# R75＋R79＋W1＋W2a：束の手順書（IF-W0-3 §10.16）

**束の構成はユーザー承認済み。現在は準備まで。以下の実行は「DG-W1 を main に入れた」の通知後に限る。** main merge・キャッシュ複製・snapshot・Lean ビルド・数学ソース編集はまだ行っていない。対象 JSON は W1 68件（move62/split3/reimport3）、W2a 1208件（move1197/split9/reimport2）。

R75 は29モジュール＋検査1本を全て削除する（[承認済みの処置一覧](r75.md)）。生成監査を利用者に数えず再生成し、SpherePowersのimport、禁止一覧、manifest・個別チェックのモジュール名参照、READMEの案内を同じR75コミットで更新する。

## 0. 開始条件と保存先

- 作業場所：`/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ifw0-3`、ブランチ `infra/if-w0-3`。
- Claude から DG-W1 の取り込み通知と凍結の開始時刻を受ける。HA・CT・HotA・∞・KST・EInfinity・ルート・監査への他セッションの取り込み停止は、束の適用から verify 後まで約1日。こちらから他者へ連絡を送らない。
- 未コミットの準備ファイルをレビュー可能な状態で保存する。main の変更と衝突する場合、無断の stash・上書きはしない。
- DG 側の build lock・warm-up の実際の場所と使用法を、取り込み後に読む。このレーンでは新作しない。

通知後のコマンド：

```sh
cd /Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ifw0-3
git branch --show-current
git status --short
git merge main
ps -axo command= | grep '[l]ake build'
# 他の worktree の全ビルドがあれば待機。無いことを確認してから：
rsync -a --delete ../SerrePositivity/.lake/build/ .lake/build/
mkdir -p .lake/verify/batch-w1w2a
```

rsync 23/24 は、ログ全体を読み、消えたのが書き換え中の出力だけと確認できる場合だけ受理。それ以外は停止。`.lake/build` を一から作り直さない。以下では証拠ディレクトリを **E = `.lake/verify/batch-w1w2a`** と記す。コマンド中の `<...>` は対象 JSON・採取した一覧から展開する値であり、そのまま実行しない。

## 1. 新 main 上の再検査と before snapshot（全適用より前）

```sh
python3 -B scripts/refactor/layer_check.py --report
python3 -B scripts/refactor/rewrite_r79_docs.py --dry-run --output .lake/verify/batch-w1w2a/r79-before.json
python3 -B scripts/refactor/check_r75.py --output .lake/verify/batch-w1w2a/r75-before.json
git rev-parse HEAD > .lake/verify/batch-w1w2a/base.txt
```

旧 snapshot を新基準の証拠に流用しない。対象ソース・移し先・import・R79件数が変われば報告して計画を更新する。W1/W2a JSON に R75 の削除を加えず、別の明示一覧として扱う。

**集合の定義**：

- `M` = W1/W2a の移動元→移動先（1259組）。`S` = split の元と先（12組）。宣言名は改名しない。
- `D` = R79 dry-run に出た635ファイル、`I` = `M` の移動元を直接 import する全利用元、`K` = 明記済み downstream_imports の利用元。
- before 保存対象 `P` = W1/W2a の変更元 ∪ D ∪ I ∪ K ∪ {SpherePowers}。ただし宣言を持たない入口 reimport は保存比較から除外する。R75 の殻は import とコメントだけであることを確認し、削除前の全文とハッシュを別保存。宣言があれば削除せず STOP。
- after 保存対象 = `M(P)` ∪ split の新規ファイル。ビルド失敗から非中核への補充が新たに必要なら、その利用元の未変更の before も保持して比較対象に追加する。

全ソースを復元できるよう、変更予定ファイル・未追跡の既存骨組み・削除候補をバイト単位で保存し、各ファイルの SHA-256 と git status を記録する。無関係なユーザー変更を復元で消さない。

`decl_snapshot.lean` は olean を読むため、**ここだけでも通知とキャッシュ複製が必要**。コピー済みの成果物の鮮度を確認し、不足した対象だけを `lake build <module...>` で補う。snapshot 自体はビルドを自動実行しない。全適用前に対象をまとめて採取し、分割ごとの下流ビルドはしない。§10.18 以降は `snapshot_batch.py` で直列採取する。通常は最大64本、KST.SConstruction・InfinityCategories.Derived・EInfinity は最大16本。全群 `-M 40000`、メモリ上限で失敗した群だけ半分に割る。単独でも失敗すれば停止する。

```sh
python3 scripts/refactor/snapshot_batch.py --modules-file E/before-modules.json --name-map E/private-name-map.json --output-dir E/before-shards --huge-terms scripts/refactor/targets/huge-terms-2026-11.md
```

全 shard の schema_version・hash_algorithm が同じこと、modules が重複しないこと、§10.21 の行の同一性（宣言名・定義元モジュール）で比較し、承認された生成補題は共通環境の定義元へ統合し、双方のソースにある同名宣言は別行に保持して、modules/sources/declarations を統合、count を再計算して `before.json` とする。元 shard も保存する。split 用には modules と宣言を元モジュールで絞った snapshot を作り、全12件を `--snapshot MODULE=FILE` に指定して静的検査する。

```sh
python3 -B scripts/refactor/validate_targets.py scripts/refactor/targets/w1.json scripts/refactor/targets/w2a.json --snapshot <MODULE=FILE> ... --output .lake/verify/batch-w1w2a/targets-before.json
```

## 2. 適用順：R75 → R79 → W1 → W2a（ここではビルドしない）

### 2.1 R75

§10.16で承認された29モジュール＋検査1本を削除する。通知後の再検査で新しい実importerが現れたらSTOP。対象の生のimporterを隠さず、承認済み処置で解消する。

1. SpherePowersの3行目を `public import SerrePositivity.CategoryTheory.Monoidal.AdjacentBraid` に向け直す。現在の行が想定と違えばSTOP。
2. 下記の30ファイルをgit rm。`r75-delete.txt`には29モジュールと `scripts/check_word_source_operators.lean` を列挙済み。
3. 生成監査の直前の全文を保存し、下記コマンドで再生成。生成物を手で編集しない。他areaの差分が出たら生成直前の内容へ戻して報告する（既存の並行変更を消さない）。
4. audit_homotopical_foundations／audit_homotopical_general_tools等の禁止モジュール一覧、manifest、残る個別チェックから、削除するモジュール名の登録行を外す。JSON配列の書式を検査し、宣言名や別のモジュール名は削除しない。
5. HA READMEの拡張子なし案内3件をRectificationの実体へ向ける。Monoidal READMEの既に正しいリンクと、短い宣言名だけの言及は保持する。
6. 消えるモジュールへの実importが残らないこと、登録とREADMEの処置、所有範囲を確認し、R75の1コミットを作る。

```sh
git rm -- <r75-delete.txt の30ファイル>
python3 scripts/make_area_audits.py
git diff -- scripts/audit/
git diff --check
git commit --only -m 'refactor: remove R75 compatibility modules and update references' -- <削除30本と承認済み参照更新の全ファイル>
```

単独の再ビルドは挟まない。SpherePowersのimport書き換えはbefore/after保存検査と束の下流ビルドに含める。R75削除対象とR79対象は重ならず、R79の期待件数は変わらない。

### 2.2 R79（文書別に2コミット）

```sh
python3 -B scripts/refactor/rewrite_r79_docs.py --document plan --dry-run --output .lake/verify/batch-w1w2a/r79-plan.json
python3 -B scripts/refactor/rewrite_r79_docs.py --document plan --apply --output .lake/verify/batch-w1w2a/r79-plan-applied.json
git diff --check
git commit --only -m 'docs: point R79 plan references to archived section 396' -- <r79-plan.json の paths>
python3 -B scripts/refactor/rewrite_r79_docs.py --document inventory --dry-run --output .lake/verify/batch-w1w2a/r79-inventory.json
python3 -B scripts/refactor/rewrite_r79_docs.py --document inventory --apply --output .lake/verify/batch-w1w2a/r79-inventory-applied.json
git diff --check
git commit --only -m 'docs: point R79 inventory references to archive' -- <r79-inventory.json の paths>
```

plan は `[plan]` 618件＋StageTwoの本文1件、inventory は `[inventory]` 618件＋本文16件。ArrowFactorization系3本はこの2コミットの該当分に含め、独立の第3コミットにしない。DG 530本には触れない。件数・ハッシュ・docstring以外の差分を確認してからコミット。R75 の index を含めないため必ず `--only`。

before snapshot の原本は変更しない。split の入力用コピーについてだけ、R79 スクリプトが出した厳密な before→after と現ソースが一致することを確認して `sources[].source` を更新する。宣言行数は変わらないため、宣言情報・位置・型・本体には手を入れない。R79以外の差があれば STOP。snapshot のためだけにR79後の全ビルドを挟まない。

### 2.3 W1、次に W2a

各窓内の順は split → imports/reimport の置換 → 明記済み downstream_imports → move。ただし複数 split の計画は、互いの import 編集をする前に全12件を dry-run で作る。保存済み preflight の moved/keep/imports は使うが、**古い plan.json の利用元への自動編集は適用しない**。

```sh
python3 -B scripts/refactor/split_module.py <module> <dest> --moved <names...> --snapshot <R79を反映した入力snapshot> --dry-run --output .lake/verify/batch-w1w2a/<module>-plan.json
# 承認済みの宣言リスト、依存方向、変更が元と先の2ファイルだけであることを確認。
```

作った plan は `split_module.apply(root, plan)` で適用する。CLI を使う場合は同じ snapshot と引数で `--apply`。**`--prune-imports` はこの段で使わない**（個別下流ビルドを起動するため）。StandardCosimplicial もこの束に含め、旧来の9本目の個別試行を再開しない。

```sh
python3 -B scripts/refactor/split_module.py <module> <dest> --moved <names...> --snapshot <input-snapshot> --apply --output .lake/verify/batch-w1w2a/<module>-applied.json
```

W1の適用でW2aの計画本文のimportが改名された場合、事前計算したW2a planの before/after 両方へ、W1と同じ `scripts/move_module.py` の `rewrite(text, moves, {})` を適用してから `split_module.apply` する。W1の既知 downstream 補充も両方へ同じ規則で合成する。**現ソースとの厳密一致が崩れたら停止し、snapshot の source を無条件に上書きして通さない。** 本文・宣言リストを別物へ作り替えない。

`imports` は完全置換。split は両側、move は移動元の現ファイルに移動先キーの値を適用、reimport は同名ファイルの入口を編集する。既存 `prune_imports.replace_imports(text, modules)` を使用（関数だけで Lean は呼ばない）。`downstream_imports` は `lean_source.add_import` で指定分だけを加える。W2a の処理中は既に済んだW1の改名を全リストへ反映する。補充の自動推定はしない。

窓ごとに `moves` だけの JSON を作り、既存の移動道具を使用する。`symbols` は空、decl名は保持、redirect は使わない。

```sh
python3 -B scripts/move_module.py .lake/verify/batch-w1w2a/w1-moves.json
python3 -B scripts/move_module.py .lake/verify/batch-w1w2a/w1-moves.json --apply
# 同じ手順を w2a-moves.json について行う。
python3 -B scripts/move_module.py .lake/verify/batch-w1w2a/w2a-moves.json
python3 -B scripts/move_module.py .lake/verify/batch-w1w2a/w2a-moves.json --apply
git diff --check
python3 -B scripts/refactor/layer_check.py --report
```

各段の before/after パス・全文ハッシュ・実コマンド・終了コードを E に記録する。実ファイルの import グラフが validator の模擬と一致するか検査する。W1/W2a JSON は適用前の一覧なので、適用後の作業木へそのまま validator を掛け直さない（元ファイルが消えている）。実際の after graph と保存済み模擬の比較で検査する。snapshot の本検査は次段。

**停止点1：全適用後、下流ビルド前。** 適用件数、R75の30本削除と参照更新、R79の2コミット、差分、importグラフ、下流集合と見積もりを報告し、続行指示を待つ。

## 3. 下流を一回ビルドし、必要な補充だけを行う

対象集合 `B` は、変更元・既知補充先・moveによりimportが変わる利用元を種にした **before graph の逆閉包を改名した集合**と、全 split の新規先と、**実 after graph の変更ファイルの逆閉包**の和集合。既存の集約を省かず、root も含まれればビルドする。R75の削除元は除く。`prune_imports.affected_modules` で集合を計算でき、Lean は実行しない。

現在の元グラフでの準備計算は、before逆閉包20,208、移動を反映しsplit先を足したafter候補 **20,220モジュール**。snapshot候補は before **2,970**／after **2,982**。`batch-module-sets.json` に集計、全名前は `.lake/verify/ifw0-3-addendum16/batch-module-sets-full.json`。これは **main取り込み後・実適用後に再計算する計画値**。その後の補充で増えた対象も含める。時間は§10.14の単独6〜8時間を目安にする。

`B` のうち他の対象から到達するものはビルド入口から省き、極大入口（SCCなら代表）だけを選ぶ。入口の推移閉包が `B` の全要素を覆うことを確認する。単純に100本ずつに分けて下流全体を何度も起動しない。全入口を **一つの `lake build` 呼び出し**で渡す。

```sh
ps -axo command= | grep '[l]ake build'
# DG 側の排他道具の実仕様を読んで取得してから、nohup付きランナーで：
lake build <Bを覆う極大入口一覧>
```

切断対策のランナーは Python の `subprocess.run(['lake','build',*targets], stdout=log, stderr=STDOUT)` で実行し、終了コード・秒数を JSON に保存。`nohup python3 -u E/run-build.py > E/launcher.log 2>&1 &` の形で開始する（Eは実パスへ展開、実装内容を先にレビュー）。ログ末尾だけで判定せず **全ログを rg で確認**する。

失敗の出力からモジュールが分かるときは束を二分しない。非中核の不足 import は、元のsnapshotの使用定数と移動先対応で確認してまとめて補充し、downstream_imports に記録。中核なら `downstream_repair_snapshot` の規則で補充せず STOP（利用元・失敗宣言・使用する移動宣言）。新規利用元のbeforeは元ソースと元成果物から確保し、現在のソースをbeforeと偽らない。補充の後の再ビルドは必要分に限定する。

**二分は原因モジュールを全ログから特定できない場合だけ。** 全件のbeforeを保持した専用worktreeで、対象項目を依存関係を壊さない二組に分けて一方ずつ再現する。splitの両側と対応するimport/moveを別々に切らない。同時に二つの全ビルドを走らせない。正常な束・既存コード・所有範囲外の失敗は直さず報告し、二分のための全復元・再ビルドを勝手に反復しない。

ビルド後、after集合をbeforeと同じ shard 規則でまとめて採取する：

```sh
python3 scripts/refactor/snapshot_batch.py --modules-file E/after-modules.json --name-map E/private-name-map.json --output-dir E/after-shards
python3 -B scripts/refactor/compare_snapshots.py .lake/verify/batch-w1w2a/before.json .lake/verify/batch-w1w2a/after.json --name-map .lake/verify/batch-w1w2a/private-name-map.json --module-map .lake/verify/batch-w1w2a/declaration-module-map.json --output .lake/verify/batch-w1w2a/preservation.json
python3 -B scripts/refactor/layer_check.py --report
```

§10.18 に従い、before の前に写像を確定し、両側で同じファイルを渡す。private 接頭辞除去だけで同名になる場合は空の写像を使う。公開宣言名は不変。追加の name-map が必要なのは `_private.<旧module>.` など移動に伴う生成名だけで、実際の宣言→移し先対応で作る（splitは宣言単位）。変更を隠す広い名前空間置換はしない。型・本体・公理・属性・宣言の増減を比較し、生成補題は§10.7/10.11、transientは一覧を残す。入口reimportは保存対象外だがビルドと層検査を必須とする。R79は宣言の完全保存が必要。

**停止点2：下流ビルドと保存検査後、verify前。** ビルド終了コード・全ログ検索・補充一覧・保存比較・transient・実グラフの数値・各段の時間を報告し、続行指示を待つ。既存監査の失敗や規則違反を直して通さない。

## 4. verify と最後の停止

承認後、他の全ビルドがないことを再確認する。監査キャッシュは使わず、試験用の変数は値0でも存在させない。

```sh
env -u VERIFY_ONLY_AUDITS -u VERIFY_SKIP_BUILD -u VERIFY_EXTRA_AUDITS -u VERIFY_BASELINE -u SORRY_AUDIT_ROOT -u SORRY_AUDIT_ALLOWED VERIFY_JOBS=3 VERIFY_CACHE=0 zsh scripts/refactor/verify.sh
```

実行は下流ビルドと同様に nohup とログ・終了コード保存付きにする。verify の全体実行はこの一回。`summary.json` の status=PASS・gate=true、99監査、sorry閉包、counts、各段時間、retried件数と対象を確認する。ログ全体も検索する。

**停止点3：verify後。** 成否を問わず報告して停止。mainへの取り込みはしない。一時適用の復元または実施結果のコミット・取り込みは、この停止報告後の指示に従う。失敗を既知の失敗として追加しない。

## 準備段階の現在地

§10.14 を道具 `b0491d1fa`、試験 `67c6ea7cb`、記録 `21258b0d9` の3コミットに保存済み。R79はdry-runのみ。R75は§10.16により29本＋検査1本の削除と参照更新が承認済み。W1/W2aを含めて未適用。次はDG-W1通知を待つ。
