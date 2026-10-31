# Codex 作業指示書 DG-W2：統合の道具（a）と、D3＋土台でない 9 ディレクトリの統合の束（b）

作成：2026-10-31（DG の整理、管理は Claude）。宛先：DG の Codex（DG-W1 を実施したセッション）。
計画：[dg-cleanup-plan.md](dg-cleanup-plan.md) §3 D3・D4・D5、§4 DG-W2、§5a（再ビルドの規則）。調査：[archive/dg-survey-2026-10-30.md](archive/dg-survey-2026-10-30.md) §5〜§6、対応表 [dg-consolidation-2026-10-30.json](archive/dg-consolidation-2026-10-30.json)、障害 [blockers](archive/dg-consolidation-blockers-2026-10-30.json)。
**共通の前提**：[IF-W0-1](infinity-codex-w0-1.md) §0。DG-W1 の [§8〜§10](dg-codex-w1.md) の規則（監査の前のビルド、rsync の扱い、全ビルドは一回）も引き続き有効。

この指示書は **(a) と (b) の二部**で、(a) はビルドを伴わない道具の作業、(b) は束の適用と一回の下流ビルド。**(b) は別途「始めてよい」と伝えるまで始めない**（∞ 側の束のビルドと機械を分け合うため。計画 §5a-5）。(a) の終わりで止めて報告する。

## 0. 作業場所

- DG-W1 を main に取り込んだ後（Claude が伝える）、**同じ worktree `../SerrePositivity-dgw1` をそのまま使う**（`.lake` が温まっている）。`git merge main` してから `git checkout -b infra/dg-w2` を切る。新しい worktree は作らない。
- main の作業木では作業もビルドもしない。

## 1. (a) 道具：所有範囲と禁止

**新しく作るファイルだけ**を所有する：
- `scripts/refactor/merge_modules.py`、`scripts/refactor/with_build_lock.sh`、`scripts/refactor/warm_build_dir.sh`
- 試験 `scripts/refactor/test_merge_modules.py`、`scripts/refactor/test_build_scripts.py`
- `scripts/refactor/targets/dg-w2-merge-plan.json`（(b) の計画の草案）と `dg-w2-merge-dryrun.md`（dry-run の報告）
- `scripts/refactor/README.md` への追記（新しい道具の節だけ）

**既存の道具（`validate_targets.py`・`split_module.py`・`prune_imports.py`・`lean_source.py`・`decl_snapshot.lean`・`compare_snapshots.py`・`verify.sh`・`verify_runner.py`・`layer_check.py`）は変更しない。** ∞ 側の Codex が同時に直しているので衝突する。既存の道具に変更が要ると分かったら、止めて報告する（必要な変更の内容を書く）。利用はしてよい（`lean_source.py` の解析関数、`decl_snapshot.lean`・`compare_snapshots.py` を subprocess で呼ぶ、など）。

## 2. (a)-1 `merge_modules.py`

BS の [bhatt-scholze-merge-modules.py](bhatt-scholze/bhatt-scholze-merge-modules.py)（314 行）を一般化する。BS の挙動（宣言・証明・名前空間・variable に手を加えない；元モジュールを順に、元の冒頭の section 行に元ファイル名を付けた名前付き section で包み `end` で閉じる；`public import` の和；見出し `/-! ## 見出し（旧 パス） -/` の下に元の module docstring；universe の和；元ファイルは git rm；import 行の書き換え；`private_renames`；`deletes`；`stubs`；既定 dry-run・`--apply`）は保つ。変える点：

1. **所有範囲とモジュール名の接頭辞を引数にする**：BS の `OWNED`・`NAME` の固定を外し、`--area SerrePositivity.DifferentialGraded`（複数可）で統合する側の接頭辞を、`--rewrite-scope <regex>`（複数可、既定はリポジトリ全体の `SerrePositivity/**/*.lean` と `scripts/**/*.lean`）で import 行を書き換える範囲を与える。DG では書き換え範囲は全体（外からの 1,188 辺は IC・KST・EInfinity にある。**DG の外は import 行だけを変える**）。
2. **計画の書式を targets の配列に合わせる**：`{"module": <統合先>, "action": "merge", "sources": [<元モジュール>…（連結順）], "docstring": <概要／方針／規約／使われ方>, "private_renames": {<元>: {<旧>: <新>}}, "deletes": [], "stubs": [], "candidate": "D4", "note": ""}` の配列。`validate_targets.py` は変更しないので、書式と整合性の検査（元の二重登録、統合先の重複、連結順が import の向きに矛盾しないこと、閉じていない section、同名 private の衝突、`set_option` の値の食い違い、`public section` のない元）は **`merge_modules.py --check` が自分で行う**。
3. **統合先の名前が元の一つと同じパス**でも扱える（上書き）。統合先が新しいパスのときは `module` 行から作る。
4. **保存検査との結合**：`--snapshot-before <json>`・`--snapshot-after <json>` で、`decl_snapshot.lean` の出力（元モジュール群と統合先）を受け取り、`compare_snapshots.py` を呼んで**宣言名で**（モジュール名を無視して）集合・型・本体ハッシュ・公理・属性の一致を確かめる。生成補題と transient は IF-W0-3 §10.7・§10.11 の規則（compare_snapshots.py の既存の挙動）に従う。
5. **大きさの上限**：`--max-lines N` を与えると、統合先が N 行を超える計画を警告として列挙する。上限は **1,500 行**（Mathlib の `longFile` の既定値。対応表はこの上限で切ってあるので、超えるものは出ないはず。出たら報告）。
6. **dry-run の報告**：`--report <md>` で、統合先ごとに 元の本数・行数の合計・import の和の本数・外からの importer の本数・警告（section・private・set_option）を表に出す。

試験（`test_merge_modules.py`、Lean を呼ばない部分と、呼ぶ部分を分ける）：
- 一時ディレクトリの小さなモジュール 3 本（`public section`・`noncomputable section`・`set_option` 違い・同名 private・閉じていない section・universe 宣言・外部 importer）を統合して、出力の形（section の包み、見出し、import の和、`end`）と、importer の import 行の書き換え、`--check` の各検出を確かめる。
- Lean を呼ぶ試験は 1 件：リポジトリ内の一時モジュール 2 本（`test_targets.py` と同じやり方で作って終了時に消す）を統合し、`decl_snapshot.lean` 前後で宣言が一致することを確かめる。`lake build` は一時モジュールだけ。

## 3. (a)-2 `with_build_lock.sh`

全ビルドを機械で一つずつにする排他。
- 使い方：`zsh scripts/refactor/with_build_lock.sh [--wait SECS] -- <command…>`。例 `with_build_lock.sh -- lake build SerrePositivity`。
- 鍵は worktree をまたいで共通の場所 `${TMPDIR:-/tmp}/serre-lake-build.lock/`（`mkdir` の原子性で取る）。中に `owner.json`（pid・worktree のパス・開始時刻・コマンド）を書く。
- 取れないときは待つ（既定は無期限、10 秒ごとに再試行、待っている間は 1 分ごとに持ち主を表示）。持ち主の pid が生きていなければ古い鍵として取り除いて取る。
- コマンドの終了コードをそのまま返し、終わりに鍵を消す（trap で中断時も消す）。
- 他の worktree で鍵なしの `lake build` が走っていても検出はできないので、取る前に `ps -axo command= | grep '[l]ake build'` を見て、あれば警告を出す（止めない）。
- 試験（`test_build_scripts.py`）：二つ同時に起動して直列になること、古い鍵の掃除、終了コードの透過。

## 4. (a)-3 `warm_build_dir.sh`

main（または指定した worktree）の `.lake/build` を複製して温める。
- 使い方：`zsh scripts/refactor/warm_build_dir.sh [--from ../SerrePositivity] [--yes]`。
- 手順：(1) 複製元で `lake build` が走っていないことを確かめる（`lsof -a -d cwd` で cwd が複製元の `lake` プロセス。あれば待つか `--yes` なしなら中止）。(2) `rsync -a --delete <from>/.lake/build/ .lake/build/` を実行。(3) 終了コード 23・24 のときはログから消えたファイルの一覧を取り、**それが `.lake/build/lib/lean/` の出力（olean・ilean・ir・c・trace・hash）で件数が 50 未満**なら受け入れて一覧を表示し終了コード 0、それ以外（packages の下、件数が多い、他の種類の失敗）なら終了コード 1 で止める。(4) 最後に `lake build SerrePositivity --no-build` の出力の先頭 20 行を表示して、未ビルドの起点の数を報告する（この時点でビルドはしない）。
- `.lake/packages/` は複製しない（lake-manifest が同じなら同一。違えば止めて報告）。
- 試験：rsync を小さな一時ディレクトリで実行し、消えたファイルの扱いと終了コードを確かめる。

## 5. (a)-4 D3・D4 の計画の草案（ビルドなし）

0. **（10-31 追記）対応表に載っているが追跡されていないモジュールは草案から外す。** `Morita/ScalarExtensionKernelOutputComponents.lean` は D レーン停止時の未追跡の作業途中ファイル（main の作業木にだけあり、コミットされていない）。草案から除外し、報告に「対応表 981 → 980」と書く。同様の未追跡ファイルが他にあれば同じ扱い（`--check` で元モジュールが `git ls-files` にあることを確かめる）。
1. [dg-consolidation-2026-10-30.json](archive/dg-consolidation-2026-10-30.json) の 126 の統合先のうち、**土台でない 9 ディレクトリ**（Morita・Endomorphism・Verdier・Quotient・Resolution・Tensor・Bimodule・Perfect・Presentation）に属するものを `dg-w2-merge-plan.json` に写す（連結順は対応表のまま）。土台 5 ディレクトリ（Module・Complexes・Category・Functor・Derived）は DG-W3 なので入れない。統合先の名前は対応表の仮名（`…1.lean` など）のままでよい。名前の確定は (b) の前に Claude が行う。
2. **D3 の項目**を同じ JSON に `move`／`split` として加える（計画 §3 D3 の表）：SConstruction の 26 本（群 A 17 本 → `DifferentialGraded/Functor/`、群 B 9 本 → `DifferentialGraded/SharedFunctoriality/`）、`Functor/ModuleExtensionConjugation`・`Module/ExtensionRepresentable*` → SharedFunctoriality、`IC/Derived/DGObjectImage` → `DifferentialGraded/Category/ObjectImage`、`Verdier/{OrderSquare, ChecksOrderSquare, ChecksU17Integration}` → `Asymptotic/DGVerdier/`、`Perfect` の `finiteProjective_exists_retract`・`strictlyPerfectComplex_biprod` → HomologicalAlgebra（split）。`strictlyPerfectComplex`・`PerfectHomotopy` の定義の依存はそのまま残し、報告に書く（未決 §7-1）。
3. `merge_modules.py --check --report dg-w2-merge-dryrun.md --max-lines 1500` を実行し、警告（同名 private・set_option・閉じていない section・外からの importer）と、統合先ごとの行数を報告に出す。既知の障害（`Derived/AssociatorMiddle` の `paste_associator`・`post_paste`）は土台側なので今回は出ないはず。
4. 1,188 本の外からの import 辺を、書き換え範囲（IC・KST・EInfinity・Paper 等）ごとに数える。
5. 下流の見積もり：束で変わるモジュール（統合元＋D3 の移動元・移動先＋import を書き換える利用元）の逆閉包の本数を `layer_check.py` のグラフ（または `lake` の import 情報）で数え、DG-W1 の実測（新規 10,693 本で約 6 時間、3 セッション同時）から単独なら 1 本 1.0〜1.5 秒として時間を見積もる。

## 6. (a) の受入条件と報告（止めて報告する点 1）

1. 試験：`python3 -B -m unittest discover -s scripts/refactor -p 'test_*.py'` が PASS（既存の 145 件を壊さない。∞ 側の変更が main に入っていれば merge してから）。
2. `merge_modules.py --check` が `dg-w2-merge-plan.json` で終了コード 0（警告は許す）。
3. `with_build_lock.sh`・`warm_build_dir.sh` の試験 PASS。`zsh -n` 成功。
4. `git status` が所有範囲（§1 の新しいファイルと README の追記）だけ。
5. 報告：統合先の数・行数の分布（1,500 行超があれば）・警告の一覧・外からの辺の内訳・下流の本数と時間の見積もり。
6. コミットは「道具」「試験」「計画の草案と報告」の 3 本。`git commit --only`。

## 7. (b) 束の適用（別途「始めてよい」と伝えてから）

概要だけ書く。詳細は (a) の報告と、統合先の名前の確定（Claude）を受けて追記する。1 ファイルの上限は 1,500 行で決定済み。

1. `with_build_lock.sh` で鍵を取り、`warm_build_dir.sh --from ../SerrePositivity` で main から温める（Claude が main を温めておく）。
2. D3 の move／split と D4 の merge を**全部適用**（`split_module.py`・`move_module.py`・`merge_modules.py --apply`）。D5：統合で写す docstring の `dg-theory-u12e-general-inventory.md`・`dg-theory-m5-status.md` への参照を `formalization-plans/archive/…` に書き換える（R79 の規則：相対パスの深さを保つ。本文の `git mv` は Claude が同じ日に行う）。
3. **内部の検証**：統合先と移動先だけを `lake build <module>…`（上流しか要らないので下流は作らない）。`decl_snapshot.lean` で後の snapshot を採り、`merge_modules.py --snapshot-before/--snapshot-after` と `compare_snapshots.py` で全対象の保存検査。
4. 外からの import の付け替え（`merge_modules.py` が行う）→ **下流の一回ビルド**（`lake build SerrePositivity` と監査対象）。失敗した利用元があれば、失敗の出力から直接 import を補う（prune の規則）。補充先が DG の外で層の規則に反する（DG → KST 等）なら止めて報告。
5. `layers.json` に DG の規則（DG が import してよいのは DG・HomologicalAlgebra・CategoryTheory・Mathlib）を加え、`layer_check.py --report` で前後を比べる（既存の `layers.json` の編集になるので、この時点で ∞ 側の変更が入っていれば merge してから。**ここだけは既存ファイルの編集を許す**）。
6. verify.sh（`VERIFY_JOBS=3`、キャッシュなし）→ PASS・gate:true → 止めて報告（点 2）。

## 8. 禁止事項

- 宣言の本文・名前・名前空間・証明の変更。
- 既存の道具ファイルの変更（§1。例外は (b)-5 の `layers.json`）。
- (b) をこちらの合図なしに始めること。全ビルド（ルート・監査対象・verify）を鍵なしで走らせること。
- main の作業木での作業・ビルド。

## 9. 追記（2026-10-31、(a) の報告への回答と (b) 前の確定事項）

**承認**：(a) の 3 コミット（道具 0ce48e2d1・試験 50d096cc2・草案と報告 406c19405）、試験 66 件（Lean 保存試験は別実行で成功）、`--check` 終了 0、草案（78 統合先・980 本、D3 move 33・split 2）、外部辺 1,182（統合元への辺 342）、下流 7,222 本（単独 120〜181 分）を確認した。

(b) の前に次のとおり確定する。**(b) の開始は別途合図する**（∞ 側の束の verify の後）。それまでに 1〜5 を草案に反映し、6 の名前の案を出して止める（ビルドなし）。

1. **`Verdier/OrderSquare` は D3 の move（→ `Asymptotic/DGVerdier/`）だけ。** 統合先 `Verdier.Comparison` の元から外す（元は `ComparisonLinear`＋`SupportSquare`）。`ChecksOrderSquare`・`ChecksU17Integration` も move のまま。
2. **D3 の split 2 件（`PerfectComplex.ProjectiveBounds`・`PerfectComplex.BiproductPerfect` → HomologicalAlgebra）は取り下げる。** PerfectComplex は論文の層の領域で統合中なので、DG の Codex は触らない。DG → PerfectComplex の 3 辺（`finiteProjective_exists_retract`・`strictlyPerfectComplex_biprod`・`strictlyPerfectComplex`／`PerfectHomotopy` の定義）は、(b)-5 で `layers.json` の `allowed_until_move` に例外として登録する（登録する辺の一覧を草案の報告に書く）。`cochainBiprodXIsoProd` の配置の確認も不要。
3. **上限超過 12 件はそのまま。** 生成後の上限を 1,700 行に改める（元の本文 1,500 行＋見出しと section の包み。計画 §5a-7）。`--max-lines 1700` で警告が 0 になることを確かめる。
4. **`set_option` の差 6 件（4 統合先）は section ごとに閉じて保つ**（計画 §3 D4 の注意どおり）。無名 section の補完 971 件はそのまま。
5. **統合先の仮名を本名にする（案を出す）。** 規則：(i) 名前は主題を表す名詞句（`Associator`・`DerivedComparison` など対応表の語幹は使ってよい）。(ii) 番号つきの仮名（`Associator1`・`Associator3`・`DerivedComparison1`・`DerivedComparison3`・`ScalarExtension1`・`ScalarExtension2`・`Compact1`・`Compact2`・`Ring2`・`Path1`・`Path2` など）は、元モジュールの basename と module docstring の概要を見て、**その塊が何を扱うか**で言い換える（例：`Associator/Components`・`Associator/Pentagon`・`DerivedComparison/Triangles`）。どうしても主題で分けられない大きさの分割だけ `…/Part1`・`Part2` を許す。(iii) 既存のモジュールと同名にしない（統合先が元の一つと同じパスのときはそのままでよい）。(iv) 対応表と草案の `module` を書き換え、旧仮名 → 本名の対応表を `dg-w2-names.md` に出す。Claude が承認してから適用。
6. 下流の見積もり（7,222 本）は (b) の直前に main 取り込み後の状態で再計算する。

以上を反映した草案（`dg-w2-merge-plan.json` の更新、`dg-w2-names.md`、報告の追記）を 1 コミットにして止めて報告する（止めて報告する点 1′）。
