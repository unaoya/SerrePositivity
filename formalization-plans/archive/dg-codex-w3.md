# Codex 作業指示書 DG-W3：土台 5 ディレクトリの統合（D4 の残り）＋ D5 の残り＋ 層の仕上げ

作成：2026-11-02（DG の整理、管理は Claude）。宛先：DG の Codex。**開始は、論文の層の区切り 1-4 が main に入った後**（[coordination.md](../coordination.md) §3 の #6 の後）に Claude が合図する。
計画：[dg-cleanup-plan.md](stage-i/dg-cleanup-plan.md) §3 D4・D5、§4 DG-W3、§5a。草案：`infra/dg-w2` の `targets/dg-w3-merge-plan.json`（48 統合先・608 元、命名 9 件は承認済み）、`dg-w3-merge-dryrun.md`、`dg-w3-names.md`。
**共通の前提**：[IF-W0-1](infinity-codex-w0-1.md) §0、[DG-W2 §12〜§16](dg-codex-w2.md)（Lake キャッシュ、判断表、名前の隠蔽、universe）、[IF-W0-3 §10.31・§10.34〜10.37](infinity-codex-w0-3.md)（判断表、保存比較の個別照合、証明無関係なハッシュ）。
worktree は `../SerrePositivity-dgw1` をそのまま使い、1-4 の取り込み後の main から `infra/dg-w3` を切る。

この束は **DG の土台**（Module・Complexes・Category・Functor・Derived）を触るので、下流は DG の全部と IC・KST・EInfinity・Asymptotic・**Paper（主定理の経路）**まで約 16,300 本（単独 4.5〜7 時間）。全ビルドは束の最後に一回、鍵のもとで。

## 1. 目的（完了条件 5・6・7）

| 項目 | 内容 |
| --- | --- |
| D4（残り） | 土台 5 ディレクトリ 608 元 → 48 統合先（`merge_modules.py`）。`Derived/AssociatorMiddle` の同名 private は草案の `private_renames`（`paste_associator_middle`・`paste_associator_second_middle`・`post_paste_second_middle`）で回避 |
| D5（残り） | 土台の docstring の旧案内参照（`dg-theory-u12e-general-inventory.md`・`dg-theory-m5-status.md`）を `formalization-plans/archive/…` へ。`targets/rewrite_dg_docs.py --plan <この束の計画>` |
| 層の仕上げ | 1-4 で `strictlyPerfectComplex`・`PerfectHomotopy`・`strictlyPerfectComplex_biprod` が HomologicalAlgebra へ下り、`finiteProjective_exists_retract` が Mathlib に置き換わっていれば、DG の import をそれに向け直し、`layers.json` の PerfectComplex の例外 3 辺を外す。DG の内部の層の順序（統合後の 126 本）を `DifferentialGraded/README.md` に表で文書化する（完了条件 7。`layers.json` への内部 tier の登録は、違反 0 で登録できる場合だけ） |

## 2. 所有範囲

- `SerrePositivity/DifferentialGraded/` の下すべて（宣言の本文は変えない。例外は §4 の修飾・heartbeat）。
- DG の外：統合元を import しているファイルの **import 行だけ**（IC・KST・EInfinity・Asymptotic・Paper・scripts の監査）。
- `scripts/refactor/layers.json`（DG の例外の削除、内部 tier の登録）、`scripts/refactor/targets/dg-w3-*`、`DifferentialGraded/README.md`。
- 道具：`merge_modules.py` は自分のものなので必要なら直してよい（試験つき、別コミット）。∞ の道具（`decl_snapshot.lean`・`compare_snapshots.py`・`validate_targets.py`・`layer_check.py`・verify）は変更しない。必要が出たら止めて報告。

## 3. 手順

### 3.0 事前（ビルドなし、止めて報告する点 1）

1. 1-4 後の main を取り込み、草案（48 統合先）を `--check --max-lines 1700` で再確認する。1-4 で DG の import 先が変わっていれば（Perfect の 3 宣言など）草案と `downstream_imports` を更新する。
2. **宣言単位の到達性**（DG-W2 §13-1）：失われる参照 0、DG に残る KST・IC・Asymptotic・PerfectComplex の宣言依存の一覧（Perfect の 3 辺が消えているはず）。
3. **名前の隠蔽の静的洗い出し**（DG-W2 §14 の型）：各統合先について、統合先の import の和で新たに閉包に入る宣言の**短い名前**と、元ファイルの中で `namespace`／`open` の下で無修飾に使われている識別子の衝突候補を列挙する（`lean_source.py` の識別子抽出と snapshot の宣言名で近似。偽陽性は許す）。候補は内部ビルドで確かめる。
4. **`universe`**：`merge_modules.py` の修正（7e1fb1dea）が入っていることを試験で確かめる。
5. 下流の逆閉包と時間の見積もりを更新して報告（短くてよい。Claude の承認は不要。止めるのは 2 で失われる参照が出たとき）。

### 3.1 適用と内部検証

1. `with_build_lock.sh` で鍵 → Lake キャッシュから復元（`lake build` の再生。`warm_build_dir.sh` は予備）→ before snapshot（proof-irrelevant、土台 5 ディレクトリ＋利用元）。
2. D4（48）→ D5（docstring）を適用。コミットは「D4 土台」「D5 土台」。
3. 内部ビルド（統合先 48）。失敗は判断表（DG-W2 §13-2・§14）：禁止辺にならない直接 import の補充／名前の隠蔽は従来の解決先へ完全修飾（保存比較で同一を証明、別コミット「修飾」）／heartbeat の上限（別コミット、D8 に記録）。
4. after snapshot → 保存比較。機械比較の残りは IF-W0-3 §10.34〜10.37 の規則で個別に照合（親への束ね、生成名、Prop インスタンス、pp 比較）。**未説明が 1 件でもあれば止めて報告**（止めて報告する点 2）。

### 3.2 外からの付け替えと下流

1. 外からの import の付け替え（統合元 → 統合先）と監査のモジュール一覧の更新（DG-W2 の 3ec3cae16 と同じ道具）。本体は import 以外が不変であることを行単位で確かめる。
2. 下流ビルド（約 16,300 本）。round の記録、判断表、条件 5 は失敗モジュール数で（IF-W0-3 §10.33）。Paper の 11 本も含む。
3. `layers.json`：PerfectComplex の例外 3 辺を外す（1-4 で解消していれば）。DG の規則で直接違反 0 を確認。内部 tier の登録は §1 の条件で。`layer_check.py --report` の前後（W1／W2a／W2b と DG）で増加 0。
4. `DifferentialGraded/README.md` に、統合後の 126 本の一覧（ディレクトリ・役割・import の向き）を表で書く。
5. verify（`VERIFY_JOBS=6 VERIFY_MEMORY_GB=40`、鍵のもと、他の全ビルドなし）→ PASS・gate:true → **止めて報告する点 3**（最終）：round の表、補充・修飾・heartbeat の件数、保存比較の結果、層検査の前後、コミット一覧、126 本の一覧へのリンク。

## 4. 許す変更（宣言の意味を変えないもの）

- 名前の隠蔽の完全修飾（保存比較で型・本体のハッシュ一致を証明）。
- `set_option maxHeartbeats` の section 内での引き上げ（D8 の候補として記録）。
- 統合先の import の和、見出し、section の包み、`universe` 行の位置（道具が行う）。

## 5. 止めて報告する条件

1. 事前検査で失われる参照がある。
2. 保存比較に未説明の不一致がある。
3. 補充の import が禁止辺になる（DG → KST・IC・Asymptotic・PerfectComplex）。
4. 宣言の本文・型・名前を変えないと直らない。
5. 補充だけの round で失敗モジュール数が減らない。
6. 1-4 の後の main で Perfect の 3 宣言の移動先が分からない（論文の層の対応表を Claude が取り寄せる）。

## 6. 禁止事項

- 宣言の本文・名前・名前空間の変更（§4 以外）。D6・D7・D8（証明を変える整理）。
- ∞ の道具の変更。鍵なしの全ビルド。main の作業木での作業・ビルド。

## 7. 追記（2026-11-02 夕、静的事前調査 `ef951fa5d` への回答）

**受領・承認**：候補 4 箇所（`InfinityCategories/DGNerve/HomotopyCategory.lean` の 34・98・104・109 行）、universe 608/608 で順序保持、`--check` 48 統合先・608 元・最大 1,621 行・超過 0。報告の判断（今は何も変えず、before/after の保存比較で重点照合する）をそのまま採る。開始の合図は変わらず **1-4 が main に入った後**（見込み 11-03 午後）。それまでビルドなし。

1. **`HomotopyCategory` の 4 箇所の見込みと扱い**：Mathlib の `HomotopyCategory V c` は `V` に `Category` と `Preadditive` のインスタンスを要るので、`HomotopyCategory A D`（`A` は `CommRing` の型）では Mathlib 側の候補は elaboration に失敗し、多重定義の解決は従来どおり `DifferentialGraded.HomotopyCategory` に落ちる見込み。したがって失敗も解決先の変化も出ないはずだが、確認は保存比較の型ハッシュ（4 宣言と、それを使う `DGNerve` の下流）で行う。失敗か不一致が出たら `DifferentialGraded.HomotopyCategory` へ完全修飾する。このファイルは DG の外だが、**この 4 箇所に限って §2 の所有範囲の例外として修飾を許す**（別コミット「修飾」、保存比較で同一を証明）。∞ の束 IF-W2a-2 はこのファイルに触れていない（Claude が 11-02 に確認）。
2. **`Complexes.SphereHom` が `Complexes.Perturbation` の import 和に Mathlib の経路を持ち込む件**：統合先の import 和はそのままでよい（元の再分割や import の削減は W3 の範囲外）。同型の事例（統合先の import 和が外側の利用元に新しい短名を届ける）が内部ビルドや下流で現れたら、1 と同じ規則で扱う。
3. **構造体フィールドの 3 出現**（`Presentation/Category.lean` の `differential`）：除外でよい。
4. **universe の 4 本**（`Category.IdempotentTelescope`・`Category.EquivalenceComparison`・`Derived.AssociatorMiddleRestrictionResolved`・`Derived.AssociatorSecondMiddleRestrictionResolved`）：before/after の型ハッシュで回帰確認の対象。宇宙引数の順序差を表示だけの差として処理しない（報告のとおり）。
5. **草案の現在値**（48・608・1,621 行、private_renames 3 箇所）を正とし、旧 `dg-w3-merge-dryrun.md` の値（611 元・1,601 行）は本報告で置き換える。
6. **main の取り込み後の再確認**：∞ の束（IF-W2a-2：CategoryTheory の統合 25 群と Nerve まわりの移動）が今夜 main に入り、翌日 1-4 が入る。`infra/dg-w3` を切ったあと §3.0-1 の `--check` と、**閉包の差分だけ**（新たに届く短名の候補が増えないか）を再確認する。静的検査の全再実行は要らない。

## 8. 追記（2026-11-02 夕、1-4 を待つ間の道具の回：ビルドなし、`infra/dg-w2` の上で別コミット）

1-4 の取り込みまでの待ち時間に、DG の道具だけを直す（Lean は触らない）：

1. **`merge_modules.py --check` に循環検出を加える**：統合先どうしの import グラフ（統合元の import の和を統合先に付け替えたもの）に循環があれば、`--check` を失敗させ、循環に含まれる統合先と元の辺を報告する。IF-W2a-2 §6-4 で見つかった `Mod.InternalHom ↔ Mod.Closed` の形を試験に再現する（小さな模擬モジュールで）。既存の `--check` の出力は変えない（追加だけ）。
2. **`test_merge_modules.py` の既存の失敗** `test_snapshot_cli_delegates_and_ignores_module`（IF-W0-4 の停止点 2 で報告されたもの）を直す。原因が道具側なら道具を、試験側なら試験を直し、どちらだったかを報告する。
3. 試験は全部 PASS にして報告（短くてよい）。これは DG-W3 の事前検査には影響しない。main への取り込みは、DG-W3 の開始時に `infra/dg-w3` を切るときに一緒に入る（Claude が cherry-pick してもよい）。

## 9. 追記（2026-11-02 20:00、§5-4 の停止への回答：束縛子の型の明示を許す）

**受領**：事前検査（48・608、失われる参照 0・禁止依存 0、universe 608/608）、before snapshot 1,626 本・23,522 宣言（v3b）、D4・D5 コミット、修飾 1 箇所（`_root_.CategoryTheory.Functor.map_id`、保存一致）、内部 round 2 で `Functor.QuasiEquivalence` の `DGFunctor.ofHomMaps` が失敗（3966182e8）。

**原因の確認**：報告の診断どおり。`H : ∀ x y, (x ⟶[Complex A] y) ⟶ …` の束縛子 `x y` の型は省略されており、enriched hom の記法の instance 合成が `?C` を未確定のまま走る。統合先 `Category.Basic` に旧 `Category.Examples` の `complexEnrichment : DGCategory A (Complex A)` が入ったため、`?C := Complex A` が先に確定し、後の `F x` と合わなくなった。IF-W2a-2 §7 の「宇宙メタ変数の捕捉」と同じ機構（環境が広がり、メタ変数を含む instance 合成が別の instance に捕まる）で、宣言の意味は変わっていない。before の elaboration では `x y : D` だった。

**処置（承認）**：`(H : ∀ (x y : D), …)` と**束縛子の型を明示**する。これを判断表の新しい項目「**束縛子の型の明示**」として、「補充の import／完全修飾／宇宙の明示／名前付き引数の明示」と同じ条件で許す（DG・∞ の両方の束で有効）：before/after の保存比較（v3b）で型・本体・公理・属性が一致すること、別コミット「修飾・型の明示」、報告に一覧。一致しなければ止める。

**再開**：処置を当てて内部 round 3 → 残りの統合先 42 本 → after snapshot → 保存比較（止めて報告する点 2）→ §3.2（外からの付け替え、下流約 16,300 本、層の仕上げ、verify）→ 止めて報告する点 3。

**道具の注意**（∞ へ回す）：`snapshot_batch.py` が v1 の形式名を検査するため、実行時ラッパーで v3b の名前に合わせたとのこと。∞ の道具の回で `snapshot_batch.py` が現行の `hash_algorithm`（v3b）を受け付けるように直す（IF-W2b §7 に追記）。

## 10. 追記（2026-11-02 21:40、今夜のうちに下流へ：停止点 2 の条件付き事前承認と鍵の優先）

1. **停止点 2 の条件付き事前承認**：内部ビルド（残り 42 本を含む 48 統合先）が通り、after snapshot v3b の保存比較で**未説明の不一致が 0**（`_proof_N` の束ね・生成名・Prop インスタンスの個別照合で説明できるものは説明済みとみなす）で、当てた処置が判断表の範囲（補充の import・完全修飾・宇宙の明示・束縛子の型の明示・heartbeat）だけなら、**Claude の承認を待たずに §3.2 へ進んでよい**：外からの付け替え → 監査の一覧 → 下流ビルド（鍵のもと）→ 層検査（例外 3 件の削除、内部 tier は違反 0 のときだけ）→ README の 126 本の表 → verify（`VERIFY_JOBS=6 VERIFY_MEMORY_GB=40`）。停止点 2 の内容は停止点 3 の報告にまとめて書く。条件を満たさなければ従来どおり止める。
2. **鍵の優先**：いま走っている論文の層の 274 本のビルドが終わったら、次は DG（round 3 → 残り → 下流）。∞ の内部ビルドは DG の下流の後（明朝）に回す（Claude が ∞ に伝える）。論文の層も今夜はこれ以上ビルドしない。
3. 下流ビルドの見込みは 4.5〜7 時間。失敗 round は判断表で処理し、§5 の条件に当たるときだけ止める。朝に停止点 3 を報告。

## 11. 追記（2026-11-02 22:15、下流 round 1 の失敗への事前回答：DG の外のファイルにも注釈型の処置を許す）

下流 round 1（22:04 開始、506 根）で `InfinityCategories/Derived/Semifree.lean:69` が `HasColimitsOfShape (Discrete E.Index) (Complex S)` の instance 探索の heartbeat 超過（`synthInstance.maxHeartbeats` 20000）で失敗している（Claude が 22:10 にログで確認）。統合先の import の和で instance の探索空間が広がった型で、宣言の意味は変わらない。

**事前承認（この束の下流 round 全体で有効）**：DG の外のファイル（InfinityCategories・KST・EInfinity・Asymptotic・Paper・監査）でも、判断表の注釈型の処置を**止めずに当ててよい**：
1. `set_option synthInstance.maxHeartbeats`／`maxHeartbeats` の section 内または `in` での引き上げ、または内部で行ったのと同じ「必要な instance を `letI`／`haveI` で局所に束縛して探索を切る」処置（b89ea0f97 の型）。
2. 補充の import（禁止辺にならないもの）、完全修飾、宇宙の明示、束縛子の型の明示。
3. 条件は従来どおり：before/after の保存比較（v3b）で型・本体・公理・属性が一致、別コミット「下流の修飾・heartbeat」、停止点 3 の報告にファイル・行・処置の一覧。宣言の本文・型・名前を変えないと直らない場合だけ止める（§5-4）。
4. ∞ の束（`infra/if-w2b`）が同じファイルを触っている可能性があるので、処置は**最小の行**に限る（import 行の追加、`set_option … in` の 1 行、修飾の 1 語）。取り込み時の衝突は Claude が両方を残して解決する。

## 12. 追記（2026-11-03 09:00、保存比較の型差への回答：落ちた section 変数を `include` で戻す）

**受領**：下流 round 5 PASS（round 1〜5、注釈処置 21 ファイル・44 箇所は v3b 一致）、全体 snapshot（before 1,645・after 1,085 モジュール）、機械比較 42 件中 38 件は説明済み、残り 4 件（3 宣言）：`DGQuotient.complexColimitComparison` の型から `[HasExactColimitsOfShape J (ModuleCat.{u} A)]` が消え、`_naturality`・`_ι` がそれを参照（06f2cf626）。

**原因**：ソースの差は import 1 行（`Complexes.ExactColimits` → 統合先 `Complexes.Perturbation`）だけ。`[HasExactColimitsOfShape …]` は 878–879 行の section `variable`。Lean 4 の取り込み規則では、instance-implicit な section 変数は宣言の elaboration で**実際に使われたときだけ**型に含まれる。統合先の import の和で同じ命題を与える大域 instance が届くようになり、elaboration が section 変数ではなく大域 instance を使ったため、束縛子が型から落ちた。宣言の内容は「仮定が一つ減って強くなった」だけで矛盾はないが、**型が変わった**ことに変わりはなく、停止は正しい。

**処置（承認）**：before の型をそのまま保つ。3 宣言の直前に `include` を置いて section 変数を明示的に取り込む（例：`include ‹HasExactColimitsOfShape J (ModuleCat.{u} A)› in` の形か、変数に名前を付けて `include hJ in`。名前を付ける場合は `variable [hJ : HasExactColimitsOfShape …]` に変えるが、これは束縛子の名前の変更にすぎず型は変わらない）。判断表の「束縛子の型の明示」と同じ扱い：v3b で型・本体・公理・属性が before と一致すること、別コミット「include」、報告に記録。`linter.unusedSectionVars` の注意が出ても許す。

**代替**（`include` で before と同じ束縛子の位置・形に戻らない場合）：型の差を「大域 instance の到達による冗長な仮定の脱落。主張は強くなり、下流 13,972 本はそのまま通った」として説明済みに分類し、3 宣言を報告に明記して進む。この場合も after の型が before の型を含意すること（仮定の削除だけ）を pp の差分で示す。

**どの instance か**：after 環境で `#synth HasExactColimitsOfShape J (ModuleCat.{u} A)`（`lake env lean` の探針、ビルドなし）で供給元を確かめ、報告に書く（Mathlib か DG の統合先か）。

**再開**：処置 → 当該モジュールの再ビルド（小）→ 3 宣言の v3b 比較 → 層検査（例外 3 件の削除、内部 tier）→ README の 126 本の表 → verify（`VERIFY_JOBS=6 VERIFY_MEMORY_GB=40`）→ **停止点 3**。
