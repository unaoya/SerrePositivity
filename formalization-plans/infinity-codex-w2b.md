# Codex 作業指示書 IF-W2b：R73（FilteredExchange の三分割）→ R37（Stable への逆向き辺）→ R38（F2 への逆向き辺）

作成：2026-11-02 夕（∞ 基盤の整備、管理は Claude）。宛先：∞ の Codex。
**開始**：草案（§3.0、ビルドなし）は今すぐ。適用と内部検証（§3.1、小さなビルドだけ）は草案の承認後。**下流の一回ビルドと verify（§3.2）は暦の #10（DG-W3 の後、見込み 11-04）に Claude が合図する**。
計画：[infinity-foundation-plan.md](infinity-foundation-plan.md) の R73・R37・R38（§5 段 C）、§3 の FilteredExchange の処置、§6 の W2b 行（完了条件：中核の層の順序の違反 0、例外一覧を除く。ここで中核の完了条件 1・5 がそろう）。
**共通の前提**：[IF-W0-1](infinity-codex-w0-1.md) §0、[IF-W0-3 §10.31・§10.33〜10.35](infinity-codex-w0-3.md)（判断表、条件 5 は失敗モジュール数、個別照合）、[IF-W2a-2 §7〜§9](infinity-codex-w2a-2.md)（宇宙の明示、保存比較は v3b、`_proof_N` の束ね）、[DG-W2 §13-1](dg-codex-w2.md)（宣言単位の到達性）。
worktree は `../SerrePositivity-ifw0-3` をそのまま使い、main（5c909058e 以降）から `infra/if-w2b` を切る。対象 JSON の書式は `scripts/refactor/targets/README.md`（move／split／archive／reimport、§10.30 の split → move）。

## 1. 目的と現状（11-02 16:50 の `layer_check.py --report`：直接違反 297）

| 対象の辺 | 本数 | 項目 |
| --- | ---: | --- |
| F2 → Derived（`FilteredExchange/PiCriterion` → `Derived.CoherentBar.Compact.FilteredSpaceBridgeInput`） | 3 | R73 |
| F1 → Stable 23、F1B → Stable 54、HomotopyLimits → Stable 50 | 127 | R37 |
| HomotopyLimits → F2 82、Stable → F2 40、F1 → F2 17 | 139 | R38 |
| **W2b の対象 計** | **269** | 終了時 0 |
| 範囲外：HomotopyLimits → KST 16、F2 → KST 7、HomotopyLimits → HA 2（W2c の R69・R70・R56b）、DG → PerfectComplex 3（DG-W3） | 28 | — |

### R73：`F2/FilteredExchange/` 2,127 本の三分割

X ＝ `FilteredExchange/` の下で `PiCriterion/` を除く 2,094 本。集約 `F2/FilteredExchange.lean`・`F2.lean`・監査（`scripts/audit/`）を除いた**外側**から直接 import されている X のモジュールを起点に、X の中の import を辿って届く集合を **A（使われている）**、残りを **B（集約からしか届かない）**、`PiCriterion/` 33 本を **C** とする。計画の数（10-28）は A 369・B 1,727・C 33。W1・W2a の後なので少し違ってよい。差は報告する。

| 集合 | 処置 | 先 |
| --- | --- | --- |
| A | `move`（または必要なら `split`）で正しい層へ。各モジュールの先は、prune 後の import がすべて収まる**最も低い層**。filtered の定義と filtered な図式の弱可縮性は **`F2/Filtered/`**（新設。既存の `F2/Filtered.lean` は入口にする）。余錐の付け替え・各点の余極限の判定・空間値の余極限の道具は、閉包に応じて Core／F1／F1B／HomotopyLimits／F2 | 中核の各層 |
| B | **`archive`**：`SerrePositivity/Archive/InfinityCategories/FilteredExchange/` へ（追跡するがビルドしない。`Archive/WIP` と同じ扱い。由来と「直接経路 X は 10-25 に停止、Ind 側の d′ が正本」を README に書く）。計画 §9-2 の未決（診断として残す／archive／削除）は **archive に決定**（11-02、Claude） | Archive |
| C | `move` で **`InfinityCategories/Derived/PiCriterion/`** へ（中核の外。橋 `FilteredSpaceBridgeInput` と同じ Derived。閉包に KST・DG が入るのは Derived では許される）。名前空間は変えない（R54） | Derived |

- 集約 `F2/FilteredExchange.lean` は削除する。`F2.lean`・ルートの入口から FilteredExchange への参照を外し、A の新しい場所を R59 の入口の規則で登録する。
- 監査：`scripts/make_area_audits.py` の area `infinity_f2_exchange`（`audit_infinity_f2_exchange`）は対象が空になるので **area ごと削除**し、A は移った先の層の監査に入る（再生成）。C は Derived の監査に入る。R60 の「archive 後の監査の扱い」はこれで決める。
- 検査：archive する B に利用者が残っていないこと（validator）、A の逆閉包が中核の層の中に収まること、`F2.lean` の入口の `#check` 一覧（`f2-entry-checks`）に B の宣言が残っていないこと。
- 記録：ルート閉包の本数の前後（B の archive で約 1,700 本減るはず）。

### R37・R38：逆向きの辺 266 本

辺ごとに（上の層のモジュール M → 下の層のモジュール N、ここでは「M が自分より上の層 N を import している」辺）：

1. **宣言単位の到達性**（DG-W2 §13-1 の道具）で、M が N から実際に使う宣言の集合 D を出す。
2. 処置を次の優先順で決め、対象 JSON に書く：
   - (i) D が一般論（安定性・sifted・PΣ を使わない）→ D を N から **split** して M の層かそれより下へ下ろす（`keep`／`moved`、§10.30）。
   - (ii) N 全体が一般論 → N を **move** で下ろす。
   - (iii) M が本当に上の層の理論を使っている → M の置き場所が誤り。M を上の層へ **move**（M の利用者がすべてその層以上のときだけ。下の利用者がいれば**止めて報告**）。
   - R38 では **sifted・PΣ は F2 に残す**（計画）。HomotopyLimits・Stable のモジュールが sifted・PΣ を要るなら (iii)。
3. 一つの split で複数の辺が消えることが多い。辺ではなくモジュールごとにまとめて計画し、辺 → 宣言 → 処置の表を報告に付ける。
4. 下ろした宣言の `attributes`（simp・instance）は JSON の `attributes` に写す。宣言の本文・名前・名前空間は変えない。

## 2. 所有範囲

- `SerrePositivity/InfinityCategories/{F1,F1B,HomotopyLimits,Stable,F2}/`、`InfinityCategories/Derived/PiCriterion/`（新設）、`SerrePositivity/Archive/InfinityCategories/`（新設）、`F2.lean`・ルートの入口、`scripts/audit/`（再生成）、`scripts/make_area_audits.py` の area 表、`scripts/refactor/targets/w2b-*.json`、`layers.json`（例外は**増やさない**。要るなら止めて報告）。
- 外側：A・C の利用者（KST・Spectra・EInfinity・Derived・DG・監査）の **import 行だけ**。
- 変更しないもの：CategoryTheory（論文の層の側）、DG の道具（`merge_modules.py` と試験は DG が直す）、宣言の本文。

## 3. 手順

### 3.0 草案（ビルドなし、**止めて報告する点 1**）

1. A／B／C の集合と本数（計画の 369／1,727／33 との差）、A の各モジュールの先、B の利用者 0 の検査、C の move 一覧 → `targets/w2b-r73.json`。
2. R37・R38 の辺 → 宣言 → 処置の表 → `targets/w2b-r37.json`・`w2b-r38.json`。(iii) で下の利用者がいる M の一覧（あれば）。
3. `validate_targets.py`、`move_module.py` の dry-run、`layer_check.py` のグラフで適用後の循環 0 と層の順序の直接違反の見込み（0 になるか。残るならどの辺か）。
4. 下流の逆閉包の本数と時間の見積もり（A・C の利用者と R37・R38 の split 先の利用者）、監査の一覧の変化、ルート閉包の本数の見込み。
5. 新しい失敗の型（split できない相互依存、上に移せない M）があれば一覧。**ここで止める。** 承認は Claude。

### 3.1 適用と内部検証（承認後。小さなビルドだけ。鍵と `ps` で他の全ビルドがないことを確かめる）

1. キャッシュから復元 → before snapshot **v3b**（対象：A・B・C、R37・R38 の split 元と先、それらの直接の利用者）。
2. R73 → R37 → R38 の順に適用（コミット 3 本。R73 は archive・move・入口・監査の再生成を含む）。
3. 内部ビルド（移動先・分割先・直接の利用者）。失敗は判断表（補充の import／完全修飾／宇宙の明示／名前付き引数。IF-W2a-2 §7〜§9）。補充が禁止辺（上の層・KST・DG・HA・モデル圏）になるなら止める。
4. after snapshot v3b → 保存比較 → 残りは §10.34〜10.35 で個別に照合 → **止めて報告する点 2**（round の表、A/B/C の最終本数、処置の件数、保存比較、`layer_check.py --report` の前後）。

### 3.2 下流と verify（**暦の合図を待つ**：#10、DG-W3 の後）

1. 下流の一回ビルド（鍵のもと。見積もりは §3.0-4）。round の記録、条件 5 は失敗モジュール数で。
2. 保存比較 v3b（全体）。層検査：`layer_check.py --enforce W2b` が通ること（中核の層の順序の直接違反 0、例外一覧を除く）、W1／W2a の禁止モジュール数が 1／166 から増えないこと、ratchet の基準の取り直し。
3. 監査の再生成の確認（`audit_infinity_f2_exchange` の削除、A・C の監査）。verify（`VERIFY_JOBS=6 VERIFY_MEMORY_GB=40`）→ PASS・gate:true → **止めて報告する点 3**（verify の summary、ルート閉包とビルド時間の前後、層検査の前後、コミット一覧）。

## 4. 許す変更（宣言の意味を変えないもの）

- 補充の import（禁止辺にならないもの）、完全修飾、宇宙の明示、名前付き引数の明示（いずれも保存比較 v3b で一致を証明、別コミット「修飾・宇宙の明示」）。
- `set_option maxHeartbeats` の section 内の引き上げ（R80 の候補として記録）。
- split に伴う import の和・見出し・section の包み・`universe` 行（道具が行う）。`attributes` の写し。

## 5. 止めて報告する条件

1. 草案で (iii) の M に下の層の利用者がいる。split できない相互依存がある。
2. B に利用者が残る。A の逆閉包が中核の外へ出る。
3. 補充の import が禁止辺になる。`layers.json` に例外を足さないと層検査が通らない。
4. 宣言の本文・型・名前を変えないと直らない。
5. 保存比較 v3b で未説明の不一致（データの差）がある。
6. 補充だけの round で失敗モジュール数が減らない。

## 6. 禁止事項

- 宣言の本文・名前・名前空間の変更（§4 以外）。archive したファイルの削除。R54（名前空間）・R78（Mathlib への置き換え）・段 G。
- DG の道具（`merge_modules.py`・その試験）の変更。`layers.json` の例外の追加。
- 鍵なしの全ビルド。暦の合図の前の下流ビルド・verify。main の作業木での作業。

## 7. 道具の回（ビルドなし。草案と並行してよい。別コミット）

1. `verify_runner.py`：`VERIFY_MEMORY_GB` の既定を 45 → **40**（IF-W0-4 の実測 50.8 GB と、IF-W2a-2 の verify の最大同時 RSS 37.5 GB・待ち 2 回から）。`scripts/refactor/README.md` の「既定の並列数（6）と予算」を直す。試験の既定値も合わせる。
2. **Lake キャッシュの掃除の方針**（`scripts/refactor/README.md` に書く。実行はしない）：11-02 時点で `~/.cache/lake` は 22 GB・成果物 331,250 本、空き 455 GB。`lake cache clean` は**空きが 150 GB を切ったときだけ**、全ビルドのない時刻に、全 worktree が温まった状態で行い、直後に main で `lake build` を走らせて現行の成果物を登録し直す。区切りごとの定期的な掃除はしない（古い版が残っても害は容量だけ）。
3. `merge_modules.py --check` の循環検出と、`test_merge_modules.py` の既存の失敗（`test_snapshot_cli_delegates_and_ignores_module`）は **DG の道具なので DG に任せる**（DG-W3 §8）。∞ は触らない。

## 8. 追記（2026-11-02 夜、草案の停止（§5-2）への回答：集計条件 3 点と、試験の既存失敗 1 件）

**受領**：X 2,094・C 33、集計 3 通り（`w2b-r73-preflight-stop.json`）、§7 完了（runner 40 GB・README、ed1981cdd）。

1. **監査の除外**：`scripts/audit/` だけでなく **`scripts/audit_*.lean`・`scripts/audit/*checks*` を含む全監査を除外**する。監査は利用者ではなく、再生成する側。
2. **C を利用者に数えるか**：**数える**（A 368・B 1,726）。archive する B を誰かが import していてはいけないので、C（PiCriterion）が使う B のモジュールは A 側。ただし、**外側の利用者が C だけ**のモジュール（368 − 365 ＝ 3 本の見込み）は中核の層ではなく **C と一緒に `Derived/PiCriterion/` へ移す**（PiCriterion の支え。中核に不要な一般論を増やさない）。対象 JSON では `dest` を `Derived/PiCriterion/` にし、`note` に「利用者は PiCriterion のみ」と書く。
3. **「A の逆閉包が中核外へ出たら停止」の意図**：書き方が悪かった。意図は **順方向の依存閉包**（A の各モジュールが import で辿り着く集合）が中核の層・Foundation・Mathlib の中に収まること（KST・DG・Derived・EInfinity・モデル圏の HA に届かないこと）。**A の利用者が中核の外（KST 35 辺・Derived 33 辺・EInfinity 3 辺）にあるのは問題ない**。利用者の import 行を新しい場所へ書き換えるだけ（所有範囲 §2 の「外側は import 行だけ」）。§5-2 を「A の**依存**閉包が中核の外へ出る」と読み替える。
4. **試験の既存失敗（∞ の道具）**：main で `test_layer_check.LayerTests.test_foundation_negative_rank_and_prefix_scope` が失敗する（`layers.json` に DG-W2(b) が **DG 層を rank −1** で登録したため、「Foundation 以外は rank > −1」の仮定が古くなった）。§7 の道具の回で直す：rank −1 の基盤層が複数あってよい（Foundation・DG）とし、検査は「中核（`core` の層）は rank ≥ 0」に改める。verify には影響しない（Python 試験は gate の外）。
5. これで §3.0 を再開：A の各モジュールの先（依存閉包から最も低い層）、B の利用者 0 の検査（全監査除外・C を利用者に含めた上で）、C ＋ 支え 3 本の move、R37・R38 の表、validator・dry-run・適用後の模擬 → 停止点 1。
