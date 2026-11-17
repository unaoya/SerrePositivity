# Codex 作業指示書 IF-W2b：R73（FilteredExchange の三分割）→ R37（Stable への逆向き辺）→ R38（F2 への逆向き辺）

作成：2026-11-02 夕（∞ 基盤の整備、管理は Claude）。宛先：∞ の Codex。
**開始**：草案（§3.0、ビルドなし）は今すぐ。適用と内部検証（§3.1、小さなビルドだけ）は草案の承認後。**下流の一回ビルドと verify（§3.2）は暦の #10（DG-W3 の後、見込み 11-04）に Claude が合図する**。
計画：[infinity-foundation-plan.md](stage-i/infinity-foundation-plan.md) の R73・R37・R38（§5 段 C）、§3 の FilteredExchange の処置、§6 の W2b 行（完了条件：中核の層の順序の違反 0、例外一覧を除く。ここで中核の完了条件 1・5 がそろう）。
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

## 9. 追記（2026-11-02 夜、§8 の読み替え後の再停止への回答：§5-2 の最終形は「直接 import」の水準）

**受領**：A 368・B 1,726・C 33、B の利用者 0、支え 3 本（C と合わせて Derived へ 36 本）、R37/R38 の辺 127/139、中核候補 365 本のうち 180 本の依存閉包が中核外 224 モジュールへ到達、試験修正 95f95cde4。

**Claude の確認（11-02 夜、main のソースで）**：PiCriterion を除く FilteredExchange のモジュールで、KST・HA のモデル圏（Quillen・Transfer・Generated・Monoidal・HomotopyFunctionComplex）・DG・EInfinity・Derived・ModelBridge を**直接** import するものは 0。180 本の到達は、既存の中核のモジュールが持つ辺（`HomotopyLimits → KST` 16、`HomotopyLimits → HA` 2。例：`IntervalHomBoundary → KST.Spectra.PointedInterval`）を経由している。これらの辺は現在の基準（W2a の禁止モジュール 166、`layer_check --report` 11-02）に含まれており、**W2c（R69・R70・R56b：KST/Spectra の一般部分を中核へ下ろす）の課題**であって、W2b の停止理由ではない。FilteredExchange はいま F2（中核）にあるので、A を中核の別の層へ動かしても中核全体の禁止閉包は変わらない。

**§5-2 の最終形**（§8-3 を置き換える）：止めるのは次のときだけ。

1. A のモジュールの**直接 import**（prune 後）に、禁止領域（KST・DG・EInfinity・モデル圏の HA・Derived・ModelBridge）か、置き先より上の層があるとき。
2. 適用後のグラフの模擬で、`layer_check.py --ratchet <基準>` の W1／W2a／W2b の禁止モジュール数・affected core が基準から**増える**とき（A が中核内で動くだけなら増えないはず。増えたら原因の辺を報告）。
3. 制限つきの層（Core・Kan、`restricted_imports`）に置こうとするモジュールの依存閉包が、その層の許可集合（Core：Simplicial・Foundation・Mathlib、Kan：＋Core）の外へ出るとき。→ そのモジュールは F1 以上に置く（Core・Kan には置かない）。

**置き先の規則**（§1 の「最も低い層」の精密化）：直接 import の層の最大値以上で最も低い層。ただし 3 により、閉包が中核外へ届くモジュールは F1 以上（実際には HL を経由するなら HomotopyLimits 以上になるはず）。

**W2c への引き継ぎ**：180 本とその経由辺（`w2b-section8-forward-closure-stop.json` の `example_paths`・`outside_by_prefix`）を停止点 1 の報告に「W2c の入力」として添える。処置は W2c。

**再開**：置き先の確定 → R37・R38 の表 → validator・dry-run → 適用後の模擬（直接違反・ratchet・`--enforce W2b` の見込み）→ **停止点 1**。

## 10. 追記（2026-11-02 夜、§5-1 の停止への回答：上移動の連鎖は宣言単位で閉じる）

**受領**：R38 で sifted・PΣ を本当に使う HomotopyLimits の上移動候補 6 本・下位利用者の辺 7 本（実参照 4、未検出 3）、R37/R38 の宣言参照表、690 本の採取、180 本は W2c の入力に記録、3ac6cf89d。

**規則**（§1 の (iii) の精密化）：

1. **未検出の 3 辺**（`FiniteCoherentProductNativeLegs → FiniteFamilyOriginalColimitTransport`、`FiniteCoherentProjectionCocones → FiniteProductIndexTransport`、`FullHomColimitDetection → CoYonedaLimitReflection`）：import は不要とみなして**削除**（prune）。確認は内部ビルドで。失敗したら instance・notation 経由の参照なので「あり」に戻して 2 へ。
2. **実参照のある辺** M → U（U が下位利用者）：U が参照する M の宣言の集合 D_M を取り、snapshot の `used_constants` を**モジュール内で推移的に**辿って、D_M が sifted・PΣ（F2 の定数）に依存するかを判定する。
   - 依存しない → **M を split**：D_M とそのモジュール内の依存先を `keep`（HomotopyLimits に残す）、残りを `moved`（F2 へ）。これが優先（計画の「一般補題は下の層へ」）。
   - 依存する → **U も上移動の候補**になる。U の下位利用者について同じ判定を繰り返し、連鎖を閉じる。閉じた集合 S（候補 6 本を含む）を**一群として F2 へ move** してよい条件は、(a) S の外からの利用者がすべて F2 以上か中核の外（KST・Spectra など、import 行の書き換えだけで済む）、(b) |S| ≤ 30 本。(b) を超えるか、(a) に反する利用者（F1・F1B・HL・Stable の、S に入れられないモジュール）が残れば、**そのモジュール名と宣言名を挙げて止める**。
3. S の置き先は F2 の既存の下位ディレクトリ（`F2/Presentable/` か `F2/Ind/`。PΣ・sifted の正本の隣）。名前空間は変えない（R54）。
4. 判定の表（辺 → D_M → PΣ 依存の有無 → split／連鎖）を停止点 1 の報告に付ける。

**再開**：上の規則で R38 の処置を確定 → validator・dry-run → 適用後の模擬 → **停止点 1**。

## 11. 追記（2026-11-02 夜、validator と §8 の食い違いへの回答：archive の利用者検査から監査を除く）

**受領**：上移動 12 本（候補 6＋連鎖 2＋独立 4）は `F2/Presentable/` へ、実参照 5 辺はモジュール内で `IsSiftedInfinity` に到達するので split 不要、未検出 3 辺は削除の模擬、validator PASS・増加指標 0、直接違反 297 → 280、禁止モジュール数 1／166／166 不変。R73 の archive 検査は `scripts.audit_infinity_f2` を外側の利用者として数えて FAIL（96fbbab87）。

**判断**：食い違いは validator 側。監査（`scripts/audit/`・`scripts/audit_*.lean`・checks）は利用者ではなく、この束で再生成・書き換える側（§1 の R73、§8-1）。`validate_targets.py` は ∞ の道具なので直してよい：

1. `validate_targets.py` に **`--ignore-importer-prefix <接頭辞>`**（複数可）を加え、archive の利用者検査でその接頭辞のモジュールを数えない。W2b では `scripts.audit`・`scripts.audit_`・`scripts.checks` を渡す。既定は空（従来どおり）。試験 1 件（監査だけが import する archive 対象が通ること、監査以外が import すれば従来どおり FAIL すること）。別コミット（道具）。
2. 監査の処置を R73 の対象に明記する：`scripts/audit_infinity_f2.lean`（手書きの import 一覧）は B の import 行を**削除**し、A の import 行を新しい場所へ書き換える。`scripts/audit/` の生成分は `make_area_audits.py` の area `infinity_f2_exchange` を削除して再生成。適用後に `--ignore-importer-prefix` **なし**で validator を再実行し、archive の利用者が本当に 0 であることを確かめる（これが本当の検査）。
3. 未検出 3 辺の削除は内部ビルドで確認（§10-1）。

**再開**：1 を入れて R73 の validator → dry-run → 適用後の全体模擬（直接違反・ratchet・`--enforce W2b` の見込み。280 からどこまで下がるか）→ **停止点 1**（A/B/C と支え、R37・R38 の処置の表、上移動 12 本、下流の見積もり）。

## 12. 追記（2026-11-02 深夜、停止点 1 の承認：ratchet の個別指標は「継承」として受け入れ、基準は W2b の終わりに取り直す）

**受領**：草案完成（R73 move 401・split 4・reimport 9・archive 1,726、R37 move 115・split 1・reimport 1、R38 move 216・split 5・reimport 67、上移動 12 本を含む）、全体模擬で対象の逆向き辺 0・循環 0、直接違反 297 → 21、W1 禁止 1 → 0、W2a/W2b 禁止モジュール 166 → 150、affected core 3,379 → 2,528、ルート閉包 25,028 → 25,005、dry-run 成功、10 分割の静的保存検査 PASS、下流 13,149 本（約 2 時間 11 分）、道具 34f2afa6d、草案 aa95d2f97。

**承認**：草案どおり適用してよい。判断 3 点：

1. **ratchet の個別指標 12 件の増加**（分割先 3 本・入口 3 本の root ごとの禁止閉包）：原因は既存の W2c 経路（HL → KST 16・HL → HA 2）の**継承**であり、新しい禁止辺はない（残る直接違反 21 はすべて既存：HL → KST 16・HL → HA 2・DG → PerfectComplex 3）。全体の禁止集合は減っている。したがって**止めない**。扱い：(a) 停止点 2・3 の報告に 12 件と経由する経路を表で記す、(b) W2b の終わり（verify PASS の後）に ratchet の基準を取り直す（W2a-2 の最終基準と同じ手順）、(c) `layers.json` の例外一覧には**加えない**。
2. **`--enforce W2b` の意味**（本束での合否）：(a) 中核の層どうしの順序の直接違反 0、(b) 直接の禁止辺が上の 21 本から増えない、(c) 全体の W1／W2a の禁止モジュール数と affected core が増えない。root ごとの指標は W2c までは診断扱い。道具の `--enforce W2b` がこれと違う判定をするなら、(a)〜(c) を検査する形に直す（∞ の道具、別コミット、試験つき）。基準の取り直しで通すのではなく、検査の定義を上の 3 条件にする。
3. **監査**：`make_area_audits.py` に area がないので、手書きの `scripts/audit_infinity_f2_exchange.lean` を**削除**する（B は archive、A・C は移った先の監査へ）。A と C（支え 3 本を含む）の全モジュールがどれかの監査の一覧に入ることを確かめ、入らないものは移った先の層の監査（生成分なら area の再生成、手書きなら import 行の追加）に加える。verify の監査は自動列挙なので、削除だけで一覧から消える。`w2b-r73-audits.json` の案をこれに合わせる。

**次**：§3.1（キャッシュから復元 → before snapshot v3b → R73 → R37 → R38 の適用（3 コミット）→ 内部ビルド（移動先・分割先・直接の利用者。未検出 3 辺の削除の確認を含む）→ after snapshot → 保存比較）→ **停止点 2**。小さなビルドだけ。**下流 13,149 本と verify は暦 #10 の合図（DG-W3 の後、見込み 11-04）を待つ。**

## 13. 追記（2026-11-03、復元の停止への回答：rsync はやめてキャッシュから、main（1-4 取り込み後）を先に取り込む）

**受領**：§12 の W2b 判定の実装（fc047fd80、18 試験 PASS）、rsync の復元 14 分で終了コード 23（`build/ir/…ModelBifibrantSourceRoofCornerEvaluation.c` の消失、現在は両側に存在）、main と依存先ソース 9 本の差分。

1. **終了コード 23 の扱い**：無害。消失は、同じ時刻に Claude が main で `lake build`（1-4 取り込み後の温め：ルート＋監査対象、11-02 深夜）を走らせていたためで、生成出力が書き直された瞬間に当たった。`warm_build_dir.sh` は DG の道具なので**変えない**（build/ir の許容追加は要らない）。
2. **復元は rsync ではなくキャッシュから**（IF-W2a-2 で行ったのと同じ：`lake build <根>` で復元、数分）。rsync は「キャッシュにない成果物が要るとき」の予備で、今回は要らない。main から複製した成果物は main の**現在の**ソース（1-4 後）に対応しており、worktree のソースと食い違う（差分 9 本がそれ）。`lake build` の trace 検査がモジュールごとに正しい版を復元するので、複製した `.lake/build` はそのまま置いて `lake build` を走らせればよい。
3. **main を先に取り込む**：`infra/if-w2b` は 85cb45f1a（1-4 前）から切ってある。**今 main（a682ec32b、1-4 を含む）を merge してから** before snapshot を取る。before ＝ merge 後の状態。1-4 は InfinityCategories を触っていない（Claude が確認）。KST・EInfinity・監査では 6 本（下の一覧）を触っているので、W2b が同じファイルの import 行を書き換える場合は merge で両方を残す。**下流ビルド（#10）の前にもう一度 main（DG-W3 取り込み後）を merge** し、内部ビルドと静的検査を再実行してから下流に入る（DG-W3 は DG の土台を 608 → 48 に統合するので、Derived・KST などの import 行が変わる）。
4. **再開**：main の merge → キャッシュから復元（`lake build` で before の対象の根）→ before snapshot v3b → R73 → R37 → R38 の適用（3 コミット）→ 内部ビルド → after snapshot → 保存比較 → **停止点 2**。
   1-4 が触った 6 本：
   - `scripts/audit/adams.lean`
   - `scripts/audit/shared.lean`
   - `scripts/audit_clmst.lean`
   - `scripts/audit_euler_betti_finite_support.lean`
   - `scripts/audit_euler_group_shared.lean`
   - `scripts/audit_triangulated_k0_shift_shared.lean`

### §7 の追記（2026-11-02 20:00）

4. `snapshot_batch.py` が v1 の `hash_algorithm` 名だけを検査するため、DG-W3 では実行時ラッパーで v3b の名前に合わせている。**現行の名前（`… proof-irrelevant v3b (term-level, proof marker)`）を受け付ける**ように直す（試験 1 件、別コミット）。
5. 判断表に「**束縛子の型の明示**」を加える（DG-W3 §9 で承認：省略した束縛子の型が、環境に新たに入った instance に捕まって別の型に推論されるとき、前の型を明示する。条件は宇宙の明示と同じ）。

## 14. 追記（2026-11-02 深夜、§5-3 の停止への回答：配置は宣言単位の依存で決め直し、補充は許される層の中で行う）

**受領**：main merge（408b0f05a、衝突なし）、復元 14 秒、before snapshot v3b 3,616 本（28 分）、R73・R37・R38 の適用（4d02ee532・d12e85d0e・9c38c984e）、適用後の静的検査 PASS（直接違反 294 → 18、中核の順序違反 0、禁止モジュール 1/166/166 → 0/150/150、archive 利用者 0、監査収録漏れ 0）、内部ビルド 1,128/1,899 まで進んで失敗 57 本、`SpecifiedApexConeRestrictions`（Core）が `SpecifiedApexLimitConeTransport`（F1）を型に使う。

**判断**：

1. **失敗 57 本の内訳**（Claude が `w2b-section13-stop.json` と `pending-imports.json` で確認）：unknown identifier 28、unknown namespace 15（Mathlib の `MonoidalCategory` など）、unknown constant 7（`SSet.Homotopy` など）、invalid field 4、failed to synthesize 2、型の不一致 1。いずれも **prune で落ちた import の補充**で直る型で、`proposals` の補充先は Mathlib と同じ層以下のモジュール。判断表の「補充の import」として**そのまま当ててよい**（禁止辺・上の層への辺にならないものに限る）。
2. **禁止辺になる 1 本**：`Core/FilteredExchange/SpecifiedApexConeRestrictions` の Core への配置が誤り。配置の規則（§9）が「直接 import の層の最大値」だったため、構造体の型を通じた依存（`SpecifiedApexLimitConeTransport.apex`・`.diagram`）を見落とした。**配置を F1（`F1/FilteredExchange/`）へ直す**（束の中の move。違反にならない）。
3. **配置の規則の最終形**：モジュール M の置き先は、**M の宣言が使う定数の定義元モジュール全部の層の最大値**（snapshot の `used_constants` → 定義元、推移的でなく直接の使用でよい）以上で最も低い層。直接 import だけで決めない。A の全モジュールと R37・R38 の split 先について**この規則で再計算し、食い違うものを補充の前に動かす**（補充が禁止辺になる事態をなくす）。再計算は snapshot のデータだけで済むのでビルド不要。
4. 補充の import は、置き先と同じ層以下と Mathlib・Foundation に限る。上の層が要るなら 3 で置き先を上げる。禁止領域（KST・DG・EInfinity・モデル圏の HA・Derived・ModelBridge）が要るなら止める（§5-3 はこの場合だけ）。

**再開**：3 の再計算と配置の修正（別コミット「配置の修正」）→ 補充の import（別コミット「補充」、件数と一覧）→ 内部ビルドの続き（残り 771 対象＋失敗 57 本）→ after snapshot v3b → 保存比較 → **停止点 2**（配置修正・補充・修飾などの件数、round の表、静的指標の前後）。

## 15. 追記（2026-11-03 11:00、main（DG-W3）取り込み後の設定ハッシュ不一致への回答）

**受領**：main の merge d135a715f（import の衝突 2 件は両方を保持）、`--report` は中核の順序違反 0・直接違反 18・禁止 0/150/150 で増加なし、`--enforce W2b` は基準の設定ハッシュ不一致で終了コード 2（DG-W3 が `layers.json` の PerfectComplex の例外 3 辺を削除したため）。

**承認**：処置案どおり。`layers.json` の変更は承認済みの束（DG-W3）による**例外の削除＝規則の強化**なので、基準の**設定ハッシュだけ**を現在の `layers.json` に合わせて更新し、承認済みの辺（直接の禁止辺 21 本の上限）と数値（禁止モジュール数・affected core）はそのまま。更新はコミット「ratchet 基準の設定ハッシュ」として記録し、DG-W3 の変更内容（例外 3 辺の削除、DG 層の tier）を注記する。

**再開**：鍵 → 内部ビルドの続き 857 本 → after snapshot v3b → 保存比較 → 停止点 2。

## 16. 追記（2026-11-03 14:30、§5-6 の停止への回答：進捗は「未検証の根」で測る）

**受領**：round 2 失敗 51（857 根、2 時間 9 分）→ round 3 失敗 12（152 根、17 分）→ round 4 失敗 13（60 根、36 分。83 根のうち 14 根は依存先の失敗で未検証、9 根は未実行）。前回の 12 本のうち 10 本は成功、KST 2 本は未確認。13 本はすべて**新たに表面化**した失敗（Claude が停止記録で確認：unknown identifier 11・unknown constant 1・invalid field 1。すべて補充で直る型）。`--enforce W2b` PASS、禁止 0/150/150、affected core 2,532（上限 3,379 内）、監査収録漏れ 0、archive 照合 差分 0。再開リストの漏れ 86 本を検証範囲に戻した。

**§5-6 の精密化**（以後の束でも有効）：補充の round の進捗は失敗モジュールの総数ではなく、(a) **前 round で補充したモジュールが再び落ちていないこと**、(b) **未検証の根（依存先の失敗で遮られた根＋未実行の根）の数が減っていること**で測る。前の失敗に遮られて初めてビルドされたモジュールの新しい失敗は、進捗の証拠であって停止理由ではない。止めるのは、(a) 補充したモジュールが次の round でも同じ型で落ちる、(b) 未検証の根が 2 round 続けて減らない、のどちらか。

**再開**：13 本に補充（別コミット「補充（round 5）」）→ round 5（未検証 23 根＋13 本の利用者）→ 以後同じ規則で収束まで → after snapshot v3b → 保存比較 → **停止点 2**（round の表に「未検証の根」の列を加える）。停止点 2 の報告の後に新しいチャットへ移る（[再開文](infinity-codex-w2b-restart.md)）。

## 17. 追記（2026-11-03 16:40、停止点 2 の承認と、下流〜停止点 3 の条件付き事前承認。以後は新しいチャット）

**承認**：内部ビルド 8 round で PASS（§16 の基準：再発 0、未検証の根 771 → 0。snapshot 対象 1,928 本と直接利用者 31 本を検証、未検出 3 辺の削除も確認）。保存比較は 1,928 本の after snapshot（22 分）で生の差 43 宣言・49 件がすべて個別照合で一致（型・本体・公理が通常表示で一致。暗黙引数つきでは `ReflQuiver.toQuiver`／`catToReflQuiver` と `CategoryStruct.toQuiver`／`Category.toCategoryStruct` の対応＝instance の経路の差で、reducible な instance の展開で定義的に等しい）。未説明 0。`--enforce W2b` PASS（直接違反 294 → 18、中核層間の順序違反 266 → 0、禁止 1/166/166 → 0/150/150、affected core 11/3,379 → 0/2,532）。§12 の個別 12 指標は承認済み草案と同数で、6 根の経路は W2c への入力として記録済み。A 368・B 1,726・C 33、監査 405 本、archive 照合 差分 0。§16 の Lean 変更は import 27 行（26 モジュール）。記録 a6ff3946a。

**次（新しいチャットで。[再開文](infinity-codex-w2b-restart.md)）**：
1. main を merge（11-03 夕の main。BS の docs と論文の層の docs だけで Lean の変更はないはず。あれば両方を残す）→ 静的検査（`--report`・`--enforce W2b`）の再実行。
2. **下流の一回ビルド（13,149 本、鍵のもと）**：Claude の合図を待つ。round の記録は §16 の基準（再発・未検証の根）で、失敗は判断表（補充・修飾・宇宙・束縛子の型・局所 instance・heartbeat。DG-W3 §11 と同じく ∞ の外のファイルでも最小の行で）。
3. **条件付き事前承認（DG-W3 §10 と同じ）**：下流が通り、全体の保存比較 v3b で未説明の不一致が 0（個別照合で説明できるものは説明済み）で、処置が判断表の範囲だけなら、Claude の承認を待たずに層検査（`--enforce W2b` の 3 条件、ratchet 基準の取り直し）→ 監査の再生成の確認（`audit_infinity_f2_exchange` の削除、A・C の監査）→ verify（`VERIFY_JOBS=6 VERIFY_MEMORY_GB=40`）まで進み、**停止点 3** にまとめて報告する。条件を満たさなければ止める。
4. 停止点 3 の報告：verify の summary、ルート閉包とビルド時間の前後、層検査の前後、処置の件数と一覧、W2c への入力（180 本と 6 根の経路）、コミット一覧。取り込みは Claude。

## 18. 追記（2026-11-03 夜、verify の失敗 5 本への回答：F1B の straightening 禁止は入口の閉包全体に適用、監査は移動に追従させる）

**事実（Claude が 11-03 夜に確認）**：
- straightening の禁止は `audit_infinity_f1b.lean`（F1B の入口の閉包全体に「straightening 系モジュールがあれば拒否」）と、`audit_infinity_f1b`・`audit_infinity_core` の Ind-S の保護対象（特定のモジュール一覧）にある。**W2b 前の main では F1B の入口だけが straightening 非依存**で、F2・F2.Ind・F2.Compact・F2.Presentable・Stable・HomotopyLimits の入口はもともと straightening に依存していた。Ind-S の保護対象 5 本は W2b 後も非依存。
- W2b 後に F1B の入口の閉包へ straightening を持ち込んでいるのは **W2b で F1B に置いた 18 本**（R38 の下ろし 8 本：`F1B/Ind/*`・`F1B/Compact/*`・`F1B/Idempotent/*`、R73 の A の配置 10 本：`F1B/FilteredExchange/*`）。F1B に元からある 2 本（`ConstantEdgeFamily`・`Roof/RightFibrationTerminalRepresentation`）も straightening に届くが、入口の閉包には入っていない（従来どおり。W2c か段 F で扱う）。
- 他の 4 本の失敗：`audit_f2_pi_criterion`（PiCriterion が Derived へ移ったので対象 0）、`audit_homotopy_limits`（`finiteCoherentProjectionCoconeIso` が R38 で F2/Presentable へ上がり、HL の監査から見えない）、`audit_infinity_f2`（`coreMap_trivialKanFibration` などが下の層へ下り、F2 の監査の閉包から外れた）、`audit_infinity_stable`（`Stable.ColimitFamilyExtension` が R37 で下り、モジュール一覧と `#check` が古い）。いずれも**監査が移動に追従していない**だけ。

**判断**：
1. **F1B の straightening 禁止は入口の閉包全体に適用する**（監査の定義どおり。W2b 前の状態を保つ）。監査は変えない。したがって **18 本を F1B から F1 へ配置し直す**（同じ tier なので HL・Stable の利用者からの import はそのまま成り立ち、R37・R38 の目的（逆向きの辺の解消）は保たれる。F1 は straightening を含む層なので禁止に触れない）。置き先は `F1/Ind/`・`F1/Compact/`・`F1/Idempotent/`・`F1/FilteredExchange/`（名前空間は変えない）。**配置の規則に追加**：straightening に依存するモジュールは F1B に置かない（F1 へ）。
2. **監査の追従（承認。検査を弱めない）**：(a) `audit_f2_pi_criterion` は対象を `Derived.PiCriterion.*` に向け直す（置き場所に合わせて `audit_derived_*` へ統合してもよい）。(b) 移動した宣言の `#check` 行とモジュール一覧は、移動先の領域の監査へ移す（HL → F2/Presentable の分は `audit_infinity_f2` へ、F2 → F1B/F1 の分は `audit_infinity_f1b`／`audit_infinity_f1` へ、Stable → F1B の分は `audit_infinity_f1b` へ）。宣言の数は前後で一致させ、報告に表を付ける。
3. 手順：配置の修正（別コミット「配置の修正（F1B → F1）」）→ 18 本と直接の利用者の小さなビルド → 影響モジュールの after snapshot v3b と比較（型・本体の一致）→ 監査の追従（別コミット「監査の追従」）→ `layer_check --report`・`--enforce W2b`（変化なしのはず）→ **verify を再実行**（通った 94 本はキャッシュで省略される見込み）→ **停止点 3**。§17-3 の条件付き事前承認はそのまま有効。
