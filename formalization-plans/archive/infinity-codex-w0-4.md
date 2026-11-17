# Codex 作業指示書 IF-W0-4：基盤の層の登録と、verify runner のメモリ予算つき並列化

作成：2026-11-01（∞ 基盤の整備、管理は Claude）。宛先：∞ の Codex。**開始は、W1＋W2a の束が main に入った後**（[coordination.md](../coordination.md) §3 の #3 の後）に Claude が合図する。
計画：[infinity-foundation-plan.md](stage-i/infinity-foundation-plan.md) §6 の IF-W0-4 行（10-31 改訂）、R67（Coxeter の登録）、R77 の前提。伝達文 [handover §1・§3・§6](stage-i/handover-ct-to-infinity-2026-10-30.md)。
**共通の前提**：[IF-W0-1](infinity-codex-w0-1.md) §0。worktree は `../SerrePositivity-ifw0-3` をそのまま使い、束の取り込み後の main から `infra/if-w0-4` を切る。
ビルドを伴う作業はほぼない（verify の試験実行 1 回だけ。§4）。止めて報告する点は 2 か所（§5）。

## 1. 目的

| 項目 | 内容 |
| --- | --- |
| A | `layers.json` に**基盤の層（Foundation）**を加える：CategoryTheory の一般部分（下位ディレクトリ Monoidal・Enriched・Limits・Quiver・Simplex・Under と、トップ階層で ∞ 側だけが使う 12 本）と GroupTheory/Coxeter。中核より下に置き、基盤は Mathlib と基盤しか import できないことを検査する |
| B | `verify_runner.py` を**メモリ予算つき**で並列化する：監査ごとの最大 RSS と所要時間を記録し、次回は長い順に、予算（既定 45 GB）に収まる範囲で最大 `VERIFY_JOBS`（既定を 3 → 6）本を同時に走らせる。狙いは監査の実時間 30 分 → 15 分 |

## 2. 所有範囲

- `scripts/refactor/layers.json`、`scripts/refactor/layer_check.py`（基盤の層の規則に必要な分だけ）、`scripts/refactor/test_layer_check.py`。
- `scripts/refactor/verify_runner.py`、`scripts/refactor/verify.sh`（既定値と環境変数の受け渡しだけ）、`scripts/refactor/test_verify.py`、`scripts/refactor/README.md`。
- DG 側が作った `merge_modules.py`・`with_build_lock.sh`・`warm_build_dir.sh`（main に入っていれば）は変更しない。Lean のソースは変更しない。

## 3. A：基盤の層

1. **層の定義**：`layers.json` の `layers` に `{"name": "Foundation", "rank": -1, "prefixes": [...]}` を加える（`rank` が負でも `layer_check.py` が扱えるようにする。負を許さない作りなら全体を 1 ずらす）。`prefixes`：
   - `SerrePositivity.CategoryTheory.Monoidal`、`.Enriched`、`.Limits`、`.Quiver`、`.Simplex`、`.Under`（伝達文 §1 の下位ディレクトリ。`Presentation` は R75 で削除済み）。
   - トップ階層の 12 本（計画 R77：AdjunctionHomLaws・CommaIdentities・FiniteBijection*4・FiniteBlockEquiv・FunctorTransport・ParametrizedAdjunctionTransport・PointwiseAdjunction・RelativeArrow）。接頭辞の区切りは最長一致（§10.3 の規則）なので、ファイル名で個別に書く。
   - `SerrePositivity.GroupTheory.Coxeter`（R67：動かさず登録）。
   - 論文の層の側の CategoryTheory（Abelian・Karoubi・TStructure・Triangulated・Groupoid・LiftingProperties・MorphismProperty のうち上に入れないもの、トップ階層の残り）は入れない。
2. **規則**：`restricted_imports` に `Foundation` を加え、基盤のモジュールが import してよいのは Mathlib と基盤だけ、とする。中核（`core`）の各層は基盤を import してよい（rank の順序で自然に許される）。
3. **現状の違反**：`layer_check.py --report` で、基盤が基盤の外（HotA・InfinityCategories・EInfinity・KST・論文の層）を import している辺を数えて報告に書く。R76（Nerve まわり 9 本を HotA へ）が未実施なら CategoryTheory ↔ HotA の相互依存が残るはずで、それは IF-W2a-2 で解消する。**ここでは `--ratchet` の基準を取るだけ**（増えないことの検査を次から有効にする）。
4. 試験：`test_layer_check.py` に、負の rank、基盤の restricted_imports、基盤 → 中核の import が違反になること、中核 → 基盤が許されることを加える。

## 4. B：メモリ予算つき runner

1. **計測**：各監査を `/usr/bin/time -l` 経由で起動し（`-o <file>` で time の出力を別ファイルへ。監査の出力はキャッシュの鍵の一部なので混ぜない）、`maximum resident set size` と所要時間を記録する。記録先は追跡しない `.lake/verify/audit-stats.json`（監査のパス → `{"seconds", "max_rss_bytes", "measured_at", "commit"}`、最新値だけ）。`summary.json` の各 audit 段にも `max_rss_bytes` を出す。
2. **並べ方**：`audit-stats.json` の所要時間の降順（未記録は先頭、未記録の RSS は 20 GB と仮定）。
3. **予算**：環境変数 `VERIFY_MEMORY_GB`（既定 45）。実行中の監査の RSS（記録値）の合計＋次の監査の RSS が予算を超えるなら待つ。同時実行の上限は `VERIFY_JOBS`（既定を 6 に変更。1 なら直列）。`ThreadPoolExecutor` の固定プールではなく、空きができるたびに条件を満たす先頭の監査を起動する簡単なスケジューラにする。
4. **安全**：記録値より実測が大きかった監査は次回から実測値を使う。環境の失敗（§10.9）の直列再試行は残す。`VERIFY_JOBS=3`・予算なし（`VERIFY_MEMORY_GB=0`）で従来どおりに動くこと。
5. **gate**：並列数と予算は合否に関係しない（従来どおり gate:true）。README の「窓の合否は VERIFY_JOBS=3 で」を「既定の並列数（6）と予算（45 GB）で」に改める。
6. 試験：`test_verify.py` に、模擬の監査（sleep と RSS の記録値）で (a) 長い順に起動する、(b) 予算で待つ、(c) 未記録を先頭に置く、(d) `VERIFY_JOBS=1` で直列、を加える。
7. **実行の確認（ビルドなし）**：`VERIFY_CACHE=1 zsh scripts/refactor/verify.sh`（gate:false）を一度走らせ、キャッシュに当たらない監査だけが新しい並べ方で走ることと、`audit-stats.json` が埋まることを確かめる。全監査の計測値がそろうのは次の gate 実行（束の verify）のとき。

## 5. 受入条件と報告

1. Python 試験が全部 PASS。`zsh -n scripts/refactor/verify.sh`。
2. `layer_check.py --report` が Foundation を含めて動き、`--ratchet` の基準が保存される。基盤の現状の違反数を報告。
3. §4-7 の実行の summary（並べ方・待ち・RSS の記録）を報告。
4. コミットは「層の登録」「runner」「試験・README」の 3 本。`git commit --only`。
5. 止めて報告する点：(1) §3 の後（基盤の接頭辞の一覧と違反数）、(2) §4-7 の後。

## 6. 禁止事項

- Lean のソースの変更。DG 側の道具の変更。
- 全ビルド（ルート・監査対象）。§4-7 の verify も `VERIFY_CACHE=1` で、他の全ビルドがないことを確かめてから。

## 7. 追記（2026-11-02、§3 の承認と Foundation の範囲の補正、§4-7 の実行の仕方）

**承認**：Foundation（rank −1、19 接頭辞・99 本）、試験 177 件 PASS、ratchet 基準の保存。

1. **Foundation の範囲を補正する**：違反 1 辺 `CategoryTheory.FiniteBijectionInduction → CategoryTheory.Groupoid.ThinComponents` は、`Groupoid/ThinComponents` が伝達文 §3.2 の統合案で `Limits` に入る一般部分だから。**R77 の統合案（伝達文 §3.2 の表）の元になるモジュールはすべて Foundation** とする：`CategoryTheory.Groupoid.ThinComponents`、`CategoryTheory.LiftingProperties.Under`・`.ParametrizedGeneration`、`CategoryTheory.MorphismProperty.UnderFactorization`（表に出てくる分。`Abelian`・`Karoubi`・`TStructure`・`Triangulated` と、表にないトップ階層は入れない）。接頭辞ではなくモジュール名で個別に書く。補正後に違反 0 になることを確かめ、ratchet の基準を取り直す。Nerve 系の相互依存（R76）は IF-W2a-2 で解消するので今は範囲外のまま。
2. **§4-7 の実行**：`VERIFY_CACHE=1` でもビルド 2 段（ルート・監査対象）は走るが、Lake キャッシュがあるので**再生と復元だけで数分**で終わる見込み。これは §6 の「全ビルド」の禁止（何時間もかかる再コンパイル）に当たらない。100 本を超えるモジュールの再コンパイルが始まったら止めて報告する。
3. 道具（`verify_runner.py`・`verify.sh`）を変えると監査キャッシュの鍵が変わって全監査が未命中になる——それでよい。むしろ**新しい runner の実測**になるので、`VERIFY_CACHE` なしで `VERIFY_JOBS=6 VERIFY_MEMORY_GB=45 zsh scripts/refactor/verify.sh`（gate:true）を一度走らせ、全 100 本の RSS と時間を `audit-stats.json` に記録する。これが 2 回目の停止点の報告になる（実時間、並べ方、待ちの発生、最大同時 RSS）。
4. **機械の規則**：この verify は DG-W2(b) の下流ビルドや verify と**重ねない**。`ps -axo command= | grep '[l]ake build'` と `with_build_lock.sh` の鍵を確かめ、DG が走っていれば終わるまで待つ（DG の下流ビルドは 2〜3 時間、verify は 1 時間）。
